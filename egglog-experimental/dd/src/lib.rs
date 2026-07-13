//! # egglog-experimental-dd
//!
//! A differential-dataflow-backed implementation of egglog's
//! [`egglog_backend_trait::Backend`] interface.
//!
//! One `run_rules` call is one bounded egglog iteration. Each rule's body
//! table-atom join runs on an in-process differential-dataflow dataflow
//! (`dd_native`); body primitives and head actions are applied
//! host-side (`interpret`) into a Rust-side materialized mirror of every
//! relation. `for_each` / `lookup_id` / `table_size` read that mirror.
//!
//! ## Why this is a DD backend
//!
//! This crate constructs Timely and Differential Dataflow operators directly;
//! it does not compile through a higher-level dataflow language or runtime. That
//! keeps this prototype focused on the backend SPI and the costs of persistent
//! incremental joins. Evaluating a higher-level compiler/runtime, including its
//! tuple generation, planning, and stratification choices, would be a separate
//! backend experiment rather than an interchangeable implementation detail here.

use std::{
    any::{Any, TypeId},
    sync::{Arc, Mutex},
};

use anyhow::{anyhow, bail, Result};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_backend_trait::{
    Backend, BaseValues, ColumnTy, ContainerMergeFn, ContainerValues, CounterId, DefaultVal,
    ExecutionState, ExternalFunction, ExternalFunctionId, FunctionConfig, FunctionId,
    IterationReport, MergeFn, ReportLevel, RuleActionCall, RuleBodyCall, RuleId, RuleSetRun,
    RuleSpec, RuleValue, RuleVar, ScanEntry, Value,
};
use egglog_core_relations::Database;
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};

mod compile;
mod dd_native;
mod interpret;

use compile::{MergeMode, MergeTree, ReadKey, Row};

type LocatedValue = (u32, RowLocation);
type RowReplacement = (Box<[u32]>, LocatedValue);

mod dd_workers {
    use hashbrown::HashMap;

    use crate::dd_native;

    /// Owns the single-threaded Timely workers behind an exclusive-access
    /// boundary. The worker map is private to this module, and every accessor
    /// requires `&mut self`, so immutable backend operations cannot touch
    /// Timely's `Rc`/`RefCell` state.
    #[derive(Default)]
    pub(super) struct DdWorkers {
        inner: HashMap<Vec<usize>, dd_native::FusedDdJoin>,
    }

    impl DdWorkers {
        pub(super) fn contains_key(&mut self, key: &[usize]) -> bool {
            self.inner.contains_key(key)
        }

        pub(super) fn insert(&mut self, key: Vec<usize>, value: dd_native::FusedDdJoin) {
            self.inner.insert(key, value);
        }

        pub(super) fn get(&mut self, key: &[usize]) -> Option<&dd_native::FusedDdJoin> {
            self.inner.get(key)
        }

        pub(super) fn get_mut(&mut self, key: &[usize]) -> Option<&mut dd_native::FusedDdJoin> {
            self.inner.get_mut(key)
        }

        pub(super) fn retain(&mut self, mut keep: impl FnMut(&Vec<usize>) -> bool) {
            self.inner.retain(|key, _| keep(key));
        }

        #[cfg(test)]
        pub(super) fn is_empty(&mut self) -> bool {
            self.inner.is_empty()
        }
    }

    // SAFETY: `FusedDdJoin` does not expose or clone its Timely handles outside
    // this private owner. Moving `DdWorkers` moves every related handle together,
    // and the only worker accessors require `&mut self`. In particular, `Sync`
    // cannot be used to reach Timely state through a shared reference.
    unsafe impl Send for DdWorkers {}
    unsafe impl Sync for DdWorkers {}
}

use dd_workers::DdWorkers;

// ---------------------------------------------------------------------------
// Relation metadata
// ---------------------------------------------------------------------------

/// What we remember about each registered relation/function.
#[derive(Clone)]
pub(crate) struct RelationInfo {
    name: String,
    /// Number of columns (including the output column for functions).
    pub(crate) arity: usize,
    /// Whether RHS lookups may create a fresh output row on miss.
    pub(crate) lookup_mints: bool,
    /// How functional-dependency conflicts are resolved.
    pub(crate) merge: MergeMode,
    /// The evaluatable merge tree, when `merge` is [`MergeMode::Computed`].
    pub(crate) merge_tree: Option<MergeTree>,
}

// ---------------------------------------------------------------------------
// EGraph
// ---------------------------------------------------------------------------

/// The experimental differential-dataflow-backed egraph.
pub struct EGraph {
    relations: Vec<RelationInfo>,
    /// Rule slots; `None` = freed.
    pub(crate) rules: Vec<Option<RuleSpec>>,
    /// Rust-side materialized mirror: the accumulated contents of each relation.
    /// This is what `for_each` / `lookup_id` / `table_size` read.
    ///
    pub(crate) mirror: HashMap<FunctionId, HashSet<Row>>,
    /// Subsumed rows, moved OUT of `mirror` by `(subsume …)` (a "soft delete").
    /// Ordinary [`egglog_backend_trait::ReadMode::Live`] queries read only
    /// `mirror`, so subsumed rows are excluded for free; include-subsumed rules
    /// and `for_each` read `mirror` union `subsumed`. Keyed like `mirror`, by
    /// `FunctionId`.
    pub(crate) subsumed: HashMap<FunctionId, HashSet<Row>>,
    /// A core-relations [`Database`] used purely as the base-value / primitive
    /// engine, so `Value`s are bit-for-bit identical to the reference backend.
    db: Database,
    /// Monotonic fresh-id counter for `fresh_id` / `add_term`.
    pub(crate) next_id: u32,
    /// Atom-less rules (`(rule () …)`) fire ONCE; an entry here marks a rule
    /// index as already fired. The DD dataflow has no input relation to drive an
    /// atom-less body, so this fired-marker is the one piece of seminaive
    /// bookkeeping the DD path reuses (see `interpret::fused_bindings`).
    /// `free_rule` removes the entry so a re-installed rule can fire again.
    pub(crate) seen: HashMap<usize, ()>,
    /// Per-RULESET fused DD join (one shared timely worker + one dataflow for the
    /// whole ruleset), keyed by the sorted live rule-index list. This is the
    /// join path the interpreter drives.
    pub(crate) dd_fused: DdWorkers,
    /// Monotone version assigned whenever a row becomes visible in one of the
    /// DD read views. This stands in for the reference backend's hidden
    /// timestamp: removing and reinserting the same row gives it a fresh version,
    /// so seminaive rules can fire on it again.
    pub(crate) next_row_version: u64,
    pub(crate) live_versions: HashMap<FunctionId, HashMap<Row, u64>>,
    pub(crate) all_versions: HashMap<FunctionId, HashMap<Row, u64>>,
    pub(crate) subsumed_versions: HashMap<FunctionId, HashMap<Row, u64>>,
    /// Per-ruleset, per-function version snapshot last fed to the fused DD join.
    pub(crate) dd_fused_fed_versions: HashMap<Vec<usize>, HashMap<ReadKey, HashMap<Row, u64>>>,
    /// Deferred error channel used by panic primitives. The embedded database's
    /// cloned external functions share this channel, matching the reference
    /// bridge's panic-function behavior.
    panic_message: Arc<Mutex<Option<String>>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowLocation {
    Live,
    Subsumed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CurrentValue {
    value: u32,
    location: RowLocation,
    rows_for_key: usize,
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl EGraph {
    /// Construct a fresh Differential Dataflow backend. Rule bodies run on the
    /// in-process DD join; body primitives and head actions are applied
    /// host-side into the mirror. Pass this backend to
    /// `egglog::EGraph::with_backend` through the frontend integration crate.
    pub fn new() -> Self {
        let mut db = Database::new();
        // Pre-register the `()` (Unit) base type so `add_table`'s relation-vs-
        // function detection can always resolve the Unit `BaseValueId`.
        // `register_type` is idempotent, so a later frontend registration is a
        // no-op that returns the same id.
        db.base_values_mut().register_type::<()>();
        EGraph {
            relations: Vec::new(),
            rules: Vec::new(),
            mirror: HashMap::new(),
            subsumed: HashMap::new(),
            db,
            // Start at 1 so id 0 stays a "null"/padding sentinel.
            next_id: 1,
            seen: HashMap::new(),
            dd_fused: DdWorkers::default(),
            next_row_version: 1,
            live_versions: HashMap::new(),
            all_versions: HashMap::new(),
            subsumed_versions: HashMap::new(),
            dd_fused_fed_versions: HashMap::new(),
            panic_message: Default::default(),
        }
    }

    pub(crate) fn info(&self, f: FunctionId) -> &RelationInfo {
        self.relations
            .get(f.rep() as usize)
            .unwrap_or_else(|| panic!("FunctionId({}) not registered", f.rep()))
    }

    /// Relation name for `f`, used in diagnostics and unsupported-shape errors.
    pub(crate) fn relation_name(&self, f: FunctionId) -> &str {
        &self.info(f).name
    }

    /// Validate the backend-facing rule form once, before assigning a rule id.
    /// The DD backend retains the accepted [`RuleSpec`] directly; this pass does
    /// not introduce a second rule IR.
    fn validate_rule(&self, rule: &RuleSpec) -> Result<()> {
        let validate_terms =
            |terms: &[GenericAtomTerm<RuleVar, RuleValue>], location: &str| -> Result<()> {
                if let Some(GenericAtomTerm::Global(_, global)) = terms
                    .iter()
                    .find(|term| matches!(term, GenericAtomTerm::Global(..)))
                {
                    bail!(
                        "DD backend cannot add rule {:?}: residual global {:?} in {location}",
                        rule.name,
                        global.name
                    );
                }
                Ok(())
            };
        let relation = |id: FunctionId, location: &str| -> Result<&RelationInfo> {
            self.relations.get(id.rep() as usize).ok_or_else(|| {
                anyhow!(
                    "DD backend cannot add rule {:?}: unregistered FunctionId({}) in {location}",
                    rule.name,
                    id.rep()
                )
            })
        };

        for atom in &rule.core.body.atoms {
            match atom.head {
                RuleBodyCall::Table { id, .. } => {
                    if atom.args.len() > dd_native::W {
                        bail!(
                            "DD backend cannot add rule {:?}: body table atom has {} columns, exceeding fixed row width {}",
                            rule.name,
                            atom.args.len(),
                            dd_native::W
                        );
                    }
                    let info = relation(id, "rule body")?;
                    if atom.args.len() != info.arity {
                        bail!(
                            "DD backend cannot add rule {:?}: body table atom for {:?} has {} columns, but relation `{}` has arity {}",
                            rule.name,
                            id,
                            atom.args.len(),
                            info.name,
                            info.arity
                        );
                    }
                    validate_terms(&atom.args, "rule body")?;
                }
                RuleBodyCall::Primitive { .. } => {
                    if atom.args.is_empty() {
                        bail!(
                            "DD backend cannot add rule {:?}: body primitive has no return term",
                            rule.name
                        );
                    }
                    validate_terms(&atom.args, "rule body primitive")?;
                }
            }
        }

        for action in &rule.core.head.0 {
            match action {
                GenericCoreAction::Let(_, _, call, arguments) => {
                    validate_terms(arguments, "rule action")?;
                    if let RuleActionCall::Table { id, .. } = call {
                        let info = relation(*id, "table lookup action")?;
                        let Some(expected) = info.arity.checked_sub(1) else {
                            bail!(
                                "DD backend cannot add rule {:?}: cannot look up nullary relation `{}` as a function",
                                rule.name,
                                info.name
                            );
                        };
                        if arguments.len() != expected {
                            bail!(
                                "DD backend cannot add rule {:?}: lookup on `{}` has {} arguments, expected {}",
                                rule.name,
                                info.name,
                                arguments.len(),
                                expected
                            );
                        }
                    }
                }
                GenericCoreAction::LetAtomTerm(_, _, term) => {
                    validate_terms(std::slice::from_ref(term), "rule let action")?;
                }
                GenericCoreAction::Set(_, call, arguments, value) => {
                    let RuleActionCall::Table { id, .. } = call else {
                        bail!(
                            "DD backend cannot add rule {:?}: cannot set a primitive",
                            rule.name
                        );
                    };
                    validate_terms(arguments, "rule set action")?;
                    validate_terms(std::slice::from_ref(value), "rule set action")?;
                    let info = relation(*id, "set action")?;
                    if arguments.len() + 1 != info.arity {
                        bail!(
                            "DD backend cannot add rule {:?}: set on `{}` writes {} columns, expected {}",
                            rule.name,
                            info.name,
                            arguments.len() + 1,
                            info.arity
                        );
                    }
                }
                GenericCoreAction::Change(_, _, call, arguments) => {
                    let RuleActionCall::Table { id, .. } = call else {
                        bail!(
                            "DD backend cannot add rule {:?}: cannot delete or subsume a primitive",
                            rule.name
                        );
                    };
                    validate_terms(arguments, "rule change action")?;
                    let info = relation(*id, "change action")?;
                    if arguments.len() > info.arity {
                        bail!(
                            "DD backend cannot add rule {:?}: change on `{}` addresses {} columns, exceeding arity {}",
                            rule.name,
                            info.name,
                            arguments.len(),
                            info.arity
                        );
                    }
                }
                GenericCoreAction::Union(..) => {
                    bail!(
                        "DD backend cannot add rule {:?}: received a native union; term encoding must lower unions to @uf writes",
                        rule.name
                    );
                }
                GenericCoreAction::Panic(..) => {}
            }
        }

        Ok(())
    }

    /// The functional-dependency merge mode of a function (from `add_table`).
    pub(crate) fn merge_mode(&self, f: FunctionId) -> MergeMode {
        self.info(f).merge
    }

    /// Evaluate a primitive through the embedded `Database` (the base-value /
    /// primitive engine). Both the host interpreter and the DD join's
    /// host-side primitive phase call this, so `Value`s are bit-for-bit
    /// identical to the reference backend.
    pub(crate) fn eval_prim_internal(
        &self,
        id: ExternalFunctionId,
        args: &[Value],
    ) -> Result<Option<Value>> {
        let result = self
            .db
            .with_execution_state(|st| st.call_external_func(id, args));
        if let Some(message) = self.take_panic_message() {
            Err(anyhow!(message))
        } else {
            Ok(result)
        }
    }

    fn take_panic_message(&self) -> Option<String> {
        self.panic_message
            .lock()
            .expect("DD panic-message side channel must not be poisoned")
            .take()
    }

    /// Allocate a fresh id (the interpreter's eq-sort constructor hash-cons uses
    /// the same counter the trait's `fresh_id` advances).
    pub(crate) fn fresh_id_internal(&mut self) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Apply this iteration's `set`s to a merge function `f`, folding each new
    /// output value against the current value for its key by the merge mode.
    /// Returns whether the mirror changed.
    ///
    /// `rows` is in EMISSION order, so the fold is insertion-order-correct: the
    /// pre-set mirror value is the "old" value and each `rows` entry is a "new"
    /// value applied in turn (`New` keeps the last, `Old` keeps the first/existing,
    /// `Min` keeps the smallest, `Computed` evaluates the retained merge tree).
    /// Current rows are read from live ∪ subsumed state, matching the reference
    /// backend's single-table representation with a merged subsumed bit. A later
    /// `set` of a subsumed key must merge with that row and remain subsumed; it
    /// must not resurrect the row into ordinary matching.
    pub(crate) fn apply_merge_sets(&mut self, f: FunctionId, rows: &[Row]) -> Result<bool> {
        if matches!(self.merge_mode(f), MergeMode::Computed) {
            return self.apply_computed_merge(f, rows);
        }
        let arity = self.info(f).arity;
        let merge = self.merge_mode(f);
        let inputs_len = arity - 1;
        let mut cur = self.current_values_by_key(f, inputs_len);
        // Fold new values in emission order, remembering each touched key's
        // original value so the stale row can be retracted.
        let mut orig: HashMap<Box<[u32]>, Option<CurrentValue>> = HashMap::new();
        for row in rows {
            let key: Box<[u32]> = row[..inputs_len].into();
            let nv = row[inputs_len];
            let existing = cur.get(&key).copied();
            orig.entry(key.clone()).or_insert(existing);
            let existing_value = existing.map(|current| current.value);
            let merged = match (existing_value, merge) {
                (None, _) => nv,
                (Some(_), MergeMode::New) => nv,
                (Some(c), MergeMode::Old) => c,
                (Some(c), MergeMode::Min) => c.min(nv),
                // Relation is filtered by the caller; Computed took the branch above.
                (Some(c), MergeMode::Relation | MergeMode::Computed) => c,
            };
            let location = existing
                .map(|current| current.location)
                .unwrap_or(RowLocation::Live);
            let rows_for_key = existing.map(|current| current.rows_for_key).unwrap_or(0);
            cur.insert(
                key,
                CurrentValue {
                    value: merged,
                    location,
                    rows_for_key,
                },
            );
        }
        // Apply the net change per touched key. The initial scan above also
        // counted duplicate rows, so normalization does not need another full
        // relation scan for every key.
        let mut replacements = Vec::new();
        for (key, old) in orig {
            let current = cur[&key];
            let new = (current.value, current.location);
            let already_normalized =
                old.is_some_and(|old| old.rows_for_key == 1 && (old.value, old.location) == new);
            if !already_normalized {
                replacements.push((key, new));
            }
        }
        Ok(self.replace_located_rows(f, inputs_len, replacements))
    }

    /// The [`MergeMode::Computed`] case of [`apply_merge_sets`]: fold each key's
    /// conflicting values by EVALUATING the retained [`MergeTree`] (a primitive
    /// like `(or old new)`, or a constructor that builds a term). Evaluation needs
    /// `&mut self` (host-side primitive calls, e-node minting), so — unlike the
    /// scalar path — it gathers the candidate values first, then reconciles the
    /// mirror after the fold.
    fn apply_computed_merge(&mut self, f: FunctionId, rows: &[Row]) -> Result<bool> {
        let inputs_len = self.info(f).arity - 1;
        let next_id_before = self.next_id;
        let cur = self.current_values_by_key(f, inputs_len);
        // Group new values by key in emission order.
        let mut order: Vec<Box<[u32]>> = Vec::new();
        let mut newv: HashMap<Box<[u32]>, Vec<u32>> = HashMap::new();
        for row in rows {
            let key: Box<[u32]> = row[..inputs_len].into();
            let v = row[inputs_len];
            match newv.get_mut(&key) {
                Some(vs) => vs.push(v),
                None => {
                    order.push(key.clone());
                    newv.insert(key, vec![v]);
                }
            }
        }
        // The merge tree, cloned out so the evaluator can borrow `&mut self`.
        let tree = self.info(f).merge_tree.clone().ok_or_else(|| {
            anyhow!(
                "DD relation metadata invariant: computed merge for `{}` has no merge tree",
                self.relation_name(f)
            )
        })?;
        let mut lookup_index: HashMap<FunctionId, HashMap<Box<[u32]>, u32>> = HashMap::new();
        // Fold each touched key: start from the current value, fold in each new
        // value via the tree (`old` = accumulator, `new` = the value).
        let mut updates: Vec<RowReplacement> = Vec::new();
        for key in order {
            let old = cur.get(&key).copied();
            let location = old
                .map(|current| current.location)
                .unwrap_or(RowLocation::Live);
            let mut acc = old.map(|current| current.value);
            for &nv in &newv[&key] {
                acc = Some(match acc {
                    None => nv,
                    Some(c) => self.eval_merge_tree(&tree, c, nv, &mut lookup_index)?,
                });
            }
            let new_val = acc.expect("DD computed-merge invariant: touched key has a value");
            let new = (new_val, location);
            if Some(new) != old.map(|old| (old.value, old.location)) {
                updates.push((key, new));
            }
        }
        // Reconcile the mirror. A `Func` node that minted an e-node advanced
        // `next_id` — that is itself a real change even if no value flipped.
        let mut changed = self.next_id != next_id_before;
        changed |= self.replace_located_rows(f, inputs_len, updates);
        Ok(changed)
    }

    /// Evaluate a [`MergeTree`] against the two conflicting output values `old`
    /// (accumulated) and `new` (incoming), returning the merged value. Primitives
    /// run host-side via `eval_prim_internal`; a `Func` node hash-cons / mints a
    /// constructor e-node via `lookup_or_create`, so a merge that builds a term
    /// works.
    fn eval_merge_tree(
        &mut self,
        node: &MergeTree,
        old: u32,
        new: u32,
        index: &mut HashMap<FunctionId, HashMap<Box<[u32]>, u32>>,
    ) -> Result<u32> {
        match node {
            MergeTree::Old => Ok(old),
            MergeTree::New => Ok(new),
            MergeTree::Const(v) => Ok(*v),
            MergeTree::Prim(id, args) => {
                let argv: Vec<Value> = args
                    .iter()
                    .map(|a| self.eval_merge_tree(a, old, new, index).map(Value::new))
                    .collect::<Result<_>>()?;
                Ok(self
                    .eval_prim_internal(*id, &argv)?
                    .map(|v| v.rep())
                    .unwrap_or(old))
            }
            MergeTree::Func(func, args) => {
                let key: Vec<Value> = args
                    .iter()
                    .map(|a| self.eval_merge_tree(a, old, new, index).map(Value::new))
                    .collect::<Result<_>>()?;
                if self.info(*func).lookup_mints {
                    Ok(interpret::lookup_or_create(self, *func, &key, index).rep())
                } else {
                    interpret::lookup_existing(self, *func, &key, index)
                        .map(|value| value.rep())
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "lookup on `{}` failed in merge function",
                                self.relation_name(*func)
                            )
                        })
                }
            }
        }
    }

    /// Move every live row of `f` whose LEADING columns equal `prefix` into the
    /// `subsumed` side-set (a "soft delete"): the row stays in the table — still
    /// counted by `table_size`, still visible to `for_each` and to
    /// `:internal-include-subsumed` rules — but is hidden from ordinary query
    /// matching. Returns whether anything moved. The subsume action addresses a
    /// view row by its children+output columns (not the trailing epoch), hence a
    /// prefix match.
    pub(crate) fn subsume_rows(&mut self, f: FunctionId, prefix: &[u32]) -> bool {
        let Some(set) = self.mirror.get(&f) else {
            return false;
        };
        let moved: Vec<Row> = set
            .iter()
            .filter(|r| r.len() >= prefix.len() && r[..prefix.len()] == *prefix)
            .cloned()
            .collect();
        if moved.is_empty() {
            return false;
        }
        {
            let live = self
                .mirror
                .get_mut(&f)
                .expect("DD mirror invariant: rows selected for subsumption remain registered");
            for r in &moved {
                live.remove(r);
            }
        }
        for r in &moved {
            self.record_row_event(f, r.clone(), -1, 0, 1);
        }
        let subs = self.subsumed.entry(f).or_default();
        for r in moved {
            subs.insert(r);
        }
        true
    }

    pub(crate) fn insert_live_row(&mut self, f: FunctionId, row: Row) -> bool {
        if self
            .subsumed
            .get(&f)
            .is_some_and(|subsumed| subsumed.contains(&row))
        {
            return false;
        }
        let inserted = self.mirror.entry(f).or_default().insert(row.clone());
        if inserted {
            self.record_row_event(f, row, 1, 1, 0);
        }
        inserted
    }

    fn current_values_by_key(
        &self,
        f: FunctionId,
        inputs_len: usize,
    ) -> HashMap<Box<[u32]>, CurrentValue> {
        let live_len = self.mirror.get(&f).map(|set| set.len()).unwrap_or(0);
        let subsumed_len = self.subsumed.get(&f).map(|set| set.len()).unwrap_or(0);
        let mut cur = HashMap::with_capacity(live_len + subsumed_len);
        for (location, store) in [
            (RowLocation::Live, &self.mirror),
            (RowLocation::Subsumed, &self.subsumed),
        ] {
            if let Some(rows) = store.get(&f) {
                for row in rows.iter() {
                    let value = row[inputs_len];
                    let key: Box<[u32]> = row[..inputs_len].into();
                    cur.entry(key)
                        .and_modify(|current: &mut CurrentValue| {
                            current.value = value;
                            current.location = location;
                            current.rows_for_key += 1;
                        })
                        .or_insert(CurrentValue {
                            value,
                            location,
                            rows_for_key: 1,
                        });
                }
            }
        }
        cur
    }

    fn replace_located_rows(
        &mut self,
        f: FunctionId,
        keylen: usize,
        replacements: Vec<RowReplacement>,
    ) -> bool {
        if replacements.is_empty() {
            return false;
        }
        let keys = replacements.iter().map(|(key, _)| key.clone()).collect();
        self.remove_matching_keys(f, keylen, &keys);
        for (key, (value, location)) in replacements {
            let mut row = key.into_vec();
            row.push(value);
            self.insert_located_row(f, location, row.into_boxed_slice());
        }
        true
    }

    fn insert_located_row(&mut self, f: FunctionId, location: RowLocation, row: Row) -> bool {
        let store = match location {
            RowLocation::Live => &mut self.mirror,
            RowLocation::Subsumed => &mut self.subsumed,
        };
        let inserted = store.entry(f).or_default().insert(row.clone());
        if inserted {
            match location {
                RowLocation::Live => self.record_row_event(f, row, 1, 1, 0),
                RowLocation::Subsumed => self.record_row_event(f, row, 0, 1, 1),
            }
        }
        inserted
    }

    pub(crate) fn remove_matching_keys(
        &mut self,
        f: FunctionId,
        keylen: usize,
        keys: &HashSet<Box<[u32]>>,
    ) -> bool {
        let mut changed = false;
        let removed_live = remove_keys_from_store(&mut self.mirror, f, keylen, keys);
        changed |= !removed_live.is_empty();
        for row in removed_live {
            self.record_row_event(f, row, -1, -1, 0);
        }
        let removed_subsumed = remove_keys_from_store(&mut self.subsumed, f, keylen, keys);
        changed |= !removed_subsumed.is_empty();
        for row in removed_subsumed {
            self.record_row_event(f, row, 0, -1, -1);
        }
        changed
    }

    fn record_row_event(
        &mut self,
        func: FunctionId,
        row: Row,
        live_delta: isize,
        all_delta: isize,
        subsumed_delta: isize,
    ) {
        let version = if live_delta > 0 || all_delta > 0 || subsumed_delta > 0 {
            let version = self.next_row_version;
            self.next_row_version += 1;
            Some(version)
        } else {
            None
        };
        update_version_map(&mut self.live_versions, func, &row, live_delta, version);
        update_version_map(&mut self.all_versions, func, &row, all_delta, version);
        update_version_map(
            &mut self.subsumed_versions,
            func,
            &row,
            subsumed_delta,
            version,
        );
    }
}

fn remove_keys_from_store(
    store: &mut HashMap<FunctionId, HashSet<Row>>,
    f: FunctionId,
    keylen: usize,
    keys: &HashSet<Box<[u32]>>,
) -> Vec<Row> {
    let mut removed = Vec::new();
    if let Some(rows) = store.get_mut(&f) {
        rows.retain(|row| {
            if keys.contains(&row[..keylen]) {
                removed.push(row.clone());
                false
            } else {
                true
            }
        });
    }
    removed
}

fn update_version_map(
    versions: &mut HashMap<FunctionId, HashMap<Row, u64>>,
    func: FunctionId,
    row: &Row,
    delta: isize,
    version: Option<u64>,
) {
    match delta.cmp(&0) {
        std::cmp::Ordering::Greater => {
            versions.entry(func).or_default().insert(
                row.clone(),
                version.expect("positive row event needs a version"),
            );
        }
        std::cmp::Ordering::Less => {
            if let Some(rows) = versions.get_mut(&func) {
                rows.remove(row);
            }
        }
        std::cmp::Ordering::Equal => {}
    }
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod tests {
    use super::*;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    use egglog_ast::{
        core::{GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreRule, Query},
        generic_ast::Change,
        span::Span,
    };
    use egglog_backend_trait::{
        Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunctionId, FunctionConfig, MergeFn,
        ReadMode, RuleActionCall, RuleBodyCall, RuleId, RuleSetRun, RuleSpec, RuleValue, RuleVar,
        Value,
    };
    use egglog_numeric_id::NumericId;

    type RuleTerm = GenericAtomTerm<RuleVar, RuleValue>;

    struct TestRule {
        spec: RuleSpec,
        next_var: u32,
    }

    impl TestRule {
        fn new(name: &str) -> Self {
            Self {
                spec: RuleSpec {
                    name: name.to_owned(),
                    seminaive: true,
                    no_decomp: false,
                    core: GenericCoreRule {
                        span: Span::Panic,
                        body: Query::default(),
                        head: Default::default(),
                    },
                },
                next_var: 0,
            }
        }

        fn new_var(&mut self, ty: ColumnTy) -> RuleTerm {
            let id = self.next_var;
            self.next_var += 1;
            GenericAtomTerm::Var(
                Span::Panic,
                RuleVar {
                    id,
                    name: format!("v{id}").into_boxed_str(),
                    ty,
                },
            )
        }

        fn query_table(&mut self, id: FunctionId, args: &[RuleTerm], is_subsumed: Option<bool>) {
            self.spec.core.body.atoms.push(GenericAtom {
                span: Span::Panic,
                head: RuleBodyCall::Table {
                    id,
                    read: match is_subsumed {
                        Some(false) => ReadMode::Live,
                        Some(true) => ReadMode::Subsumed,
                        None => ReadMode::All,
                    },
                },
                args: args.to_vec(),
            });
        }

        fn query_prim(&mut self, id: ExternalFunctionId, args: &[RuleTerm], output: ColumnTy) {
            self.spec.core.body.atoms.push(GenericAtom {
                span: Span::Panic,
                head: RuleBodyCall::Primitive {
                    id,
                    name: "external".into(),
                    output,
                },
                args: args.to_vec(),
            });
        }

        fn set(&mut self, id: FunctionId, entries: &[RuleTerm]) {
            let (value, args) = entries.split_last().expect("set has a value");
            self.spec.core.head.0.push(GenericCoreAction::Set(
                Span::Panic,
                RuleActionCall::Table {
                    id,
                    name: "table".into(),
                },
                args.to_vec(),
                value.clone(),
            ));
        }

        fn change(&mut self, id: FunctionId, entries: &[RuleTerm], change: Change) {
            self.spec.core.head.0.push(GenericCoreAction::Change(
                Span::Panic,
                change,
                RuleActionCall::Table {
                    id,
                    name: "table".into(),
                },
                entries.to_vec(),
            ));
        }

        fn remove(&mut self, id: FunctionId, entries: &[RuleTerm]) {
            self.change(id, entries, Change::Delete);
        }

        fn subsume(&mut self, id: FunctionId, entries: &[RuleTerm]) {
            self.change(id, entries, Change::Subsume);
        }

        fn union(&mut self, lhs: RuleTerm, rhs: RuleTerm) {
            self.spec
                .core
                .head
                .0
                .push(GenericCoreAction::Union(Span::Panic, lhs, rhs));
        }

        fn build(self, egraph: &mut EGraph) -> RuleId {
            Backend::add_rule(egraph, self.spec).unwrap()
        }
    }

    fn row(vals: &[u32]) -> Row {
        vals.to_vec().into_boxed_slice()
    }

    fn run_rules(egraph: &mut EGraph, rules: &[RuleId]) -> Result<IterationReport> {
        Backend::run_rules(
            egraph,
            RuleSetRun {
                name: Some("test"),
                rules,
            },
        )
    }

    fn constant(value: u32, ty: ColumnTy) -> RuleTerm {
        GenericAtomTerm::Literal(
            Span::Panic,
            RuleValue {
                value: Value::new(value),
                ty,
            },
        )
    }

    fn id_function(eg: &mut EGraph, name: &str, merge: MergeFn) -> FunctionId {
        Backend::add_table(
            eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                default: DefaultVal::Fail,
                merge,
                name: name.to_string(),
                can_subsume: true,
            },
        )
    }

    fn id_table(eg: &mut EGraph, name: &str, arity: usize) -> FunctionId {
        Backend::add_table(
            eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id; arity],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: name.to_string(),
                can_subsume: false,
            },
        )
    }

    fn neq_primitive(eg: &mut EGraph) -> ExternalFunctionId {
        Backend::register_external_func(
            eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                (args[0] != args[1]).then_some(Value::new(0))
            })),
        )
    }

    fn max_primitive(eg: &mut EGraph) -> ExternalFunctionId {
        Backend::register_external_func(
            eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                Some(args[0].max(args[1]))
            })),
        )
    }

    fn self_join_tables(eg: &mut EGraph) -> (BaseValueId, FunctionId, FunctionId) {
        let unit_ty = eg.db.base_values().get_ty::<()>();
        let relation = Backend::add_table(
            eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "R".to_string(),
                can_subsume: false,
            },
        );
        let out = Backend::add_table(
            eg,
            FunctionConfig {
                schema: vec![
                    ColumnTy::Id,
                    ColumnTy::Id,
                    ColumnTy::Id,
                    ColumnTy::Base(unit_ty),
                ],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "Out".to_string(),
                can_subsume: false,
            },
        );
        eg.insert_live_row(relation, row(&[1, 2, 0]));
        eg.insert_live_row(relation, row(&[1, 3, 0]));
        (unit_ty, relation, out)
    }

    fn path_compression_fixture(eg: &mut EGraph) -> (FunctionId, RuleId) {
        let neq = neq_primitive(eg);
        let unit_ty = eg.db.base_values().get_ty::<()>();
        let uf = Backend::add_table(
            eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "UF".to_string(),
                can_subsume: false,
            },
        );
        let mut rb = TestRule::new("path_compress");
        let a = rb.new_var(ColumnTy::Id);
        let b = rb.new_var(ColumnTy::Id);
        let c = rb.new_var(ColumnTy::Id);
        let unit = constant(0, ColumnTy::Base(unit_ty));
        rb.query_table(uf, &[a.clone(), b.clone(), unit.clone()], Some(false));
        rb.query_table(uf, &[b.clone(), c.clone(), unit.clone()], Some(false));
        rb.query_prim(
            neq,
            &[b.clone(), c.clone(), unit.clone()],
            ColumnTy::Base(unit_ty),
        );
        rb.remove(uf, &[a.clone(), b]);
        rb.set(uf, &[a, c, unit]);
        (uf, rb.build(eg))
    }

    fn write_order_tables(eg: &mut EGraph) -> (BaseValueId, FunctionId, FunctionId) {
        let unit_ty = eg.db.base_values().get_ty::<()>();
        let trigger = Backend::add_table(
            eg,
            FunctionConfig {
                schema: vec![ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "Trigger".to_string(),
                can_subsume: false,
            },
        );
        let f = Backend::add_table(
            eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                default: DefaultVal::Fail,
                merge: MergeFn::New,
                name: "F".to_string(),
                can_subsume: true,
            },
        );
        eg.insert_live_row(trigger, row(&[0]));
        (unit_ty, trigger, f)
    }

    #[test]
    fn native_union_is_rejected_when_rule_is_added() {
        let mut eg = EGraph::new();
        let left = constant(1, ColumnTy::Id);
        let right = constant(2, ColumnTy::Id);
        let mut builder = TestRule::new("native union");
        builder.union(left, right);

        let error = Backend::add_rule(&mut eg, builder.spec).unwrap_err();
        assert!(error.to_string().contains("received a native union"));
    }

    #[test]
    fn table_and_rule_arity_match_fixed_dd_row_width() {
        let mut eg = EGraph::new();
        let wide = id_table(&mut eg, "wide", dd_native::W);

        let mut boundary = TestRule::new("width boundary");
        let boundary_args = (0..dd_native::W)
            .map(|_| boundary.new_var(ColumnTy::Id))
            .collect::<Vec<_>>();
        boundary.query_table(wide, &boundary_args, Some(false));
        Backend::add_rule(&mut eg, boundary.spec).expect("width-W rule must be admitted");

        let mut too_wide_rule = TestRule::new("too wide");
        let too_wide_args = (0..=dd_native::W)
            .map(|_| too_wide_rule.new_var(ColumnTy::Id))
            .collect::<Vec<_>>();
        too_wide_rule.query_table(wide, &too_wide_args, Some(false));
        let error = Backend::add_rule(&mut eg, too_wide_rule.spec).unwrap_err();
        assert!(error
            .to_string()
            .contains(&format!("{} columns", dd_native::W + 1)));
        assert!(error
            .to_string()
            .contains(&format!("fixed row width {}", dd_native::W)));

        let relation_count = eg.relations.len();
        let oversized_table = catch_unwind(AssertUnwindSafe(|| {
            id_table(&mut eg, "oversized", dd_native::W + 1)
        }));
        assert!(oversized_table.is_err());
        assert_eq!(eg.relations.len(), relation_count);
    }

    #[test]
    fn add_rule_rejects_residual_globals() {
        let mut eg = EGraph::new();
        let input = id_table(&mut eg, "input", 1);
        let mut rule = TestRule::new("global");
        let global = GenericAtomTerm::Global(
            Span::Panic,
            RuleVar {
                id: 0,
                name: "global".into(),
                ty: ColumnTy::Id,
            },
        );
        rule.query_table(input, &[global], Some(false));

        let error = Backend::add_rule(&mut eg, rule.spec).unwrap_err();
        assert!(error.to_string().contains("residual global"));
    }

    #[test]
    fn join_planning_failure_is_returned_without_unwinding() {
        let mut eg = EGraph::new();
        let wide = id_table(&mut eg, "wide", dd_native::W);
        let edge = id_table(&mut eg, "edge", 2);
        let primitive = max_primitive(&mut eg);
        let mut rule = TestRule::new("wide live frontier");
        let vars = (0..=dd_native::W)
            .map(|_| rule.new_var(ColumnTy::Id))
            .collect::<Vec<_>>();
        rule.query_table(wide, &vars[..dd_native::W], Some(false));
        rule.query_table(
            edge,
            &[vars[0].clone(), vars[dd_native::W].clone()],
            Some(false),
        );
        rule.query_prim(primitive, &vars, ColumnTy::Id);
        let rule = rule.build(&mut eg);

        let outcome = catch_unwind(AssertUnwindSafe(|| run_rules(&mut eg, &[rule])));
        let error = outcome
            .expect("unsupported join planning must not unwind")
            .unwrap_err();
        assert!(error
            .to_string()
            .contains("live body-variable frontier exceeds W 48"));
    }

    #[test]
    fn merge_set_preserves_subsumed_status() {
        let mut eg = EGraph::new();
        let f = id_function(&mut eg, "f", MergeFn::New);
        eg.subsumed.entry(f).or_default().insert(row(&[1, 10]));

        assert!(eg.apply_merge_sets(f, &[row(&[1, 11])]).unwrap());

        assert!(!eg.mirror[&f].contains(&row(&[1, 11])));
        assert!(!eg.subsumed[&f].contains(&row(&[1, 10])));
        assert!(eg.subsumed[&f].contains(&row(&[1, 11])));
    }

    #[test]
    fn lookup_or_create_finds_subsumed_rows() {
        let mut eg = EGraph::new();
        let f = id_function(&mut eg, "f", MergeFn::New);
        eg.next_id = 100;
        eg.subsumed.entry(f).or_default().insert(row(&[42, 7]));

        let mut lookup_index = HashMap::new();
        let value = interpret::lookup_or_create(&mut eg, f, &[Value::new(42)], &mut lookup_index);

        assert_eq!(value.rep(), 7);
        assert_eq!(eg.next_id, 100);
        assert!(eg.mirror[&f].is_empty());
    }

    #[test]
    fn merge_set_collapses_live_subsumed_key_duplicate() {
        let mut eg = EGraph::new();
        let f = id_function(&mut eg, "f", MergeFn::New);
        eg.mirror.entry(f).or_default().insert(row(&[1, 10]));
        eg.subsumed.entry(f).or_default().insert(row(&[1, 11]));

        assert!(eg.apply_merge_sets(f, &[row(&[1, 12])]).unwrap());

        assert!(eg.mirror[&f].is_empty());
        assert_eq!(eg.subsumed[&f].len(), 1);
        assert!(eg.subsumed[&f].contains(&row(&[1, 12])));
    }

    #[test]
    fn same_table_self_join_produces_cross_pairs() {
        let mut eg = EGraph::new();
        let (unit_ty, relation, out) = self_join_tables(&mut eg);

        let rule = {
            let mut rb = TestRule::new("self_join");
            let a = rb.new_var(ColumnTy::Id);
            let b = rb.new_var(ColumnTy::Id);
            let c = rb.new_var(ColumnTy::Id);
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(relation, &[a.clone(), b.clone(), unit.clone()], Some(false));
            rb.query_table(relation, &[a.clone(), c.clone(), unit.clone()], Some(false));
            rb.set(out, &[a, b, c, unit]);
            rb.build(&mut eg)
        };

        run_rules(&mut eg, &[rule]).unwrap();

        assert!(eg.mirror[&out].contains(&row(&[1, 2, 3, 0])));
        assert!(eg.mirror[&out].contains(&row(&[1, 3, 2, 0])));
    }

    #[test]
    fn fused_ruleset_allows_mixed_read_modes_same_relation() {
        let mut eg = EGraph::new();
        let unit_ty = eg.db.base_values().get_ty::<()>();
        let relation = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "R".to_string(),
                can_subsume: true,
            },
        );
        let live_out = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "LiveOut".to_string(),
                can_subsume: false,
            },
        );
        let all_out = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "AllOut".to_string(),
                can_subsume: false,
            },
        );
        eg.insert_live_row(relation, row(&[1, 0]));
        eg.insert_located_row(relation, RowLocation::Subsumed, row(&[2, 0]));

        let live_rule = {
            let mut rb = TestRule::new("live_read");
            let x = rb.new_var(ColumnTy::Id);
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(relation, &[x.clone(), unit.clone()], Some(false));
            rb.set(live_out, &[x, unit]);
            rb.build(&mut eg)
        };
        let all_rule = {
            let mut rb = TestRule::new("all_read");
            let x = rb.new_var(ColumnTy::Id);
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(relation, &[x.clone(), unit.clone()], None);
            rb.set(all_out, &[x, unit]);
            rb.build(&mut eg)
        };

        run_rules(&mut eg, &[live_rule, all_rule]).unwrap();

        assert!(eg.mirror[&live_out].contains(&row(&[1, 0])));
        assert!(!eg.mirror[&live_out].contains(&row(&[2, 0])));
        assert!(eg.mirror[&all_out].contains(&row(&[1, 0])));
        assert!(eg.mirror[&all_out].contains(&row(&[2, 0])));
    }

    #[test]
    fn fused_ruleset_cache_maps_reordered_rules_by_id() {
        let mut eg = EGraph::new();
        let input_a = id_table(&mut eg, "InputA", 2);
        let input_b = id_table(&mut eg, "InputB", 3);
        let output_a = id_table(&mut eg, "OutputA", 2);
        let output_b = id_table(&mut eg, "OutputB", 2);

        let rule_a = {
            let mut rb = TestRule::new("rule_a");
            let x = rb.new_var(ColumnTy::Id);
            let y = rb.new_var(ColumnTy::Id);
            rb.query_table(input_a, &[x.clone(), y.clone()], Some(false));
            rb.set(output_a, &[y, x]);
            rb.build(&mut eg)
        };
        let rule_b = {
            let mut rb = TestRule::new("rule_b");
            let p = rb.new_var(ColumnTy::Id);
            let q = rb.new_var(ColumnTy::Id);
            let r = rb.new_var(ColumnTy::Id);
            rb.query_table(input_b, &[r.clone(), p.clone(), q], Some(false));
            rb.set(output_b, &[p, r]);
            rb.build(&mut eg)
        };

        eg.insert_live_row(input_a, row(&[1, 2]));
        eg.insert_live_row(input_b, row(&[5, 3, 4]));
        run_rules(&mut eg, &[rule_a, rule_b]).unwrap();

        eg.insert_live_row(input_a, row(&[10, 20]));
        eg.insert_live_row(input_b, row(&[50, 30, 40]));
        run_rules(&mut eg, &[rule_b, rule_a]).unwrap();

        assert!(eg.mirror[&output_a].contains(&row(&[20, 10])));
        assert!(eg.mirror[&output_b].contains(&row(&[30, 50])));
    }

    #[test]
    fn same_table_self_join_applies_primitive_guards() {
        let mut eg = EGraph::new();
        let neq = neq_primitive(&mut eg);
        let ordering_max = max_primitive(&mut eg);
        let (unit_ty, relation, out) = self_join_tables(&mut eg);

        let rule = {
            let mut rb = TestRule::new("guarded_self_join");
            let a = rb.new_var(ColumnTy::Id);
            let b = rb.new_var(ColumnTy::Id);
            let c = rb.new_var(ColumnTy::Id);
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(relation, &[a.clone(), b.clone(), unit.clone()], Some(false));
            rb.query_table(relation, &[a.clone(), c.clone(), unit.clone()], Some(false));
            rb.query_prim(
                neq,
                &[b.clone(), c.clone(), unit.clone()],
                ColumnTy::Base(unit_ty),
            );
            rb.query_prim(
                ordering_max,
                &[b.clone(), c.clone(), b.clone()],
                ColumnTy::Id,
            );
            rb.set(out, &[a, b, c, unit]);
            rb.build(&mut eg)
        };

        run_rules(&mut eg, &[rule]).unwrap();

        assert!(eg.mirror[&out].contains(&row(&[1, 3, 2, 0])));
        assert!(!eg.mirror[&out].contains(&row(&[1, 2, 3, 0])));
    }

    #[test]
    fn same_table_self_join_allows_independent_unit_outputs() {
        let mut eg = EGraph::new();
        let neq = neq_primitive(&mut eg);
        let ordering_max = max_primitive(&mut eg);
        let (unit_ty, relation, out) = self_join_tables(&mut eg);

        let rule = {
            let mut rb = TestRule::new("unit_var_self_join");
            let a = rb.new_var(ColumnTy::Id);
            let b = rb.new_var(ColumnTy::Id);
            let c = rb.new_var(ColumnTy::Id);
            let unit1 = rb.new_var(ColumnTy::Base(unit_ty));
            let unit2 = rb.new_var(ColumnTy::Base(unit_ty));
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(relation, &[a.clone(), b.clone(), unit1], Some(false));
            rb.query_table(relation, &[a.clone(), c.clone(), unit2], Some(false));
            rb.query_prim(
                neq,
                &[b.clone(), c.clone(), unit.clone()],
                ColumnTy::Base(unit_ty),
            );
            rb.query_prim(
                ordering_max,
                &[b.clone(), c.clone(), b.clone()],
                ColumnTy::Id,
            );
            rb.set(out, &[a, b, c, unit]);
            rb.build(&mut eg)
        };

        run_rules(&mut eg, &[rule]).unwrap();

        assert!(eg.mirror[&out].contains(&row(&[1, 3, 2, 0])));
        assert!(!eg.mirror[&out].contains(&row(&[1, 2, 3, 0])));
    }

    #[test]
    fn incremental_self_join_retracts_old_path_edge() {
        let mut eg = EGraph::new();
        let (uf, rule) = path_compression_fixture(&mut eg);

        eg.insert_live_row(uf, row(&[40, 4, 0]));
        run_rules(&mut eg, &[rule]).unwrap();
        eg.insert_live_row(uf, row(&[75, 40, 0]));
        run_rules(&mut eg, &[rule]).unwrap();

        assert!(!eg.mirror[&uf].contains(&row(&[75, 40, 0])));
        assert!(eg.mirror[&uf].contains(&row(&[75, 4, 0])));
    }

    #[test]
    fn reinserted_same_row_refires_incremental_join() {
        let mut eg = EGraph::new();
        let (uf, rule) = path_compression_fixture(&mut eg);

        eg.insert_live_row(uf, row(&[40, 4, 0]));
        eg.insert_live_row(uf, row(&[75, 40, 0]));
        run_rules(&mut eg, &[rule]).unwrap();
        assert!(!eg.mirror[&uf].contains(&row(&[75, 40, 0])));
        assert!(eg.mirror[&uf].contains(&row(&[75, 4, 0])));

        eg.insert_live_row(uf, row(&[75, 40, 0]));
        run_rules(&mut eg, &[rule]).unwrap();

        assert!(!eg.mirror[&uf].contains(&row(&[75, 40, 0])));
        assert!(eg.mirror[&uf].contains(&row(&[75, 4, 0])));
    }

    #[test]
    fn clone_preserves_authoritative_state_and_rebuilds_transient_join() {
        let mut eg = EGraph::new();
        let (uf, rule) = path_compression_fixture(&mut eg);
        eg.insert_live_row(uf, row(&[40, 4, 0]));
        eg.insert_live_row(uf, row(&[75, 40, 0]));
        run_rules(&mut eg, &[rule]).unwrap();
        assert!(!eg.dd_fused.is_empty());
        assert!(!eg.dd_fused_fed_versions.is_empty());
        let panic = Backend::new_panic(&mut eg, "cloned panic".to_owned());

        let mut cloned = Backend::clone_boxed(&eg);
        let cloned = cloned
            .as_any_mut()
            .downcast_mut::<EGraph>()
            .expect("DD clone must retain its concrete backend type");

        assert!(cloned.dd_fused.is_empty());
        assert!(cloned.dd_fused_fed_versions.is_empty());
        assert_eq!(cloned.relations.len(), eg.relations.len());
        assert_eq!(cloned.rules.len(), eg.rules.len());
        assert_eq!(cloned.mirror, eg.mirror);
        assert_eq!(cloned.subsumed, eg.subsumed);
        assert_eq!(cloned.next_id, eg.next_id);
        assert_eq!(cloned.next_row_version, eg.next_row_version);
        assert_eq!(cloned.live_versions, eg.live_versions);
        assert_eq!(cloned.all_versions, eg.all_versions);
        assert_eq!(cloned.subsumed_versions, eg.subsumed_versions);

        let outcome = catch_unwind(AssertUnwindSafe(|| {
            cloned.eval_prim_internal(panic, &[Value::new(7)])
        }));
        let error = outcome
            .expect("a cloned panic primitive must not unwind")
            .unwrap_err();
        assert_eq!(error.to_string(), "cloned panic");

        cloned.insert_live_row(uf, row(&[90, 75, 0]));
        run_rules(cloned, &[rule]).unwrap();
        assert!(cloned.mirror[&uf].contains(&row(&[90, 4, 0])));
        assert!(!eg.mirror[&uf].contains(&row(&[90, 4, 0])));
        assert!(!cloned.dd_fused.is_empty());
        assert!(!cloned.dd_fused_fed_versions.is_empty());
    }

    #[test]
    fn same_iteration_remove_then_set_keeps_set_value() {
        let mut eg = EGraph::new();
        let (unit_ty, trigger, f) = write_order_tables(&mut eg);
        eg.insert_live_row(f, row(&[1, 9]));

        let rule = {
            let mut rb = TestRule::new("remove_then_set");
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(trigger, std::slice::from_ref(&unit), Some(false));
            let key = constant(1, ColumnTy::Id);
            let new = constant(2, ColumnTy::Id);
            rb.remove(f, std::slice::from_ref(&key));
            rb.set(f, &[key, new]);
            rb.build(&mut eg)
        };

        run_rules(&mut eg, &[rule]).unwrap();

        assert!(!eg.mirror[&f].contains(&row(&[1, 9])));
        assert!(eg.mirror[&f].contains(&row(&[1, 2])));
    }

    #[test]
    fn same_iteration_set_then_subsume_ends_subsumed() {
        let mut eg = EGraph::new();
        let (unit_ty, trigger, f) = write_order_tables(&mut eg);

        let rule = {
            let mut rb = TestRule::new("set_then_subsume");
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(trigger, std::slice::from_ref(&unit), Some(false));
            let key = constant(1, ColumnTy::Id);
            let value = constant(2, ColumnTy::Id);
            rb.set(f, &[key.clone(), value]);
            rb.subsume(f, &[key]);
            rb.build(&mut eg)
        };

        run_rules(&mut eg, &[rule]).unwrap();

        assert!(!eg.mirror[&f].contains(&row(&[1, 2])));
        assert!(eg.subsumed[&f].contains(&row(&[1, 2])));
    }

    #[test]
    fn fused_delta_feed_does_not_expose_mixed_old_new_snapshots() {
        let mut eg = EGraph::new();
        let neq = neq_primitive(&mut eg);
        let unit_ty = eg.db.base_values().get_ty::<()>();
        let view = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "View".to_string(),
                can_subsume: false,
            },
        );
        let current = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id],
                default: DefaultVal::Fail,
                merge: MergeFn::New,
                name: "Current".to_string(),
                can_subsume: false,
            },
        );
        let dummy = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "Dummy".to_string(),
                can_subsume: false,
            },
        );
        eg.insert_live_row(view, row(&[10, 0]));
        assert!(eg.apply_merge_sets(current, &[row(&[10])]).unwrap());

        let view_first_rule = {
            let mut rb = TestRule::new("view_first");
            let x = rb.new_var(ColumnTy::Id);
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(view, &[x.clone(), unit.clone()], Some(false));
            rb.set(dummy, &[x, unit]);
            rb.build(&mut eg)
        };
        let cleanup_rule = {
            let mut rb = TestRule::new("current_cleanup");
            let selected = rb.new_var(ColumnTy::Id);
            let old = rb.new_var(ColumnTy::Id);
            let unit = constant(0, ColumnTy::Base(unit_ty));
            rb.query_table(current, std::slice::from_ref(&selected), Some(false));
            rb.query_table(view, &[selected.clone(), unit.clone()], Some(false));
            rb.query_table(view, &[old.clone(), unit.clone()], Some(false));
            rb.query_prim(
                neq,
                &[selected.clone(), old.clone(), unit.clone()],
                ColumnTy::Base(unit_ty),
            );
            rb.remove(view, &[old]);
            rb.build(&mut eg)
        };

        run_rules(&mut eg, &[view_first_rule, cleanup_rule]).unwrap();
        assert!(eg.mirror[&view].contains(&row(&[10, 0])));

        eg.insert_live_row(view, row(&[4, 0]));
        assert!(eg.apply_merge_sets(current, &[row(&[4])]).unwrap());

        run_rules(&mut eg, &[view_first_rule, cleanup_rule]).unwrap();

        assert!(eg.mirror[&view].contains(&row(&[4, 0])));
        assert!(!eg.mirror[&view].contains(&row(&[10, 0])));
    }
}

// ---------------------------------------------------------------------------
// Merge-mode recognition (shared by `add_table`)
// ---------------------------------------------------------------------------

/// Map a single-output-column [`MergeFn`] to this backend's [`MergeMode`] (plus, for
/// [`MergeMode::Computed`], the evaluatable [`MergeTree`]) that resolves its FD
/// conflict:
///   - `AssertEq` / `Old`     => keep the old value
///   - `New`                  => keep the new value
///   - `UnionId`              => lattice-min (the union-find leader)
///   - `Primitive` / `Function` / `Const` => `Computed`: fold by evaluating the
///     retained tree (`or`/`max`/`+`, or a constructor that builds a term)
fn merge_mode_for(merge: &MergeFn) -> (MergeMode, Option<MergeTree>) {
    match merge {
        MergeFn::AssertEq | MergeFn::Old => (MergeMode::Old, None),
        MergeFn::New => (MergeMode::New, None),
        MergeFn::UnionId => (MergeMode::Min, None),
        MergeFn::Primitive(_, _) | MergeFn::Function(_, _) | MergeFn::Const(_) => {
            (MergeMode::Computed, translate_merge_tree(merge))
        }
    }
}

/// Translate a trait [`MergeFn`] into the evaluatable [`MergeTree`]. `UnionId`
/// has no tree form (it is `MergeMode::Min`); it only appears nested if the term
/// encoder builds one, in which case lattice-min is the faithful lowering.
fn translate_merge_tree(merge: &MergeFn) -> Option<MergeTree> {
    Some(match merge {
        MergeFn::Old | MergeFn::AssertEq => MergeTree::Old,
        MergeFn::New => MergeTree::New,
        MergeFn::Const(v) => MergeTree::Const(v.rep()),
        MergeFn::Primitive(id, args) => MergeTree::Prim(
            *id,
            args.iter()
                .map(translate_merge_tree)
                .collect::<Option<_>>()?,
        ),
        MergeFn::Function(f, args) => MergeTree::Func(
            *f,
            args.iter()
                .map(translate_merge_tree)
                .collect::<Option<_>>()?,
        ),
        MergeFn::UnionId => return None,
    })
}

// ---------------------------------------------------------------------------
// impl Backend
// ---------------------------------------------------------------------------

impl Backend for EGraph {
    // -- table lifecycle ----------------------------------------------------

    fn add_table(&mut self, config: FunctionConfig) -> FunctionId {
        let id = FunctionId::new(self.relations.len() as u32);
        let arity = config.schema.len();
        assert!(
            arity <= dd_native::W,
            "DD backend fixed row width supports relations of arity <= {} (got {} for `{}`)",
            dd_native::W,
            arity,
            config.name
        );
        // Relation vs function: a table is a **relation** (whole row is the key,
        // no output column to merge) iff it is nullary OR its last column is
        // `Unit` — the term encoder's view-table pattern
        // `(function @XView (...) Unit :merge old)` AND ordinary relations.
        // Otherwise the last column is a function OUTPUT, resolved by the merge
        // mode. Detected via Unit — NOT `DefaultVal`, which is `Fail` for every
        // custom function regardless of whether it has a real output column.
        let output_is_unit = config.schema.last().is_some_and(|t| match t {
            ColumnTy::Base(bv) => {
                // `()` is pre-registered in `new`, so this never panics.
                *bv == self
                    .db
                    .base_values()
                    .get_ty_by_id(std::any::TypeId::of::<()>())
            }
            _ => false,
        });
        let has_output = arity > 0 && !output_is_unit;
        let (merge, merge_tree) = if !has_output {
            (MergeMode::Relation, None)
        } else {
            merge_mode_for(&config.merge)
        };
        self.relations.push(RelationInfo {
            name: config.name,
            arity,
            lookup_mints: matches!(config.default, DefaultVal::FreshId),
            merge,
            merge_tree,
        });
        self.mirror.insert(id, HashSet::new());
        id
    }

    fn table_size(&self, table: FunctionId) -> usize {
        // Subsumed rows still count (they remain in the table, just hidden from
        // ordinary matching), so `(print-size)` matches the reference backend.
        let live = self.mirror.get(&table).map(|s| s.len()).unwrap_or(0);
        let subsumed = self.subsumed.get(&table).map(|s| s.len()).unwrap_or(0);
        live + subsumed
    }

    // -- iteration ----------------------------------------------------------

    fn for_each_while_dyn(
        &self,
        table: FunctionId,
        f: &mut dyn for<'r> FnMut(ScanEntry<'r>) -> bool,
    ) {
        let arity = self.info(table).arity;
        // Live rows first, then subsumed rows (reported with `subsumed: true`), so
        // extraction/serialization see the whole table with the flag.
        let live = self.mirror.get(&table).into_iter().flat_map(|s| s.iter());
        let subs = self.subsumed.get(&table).into_iter().flat_map(|s| s.iter());
        for (row, subsumed) in live.map(|r| (r, false)).chain(subs.map(|r| (r, true))) {
            let vals = row[..arity]
                .iter()
                .copied()
                .map(Value::new)
                .collect::<Vec<_>>();
            let entry = ScanEntry {
                vals: &vals,
                subsumed,
            };
            if !f(entry) {
                break;
            }
        }
    }

    // -- direct access ------------------------------------------------------

    fn get_canon_repr(&self, val: Value, _ty: ColumnTy) -> Value {
        // No union-find; canonicalization is the identity.
        val
    }

    fn clear_table(&mut self, func: FunctionId) {
        if let Some(set) = self.mirror.get_mut(&func) {
            let removed: Vec<Row> = set.iter().cloned().collect();
            set.clear();
            for row in removed {
                self.record_row_event(func, row, -1, -1, 0);
            }
        }
        if let Some(set) = self.subsumed.get_mut(&func) {
            let removed: Vec<Row> = set.iter().cloned().collect();
            set.clear();
            for row in removed {
                self.record_row_event(func, row, 0, -1, -1);
            }
        }
    }

    fn base_values(&self) -> &BaseValues {
        self.db.base_values()
    }

    fn base_values_mut(&mut self) -> &mut BaseValues {
        self.db.base_values_mut()
    }

    fn container_values(&self) -> &ContainerValues {
        self.db.container_values()
    }

    fn lookup_id(&self, func: FunctionId, key: &[Value]) -> Option<Value> {
        let info = self.info(func);
        if info.merge == MergeMode::Relation || key.len() + 1 != info.arity {
            return None;
        }
        let key: Vec<u32> = key.iter().map(|value| value.rep()).collect();
        let find = |rows: Option<&HashSet<Row>>| {
            rows?
                .iter()
                .find_map(|row| (row[..key.len()] == key[..]).then(|| Value::new(row[key.len()])))
        };
        find(self.mirror.get(&func)).or_else(|| find(self.subsumed.get(&func)))
    }

    fn container_values_mut_dyn(&mut self) -> Option<&mut ContainerValues> {
        Some(self.db.container_values_mut())
    }

    fn new_container_id_counter(&mut self) -> Option<CounterId> {
        Some(self.db.add_counter())
    }

    fn container_merge_fn(&self, _container_type: TypeId) -> Option<ContainerMergeFn> {
        // The supported proof/term subset interns container values but does not
        // rely on merging distinct ids for one rebuilt value. Keep that subset's
        // handles deterministic. Faithful conflicting-id rebuild would also need
        // to stage equality into the authoritative DD mirror, which is outside
        // this backend's current container contract.
        Some(Arc::new(|_state, old, new| std::cmp::min(old, new)))
    }

    fn with_execution_state_tracked_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) -> bool {
        self.db.with_execution_state_tracked(|st| f(st)).1
    }

    // -- rule management ----------------------------------------------------

    fn add_rule(&mut self, rule: RuleSpec) -> Result<RuleId> {
        self.validate_rule(&rule)?;
        let id = RuleId::new(self.rules.len() as u32);
        self.rules.push(Some(rule));
        Ok(id)
    }

    fn free_rule(&mut self, id: RuleId) {
        if let Some(slot) = self.rules.get_mut(id.rep() as usize) {
            *slot = None;
            let i = id.rep() as usize;
            self.seen.remove(&i);
            // Any fused ruleset that included this rule is now stale: drop it so
            // it is rebuilt (without the freed rule) on the next `run_rules`.
            self.dd_fused.retain(|key| !key.contains(&i));
            self.dd_fused_fed_versions
                .retain(|key, _| !key.contains(&i));
        }
    }

    fn run_rules(&mut self, run: RuleSetRun<'_>) -> Result<IterationReport> {
        // One `run_rules` call = one bounded egglog iteration. The frontend calls
        // this N times for `(run N)`.
        if let Some(message) = self.take_panic_message() {
            return Err(anyhow!(message));
        }
        if run.rules.is_empty() {
            return Ok(IterationReport::default());
        }
        let rules: Vec<(usize, RuleSpec)> = run
            .rules
            .iter()
            .map(|r| r.rep() as usize)
            .filter_map(|i| {
                self.rules
                    .get(i)
                    .and_then(Option::as_ref)
                    .cloned()
                    .map(|rule| (i, rule))
            })
            .collect();
        if rules.is_empty() {
            return Ok(IterationReport::default());
        }

        let changed = interpret::run_iteration(self, &rules);
        if let Some(message) = self.take_panic_message() {
            return Err(anyhow!(message));
        }
        let changed = changed?;

        let mut report = IterationReport::default();
        report.rule_set_report.changed = changed;
        Ok(report)
    }

    fn flush_updates(&mut self) -> bool {
        // Seed inserts land in the mirror immediately; the DD join runs inside
        // `run_rules`. No separate flush.
        false
    }

    // -- primitives ---------------------------------------------------------

    fn register_external_func(
        &mut self,
        func: Box<dyn ExternalFunction + 'static>,
    ) -> ExternalFunctionId {
        self.db.add_external_function(func)
    }

    fn free_external_func(&mut self, func: ExternalFunctionId) {
        self.db.free_external_function(func);
    }

    fn new_panic(&mut self, message: String) -> ExternalFunctionId {
        let panic_message = Arc::clone(&self.panic_message);
        self.db
            .add_external_function(Box::new(egglog_core_relations::make_external_func(
                move |state, _args| {
                    state.trigger_early_stop();
                    let mut pending = panic_message
                        .lock()
                        .expect("DD panic-message side channel must not be poisoned");
                    if pending.is_none() {
                        *pending = Some(message.clone());
                    }
                    None
                },
            )))
    }

    // -- capability flags ---------------------------------------------------

    fn requires_term_encoding(&self) -> bool {
        // This backend has no native union-find: congruence and rebuild are
        // lowered to ordinary rules over `@uf` tables by the term encoder. The
        // frontend refuses to run this backend without that encoding, and rule
        // registration defensively rejects a native `GenericCoreAction::Union`.
        true
    }

    fn supports_containers(&self) -> bool {
        true
    }

    // -- diagnostics --------------------------------------------------------

    fn set_report_level(&mut self, _level: ReportLevel) {}

    fn dump_debug_info(&self) {
        for (i, info) in self.relations.iter().enumerate() {
            let f = FunctionId::new(i as u32);
            let n = self.table_size(f);
            if n == 0 {
                continue;
            }
            log::info!("== DD relation `{}` ({} rows) ==", info.name, n);
        }
    }

    // -- cloning ------------------------------------------------------------

    fn clone_boxed(&self) -> Box<dyn Backend> {
        // Timely workers are transient and cannot be cloned. The authoritative
        // relation/rule/database/mirror/version state is copied, while workers
        // and their fed-version snapshots start empty. The next `run_rules`
        // lazily rebuilds the fused dataflow and feeds the cloned current state.
        Box::new(Self {
            relations: self.relations.clone(),
            rules: self.rules.clone(),
            mirror: self.mirror.clone(),
            subsumed: self.subsumed.clone(),
            db: self.db.clone(),
            next_id: self.next_id,
            seen: self.seen.clone(),
            dd_fused: DdWorkers::default(),
            next_row_version: self.next_row_version,
            live_versions: self.live_versions.clone(),
            all_versions: self.all_versions.clone(),
            subsumed_versions: self.subsumed_versions.clone(),
            dd_fused_fed_versions: HashMap::new(),
            panic_message: Arc::clone(&self.panic_message),
        })
    }

    // -- bridge-only escape hatch ------------------------------------------

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
