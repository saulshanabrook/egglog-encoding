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
    IterationReport, MergeAction, MergeFn, ReportLevel, RuleActionCall, RuleBodyCall, RuleId,
    RuleSetRun, RuleSpec, RuleValue, RuleVar, ScanEntry, Value,
};
use egglog_core_relations::Database;
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};

mod compile;
mod dd_native;
mod interpret;

use compile::{validate_merge, visit_merge_read_dependencies, ReadKey, Row};

type LocatedValues = (Row, RowLocation);
type RowReplacement = (Row, LocatedValues);

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
    /// Number of visible columns.
    pub(crate) arity: usize,
    n_keys: usize,
    merge: Arc<MergeFn>,
    default: TableDefault,
    n_identity_vals: Option<usize>,
    /// Read dependencies are registered before their owners, so this level
    /// orders each pending merge wave from readable targets to readers.
    merge_level: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TableDefault {
    FreshId,
    Fail,
    Const(u32),
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
    /// Monotonic fresh-id counter, shared by the native `FreshId` default
    /// (`fresh_id_internal`) and the term encoder's `get-fresh!` primitive (via
    /// [`Backend::eclass_id_counter`]) so the two id sources never collide. Lives
    /// in `db` (survives `db.clone()`); `id_counter` is its handle.
    pub(crate) id_counter: CounterId,
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
    /// Relation name → `FunctionId`, populated by `add_table`. Lets the term
    /// encoder's `set-if-empty` / view-proof ops (registered by view NAME before
    /// the view table exists) resolve their view to a live relation at invoke
    /// time.
    pub(crate) table_ids: HashMap<String, FunctionId>,
    /// `set-if-empty` ops keyed by the `ExternalFunctionId` the frontend resolves
    /// their call sites to. The interpreter services these against the `mirror`
    /// instead of calling the (panic) db external function.
    pub(crate) set_if_empty_ops: HashMap<ExternalFunctionId, ViewOp>,
    /// View-proof reader ops, keyed like `set_if_empty_ops`.
    pub(crate) view_proof_ops: HashMap<ExternalFunctionId, ViewOp>,
}

/// A term-encoding view op (`set-if-empty` or view-proof) the DD interpreter
/// services against its `mirror`: the FD view table name plus its key/output
/// column counts.
#[derive(Clone)]
pub(crate) struct ViewOp {
    pub(crate) view_name: String,
    pub(crate) n_keys: usize,
    pub(crate) out_arity: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowLocation {
    Live,
    Subsumed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CurrentRow {
    values: Row,
    location: RowLocation,
    rows_for_key: usize,
}

impl CurrentRow {
    fn located(&self) -> LocatedValues {
        (self.values.clone(), self.location)
    }
}

#[derive(Default)]
struct FunctionMergeState {
    current: HashMap<Row, CurrentRow>,
    original: HashMap<Row, Option<CurrentRow>>,
    touched: Vec<Row>,
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
        // One counter feeds both `fresh_id_internal` and `get-fresh!`. Burn its
        // initial 0 so the first minted id is 1, keeping 0 as a "null"/padding
        // sentinel for the fixed-width DD rows.
        let id_counter = db.add_counter();
        db.inc_counter(id_counter);
        EGraph {
            relations: Vec::new(),
            rules: Vec::new(),
            mirror: HashMap::new(),
            subsumed: HashMap::new(),
            db,
            id_counter,
            seen: HashMap::new(),
            dd_fused: DdWorkers::default(),
            next_row_version: 1,
            live_versions: HashMap::new(),
            all_versions: HashMap::new(),
            subsumed_versions: HashMap::new(),
            dd_fused_fed_versions: HashMap::new(),
            panic_message: Default::default(),
            table_ids: HashMap::new(),
            set_if_empty_ops: HashMap::new(),
            view_proof_ops: HashMap::new(),
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
                        if info.arity - info.n_keys != 1 {
                            bail!(
                                "DD backend cannot add rule {:?}: cannot bind tuple-output function `{}` as one value",
                                rule.name,
                                info.name
                            );
                        }
                        let expected = info.n_keys;
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
                GenericCoreAction::Set(_, call, arguments, values) => {
                    let RuleActionCall::Table { id, .. } = call else {
                        bail!(
                            "DD backend cannot add rule {:?}: cannot set a primitive",
                            rule.name
                        );
                    };
                    validate_terms(arguments, "rule set action")?;
                    validate_terms(values, "rule set action")?;
                    let info = relation(*id, "set action")?;
                    if arguments.len() + values.len() != info.arity {
                        bail!(
                            "DD backend cannot add rule {:?}: set on `{}` writes {} columns, expected {}",
                            rule.name,
                            info.name,
                            arguments.len() + values.len(),
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

    pub(crate) fn function_spec(
        &self,
        function: FunctionId,
    ) -> (usize, Arc<MergeFn>, TableDefault, Option<usize>) {
        let info = self.info(function);
        (
            info.n_keys,
            Arc::clone(&info.merge),
            info.default,
            info.n_identity_vals,
        )
    }

    pub(crate) fn n_keys(&self, function: FunctionId) -> usize {
        self.info(function).n_keys
    }

    pub(crate) fn n_vals(&self, function: FunctionId) -> usize {
        self.info(function).arity - self.n_keys(function)
    }

    /// Evaluate a primitive through the embedded database. The deferred panic
    /// channel turns bridge-style panic primitives back into backend errors.
    pub(crate) fn eval_prim_internal(
        &self,
        id: ExternalFunctionId,
        arguments: &[Value],
    ) -> Result<Option<Value>> {
        let result = self
            .db
            .with_execution_state(|state| state.call_external_func(id, arguments));
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

    pub(crate) fn fresh_id_internal(&mut self) -> u32 {
        self.db.inc_counter(self.id_counter) as u32
    }

    /// Apply full-row sets in dependency-ordered waves. Merge-generated sets
    /// enter the next wave and are processed until the transaction reaches a
    /// fixed point.
    pub(crate) fn apply_sets(&mut self, sets: Vec<(FunctionId, Row)>) -> Result<bool> {
        MergeTransaction::new(self, sets).run()
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

    fn current_rows_by_key(&self, f: FunctionId, n_keys: usize) -> HashMap<Row, CurrentRow> {
        let live_len = self.mirror.get(&f).map(|set| set.len()).unwrap_or(0);
        let subsumed_len = self.subsumed.get(&f).map(|set| set.len()).unwrap_or(0);
        let mut cur = HashMap::with_capacity(live_len + subsumed_len);
        for (location, store) in [
            (RowLocation::Live, &self.mirror),
            (RowLocation::Subsumed, &self.subsumed),
        ] {
            if let Some(rows) = store.get(&f) {
                for row in rows.iter() {
                    let values: Row = row[n_keys..].into();
                    let key: Row = row[..n_keys].into();
                    cur.entry(key)
                        .and_modify(|current: &mut CurrentRow| {
                            current.values = values.clone();
                            current.location = location;
                            current.rows_for_key += 1;
                        })
                        .or_insert(CurrentRow {
                            values,
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
        for (key, (values, location)) in replacements {
            self.insert_located_row(f, location, row_with_values(&key, &values));
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

/// Transaction-local function state for head writes and merge side effects.
/// DD owns body joins; this host transaction preserves egglog's ordered merge
/// semantics over complete key/value rows.
struct MergeTransaction<'a> {
    eg: &'a mut EGraph,
    pending: Vec<(FunctionId, Row)>,
    next_wave: Vec<(FunctionId, Row)>,
    states: HashMap<FunctionId, FunctionMergeState>,
    state_order: Vec<FunctionId>,
    changed: bool,
    next_id_at_start: u32,
}

impl<'a> MergeTransaction<'a> {
    fn new(eg: &'a mut EGraph, sets: Vec<(FunctionId, Row)>) -> Self {
        let next_id_at_start = eg.db.read_counter(eg.id_counter) as u32;
        Self {
            eg,
            pending: sets,
            next_wave: Vec::new(),
            states: HashMap::new(),
            state_order: Vec::new(),
            changed: false,
            next_id_at_start,
        }
    }

    fn run(mut self) -> Result<bool> {
        let result = self.run_inner();
        if result.is_err() {
            self.eg
                .db
                .set_counter(self.eg.id_counter, self.next_id_at_start as usize);
        }
        result
    }

    fn run_inner(&mut self) -> Result<bool> {
        while !self.pending.is_empty() {
            let mut wave = std::mem::take(&mut self.pending);
            wave.sort_by_key(|(function, _)| (self.eg.info(*function).merge_level, function.rep()));
            for (function, row) in wave {
                self.apply_set(function, &row)?;
            }
            self.pending = std::mem::take(&mut self.next_wave);
        }

        let states = std::mem::take(&mut self.states);
        for function in std::mem::take(&mut self.state_order) {
            let state = states
                .get(&function)
                .expect("merge state order must reference initialized state");
            let n_keys = self.eg.n_keys(function);
            let mut replacements = Vec::new();
            for key in &state.touched {
                let current = state
                    .current
                    .get(key)
                    .expect("a touched merge key must have a current row");
                let original = state.original[key].as_ref();
                let already_normalized = original.is_some_and(|old| {
                    old.rows_for_key == 1
                        && old.location == current.location
                        && old.values == current.values
                });
                if !already_normalized {
                    replacements.push((key.clone(), current.located()));
                }
            }
            self.changed |= self.eg.replace_located_rows(function, n_keys, replacements);
        }

        Ok(self.changed
            || self.eg.db.read_counter(self.eg.id_counter) as u32 != self.next_id_at_start)
    }

    fn ensure_state(&mut self, function: FunctionId, n_keys: usize) {
        if self.states.contains_key(&function) {
            return;
        }
        self.state_order.push(function);
        self.states.insert(
            function,
            FunctionMergeState {
                current: self.eg.current_rows_by_key(function, n_keys),
                ..FunctionMergeState::default()
            },
        );
    }

    fn current_row(
        &mut self,
        function: FunctionId,
        n_keys: usize,
        key: &[u32],
    ) -> Option<CurrentRow> {
        self.ensure_state(function, n_keys);
        self.states[&function].current.get(key).cloned()
    }

    fn set_current(&mut self, function: FunctionId, n_keys: usize, key: Row, current: CurrentRow) {
        self.ensure_state(function, n_keys);
        let state = self
            .states
            .get_mut(&function)
            .expect("merge state was initialized");
        if !state.original.contains_key(&key) {
            state
                .original
                .insert(key.clone(), state.current.get(&key).cloned());
            state.touched.push(key.clone());
        }
        state.current.insert(key, current);
    }

    fn apply_set(&mut self, function: FunctionId, row: &[u32]) -> Result<()> {
        let arity = self.eg.info(function).arity;
        if row.len() != arity {
            return Err(anyhow!(
                "set on `{}` has {} columns, expected {arity}",
                self.eg.relation_name(function),
                row.len()
            ));
        }
        let (n_keys, merge, _, n_identity_vals) = self.eg.function_spec(function);
        let key: Row = row[..n_keys].into();
        let incoming: Row = row[n_keys..].into();
        let Some(old) = self.current_row(function, n_keys, &key) else {
            self.set_current(
                function,
                n_keys,
                key,
                CurrentRow {
                    values: incoming,
                    location: RowLocation::Live,
                    rows_for_key: 1,
                },
            );
            return Ok(());
        };

        let values_unchanged = old.values == incoming;
        let identity_unchanged =
            n_identity_vals.is_some_and(|count| old.values[..count] == incoming[..count]);
        let merged = if values_unchanged || identity_unchanged {
            old.values.clone()
        } else {
            let (actions, result) = match merge.as_ref() {
                MergeFn::Block { actions, result } => (actions.as_slice(), result.as_ref()),
                result => (&[][..], result),
            };
            let mut environment = Vec::new();
            for action in actions {
                self.run_action(action, function, &old.values, &incoming, &mut environment)?;
            }
            let mut values = Vec::with_capacity(incoming.len());
            match result {
                MergeFn::Columns(results) => {
                    for (self_col, expression) in results.iter().enumerate() {
                        values.push(self.eval(
                            expression,
                            function,
                            &old.values,
                            &incoming,
                            self_col,
                            &environment,
                        )?);
                    }
                }
                expression => values.push(self.eval(
                    expression,
                    function,
                    &old.values,
                    &incoming,
                    0,
                    &environment,
                )?),
            }
            values.into_boxed_slice()
        };

        self.set_current(
            function,
            n_keys,
            key,
            CurrentRow {
                values: merged,
                location: old.location,
                rows_for_key: 1,
            },
        );
        Ok(())
    }

    fn run_action(
        &mut self,
        action: &MergeAction,
        owner: FunctionId,
        old: &[u32],
        new: &[u32],
        environment: &mut Vec<u32>,
    ) -> Result<()> {
        match action {
            MergeAction::Set(function, arguments) => {
                let row = self
                    .eval_args(arguments, owner, old, new, 0, environment)?
                    .into_boxed_slice();
                self.next_wave.push((*function, row));
            }
            MergeAction::Let { slot, value } => {
                if *slot != environment.len() {
                    return Err(anyhow!(
                        "merge let slot {slot} for `{}` is out of order; expected {}",
                        self.eg.relation_name(owner),
                        environment.len()
                    ));
                }
                let value = self.eval(value, owner, old, new, 0, environment)?;
                environment.push(value);
            }
            MergeAction::Union(..) => unreachable!("native merge unions are rejected by add_table"),
        }
        Ok(())
    }

    fn eval_args(
        &mut self,
        arguments: &[MergeFn],
        owner: FunctionId,
        old: &[u32],
        new: &[u32],
        self_col: usize,
        environment: &[u32],
    ) -> Result<Vec<u32>> {
        let mut values = Vec::with_capacity(arguments.len());
        for argument in arguments {
            values.push(self.eval(argument, owner, old, new, self_col, environment)?);
        }
        Ok(values)
    }

    fn eval(
        &mut self,
        expression: &MergeFn,
        owner: FunctionId,
        old: &[u32],
        new: &[u32],
        self_col: usize,
        environment: &[u32],
    ) -> Result<u32> {
        match expression {
            MergeFn::AssertEq => {
                if old[self_col] != new[self_col] {
                    return Err(anyhow!(
                        "illegal merge attempted for function `{}`",
                        self.eg.relation_name(owner)
                    ));
                }
                Ok(old[self_col])
            }
            MergeFn::UnionId => Ok(old[self_col].min(new[self_col])),
            MergeFn::Old => Ok(old[self_col]),
            MergeFn::New => Ok(new[self_col]),
            MergeFn::OldCol(index) => Ok(old[*index]),
            MergeFn::NewCol(index) => Ok(new[*index]),
            MergeFn::LetVar(slot) => environment.get(*slot).copied().ok_or_else(|| {
                anyhow!(
                    "merge for `{}` references unbound let slot {slot}",
                    self.eg.relation_name(owner)
                )
            }),
            MergeFn::Const(value) => Ok(value.rep()),
            MergeFn::Primitive(id, arguments) => {
                let args = self.eval_args(arguments, owner, old, new, self_col, environment)?;
                // A custom merge lowered into the FD view's `:merge` may build
                // terms, so the term encoder's `set-if-empty` / view-proof ops can
                // be invoked here too. Service them against the transaction's own
                // view state (the db external function for them only panics).
                if let Some(op) = self.eg.set_if_empty_ops.get(id).cloned() {
                    return self.set_if_empty_in_merge(&op, &args);
                }
                if let Some(op) = self.eg.view_proof_ops.get(id).cloned() {
                    return self.view_proof_in_merge(&op, &args);
                }
                let arguments = args.into_iter().map(Value::new).collect::<Vec<_>>();
                self.eg
                    .eval_prim_internal(*id, &arguments)?
                    .map(|value| value.rep())
                    .ok_or_else(|| {
                        anyhow!(
                            "merge primitive failed for function `{}`",
                            self.eg.relation_name(owner)
                        )
                    })
            }
            MergeFn::Function(function, arguments) => {
                if old[self_col] == new[self_col] {
                    return Ok(old[self_col]);
                }
                let key = self.eval_args(arguments, owner, old, new, self_col, environment)?;
                self.lookup_or_insert(*function, &key)?
                    .map(|values| values[0])
                    .ok_or_else(|| {
                        anyhow!(
                            "lookup on `{}` failed in merge function for `{}`",
                            self.eg.relation_name(*function),
                            self.eg.relation_name(owner)
                        )
                    })
            }
            MergeFn::Lookup(function, arguments) => {
                let key = self.eval_args(arguments, owner, old, new, self_col, environment)?;
                Ok(self
                    .lookup_or_insert(*function, &key)?
                    .map_or(old[self_col], |values| values[0]))
            }
            MergeFn::Columns(_) | MergeFn::Block { .. } => {
                unreachable!("nested merge programs are rejected by add_table")
            }
        }
    }

    fn lookup_or_insert(&mut self, function: FunctionId, key: &[u32]) -> Result<Option<Row>> {
        let (n_keys, _, default, _) = self.eg.function_spec(function);
        if key.len() != n_keys {
            return Err(anyhow!(
                "lookup on `{}` has {} keys, expected {n_keys}",
                self.eg.relation_name(function),
                key.len()
            ));
        }
        if let Some(current) = self.current_row(function, n_keys, key) {
            return Ok(Some(current.values));
        }
        if self.eg.n_vals(function) != 1 {
            return Err(anyhow!(
                "lookup on missing tuple-output function `{}` needs explicit additional output values",
                self.eg.relation_name(function)
            ));
        }
        let value = match default {
            TableDefault::FreshId => self.eg.fresh_id_internal(),
            TableDefault::Const(value) => value,
            TableDefault::Fail => return Ok(None),
        };
        let values = vec![value].into_boxed_slice();
        self.set_current(
            function,
            n_keys,
            key.into(),
            CurrentRow {
                values: values.clone(),
                location: RowLocation::Live,
                rows_for_key: 1,
            },
        );
        Ok(Some(values))
    }

    /// Service a `set-if-empty` op invoked from inside a merge, against the
    /// transaction's staged view state: return the e-class of the current
    /// `(view keys)` row, or stage `(keys, default_vals)` and return the default
    /// e-class. Mirrors [`crate::interpret`]'s action-time handler, but reads and
    /// writes the transaction so same-transaction inserts and rollback apply.
    fn set_if_empty_in_merge(&mut self, op: &ViewOp, args: &[u32]) -> Result<u32> {
        let view = self.view_op_table(op)?;
        let n_keys = op.n_keys;
        let key: Row = args[..n_keys].into();
        if let Some(current) = self.current_row(view, n_keys, &key) {
            return Ok(current.values[0]);
        }
        let values: Row = args[n_keys..n_keys + op.out_arity].into();
        let eclass = values[0];
        self.set_current(
            view,
            n_keys,
            key,
            CurrentRow {
                values,
                location: RowLocation::Live,
                rows_for_key: 1,
            },
        );
        Ok(eclass)
    }

    /// Service a view-proof read invoked from inside a merge: the proof column
    /// (output col 1) of the current `(view keys)` row, or the `fallback` arg.
    fn view_proof_in_merge(&mut self, op: &ViewOp, args: &[u32]) -> Result<u32> {
        let view = self.view_op_table(op)?;
        let n_keys = op.n_keys;
        let key: Row = args[..n_keys].into();
        let fallback = args[n_keys];
        Ok(match self.current_row(view, n_keys, &key) {
            Some(current) => current.values[1],
            None => fallback,
        })
    }

    fn view_op_table(&self, op: &ViewOp) -> Result<FunctionId> {
        self.eg
            .table_ids
            .get(&op.view_name)
            .copied()
            .ok_or_else(|| anyhow!("view op table `{}` is not registered", op.view_name))
    }
}

fn row_with_values(key: &[u32], values: &[u32]) -> Row {
    let mut row = key.to_vec();
    row.extend_from_slice(values);
    row.into_boxed_slice()
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
        Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunctionId, FunctionConfig,
        MergeAction, MergeFn, ReadMode, RuleActionCall, RuleBodyCall, RuleId, RuleSetRun, RuleSpec,
        RuleValue, RuleVar, Value,
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
            self.set_values(id, args, std::slice::from_ref(value));
        }

        fn set_values(&mut self, id: FunctionId, keys: &[RuleTerm], values: &[RuleTerm]) {
            self.spec.core.head.0.push(GenericCoreAction::Set(
                Span::Panic,
                RuleActionCall::Table {
                    id,
                    name: "table".into(),
                },
                keys.to_vec(),
                values.to_vec(),
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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: name.to_string(),
                can_subsume: false,
            },
        )
    }

    fn tuple_function(
        eg: &mut EGraph,
        name: &str,
        merge: MergeFn,
        n_identity_vals: Option<usize>,
        can_subsume: bool,
    ) -> FunctionId {
        Backend::add_table(
            eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
                n_vals: 2,
                n_identity_vals,
                default: DefaultVal::Fail,
                merge,
                name: name.to_string(),
                can_subsume,
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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
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
    fn tuple_merge_reads_all_old_and_new_columns_atomically() {
        let mut eg = EGraph::new();
        let f = tuple_function(
            &mut eg,
            "tuple",
            MergeFn::Columns(vec![MergeFn::NewCol(1), MergeFn::OldCol(0)]),
            None,
            false,
        );
        eg.insert_live_row(f, row(&[1, 10, 20]));

        assert!(eg.apply_sets(vec![(f, row(&[1, 30, 40]))]).unwrap());
        assert_eq!(eg.mirror[&f], HashSet::from([row(&[1, 40, 10])]));
    }

    #[test]
    #[should_panic(expected = "references OldCol(1) but has only 1 value columns")]
    fn merge_rejects_out_of_range_output_column() {
        let mut eg = EGraph::new();
        id_function(&mut eg, "invalid column", MergeFn::OldCol(1));
    }

    #[test]
    #[should_panic(expected = "declares let slot 1, expected 0")]
    fn merge_rejects_out_of_order_let_slot() {
        let mut eg = EGraph::new();
        id_function(
            &mut eg,
            "invalid let",
            MergeFn::Block {
                actions: vec![MergeAction::Let {
                    slot: 1,
                    value: MergeFn::Old,
                }],
                result: Box::new(MergeFn::Old),
            },
        );
    }

    #[test]
    fn failed_tuple_merge_rolls_back_fresh_ids_and_staged_rows() {
        let mut eg = EGraph::new();
        let fresh = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                n_vals: 1,
                n_identity_vals: None,
                default: DefaultVal::FreshId,
                merge: MergeFn::Old,
                name: "fresh".to_string(),
                can_subsume: false,
            },
        );
        let f = tuple_function(
            &mut eg,
            "failing tuple",
            MergeFn::Columns(vec![
                MergeFn::Lookup(fresh, vec![MergeFn::Const(Value::new(7))]),
                MergeFn::AssertEq,
            ]),
            None,
            false,
        );
        eg.insert_live_row(f, row(&[1, 10, 20]));
        let next_id = eg.db.read_counter(eg.id_counter);

        let error = eg.apply_sets(vec![(f, row(&[1, 30, 40]))]).unwrap_err();

        assert!(error.to_string().contains("illegal merge attempted"));
        assert_eq!(eg.db.read_counter(eg.id_counter), next_id);
        assert!(eg.mirror[&fresh].is_empty());
        assert_eq!(eg.mirror[&f], HashSet::from([row(&[1, 10, 20])]));
    }

    #[test]
    fn identical_row_skips_recursive_merge_actions() {
        let mut eg = EGraph::new();
        let function = Backend::peek_next_function_id(&eg);
        let actual = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                n_vals: 1,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge: MergeFn::Block {
                    actions: vec![MergeAction::Set(
                        function,
                        vec![MergeFn::Const(Value::new(1)), MergeFn::Old],
                    )],
                    result: Box::new(MergeFn::Old),
                },
                name: "recursive".to_string(),
                can_subsume: false,
            },
        );
        assert_eq!(actual, function);
        eg.insert_live_row(function, row(&[1, 10]));

        let mut transaction = MergeTransaction::new(&mut eg, Vec::new());
        transaction.apply_set(function, &[1, 10]).unwrap();

        assert!(transaction.next_wave.is_empty());
    }

    #[test]
    fn identity_column_guard_skips_payload_only_conflicts() {
        let mut eg = EGraph::new();
        let f = tuple_function(
            &mut eg,
            "guarded",
            MergeFn::Columns(vec![MergeFn::NewCol(0), MergeFn::NewCol(1)]),
            Some(1),
            false,
        );
        eg.insert_live_row(f, row(&[1, 10, 100]));

        assert!(!eg.apply_sets(vec![(f, row(&[1, 10, 200]))]).unwrap());
        assert_eq!(eg.mirror[&f], HashSet::from([row(&[1, 10, 100])]));

        assert!(eg.apply_sets(vec![(f, row(&[1, 20, 300]))]).unwrap());
        assert_eq!(eg.mirror[&f], HashSet::from([row(&[1, 20, 300])]));
    }

    #[test]
    fn block_let_var_feeds_set_and_tuple_result() {
        let mut eg = EGraph::new();
        let side = id_function(&mut eg, "side", MergeFn::Old);
        let max = max_primitive(&mut eg);
        let f = tuple_function(
            &mut eg,
            "block",
            MergeFn::Block {
                actions: vec![
                    MergeAction::Let {
                        slot: 0,
                        value: MergeFn::Primitive(
                            max,
                            vec![MergeFn::OldCol(0), MergeFn::NewCol(0)],
                        ),
                    },
                    MergeAction::Set(
                        side,
                        vec![MergeFn::Const(Value::new(7)), MergeFn::LetVar(0)],
                    ),
                ],
                result: Box::new(MergeFn::Columns(vec![
                    MergeFn::LetVar(0),
                    MergeFn::NewCol(1),
                ])),
            },
            None,
            false,
        );
        eg.insert_live_row(f, row(&[1, 10, 100]));

        assert!(eg.apply_sets(vec![(f, row(&[1, 20, 200]))]).unwrap());
        assert_eq!(eg.mirror[&f], HashSet::from([row(&[1, 20, 200])]));
        assert_eq!(eg.mirror[&side], HashSet::from([row(&[7, 20])]));
    }

    #[test]
    fn recursive_self_write_reaches_a_fixed_point() {
        let mut eg = EGraph::new();
        let max = max_primitive(&mut eg);
        let uf = Backend::peek_next_function_id(&eg);
        let actual = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                n_vals: 1,
                n_identity_vals: Some(1),
                default: DefaultVal::Fail,
                merge: MergeFn::Block {
                    actions: vec![MergeAction::Set(
                        uf,
                        vec![
                            MergeFn::Primitive(max, vec![MergeFn::Old, MergeFn::New]),
                            MergeFn::UnionId,
                        ],
                    )],
                    result: Box::new(MergeFn::UnionId),
                },
                name: "uf".to_string(),
                can_subsume: false,
            },
        );
        assert_eq!(actual, uf);

        assert!(eg
            .apply_sets(vec![(uf, row(&[5, 3])), (uf, row(&[5, 1]))])
            .unwrap());
        assert!(eg.mirror[&uf].contains(&row(&[5, 1])));
        assert!(eg.mirror[&uf].contains(&row(&[3, 1])));
    }

    #[test]
    fn tuple_rule_set_writes_all_value_columns() {
        let mut eg = EGraph::new();
        let trigger = id_table(&mut eg, "trigger", 1);
        let tuple = tuple_function(
            &mut eg,
            "tuple-output",
            MergeFn::Columns(vec![MergeFn::OldCol(0), MergeFn::OldCol(1)]),
            None,
            false,
        );
        eg.insert_live_row(trigger, row(&[0]));
        let mut rule = TestRule::new("tuple set");
        rule.query_table(trigger, &[constant(0, ColumnTy::Id)], Some(false));
        rule.set_values(
            tuple,
            &[constant(1, ColumnTy::Id)],
            &[constant(10, ColumnTy::Id), constant(20, ColumnTy::Id)],
        );
        let rule = rule.build(&mut eg);

        run_rules(&mut eg, &[rule]).unwrap();
        assert_eq!(eg.mirror[&tuple], HashSet::from([row(&[1, 10, 20])]));
    }

    #[test]
    fn tuple_merge_preserves_subsumed_status() {
        let mut eg = EGraph::new();
        let f = tuple_function(
            &mut eg,
            "subsumed tuple",
            MergeFn::Columns(vec![MergeFn::NewCol(0), MergeFn::NewCol(1)]),
            None,
            true,
        );
        eg.subsumed.entry(f).or_default().insert(row(&[1, 10, 20]));

        assert!(eg.apply_sets(vec![(f, row(&[1, 30, 40]))]).unwrap());
        assert!(eg.mirror[&f].is_empty());
        assert_eq!(eg.subsumed[&f], HashSet::from([row(&[1, 30, 40])]));
    }

    #[test]
    fn merge_set_preserves_subsumed_status() {
        let mut eg = EGraph::new();
        let f = id_function(&mut eg, "f", MergeFn::New);
        eg.subsumed.entry(f).or_default().insert(row(&[1, 10]));

        assert!(eg.apply_sets(vec![(f, row(&[1, 11]))]).unwrap());

        assert!(!eg.mirror[&f].contains(&row(&[1, 11])));
        assert!(!eg.subsumed[&f].contains(&row(&[1, 10])));
        assert!(eg.subsumed[&f].contains(&row(&[1, 11])));
    }

    #[test]
    fn lookup_or_create_finds_subsumed_rows() {
        let mut eg = EGraph::new();
        let f = id_function(&mut eg, "f", MergeFn::New);
        eg.db.set_counter(eg.id_counter, 100);
        eg.subsumed.entry(f).or_default().insert(row(&[42, 7]));

        let mut lookup_index = HashMap::new();
        let value =
            interpret::lookup_or_create(&mut eg, f, &[Value::new(42)], &mut lookup_index).unwrap();

        assert_eq!(value[0], 7);
        assert_eq!(eg.db.read_counter(eg.id_counter), 100);
        assert!(eg.mirror[&f].is_empty());
    }

    #[test]
    fn merge_set_collapses_live_subsumed_key_duplicate() {
        let mut eg = EGraph::new();
        let f = id_function(&mut eg, "f", MergeFn::New);
        eg.mirror.entry(f).or_default().insert(row(&[1, 10]));
        eg.subsumed.entry(f).or_default().insert(row(&[1, 11]));

        assert!(eg.apply_sets(vec![(f, row(&[1, 12]))]).unwrap());

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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
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
        assert_eq!(cloned.id_counter, eg.id_counter);
        assert_eq!(
            cloned.db.read_counter(cloned.id_counter),
            eg.db.read_counter(eg.id_counter)
        );
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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
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
                n_vals: 1,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "Dummy".to_string(),
                can_subsume: false,
            },
        );
        eg.insert_live_row(view, row(&[10, 0]));
        assert!(eg.apply_sets(vec![(current, row(&[10]))]).unwrap());

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
        assert!(eg.apply_sets(vec![(current, row(&[4]))]).unwrap());

        run_rules(&mut eg, &[view_first_rule, cleanup_rule]).unwrap();

        assert!(eg.mirror[&view].contains(&row(&[4, 0])));
        assert!(!eg.mirror[&view].contains(&row(&[10, 0])));
    }
}

// impl Backend
// ---------------------------------------------------------------------------

impl Backend for EGraph {
    // -- table lifecycle ----------------------------------------------------

    fn add_table(&mut self, config: FunctionConfig) -> FunctionId {
        let id = FunctionId::new(self.relations.len() as u32);
        let arity = config.schema.len();
        assert!(
            (1..=arity).contains(&config.n_vals),
            "function `{}` declares {} output columns but has {arity} columns total",
            config.name,
            config.n_vals
        );
        assert!(
            arity <= dd_native::W,
            "DD backend fixed row width supports relations of arity <= {} (got {} for `{}`)",
            dd_native::W,
            arity,
            config.name
        );
        if let Some(count) = config.n_identity_vals {
            assert!(
                (1..=config.n_vals).contains(&count),
                "function `{}` declares {count} identity columns but has {} value columns",
                config.name,
                config.n_vals
            );
        }
        let n_keys = arity - config.n_vals;
        let default = match config.default {
            DefaultVal::FreshId => TableDefault::FreshId,
            DefaultVal::Fail => TableDefault::Fail,
            DefaultVal::Const(value) => TableDefault::Const(value.rep()),
        };
        validate_merge(&config.merge, config.n_vals, &config.name);
        let merge = Arc::new(config.merge);
        let mut merge_level = 0;
        visit_merge_read_dependencies(&merge, &mut |dependency| {
            let dependency = self
                .relations
                .get(dependency.rep() as usize)
                .unwrap_or_else(|| {
                    panic!(
                        "merge for `{}` reads function id {} before it is registered",
                        config.name,
                        dependency.rep()
                    )
                });
            merge_level = merge_level.max(dependency.merge_level + 1);
        });
        self.table_ids.insert(config.name.clone(), id);
        self.relations.push(RelationInfo {
            name: config.name,
            arity,
            n_keys,
            merge,
            default,
            n_identity_vals: config.n_identity_vals,
            merge_level,
        });
        self.mirror.insert(id, HashSet::new());
        id
    }

    fn peek_next_function_id(&self) -> FunctionId {
        FunctionId::new(self.relations.len() as u32)
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

    fn lookup_row(&self, func: FunctionId, key: &[Value]) -> Option<Vec<Value>> {
        let info = self.info(func);
        if key.len() != info.n_keys {
            return None;
        }
        let key = key.iter().map(|value| value.rep()).collect::<Vec<_>>();
        let find = |rows: Option<&HashSet<Row>>| {
            rows?
                .iter()
                .find(|row| row[..key.len()] == key[..])
                .map(|row| row[..info.arity].iter().copied().map(Value::new).collect())
        };
        find(self.mirror.get(&func)).or_else(|| find(self.subsumed.get(&func)))
    }

    fn lookup_id(&self, func: FunctionId, key: &[Value]) -> Option<Value> {
        self.lookup_row(func, key).map(|row| row[key.len()])
    }

    fn container_values_mut_dyn(&mut self) -> Option<&mut ContainerValues> {
        Some(self.db.container_values_mut())
    }

    fn new_container_id_counter(&mut self) -> Option<CounterId> {
        Some(self.db.add_counter())
    }

    fn eclass_id_counter(&self) -> Option<CounterId> {
        // Same counter `fresh_id_internal` mints from, so the term encoder's
        // `get-fresh!` ids and native `FreshId`-default ids share one id space.
        Some(self.id_counter)
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

    fn fresh_eclass_id(&mut self) -> Value {
        Value::new(self.fresh_id_internal())
    }

    fn add_values(&mut self, values: Vec<(FunctionId, Vec<Value>)>) {
        // Insert each logical row (keys + value columns) straight into the mirror.
        // Duplicate view keys are resolved by the view's `:merge` on the next run.
        for (func, row) in values {
            let r: Row = row.iter().map(|v| v.rep()).collect();
            self.insert_live_row(func, r);
        }
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

    fn register_set_if_empty(
        &mut self,
        view_name: String,
        n_keys: usize,
        out_arity: usize,
    ) -> ExternalFunctionId {
        // The interpreter intercepts this id and services it against the mirror
        // (see `interpret::apply_head`); the registered db function only fires if
        // that interception is ever missed, so make it a loud error.
        let id = Backend::new_panic(
            self,
            format!("set-if-empty for `{view_name}` reached the db path; DD must intercept it"),
        );
        self.set_if_empty_ops.insert(
            id,
            ViewOp {
                view_name,
                n_keys,
                out_arity,
            },
        );
        id
    }

    fn register_view_proof(&mut self, view_name: String, n_keys: usize) -> ExternalFunctionId {
        let id = Backend::new_panic(
            self,
            format!("view-proof for `{view_name}` reached the db path; DD must intercept it"),
        );
        self.view_proof_ops.insert(
            id,
            ViewOp {
                view_name,
                n_keys,
                // A view-proof reader never inserts, so out_arity is unused; the
                // view always has (eclass, proof) outputs.
                out_arity: 2,
            },
        );
        id
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
            id_counter: self.id_counter,
            seen: self.seen.clone(),
            dd_fused: DdWorkers::default(),
            next_row_version: self.next_row_version,
            live_versions: self.live_versions.clone(),
            all_versions: self.all_versions.clone(),
            subsumed_versions: self.subsumed_versions.clone(),
            dd_fused_fed_versions: HashMap::new(),
            panic_message: Arc::clone(&self.panic_message),
            table_ids: self.table_ids.clone(),
            set_if_empty_ops: self.set_if_empty_ops.clone(),
            view_proof_ops: self.view_proof_ops.clone(),
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
