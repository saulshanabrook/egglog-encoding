//! # egglog-experimental-flowlog
//!
//! A differential-dataflow-backed implementation of egglog's
//! [`egglog_backend_trait::Backend`] interface.
//!
//! One `run_rules` call is one bounded egglog iteration. Each rule's body
//! table-atom join runs on an in-process differential-dataflow dataflow
//! ([`dd_native`]); the body primitive tail and head actions are applied
//! host-side ([`interpret`]) into a Rust-side materialized mirror of every
//! relation. `for_each` / `lookup_id` / `table_size` read that mirror.

use std::any::Any;

use anyhow::Result;
use egglog_backend_trait::{
    Backend, BaseValues, ColumnTy, ContainerValues, CounterId, DefaultVal, ExecutionState,
    ExternalFunction, ExternalFunctionId, FunctionConfig, FunctionId, IterationReport, MergeFn,
    ReportLevel, RuleBuilderOps, RuleId, ScanEntry, Value,
};
use egglog_core_relations::Database;
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};

pub mod compile;
pub mod dd_native;
mod external_func;
pub mod interpret;
mod rule_builder;

use compile::{row_col, unpack_row, MergeMode, MergeTree, ReadKey, Row, RuleIr};

type MergeUpdate = (Box<[u32]>, Option<(u32, RowLocation)>, (u32, RowLocation));

// ---------------------------------------------------------------------------
// Relation metadata
// ---------------------------------------------------------------------------

/// What we remember about each registered relation/function.
pub(crate) struct RelationInfo {
    #[allow(dead_code)]
    name: String,
    /// Number of columns (including the output column for functions).
    pub(crate) arity: usize,
    /// True for functions/constructors that have an output column.
    #[allow(dead_code)]
    has_output: bool,
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
    pub(crate) rules: Vec<Option<RuleIr>>,
    /// Rust-side materialized mirror: the accumulated contents of each relation.
    /// This is what `for_each` / `lookup_id` / `table_size` read.
    ///
    /// The set per function is shared by `Rc` so the per-iteration read snapshot
    /// (see `interpret::run_iteration`) is O(#functions), not O(state):
    /// mutations copy-on-write via `Rc::make_mut` only the functions actually
    /// changed while a snapshot is alive.
    pub(crate) mirror: HashMap<FunctionId, std::rc::Rc<HashSet<Row>>>,
    /// Subsumed rows, moved OUT of `mirror` by `(subsume …)` (a "soft delete").
    /// Ordinary queries (`is_subsumed = Some(false)`) read only `mirror`, so
    /// subsumed rows are excluded for free; `:internal-include-subsumed` rules and
    /// `for_each` read `mirror` ∪ `subsumed`. Keyed like `mirror`, by `FunctionId`.
    pub(crate) subsumed: HashMap<FunctionId, std::rc::Rc<HashSet<Row>>>,
    /// A core-relations [`Database`] used purely as the base-value / primitive
    /// engine, so `Value`s are bit-for-bit identical to the reference backend.
    db: Database,
    /// Monotonic fresh-id counter for `fresh_id` / `add_term`.
    pub(crate) next_id: u32,
    report_level: ReportLevel,
    /// Diagnostics: rule firings whose body join ran on the DD engine.
    pub(crate) dd_rule_runs: u64,
    /// Atom-less rules (`(rule () …)`) fire ONCE; an entry here marks a rule
    /// index as already fired. The DD dataflow has no input relation to drive an
    /// atom-less body, so this fired-marker is the one piece of seminaive
    /// bookkeeping the DD path reuses (see `interpret::dd_native_bindings`).
    /// `free_rule` removes the entry so a re-installed rule can fire again.
    pub(crate) seen: HashMap<usize, ()>,
    /// Per-RULESET fused DD join (one shared timely worker + one dataflow for the
    /// whole ruleset), keyed by the sorted live rule-index list. This is the
    /// join path the interpreter drives.
    pub(crate) dd_fused: HashMap<Vec<usize>, dd_native::FusedDdJoin>,
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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RowLocation {
    Live,
    Subsumed,
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new_interpret()
    }
}

impl EGraph {
    /// Construct a fresh DD-backed egraph. Rule bodies run on the in-process
    /// differential-dataflow join; body primitives and head actions are applied
    /// host-side into the mirror. This is the constructor the egglog frontend
    /// uses (`EGraph::with_flowlog_backend`).
    pub fn new_interpret() -> Self {
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
            report_level: ReportLevel::default(),
            dd_rule_runs: 0,
            seen: HashMap::new(),
            dd_fused: HashMap::new(),
            next_row_version: 1,
            live_versions: HashMap::new(),
            all_versions: HashMap::new(),
            subsumed_versions: HashMap::new(),
            dd_fused_fed_versions: HashMap::new(),
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

    /// Inherent accessor for the embedded [`BaseValues`] registry (the frontend
    /// extraction path threads `&BaseValues` through `reconstruct_termdag_base`).
    pub fn base_values_inner(&self) -> &egglog_core_relations::BaseValues {
        self.db.base_values()
    }

    /// Inherent accessor for the embedded [`Database`]'s container registry, so
    /// the frontend extraction path can read interned container values.
    pub fn container_values_inner(&self) -> &egglog_core_relations::ContainerValues {
        self.db.container_values()
    }

    /// Diagnostics: the number of rule firings whose body table-atom join ran on
    /// the in-process Differential-Dataflow dataflow. Every atom-bearing rule
    /// runs there (no host fallback); lets a test assert the join genuinely ran
    /// on DD.
    pub fn flowlog_dd_rule_runs(&self) -> u64 {
        self.dd_rule_runs
    }

    /// The functional-dependency merge mode of a function (from `add_table`).
    pub(crate) fn merge_mode(&self, f: FunctionId) -> MergeMode {
        self.info(f).merge
    }

    /// Evaluate a primitive through the embedded `Database` (the base-value /
    /// primitive engine). Both the host interpreter and the DD-join path's
    /// host-side primitive tail call this, so `Value`s are bit-for-bit
    /// identical to the reference backend.
    pub(crate) fn eval_prim_internal(
        &self,
        id: ExternalFunctionId,
        args: &[Value],
    ) -> Option<Value> {
        self.db
            .with_execution_state(|st| st.call_external_func(id, args))
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
        let mut orig: HashMap<Box<[u32]>, Option<(u32, RowLocation)>> = HashMap::new();
        for row in rows {
            let key: Box<[u32]> = row[..inputs_len].into();
            let nv = row_col(row, inputs_len);
            let existing = cur.get(&key).copied();
            orig.entry(key.clone()).or_insert(existing);
            let existing_value = existing.map(|(value, _)| value);
            let merged = match (existing_value, merge) {
                (None, _) => nv,
                (Some(_), MergeMode::New) => nv,
                (Some(c), MergeMode::Old) => c,
                (Some(c), MergeMode::Min) => c.min(nv),
                // Relation is filtered by the caller; Computed took the branch above.
                (Some(c), MergeMode::Relation | MergeMode::Computed) => c,
            };
            let location = existing
                .map(|(_, location)| location)
                .unwrap_or(RowLocation::Live);
            cur.insert(key, (merged, location));
        }
        // Apply the net change per touched key.
        let mut changed = false;
        for (key, old) in orig {
            let new = cur[&key];
            changed |= self.reconcile_located_row(f, &key, old, new);
        }
        Ok(changed)
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
            let v = row_col(row, inputs_len);
            match newv.get_mut(&key) {
                Some(vs) => vs.push(v),
                None => {
                    order.push(key.clone());
                    newv.insert(key, vec![v]);
                }
            }
        }
        // The merge tree, cloned out so the evaluator can borrow `&mut self`.
        let tree = self
            .info(f)
            .merge_tree
            .clone()
            .expect("Computed merge has a merge tree");
        let mut lookup_index: HashMap<FunctionId, HashMap<Box<[u32]>, u32>> = HashMap::new();
        // Fold each touched key: start from the current value, fold in each new
        // value via the tree (`old` = accumulator, `new` = the value).
        let mut updates: Vec<MergeUpdate> = Vec::new();
        for key in order {
            let old = cur.get(&key).copied();
            let location = old
                .map(|(_, location)| location)
                .unwrap_or(RowLocation::Live);
            let mut acc = old.map(|(value, _)| value);
            for &nv in &newv[&key] {
                acc = Some(match acc {
                    None => nv,
                    Some(c) => self.eval_merge_tree(&tree, c, nv, &mut lookup_index)?,
                });
            }
            let new_val = acc.unwrap();
            let new = (new_val, location);
            if Some(new) != old {
                updates.push((key, old, new));
            }
        }
        // Reconcile the mirror. A `Func` node that minted an e-node advanced
        // `next_id` — that is itself a real change even if no value flipped.
        let mut changed = self.next_id != next_id_before;
        for (key, old, new) in updates {
            changed |= self.reconcile_located_row(f, &key, old, new);
        }
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
                    .eval_prim_internal(*id, &argv)
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
            let live = std::rc::Rc::make_mut(self.mirror.get_mut(&f).unwrap());
            for r in &moved {
                live.remove(r);
            }
        }
        for r in &moved {
            self.record_row_event(f, r.clone(), -1, 0, 1);
        }
        let subs = std::rc::Rc::make_mut(self.subsumed.entry(f).or_default());
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
        let inserted = std::rc::Rc::make_mut(self.mirror.entry(f).or_default()).insert(row.clone());
        if inserted {
            self.record_row_event(f, row, 1, 1, 0);
        }
        inserted
    }

    fn current_values_by_key(
        &self,
        f: FunctionId,
        inputs_len: usize,
    ) -> HashMap<Box<[u32]>, (u32, RowLocation)> {
        let live_len = self.mirror.get(&f).map(|set| set.len()).unwrap_or(0);
        let subsumed_len = self.subsumed.get(&f).map(|set| set.len()).unwrap_or(0);
        let mut cur = HashMap::with_capacity(live_len + subsumed_len);
        if let Some(set) = self.mirror.get(&f) {
            for row in set.iter() {
                let key: Box<[u32]> = row[..inputs_len].into();
                cur.insert(key, (row_col(row, inputs_len), RowLocation::Live));
            }
        }
        if let Some(set) = self.subsumed.get(&f) {
            for row in set.iter() {
                let key: Box<[u32]> = row[..inputs_len].into();
                cur.insert(key, (row_col(row, inputs_len), RowLocation::Subsumed));
            }
        }
        cur
    }

    fn reconcile_located_row(
        &mut self,
        f: FunctionId,
        key: &[u32],
        old: Option<(u32, RowLocation)>,
        new: (u32, RowLocation),
    ) -> bool {
        if Some(new) == old && self.key_is_normalized_to(f, key, new) {
            return false;
        }
        let was_normalized = self.key_is_normalized_to(f, key, new);
        self.remove_key_from_all_locations(f, key);
        let new_row = row_with_value(key, new.0);
        self.insert_located_row(f, new.1, new_row);
        Some(new) != old || !was_normalized
    }

    fn key_is_normalized_to(
        &self,
        f: FunctionId,
        key: &[u32],
        expected: (u32, RowLocation),
    ) -> bool {
        let expected_row = row_with_value(key, expected.0);
        let mut matching_rows = 0;
        let mut found_expected = false;
        for (location, store) in [
            (RowLocation::Live, &self.mirror),
            (RowLocation::Subsumed, &self.subsumed),
        ] {
            if let Some(rows) = store.get(&f) {
                for row in rows.iter().filter(|row| row_key_matches(row, key)) {
                    matching_rows += 1;
                    found_expected |=
                        location == expected.1 && row.as_ref() == expected_row.as_ref();
                }
            }
        }
        matching_rows == 1 && found_expected
    }

    fn remove_key_from_all_locations(&mut self, f: FunctionId, key: &[u32]) {
        let removed_live = remove_key_from_store(&mut self.mirror, f, key);
        for row in removed_live {
            self.record_row_event(f, row, -1, -1, 0);
        }
        let removed_subsumed = remove_key_from_store(&mut self.subsumed, f, key);
        for row in removed_subsumed {
            self.record_row_event(f, row, 0, -1, -1);
        }
    }

    fn insert_located_row(&mut self, f: FunctionId, location: RowLocation, row: Row) -> bool {
        let store = match location {
            RowLocation::Live => &mut self.mirror,
            RowLocation::Subsumed => &mut self.subsumed,
        };
        let inserted = std::rc::Rc::make_mut(store.entry(f).or_default()).insert(row.clone());
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

fn row_with_value(key: &[u32], value: u32) -> Row {
    let mut row = key.to_vec();
    row.push(value);
    row.into_boxed_slice()
}

fn row_key_matches(row: &Row, key: &[u32]) -> bool {
    row.len() >= key.len() && &row[..key.len()] == key
}

fn remove_key_from_store(
    store: &mut HashMap<FunctionId, std::rc::Rc<HashSet<Row>>>,
    f: FunctionId,
    key: &[u32],
) -> Vec<Row> {
    let mut removed = Vec::new();
    if let Some(rows) = store.get_mut(&f) {
        std::rc::Rc::make_mut(rows).retain(|row| {
            if row_key_matches(row, key) {
                removed.push(row.clone());
                false
            } else {
                true
            }
        });
    }
    removed
}

fn remove_keys_from_store(
    store: &mut HashMap<FunctionId, std::rc::Rc<HashSet<Row>>>,
    f: FunctionId,
    keylen: usize,
    keys: &HashSet<Box<[u32]>>,
) -> Vec<Row> {
    let mut removed = Vec::new();
    if let Some(rows) = store.get_mut(&f) {
        std::rc::Rc::make_mut(rows).retain(|row| {
            let k: Box<[u32]> = (0..keylen).map(|i| row_col(row, i)).collect();
            if keys.contains(&k) {
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

// ---------------------------------------------------------------------------
// Send + Sync (single-threaded use)
// ---------------------------------------------------------------------------
//
// The embedded differential-dataflow worker and its handles are not all
// auto-`Send`/`Sync`. The egraph is only ever driven from a single thread, so
// we assert the bounds the trait requires. Concurrent multi-thread use is
// unsupported.
unsafe impl Send for EGraph {}
unsafe impl Sync for EGraph {}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod tests {
    use super::*;
    use egglog_backend_trait::{
        Backend, ColumnTy, DefaultVal, FunctionConfig, MergeFn, QueryEntry, Value,
    };
    use egglog_numeric_id::NumericId;

    fn row(vals: &[u32]) -> Row {
        vals.to_vec().into_boxed_slice()
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

    #[test]
    fn merge_set_preserves_subsumed_status() {
        let mut eg = EGraph::new_interpret();
        let f = id_function(&mut eg, "f", MergeFn::New);
        std::rc::Rc::make_mut(eg.subsumed.entry(f).or_default()).insert(row(&[1, 10]));

        assert!(eg.apply_merge_sets(f, &[row(&[1, 11])]).unwrap());

        assert!(!eg.mirror[&f].contains(&row(&[1, 11])));
        assert!(!eg.subsumed[&f].contains(&row(&[1, 10])));
        assert!(eg.subsumed[&f].contains(&row(&[1, 11])));
    }

    #[test]
    fn lookup_or_create_finds_subsumed_rows() {
        let mut eg = EGraph::new_interpret();
        let f = id_function(&mut eg, "f", MergeFn::New);
        eg.next_id = 100;
        std::rc::Rc::make_mut(eg.subsumed.entry(f).or_default()).insert(row(&[42, 7]));

        let mut lookup_index = HashMap::new();
        let value = interpret::lookup_or_create(&mut eg, f, &[Value::new(42)], &mut lookup_index);

        assert_eq!(value.rep(), 7);
        assert_eq!(eg.next_id, 100);
        assert!(eg.mirror[&f].is_empty());
    }

    #[test]
    fn merge_set_collapses_live_subsumed_key_duplicate() {
        let mut eg = EGraph::new_interpret();
        let f = id_function(&mut eg, "f", MergeFn::New);
        std::rc::Rc::make_mut(eg.mirror.entry(f).or_default()).insert(row(&[1, 10]));
        std::rc::Rc::make_mut(eg.subsumed.entry(f).or_default()).insert(row(&[1, 11]));

        assert!(eg.apply_merge_sets(f, &[row(&[1, 12])]).unwrap());

        assert!(eg.mirror[&f].is_empty());
        assert_eq!(eg.subsumed[&f].len(), 1);
        assert!(eg.subsumed[&f].contains(&row(&[1, 12])));
    }

    #[test]
    fn same_table_self_join_produces_cross_pairs() {
        let mut eg = EGraph::new_interpret();
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
        let relation = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "R".to_string(),
                can_subsume: false,
            },
        );
        let out = Backend::add_table(
            &mut eg,
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

        let rule = {
            let mut rb = Backend::new_rule(&mut eg, "self_join", true);
            let a = rb.new_var(ColumnTy::Id);
            let b = rb.new_var(ColumnTy::Id);
            let c = rb.new_var(ColumnTy::Id);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(relation, &[a.clone(), b.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_table(relation, &[a.clone(), c.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.set(out, &[a, b, c, unit]);
            rb.build().unwrap()
        };

        Backend::run_rules(&mut eg, &[rule]).unwrap();

        assert!(eg.mirror[&out].contains(&row(&[1, 2, 3, 0])));
        assert!(eg.mirror[&out].contains(&row(&[1, 3, 2, 0])));
    }

    #[test]
    fn fused_ruleset_allows_mixed_read_modes_same_relation() {
        let mut eg = EGraph::new_interpret();
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
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
            let mut rb = Backend::new_rule(&mut eg, "live_read", true);
            let x = rb.new_var(ColumnTy::Id);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(relation, &[x.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.set(live_out, &[x, unit]);
            rb.build().unwrap()
        };
        let all_rule = {
            let mut rb = Backend::new_rule(&mut eg, "all_read", true);
            let x = rb.new_var(ColumnTy::Id);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(relation, &[x.clone(), unit.clone()], None)
                .unwrap();
            rb.set(all_out, &[x, unit]);
            rb.build().unwrap()
        };

        Backend::run_rules(&mut eg, &[live_rule, all_rule]).unwrap();

        assert!(eg.mirror[&live_out].contains(&row(&[1, 0])));
        assert!(!eg.mirror[&live_out].contains(&row(&[2, 0])));
        assert!(eg.mirror[&all_out].contains(&row(&[1, 0])));
        assert!(eg.mirror[&all_out].contains(&row(&[2, 0])));
    }

    #[test]
    fn same_table_self_join_applies_primitive_guards() {
        let mut eg = EGraph::new_interpret();
        let neq = Backend::register_external_func(
            &mut eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                (args[0] != args[1]).then_some(Value::new(0))
            })),
        );
        let ordering_max = Backend::register_external_func(
            &mut eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                Some(args[0].max(args[1]))
            })),
        );
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
        let relation = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "R".to_string(),
                can_subsume: false,
            },
        );
        let out = Backend::add_table(
            &mut eg,
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

        let rule = {
            let mut rb = Backend::new_rule(&mut eg, "guarded_self_join", true);
            let a = rb.new_var(ColumnTy::Id);
            let b = rb.new_var(ColumnTy::Id);
            let c = rb.new_var(ColumnTy::Id);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(relation, &[a.clone(), b.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_table(relation, &[a.clone(), c.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_prim(
                neq,
                &[b.clone(), c.clone(), unit.clone()],
                ColumnTy::Base(unit_ty),
            )
            .unwrap();
            rb.query_prim(
                ordering_max,
                &[b.clone(), c.clone(), b.clone()],
                ColumnTy::Id,
            )
            .unwrap();
            rb.set(out, &[a, b, c, unit]);
            rb.build().unwrap()
        };

        Backend::run_rules(&mut eg, &[rule]).unwrap();

        assert!(eg.mirror[&out].contains(&row(&[1, 3, 2, 0])));
        assert!(!eg.mirror[&out].contains(&row(&[1, 2, 3, 0])));
    }

    #[test]
    fn same_table_self_join_allows_independent_unit_outputs() {
        let mut eg = EGraph::new_interpret();
        let neq = Backend::register_external_func(
            &mut eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                (args[0] != args[1]).then_some(Value::new(0))
            })),
        );
        let ordering_max = Backend::register_external_func(
            &mut eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                Some(args[0].max(args[1]))
            })),
        );
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
        let relation = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "R".to_string(),
                can_subsume: false,
            },
        );
        let out = Backend::add_table(
            &mut eg,
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

        let rule = {
            let mut rb = Backend::new_rule(&mut eg, "unit_var_self_join", true);
            let a = rb.new_var(ColumnTy::Id);
            let b = rb.new_var(ColumnTy::Id);
            let c = rb.new_var(ColumnTy::Id);
            let unit1 = rb.new_var(ColumnTy::Base(unit_ty));
            let unit2 = rb.new_var(ColumnTy::Base(unit_ty));
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(relation, &[a.clone(), b.clone(), unit1], Some(false))
                .unwrap();
            rb.query_table(relation, &[a.clone(), c.clone(), unit2], Some(false))
                .unwrap();
            rb.query_prim(
                neq,
                &[b.clone(), c.clone(), unit.clone()],
                ColumnTy::Base(unit_ty),
            )
            .unwrap();
            rb.query_prim(
                ordering_max,
                &[b.clone(), c.clone(), b.clone()],
                ColumnTy::Id,
            )
            .unwrap();
            rb.set(out, &[a, b, c, unit]);
            rb.build().unwrap()
        };

        Backend::run_rules(&mut eg, &[rule]).unwrap();

        assert!(eg.mirror[&out].contains(&row(&[1, 3, 2, 0])));
        assert!(!eg.mirror[&out].contains(&row(&[1, 2, 3, 0])));
    }

    #[test]
    fn incremental_self_join_retracts_old_path_edge() {
        let mut eg = EGraph::new_interpret();
        let neq = Backend::register_external_func(
            &mut eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                (args[0] != args[1]).then_some(Value::new(0))
            })),
        );
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
        let uf = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "UF".to_string(),
                can_subsume: false,
            },
        );

        let rule = {
            let mut rb = Backend::new_rule(&mut eg, "path_compress", true);
            let a = rb.new_var(ColumnTy::Id);
            let b = rb.new_var(ColumnTy::Id);
            let c = rb.new_var(ColumnTy::Id);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(uf, &[a.clone(), b.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_table(uf, &[b.clone(), c.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_prim(
                neq,
                &[b.clone(), c.clone(), unit.clone()],
                ColumnTy::Base(unit_ty),
            )
            .unwrap();
            rb.remove(uf, &[a.clone(), b]);
            rb.set(uf, &[a, c, unit]);
            rb.build().unwrap()
        };

        eg.insert_live_row(uf, row(&[40, 4, 0]));
        Backend::run_rules(&mut eg, &[rule]).unwrap();
        eg.insert_live_row(uf, row(&[75, 40, 0]));
        Backend::run_rules(&mut eg, &[rule]).unwrap();

        assert!(!eg.mirror[&uf].contains(&row(&[75, 40, 0])));
        assert!(eg.mirror[&uf].contains(&row(&[75, 4, 0])));
    }

    #[test]
    fn reinserted_same_row_refires_incremental_join() {
        let mut eg = EGraph::new_interpret();
        let neq = Backend::register_external_func(
            &mut eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                (args[0] != args[1]).then_some(Value::new(0))
            })),
        );
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
        let uf = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "UF".to_string(),
                can_subsume: false,
            },
        );

        let rule = {
            let mut rb = Backend::new_rule(&mut eg, "path_compress", true);
            let a = rb.new_var(ColumnTy::Id);
            let b = rb.new_var(ColumnTy::Id);
            let c = rb.new_var(ColumnTy::Id);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(uf, &[a.clone(), b.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_table(uf, &[b.clone(), c.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_prim(
                neq,
                &[b.clone(), c.clone(), unit.clone()],
                ColumnTy::Base(unit_ty),
            )
            .unwrap();
            rb.remove(uf, &[a.clone(), b]);
            rb.set(uf, &[a, c, unit]);
            rb.build().unwrap()
        };

        eg.insert_live_row(uf, row(&[40, 4, 0]));
        eg.insert_live_row(uf, row(&[75, 40, 0]));
        Backend::run_rules(&mut eg, &[rule]).unwrap();
        assert!(!eg.mirror[&uf].contains(&row(&[75, 40, 0])));
        assert!(eg.mirror[&uf].contains(&row(&[75, 4, 0])));

        eg.insert_live_row(uf, row(&[75, 40, 0]));
        Backend::run_rules(&mut eg, &[rule]).unwrap();

        assert!(!eg.mirror[&uf].contains(&row(&[75, 40, 0])));
        assert!(eg.mirror[&uf].contains(&row(&[75, 4, 0])));
    }

    #[test]
    fn same_iteration_remove_then_set_keeps_set_value() {
        let mut eg = EGraph::new_interpret();
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
        let trigger = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "Trigger".to_string(),
                can_subsume: false,
            },
        );
        let f = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                default: DefaultVal::Fail,
                merge: MergeFn::New,
                name: "F".to_string(),
                can_subsume: true,
            },
        );
        eg.insert_live_row(trigger, row(&[0]));
        eg.insert_live_row(f, row(&[1, 9]));

        let rule = {
            let mut rb = Backend::new_rule(&mut eg, "remove_then_set", true);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(trigger, std::slice::from_ref(&unit), Some(false))
                .unwrap();
            let key = QueryEntry::Const {
                val: Value::new(1),
                ty: ColumnTy::Id,
            };
            let new = QueryEntry::Const {
                val: Value::new(2),
                ty: ColumnTy::Id,
            };
            rb.remove(f, std::slice::from_ref(&key));
            rb.set(f, &[key, new]);
            rb.build().unwrap()
        };

        Backend::run_rules(&mut eg, &[rule]).unwrap();

        assert!(!eg.mirror[&f].contains(&row(&[1, 9])));
        assert!(eg.mirror[&f].contains(&row(&[1, 2])));
    }

    #[test]
    fn same_iteration_set_then_subsume_ends_subsumed() {
        let mut eg = EGraph::new_interpret();
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
        let trigger = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Base(unit_ty)],
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: "Trigger".to_string(),
                can_subsume: false,
            },
        );
        let f = Backend::add_table(
            &mut eg,
            FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                default: DefaultVal::Fail,
                merge: MergeFn::New,
                name: "F".to_string(),
                can_subsume: true,
            },
        );
        eg.insert_live_row(trigger, row(&[0]));

        let rule = {
            let mut rb = Backend::new_rule(&mut eg, "set_then_subsume", true);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(trigger, std::slice::from_ref(&unit), Some(false))
                .unwrap();
            let key = QueryEntry::Const {
                val: Value::new(1),
                ty: ColumnTy::Id,
            };
            let value = QueryEntry::Const {
                val: Value::new(2),
                ty: ColumnTy::Id,
            };
            rb.set(f, &[key.clone(), value]);
            rb.subsume(f, &[key]).unwrap();
            rb.build().unwrap()
        };

        Backend::run_rules(&mut eg, &[rule]).unwrap();

        assert!(!eg.mirror[&f].contains(&row(&[1, 2])));
        assert!(eg.subsumed[&f].contains(&row(&[1, 2])));
    }

    #[test]
    fn fused_delta_feed_does_not_expose_mixed_old_new_snapshots() {
        let mut eg = EGraph::new_interpret();
        let neq = Backend::register_external_func(
            &mut eg,
            Box::new(egglog_core_relations::make_external_func(|_, args| {
                (args[0] != args[1]).then_some(Value::new(0))
            })),
        );
        let unit_ty = eg
            .db
            .base_values()
            .get_ty_by_id(std::any::TypeId::of::<()>());
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
            let mut rb = Backend::new_rule(&mut eg, "view_first", true);
            let x = rb.new_var(ColumnTy::Id);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(view, &[x.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.set(dummy, &[x, unit]);
            rb.build().unwrap()
        };
        let cleanup_rule = {
            let mut rb = Backend::new_rule(&mut eg, "current_cleanup", true);
            let selected = rb.new_var(ColumnTy::Id);
            let old = rb.new_var(ColumnTy::Id);
            let unit = QueryEntry::Const {
                val: Value::new(0),
                ty: ColumnTy::Base(unit_ty),
            };
            rb.query_table(current, std::slice::from_ref(&selected), Some(false))
                .unwrap();
            rb.query_table(view, &[selected.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_table(view, &[old.clone(), unit.clone()], Some(false))
                .unwrap();
            rb.query_prim(
                neq,
                &[selected.clone(), old.clone(), unit.clone()],
                ColumnTy::Base(unit_ty),
            )
            .unwrap();
            rb.remove(view, &[old]);
            rb.build().unwrap()
        };

        Backend::run_rules(&mut eg, &[view_first_rule, cleanup_rule]).unwrap();
        assert!(eg.mirror[&view].contains(&row(&[10, 0])));

        eg.insert_live_row(view, row(&[4, 0]));
        assert!(eg.apply_merge_sets(current, &[row(&[4])]).unwrap());

        Backend::run_rules(&mut eg, &[view_first_rule, cleanup_rule]).unwrap();

        assert!(eg.mirror[&view].contains(&row(&[4, 0])));
        assert!(!eg.mirror[&view].contains(&row(&[10, 0])));
    }
}

// ---------------------------------------------------------------------------
// Merge-mode recognition (shared by `add_table`)
// ---------------------------------------------------------------------------

/// Map a single-output-column [`MergeFn`] to the FlowLog [`MergeMode`] (plus, for
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
            arity <= compile::MAX_ARITY,
            "FlowLog backend supports relations of arity <= {} (got {} for `{}`)",
            compile::MAX_ARITY,
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
                // `()` is pre-registered in `new_interpret`, so this never panics.
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
            has_output,
            lookup_mints: matches!(config.default, DefaultVal::FreshId),
            merge,
            merge_tree,
        });
        self.mirror.insert(id, std::rc::Rc::new(HashSet::new()));
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

    fn for_each_dyn(&self, table: FunctionId, f: &mut dyn for<'r> FnMut(ScanEntry<'r>)) {
        self.for_each_while_dyn(table, &mut |row| {
            f(row);
            true
        });
    }

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
            let vals = unpack_row(row, arity);
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
            std::rc::Rc::make_mut(set).clear();
            for row in removed {
                self.record_row_event(func, row, -1, -1, 0);
            }
        }
        if let Some(set) = self.subsumed.get_mut(&func) {
            let removed: Vec<Row> = set.iter().cloned().collect();
            std::rc::Rc::make_mut(set).clear();
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

    fn container_values_mut_dyn(&mut self) -> Option<&mut ContainerValues> {
        Some(self.db.container_values_mut())
    }

    fn new_container_id_counter(&mut self) -> Option<CounterId> {
        Some(self.db.add_counter())
    }

    fn with_execution_state_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) {
        self.db.with_execution_state(|st| f(st));
    }

    fn with_execution_state_tracked_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) -> bool {
        self.db.with_execution_state_tracked(|st| f(st)).1
    }

    // -- rule management ----------------------------------------------------

    fn new_rule<'a>(&'a mut self, desc: &str, _seminaive: bool) -> Box<dyn RuleBuilderOps + 'a> {
        // Seminaive is native to differential dataflow; the flag is accepted
        // for parity and ignored.
        Box::new(rule_builder::FlowlogRuleBuilder::new(self, desc))
    }

    fn free_rule(&mut self, id: RuleId) {
        if let Some(slot) = self.rules.get_mut(id.rep() as usize) {
            *slot = None;
            let i = id.rep() as usize;
            self.seen.remove(&i);
            // Any fused ruleset that included this rule is now stale: drop it so
            // it is rebuilt (without the freed rule) on the next `run_rules`.
            self.dd_fused.retain(|key, _| !key.contains(&i));
            self.dd_fused_fed_versions
                .retain(|key, _| !key.contains(&i));
        }
    }

    fn run_rules(&mut self, rules: &[RuleId]) -> Result<IterationReport> {
        // One `run_rules` call = one bounded egglog iteration. The frontend calls
        // this N times for `(run N)`.
        if rules.is_empty() {
            return Ok(IterationReport::default());
        }
        let live: Vec<usize> = rules
            .iter()
            .map(|r| r.rep() as usize)
            .filter(|&i| self.rules.get(i).map(|s| s.is_some()).unwrap_or(false))
            .collect();
        if live.is_empty() {
            return Ok(IterationReport::default());
        }

        let changed = interpret::run_iteration(self, &live)?;

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
        self.db
            .add_external_function(Box::new(external_func::PanicFunc::new(message)))
    }

    // -- capability flags ---------------------------------------------------

    fn requires_term_encoding(&self) -> bool {
        // FlowLog has no native union-find: congruence and rebuild are lowered
        // to ordinary rules over `@uf` tables by the term encoder. Without it,
        // `union`s would be silently dropped (see `HeadOp::Union` in interpret).
        true
    }

    fn supports_containers(&self) -> bool {
        true
    }

    fn supports_action_registry(&self) -> bool {
        // No egglog `ActionRegistry`. Ordinary primitives execute through the
        // embedded `Database`; registry-backed read/write/full primitives that
        // need live table access are outside this backend's current contract.
        false
    }

    // -- diagnostics --------------------------------------------------------

    fn set_report_level(&mut self, level: ReportLevel) {
        self.report_level = level;
    }

    fn dump_debug_info(&self) {
        for (i, info) in self.relations.iter().enumerate() {
            let f = FunctionId::new(i as u32);
            let n = self.table_size(f);
            if n == 0 {
                continue;
            }
            log::info!("== FlowLog relation `{}` ({} rows) ==", info.name, n);
        }
    }

    // -- cloning ------------------------------------------------------------

    fn clone_boxed(&self) -> Box<dyn Backend> {
        // A running differential-dataflow dataflow can't be cloned; push/pop
        // snapshot support (replaying the mirror + rule IR + relation metadata
        // into a fresh engine) is not implemented.
        unimplemented!("FlowLog backend clone_boxed (push/pop) is not implemented")
    }

    // -- bridge-only escape hatch ------------------------------------------

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
