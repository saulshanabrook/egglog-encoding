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
    Backend, BaseValues, ColumnTy, ContainerValues, ExecutionState, ExternalFunction,
    ExternalFunctionId, FunctionConfig, FunctionId, IterationReport, MergeFn, ReportLevel,
    RuleBuilderOps, RuleId, ScanEntry, Value,
};
use egglog_core_relations::Database;
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};

pub mod compile;
pub mod dd_native;
mod external_func;
pub mod interpret;
mod rule_builder;

use compile::{row_col, unpack_row, MergeMode, MergeTree, Row, RuleIr};
use external_func::ExternalFuncRegistry;

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
    /// How functional-dependency conflicts are resolved.
    pub(crate) merge: MergeMode,
    /// The evaluatable merge tree, when `merge` is [`MergeMode::Computed`].
    pub(crate) merge_tree: Option<MergeTree>,
}

// ---------------------------------------------------------------------------
// EGraph
// ---------------------------------------------------------------------------

/// The FlowLog-backed egraph.
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
    pub(crate) external_funcs: ExternalFuncRegistry,
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
    /// Per-ruleset, per-function last-fed row snapshot `Rc`, for computing the
    /// signed delta fed into the FUSED join's shared inputs.
    pub(crate) dd_fused_fed: HashMap<Vec<usize>, HashMap<FunctionId, std::rc::Rc<HashSet<Row>>>>,
    /// `--wcoj`: route the reverse-distributivity triangle rule through the
    /// worst-case-optimal delta-query join (dogsdogsdogs prefix-extension +
    /// AltNeu 3-stream decomposition in [`dd_native`]) instead of the left-deep
    /// binary `.join` chain. Detected structurally per rule at fused-build time;
    /// non-triangle rules are unaffected. Off by default — when off the FlowLog
    /// join path is byte-identical to the pre-WCOJ behavior.
    pub(crate) wcoj_enabled: bool,
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new_interpret()
    }
}

impl Drop for EGraph {
    fn drop(&mut self) {
        // Step-0 profile dump (gated FLOWLOG_DD_PROF): #workers, #InputSessions,
        // and the worker.step vs host-side prim/delta split. No-op otherwise.
        dd_native::dd_prof_dump();
        // Per-ruleset profile dump (gated FLOWLOG_DD_RULESET_PROF): attribute
        // DD wall time to the ruleset NAME, sorted descending. No-op otherwise.
        dd_native::dd_ruleset_prof_dump();
    }
}

impl EGraph {
    /// Construct a fresh FlowLog-backed egraph. Rule bodies run on the in-process
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
            external_funcs: ExternalFuncRegistry::default(),
            // Start at 1 so id 0 stays a "null"/padding sentinel.
            next_id: 1,
            report_level: ReportLevel::default(),
            dd_rule_runs: 0,
            seen: HashMap::new(),
            dd_fused: HashMap::new(),
            dd_fused_fed: HashMap::new(),
            wcoj_enabled: false,
        }
    }

    /// Turn on `--wcoj`: route the reverse-distributivity triangle rule through
    /// the worst-case-optimal delta-query join (see [`dd_native`]). When off,
    /// every rule lowers to the left-deep binary `.join` chain exactly as
    /// before. Detected structurally at fused-build time; non-triangle rules are
    /// unaffected. Off by default.
    pub fn enable_wcoj(&mut self) {
        self.wcoj_enabled = true;
    }

    pub(crate) fn info(&self, f: FunctionId) -> &RelationInfo {
        self.relations
            .get(f.rep() as usize)
            .unwrap_or_else(|| panic!("FunctionId({}) not registered", f.rep()))
    }

    /// Relation name for `f` (used by the per-ruleset profiler to detect `@uf`
    /// body atoms — the union-find tables are named `@UF_<sort>` / `@UF_<sort>f`).
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
    /// The pre-set mirror is already FD-resolved (this runs every `run_rules`
    /// call), so each key holds one row; building the key index is O(state) and
    /// the fold is O(new rows).
    pub(crate) fn apply_merge_sets(&mut self, f: FunctionId, rows: &[Row]) -> bool {
        if matches!(self.merge_mode(f), MergeMode::Computed) {
            return self.apply_computed_merge(f, rows);
        }
        let arity = self.info(f).arity;
        let merge = self.merge_mode(f);
        let inputs_len = arity - 1;
        let set = std::rc::Rc::make_mut(self.mirror.entry(f).or_default());
        // Current value per key (the mirror is FD-resolved: one row per key).
        let mut cur: HashMap<Box<[u32]>, u32> = HashMap::with_capacity(set.len());
        for r in set.iter() {
            cur.insert(r[..inputs_len].into(), row_col(r, inputs_len));
        }
        // Fold new values in emission order, remembering each touched key's
        // original value so the stale row can be retracted.
        let mut orig: HashMap<Box<[u32]>, Option<u32>> = HashMap::new();
        for row in rows {
            let key: Box<[u32]> = row[..inputs_len].into();
            let nv = row_col(row, inputs_len);
            let existing = cur.get(&key).copied();
            orig.entry(key.clone()).or_insert(existing);
            let merged = match (existing, merge) {
                (None, _) => nv,
                (Some(_), MergeMode::New) => nv,
                (Some(c), MergeMode::Old) => c,
                (Some(c), MergeMode::Min) => c.min(nv),
                // Relation is filtered by the caller; Computed took the branch above.
                (Some(c), MergeMode::Relation | MergeMode::Computed) => c,
            };
            cur.insert(key, merged);
        }
        // Apply the net change per touched key.
        let mut changed = false;
        for (key, old_val) in orig {
            let new_val = cur[&key];
            if Some(new_val) == old_val {
                continue;
            }
            if let Some(ov) = old_val {
                let mut old_row: Vec<u32> = key.to_vec();
                old_row.push(ov);
                set.remove(old_row.as_slice());
            }
            let mut new_row: Vec<u32> = key.to_vec();
            new_row.push(new_val);
            set.insert(new_row.into_boxed_slice());
            changed = true;
        }
        changed
    }

    /// The [`MergeMode::Computed`] case of [`apply_merge_sets`]: fold each key's
    /// conflicting values by EVALUATING the retained [`MergeTree`] (a primitive
    /// like `(or old new)`, or a constructor that builds a term). Evaluation needs
    /// `&mut self` (host-side primitive calls, e-node minting), so — unlike the
    /// scalar path — it gathers the candidate values first, then reconciles the
    /// mirror after the fold.
    fn apply_computed_merge(&mut self, f: FunctionId, rows: &[Row]) -> bool {
        let inputs_len = self.info(f).arity - 1;
        let next_id_before = self.next_id;
        // Current value per key (FD-resolved: one row per key).
        let mut cur: HashMap<Box<[u32]>, u32> = HashMap::new();
        if let Some(set) = self.mirror.get(&f) {
            cur.reserve(set.len());
            for r in set.iter() {
                cur.insert(r[..inputs_len].into(), row_col(r, inputs_len));
            }
        }
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
        let mut updates: Vec<(Box<[u32]>, Option<u32>, u32)> = Vec::new();
        for key in order {
            let old = cur.get(&key).copied();
            let mut acc = old;
            for &nv in &newv[&key] {
                acc = Some(match acc {
                    None => nv,
                    Some(c) => self.eval_merge_tree(&tree, c, nv, &mut lookup_index),
                });
            }
            let new_val = acc.unwrap();
            if Some(new_val) != old {
                updates.push((key, old, new_val));
            }
        }
        // Reconcile the mirror. A `Func` node that minted an e-node advanced
        // `next_id` — that is itself a real change even if no value flipped.
        let mut changed = self.next_id != next_id_before;
        if !updates.is_empty() {
            let set = std::rc::Rc::make_mut(self.mirror.entry(f).or_default());
            for (key, old, new_val) in updates {
                if let Some(ov) = old {
                    let mut r = key.to_vec();
                    r.push(ov);
                    set.remove(r.as_slice());
                }
                let mut r = key.to_vec();
                r.push(new_val);
                set.insert(r.into_boxed_slice());
            }
            changed = true;
        }
        changed
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
    ) -> u32 {
        match node {
            MergeTree::Old => old,
            MergeTree::New => new,
            MergeTree::Const(v) => *v,
            MergeTree::Prim(id, args) => {
                let argv: Vec<Value> = args
                    .iter()
                    .map(|a| Value::new(self.eval_merge_tree(a, old, new, index)))
                    .collect();
                self.eval_prim_internal(*id, &argv)
                    .map(|v| v.rep())
                    .unwrap_or(old)
            }
            MergeTree::Func(func, args) => {
                let key: Vec<Value> = args
                    .iter()
                    .map(|a| Value::new(self.eval_merge_tree(a, old, new, index)))
                    .collect();
                interpret::lookup_or_create(self, *func, &key, index).rep()
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
        let live = std::rc::Rc::make_mut(self.mirror.get_mut(&f).unwrap());
        for r in &moved {
            live.remove(r);
        }
        let subs = std::rc::Rc::make_mut(self.subsumed.entry(f).or_default());
        for r in moved {
            subs.insert(r);
        }
        true
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
            std::rc::Rc::make_mut(set).clear();
        }
        if let Some(set) = self.subsumed.get_mut(&func) {
            std::rc::Rc::make_mut(set).clear();
        }
        // The DD `fed` snapshot (`dd_fused_fed`) is diffed against the live
        // mirror each iteration, so clearing the mirror is picked up as a
        // retraction delta automatically — no extra bookkeeping
        // needed here.
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
            self.dd_fused_fed.retain(|key, _| !key.contains(&i));
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
        let func2 = dyn_clone::clone_box(&*func);
        let id = self.db.add_external_function(func);
        self.external_funcs.add_func_at(id, func2);
        id
    }

    fn free_external_func(&mut self, func: ExternalFunctionId) {
        self.db.free_external_function(func);
        self.external_funcs.free(func);
    }

    fn new_panic(&mut self, message: String) -> ExternalFunctionId {
        let panic_fn = external_func::PanicFunc::new(message.clone());
        let id = self.db.add_external_function(Box::new(panic_fn));
        self.external_funcs.add_panic_at(id, message);
        id
    }

    // -- capability flags ---------------------------------------------------

    fn requires_term_encoding(&self) -> bool {
        // FlowLog has no native union-find: congruence and rebuild are lowered
        // to ordinary rules over `@uf` tables by the term encoder. Without it,
        // `union`s would be silently dropped (see `HeadOp::Union` in interpret).
        true
    }

    fn supports_containers(&self) -> bool {
        false
    }

    fn supports_action_registry(&self) -> bool {
        // No egglog `ActionRegistry`. Registry-backed primitives are registered
        // via the frontend's registry-free placeholder/snapshot path and
        // dispatched by the FlowLog interpreter's external-func mechanism.
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
