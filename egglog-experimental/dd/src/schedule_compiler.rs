//! Compile a backend [`ScheduleSpec`] tree into ONE DD dataflow and run it in
//! a single epoch (docs/rebuild-in-dataflow.md).
//!
//! Architecture: DD computes rule-body JOINS incrementally; the
//! [`crate::engine`] executes the schedule — control flow (any nesting
//! depth), per-leaf seminaive firing, body primitives, head actions
//! (mints, constructor lookups, hash-cons, sets, deletes, subsumes), and
//! merge waves — as ONE stateful operator, one leaf execution per round:
//!
//! ```text
//!   state(f, loc) = entered seeds ∪ engine output deltas(f, loc)
//!   bindings      = per-rule join pipelines over the state collections
//!   Variable(+1)  feeds ±(leaf, rule, binding) match deltas (and the
//!                 engine's tick) back to the engine each round
//! ```
//!
//! Effects from turn r reach the joins' output at turn r+1, so every leaf
//! matches against the state left by the previous leaf execution — the
//! host's exact match-then-apply sequencing. Turn reports reproduce the
//! interpreter's per-leaf-execution report stream verbatim.
//!
//! Falls back to the interpreter (with an env-gated reason,
//! `EGGLOG_DD_DUMP_PLANS=1`) for: atom-less rules (their fire-once `seen`
//! marker outlives a schedule), residual globals, merge-time table lookups,
//! deletes not addressing exactly the key columns, tables holding multiple
//! rows per key or rows wider than their arity, and — dynamically, cached,
//! before any host mutation — primitives whose results prove unsafe to
//! evaluate off-host (neither argument echoes nor unit).

use std::cell::RefCell;
use std::rc::Rc;

use anyhow::{anyhow, Result};
use differential_dataflow::input::Input;
use differential_dataflow::operators::iterate::Variable;
use differential_dataflow::VecCollection;
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_backend_trait::{
    FunctionId, IterationReport, MergeAction, MergeFn, ReadMode, RuleActionCall, RuleBodyCall,
    ScheduleLeafReport, ScheduleSpec,
};
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};
use timely::dataflow::operators::probe::Handle as ProbeHandle;

use crate::compile::{ReadKey, Slot};
use crate::dd_native::{
    atom_vars, pack_key128, pack_row, plan_join_with, AtomOps, RowN, ViewStats, W, WIDTH_LADDER,
};
use crate::engine::{
    engine, EngineChannels, EngineConfig, EngineLeaf, EngineRule, EngineTable, MatchDelta,
    Schedule, ScheduleNode, SharedLeaf, StateDelta, TableRows, ViewOpSpec, LOC_LIVE, LOC_SUBSUMED,
    LOC_TICK, TICK,
};
use crate::{EGraph, RowLocation};

/// Compiled-region rows run at the planner cap width; per-region ladder
/// selection (as the fused join does) is a later optimization.
type Coll<'s, T, const WIDTH: usize> = VecCollection<'s, T, RowN<WIDTH>>;
type DeltaSink<const WIDTH: usize> = Rc<RefCell<Vec<((u32, u8, RowN<WIDTH>), isize)>>>;
type PrimId = egglog_backend_trait::ExternalFunctionId;

/// One rule's join pipeline (the dataflow side; the engine holds the rest).
struct RulePipeline {
    first: ReadKey,
    first_ops: AtomOps,
    /// For 2+-atom rules: the first atom's join-key columns (first-occurrence
    /// positions of the variables shared with atom 1), enabling an
    /// arranged-vs-arranged first join over SHARED raw-view arrangements.
    first_left_cols: Vec<usize>,
    stages: Vec<StagePlan>,
    /// Widest binding row this rule's stages produce (from the join plan).
    width: usize,
}

struct StagePlan {
    read: ReadKey,
    left_cols: Vec<usize>,
    right_cols: Vec<usize>,
    ops: AtomOps,
}

struct LeafPipelines {
    ruleset: String,
    rules: Vec<RulePipeline>,
}

struct Prep {
    tree: ScheduleNode,
    leaves: Vec<LeafPipelines>,
    engine_leaves: Vec<SharedLeaf>,
    /// Distinct relation read views across all pipelines.
    read_keys: Vec<ReadKey>,
    /// Tables the engine owns state for (write/lookup targets plus the merge
    /// side-effect closure).
    engine_tables: HashMap<u32, EngineTable>,
    fresh_prims: HashSet<PrimId>,
    set_if_empty: HashMap<PrimId, ViewOpSpec>,
    view_proof: HashMap<PrimId, ViewOpSpec>,
    /// Smallest row width the whole schedule needs: every binding layout and
    /// every touched table's full row must fit.
    width: usize,
}

/// Log (env-gated) why a schedule fell back to the interpreter, then `None`.
fn fallback<T>(reason: &str) -> Option<T> {
    if std::env::var("EGGLOG_DD_DUMP_PLANS").is_ok() {
        eprintln!("[dd-compile] fallback: {reason}");
    }
    None
}

/// Compile and run `spec`. `None` means the schedule is outside the supported
/// subset — including the DYNAMIC case where a primitive proved unsafe to
/// evaluate off-host (cached; nothing was mutated) — and the caller falls
/// back to the interpreter.
pub(crate) fn try_run_compiled(
    eg: &mut EGraph,
    spec: &ScheduleSpec,
) -> Option<Result<Vec<ScheduleLeafReport>>> {
    if std::env::var("EGGLOG_DD_DUMP_SCHEDULES").is_ok() {
        eprintln!("[dd-compile] offered: {spec:?}");
    }
    // Replay cache: if an identical schedule ran compiled and NOTHING has
    // changed since it finished (global row-event watermark), it is
    // quiescent-idempotent — replay its reports without building a dataflow.
    // (Fresh-id minting in such a run never reached a table, so skipping it
    // is unobservable.)
    let replay_key = format!("{spec:?}");
    if let Some((watermark, reports)) = eg.schedule_replay.get(&replay_key) {
        if *watermark == eg.mutation_counter {
            if let Some(message) = eg.take_panic_message() {
                return Some(Err(anyhow!(message)));
            }
            if std::env::var("EGGLOG_DD_ENGINE_DEBUG").is_ok() {
                eprintln!("[compiled] replayed quiescent schedule");
            }
            return Some(Ok(reports.clone()));
        }
    }
    let t0 = std::time::Instant::now();
    let prep = prepare(eg, spec)?;
    if std::env::var("EGGLOG_DD_ENGINE_DEBUG").is_ok() {
        eprintln!("[compiled] prepare: {:.1?}", t0.elapsed());
    }
    if std::env::var("EGGLOG_DD_DUMP_PLANS").is_ok() {
        eprintln!(
            "[dd-compile] compiled schedule: {} leaves, {} read views, {} engine tables",
            prep.leaves.len(),
            prep.read_keys.len(),
            prep.engine_tables.len(),
        );
    }
    // Monomorphized width ladder: run at the smallest row width that fits
    // (the same ladder as the fused path — row bytes dominate join cost).
    let result = match WIDTH_LADDER.iter().copied().find(|&w| w >= prep.width) {
        Some(8) => run_compiled::<8>(eg, prep),
        Some(16) => run_compiled::<16>(eg, prep),
        Some(32) => run_compiled::<32>(eg, prep),
        Some(48) => run_compiled::<48>(eg, prep),
        _ => return fallback("row width exceeds the ladder cap"),
    };
    match result {
        Ok(Some((leaves, quiescent))) => {
            // Cache ONLY no-op runs: re-running a schedule that changed state
            // (e.g. a budget-limited `(run n)`) does further work, so it must
            // never be short-circuited; a no-op run from an identical state
            // deterministically no-ops again.
            if quiescent {
                eg.schedule_replay
                    .insert(replay_key, (eg.mutation_counter, leaves.clone()));
            }
            Some(Ok(leaves))
        }
        Ok(None) => fallback("a primitive proved unsafe to evaluate off-host (cached)"),
        Err(e) => Some(Err(e)),
    }
}

// ---------------------------------------------------------------------------
// Preparation.
// ---------------------------------------------------------------------------

fn prepare(eg: &EGraph, spec: &ScheduleSpec) -> Option<Prep> {
    // Compile-time view statistics for join ordering, memoized per view.
    let stats_cache: RefCell<HashMap<ReadKey, Option<ViewStats>>> = RefCell::default();
    let stats = |read: ReadKey| -> Option<ViewStats> {
        stats_cache
            .borrow_mut()
            .entry(read)
            .or_insert_with(|| {
                let arity = eg.info(read.func).arity;
                let mut rows = 0usize;
                let mut distinct: Vec<HashSet<u32>> = vec![HashSet::new(); arity];
                let stores: &[_] = match read.mode {
                    ReadMode::Live => &[&eg.mirror],
                    ReadMode::Subsumed => &[&eg.subsumed],
                    ReadMode::All => &[&eg.mirror, &eg.subsumed],
                };
                // Distinct counts come from a bounded sample; relative
                // magnitudes are all the planner needs.
                const SAMPLE: usize = 65_536;
                let mut sampled = 0usize;
                for store in stores {
                    if let Some(table) = store.get(&read.func) {
                        rows += table.len();
                        for row in table.iter().take(SAMPLE.saturating_sub(sampled)) {
                            sampled += 1;
                            for (c, v) in row.iter().take(arity).enumerate() {
                                distinct[c].insert(*v);
                            }
                        }
                    }
                }
                let scale = (rows.max(1) as f64 / sampled.max(1) as f64).max(1.0);
                Some((
                    rows,
                    distinct
                        .into_iter()
                        .map(|d| ((d.len() as f64 * scale) as usize).min(rows))
                        .collect(),
                ))
            })
            .clone()
    };

    let mut leaves = Vec::new();
    let mut engine_leaves = Vec::new();
    let tree = shape(eg, spec, &mut leaves, &mut engine_leaves, &stats)?;

    // Gather reads, engine-owned tables, and special primitive ids.
    let mut read_keys: Vec<ReadKey> = Vec::new();
    let mut engine_funcs: HashSet<FunctionId> = HashSet::new();
    let mut fresh_prims = HashSet::new();
    let mut set_if_empty = HashMap::new();
    let mut view_proof = HashMap::new();
    for (pipes, eleaf) in leaves.iter().zip(&engine_leaves) {
        for pipe in &pipes.rules {
            for read in std::iter::once(pipe.first).chain(pipe.stages.iter().map(|s| s.read)) {
                if !read_keys.contains(&read) {
                    read_keys.push(read);
                }
            }
        }
        for rule in eleaf.rules.iter() {
            for atom in &rule.prims {
                let RuleBodyCall::Primitive { id, .. } = atom.head else {
                    continue;
                };
                if eg.unsafe_prims.contains(&id) {
                    return fallback("a body primitive is cached as unsafe off-host");
                }
                if atom.args.iter().any(is_global) {
                    return fallback("a residual global in a body primitive");
                }
            }
            for action in &rule.head {
                if let Some(reason) = scan_head_action(
                    eg,
                    action,
                    &mut engine_funcs,
                    &mut fresh_prims,
                    &mut set_if_empty,
                    &mut view_proof,
                ) {
                    return fallback(reason);
                }
            }
        }
    }

    // Close over merge-block side-effect targets, validating merge shapes.
    let mut frontier: Vec<FunctionId> = engine_funcs.iter().copied().collect();
    while let Some(f) = frontier.pop() {
        let (_, merge, _, _) = eg.function_spec(f);
        let mut targets = Vec::new();
        if !merge_supported(eg, &merge, &mut targets) {
            return fallback(
                "a written table's merge is not compiled (table lookup or unsafe primitive)",
            );
        }
        for t in targets {
            if engine_funcs.insert(t) {
                frontier.push(t);
            }
        }
    }

    // Table gates: bounded arity, honest row widths, one row per key for
    // engine-owned tables (the engine's key -> row model).
    let read_funcs: HashSet<FunctionId> = read_keys.iter().map(|r| r.func).collect();
    for &f in read_funcs.iter().chain(engine_funcs.iter()) {
        let arity = eg.info(f).arity;
        if arity > W {
            return fallback("table arity exceeds the row width cap");
        }
        for store in [&eg.mirror, &eg.subsumed] {
            if let Some(rows) = store.get(&f) {
                if rows.iter().any(|r| r.len() != arity) {
                    return fallback("a table stores rows wider than its arity");
                }
            }
        }
    }
    for &f in &engine_funcs {
        if let Some(keys) = eg.by_key.get(&f) {
            if keys.values().any(|entries| entries.len() != 1) {
                return fallback("an engine table transiently holds multiple rows per key");
            }
        }
    }

    let engine_tables: HashMap<u32, EngineTable> = engine_funcs
        .iter()
        .map(|&f| {
            let (n_keys, merge, default, n_identity_vals) = eg.function_spec(f);
            (
                f.rep(),
                EngineTable {
                    n_keys,
                    arity: eg.info(f).arity,
                    merge,
                    n_identity_vals,
                    level: eg.merge_level(f),
                    default,
                    name: eg.relation_name(f).to_string(),
                },
            )
        })
        .collect();

    let width = leaves
        .iter()
        .flat_map(|l| l.rules.iter().map(|p| p.width))
        .chain(read_funcs.iter().map(|&f| eg.info(f).arity))
        .chain(engine_tables.values().map(|t| t.arity))
        .max()
        .unwrap_or(1);

    Some(Prep {
        tree,
        leaves,
        engine_leaves,
        read_keys,
        engine_tables,
        fresh_prims,
        set_if_empty,
        view_proof,
        width,
    })
}

type HeadAction = GenericCoreAction<
    RuleActionCall,
    egglog_backend_trait::RuleVar,
    egglog_backend_trait::RuleValue,
>;
type HeadTerm = GenericAtomTerm<egglog_backend_trait::RuleVar, egglog_backend_trait::RuleValue>;

/// Validate one head action and record its table/primitive uses. Returns a
/// fallback reason on unsupported shapes.
fn scan_head_action(
    eg: &EGraph,
    action: &HeadAction,
    engine_funcs: &mut HashSet<FunctionId>,
    fresh_prims: &mut HashSet<PrimId>,
    set_if_empty: &mut HashMap<PrimId, ViewOpSpec>,
    view_proof: &mut HashMap<PrimId, ViewOpSpec>,
) -> Option<&'static str> {
    fn check_terms(terms: &[HeadTerm]) -> Option<&'static str> {
        terms
            .iter()
            .any(is_global)
            .then_some("a residual global in a rule head")
    }
    match action {
        GenericCoreAction::Let(_, _, call, args) => {
            if let Some(r) = check_terms(args) {
                return Some(r);
            }
            match call {
                RuleActionCall::Table { id, .. } => {
                    engine_funcs.insert(*id);
                }
                RuleActionCall::Primitive { id, name, .. } => {
                    if &**name == "get-fresh!" {
                        fresh_prims.insert(*id);
                    } else if let Some(op) = eg.set_if_empty_ops.get(id) {
                        let Some(view) = eg.table_ids.get(&op.view_name) else {
                            return Some("a hash-cons view is not registered");
                        };
                        engine_funcs.insert(*view);
                        set_if_empty.insert(
                            *id,
                            ViewOpSpec {
                                view: view.rep(),
                                n_keys: op.n_keys,
                            },
                        );
                    } else if let Some(op) = eg.view_proof_ops.get(id) {
                        let Some(view) = eg.table_ids.get(&op.view_name) else {
                            return Some("a view-proof view is not registered");
                        };
                        engine_funcs.insert(*view);
                        view_proof.insert(
                            *id,
                            ViewOpSpec {
                                view: view.rep(),
                                n_keys: op.n_keys,
                            },
                        );
                    } else if eg.unsafe_prims.contains(id) {
                        return Some("a head primitive is cached as unsafe off-host");
                    }
                }
            }
            None
        }
        GenericCoreAction::LetAtomTerm(_, _, term) => {
            if is_global(term) {
                return Some("a residual global in a rule head");
            }
            None
        }
        GenericCoreAction::Set(_, call, args, values) => {
            if let Some(r) = check_terms(args).or_else(|| check_terms(values)) {
                return Some(r);
            }
            match call {
                RuleActionCall::Table { id, .. } => {
                    engine_funcs.insert(*id);
                    None
                }
                RuleActionCall::Primitive { .. } => Some("a Set on a primitive is not compiled"),
            }
        }
        GenericCoreAction::Change(_, change, call, args) => {
            if let Some(r) = check_terms(args) {
                return Some(r);
            }
            match call {
                RuleActionCall::Table { id, .. } => {
                    if matches!(change, egglog_ast::generic_ast::Change::Delete)
                        && args.len() != eg.n_keys(*id)
                    {
                        return Some("a delete does not address exactly the key columns");
                    }
                    engine_funcs.insert(*id);
                    None
                }
                RuleActionCall::Primitive { .. } => {
                    Some("a delete/subsume on a primitive is not compiled")
                }
            }
        }
        GenericCoreAction::Union(..) => Some("a native union is not compiled"),
        GenericCoreAction::Panic(..) => None,
    }
}

fn is_global(term: &HeadTerm) -> bool {
    matches!(term, GenericAtomTerm::Global(..))
}

/// Merge programs the engine can fold: column ops, constants, primitives not
/// known-unsafe, and merge-block `set`/`let` actions. Table lookups fall
/// back. Collects merge-block set targets into `targets`.
fn merge_supported(eg: &EGraph, merge: &MergeFn, targets: &mut Vec<FunctionId>) -> bool {
    match merge {
        MergeFn::AssertEq
        | MergeFn::UnionId
        | MergeFn::Old
        | MergeFn::New
        | MergeFn::OldCol(_)
        | MergeFn::NewCol(_)
        | MergeFn::LetVar(_)
        | MergeFn::Const(_) => true,
        MergeFn::Primitive(id, args) => {
            !eg.unsafe_prims.contains(id)
                && !eg.set_if_empty_ops.contains_key(id)
                && !eg.view_proof_ops.contains_key(id)
                && args.iter().all(|a| merge_supported(eg, a, targets))
        }
        MergeFn::Function(..) | MergeFn::Lookup(..) => false,
        MergeFn::Columns(columns) => columns.iter().all(|c| merge_supported(eg, c, targets)),
        MergeFn::Block { actions, result } => {
            for action in actions {
                match action {
                    MergeAction::Set(f, args) => {
                        targets.push(*f);
                        if !args.iter().all(|a| merge_supported(eg, a, targets)) {
                            return false;
                        }
                    }
                    MergeAction::Let { value, .. } => {
                        if !merge_supported(eg, value, targets) {
                            return false;
                        }
                    }
                    MergeAction::Union(..) => return false,
                }
            }
            merge_supported(eg, result, targets)
        }
    }
}

fn shape(
    eg: &EGraph,
    spec: &ScheduleSpec,
    leaves: &mut Vec<LeafPipelines>,
    engine_leaves: &mut Vec<SharedLeaf>,
    stats: &impl Fn(ReadKey) -> Option<ViewStats>,
) -> Option<ScheduleNode> {
    match spec {
        ScheduleSpec::Run { ruleset, rules } => {
            let (pipes, eleaf) = prepare_leaf(eg, ruleset, rules, stats)?;
            leaves.push(pipes);
            engine_leaves.push(Rc::new(eleaf));
            Some(ScheduleNode::Leaf(leaves.len() - 1))
        }
        ScheduleSpec::Sequence(inners) => Some(ScheduleNode::Seq(
            inners
                .iter()
                .map(|s| shape(eg, s, leaves, engine_leaves, stats))
                .collect::<Option<Vec<_>>>()?,
        )),
        ScheduleSpec::Repeat(limit, inner) => Some(ScheduleNode::Repeat(
            *limit as u64,
            Box::new(shape(eg, inner, leaves, engine_leaves, stats)?),
        )),
        ScheduleSpec::Saturate(inner) => Some(ScheduleNode::Saturate(Box::new(shape(
            eg,
            inner,
            leaves,
            engine_leaves,
            stats,
        )?))),
    }
}

fn prepare_leaf(
    eg: &EGraph,
    ruleset: &str,
    rules: &[egglog_backend_trait::RuleId],
    stats: &impl Fn(ReadKey) -> Option<ViewStats>,
) -> Option<(LeafPipelines, EngineLeaf)> {
    let mut pipelines = Vec::new();
    let mut engine_rules = Vec::new();
    for id in rules {
        // Freed rules are skipped, mirroring `run_rules`' filter.
        let Some(rule) = eg.rules.get(id.rep() as usize).and_then(Option::as_ref) else {
            continue;
        };
        if std::env::var("EGGLOG_DD_DUMP_RULES").is_ok() {
            eprintln!(
                "[dd-rule] {:?}\n  body: {:?}\n  head: {:?}",
                rule.name, rule.core.body.atoms, rule.core.head.0
            );
        }

        let Ok(plan) = plan_join_with(rule, stats) else {
            return fallback("the body does not plan (atom-less or too wide)");
        };
        for atom in &rule.core.body.atoms {
            if matches!(atom.head, RuleBodyCall::Table { .. }) && atom.args.iter().any(is_global) {
                return fallback("a residual global in a body atom");
            }
        }
        let step_col = &plan.projection.step_col;
        let first_ops = AtomOps::bind_stage(&plan.atoms[0].slots, &step_col[0]);
        let mut first_left_cols = Vec::new();
        let mut stages = Vec::new();
        for i in 1..plan.atoms.len() {
            let slots = &plan.atoms[i].slots;
            let prev = &step_col[i - 1];
            let next = &step_col[i];
            let shared: Vec<u32> = atom_vars(slots)
                .into_iter()
                .filter(|v| prev.contains_key(v))
                .collect();
            let left_cols: Vec<usize> = shared.iter().map(|v| prev[v]).collect();
            let right_cols: Vec<usize> = shared
                .iter()
                .map(|v| {
                    slots
                        .iter()
                        .position(|s| matches!(s, Slot::Var(x) if x == v))
                        .expect("a shared variable occurs in the joined atom")
                })
                .collect();
            if i == 1 {
                // The same shared-variable order, located in atom 0.
                first_left_cols = shared
                    .iter()
                    .map(|v| {
                        plan.atoms[0]
                            .slots
                            .iter()
                            .position(|s| matches!(s, Slot::Var(x) if x == v))
                            .expect("a shared variable occurs in the first atom")
                    })
                    .collect();
            }
            stages.push(StagePlan {
                read: plan.atoms[i].read_key,
                left_cols,
                right_cols,
                ops: AtomOps::join_stage(slots, prev, next),
            });
        }

        pipelines.push(RulePipeline {
            first: plan.atoms[0].read_key,
            first_ops,
            first_left_cols,
            stages,
            width: plan.width,
        });
        engine_rules.push(EngineRule {
            layout: step_col
                .last()
                .expect("plans have at least one atom")
                .clone(),
            prims: rule
                .core
                .body
                .atoms
                .iter()
                .filter(|a| matches!(a.head, RuleBodyCall::Primitive { .. }))
                .cloned()
                .collect(),
            head: rule.core.head.0.clone(),
            seminaive: rule.seminaive,
        });
    }
    Some((
        LeafPipelines {
            ruleset: ruleset.to_string(),
            rules: pipelines,
        },
        EngineLeaf {
            rules: engine_rules,
        },
    ))
}

// ---------------------------------------------------------------------------
// Execution.
// ---------------------------------------------------------------------------

/// `Ok(None)` = a primitive proved unsafe off-host: nothing was mutated, the
/// primitive is cached, and the caller must interpret instead.
fn run_compiled<const WIDTH: usize>(
    eg: &mut EGraph,
    prep: Prep,
) -> Result<Option<(Vec<ScheduleLeafReport>, bool)>> {
    use timely::communication::allocator::thread::Thread;
    use timely::communication::allocator::Allocator;
    use timely::worker::Worker;
    use timely::WorkerConfig;

    if let Some(message) = eg.take_panic_message() {
        return Err(anyhow!(message));
    }

    let debug = std::env::var("EGGLOG_DD_ENGINE_DEBUG").is_ok();
    let mut mark = std::time::Instant::now();
    let mut lap = move |what: &str| {
        if debug {
            eprintln!("[compiled] {what}: {:.1?}", mark.elapsed());
        }
        mark = std::time::Instant::now();
    };
    let channels = EngineChannels::default();
    let first_id = eg.peek_fresh_id();
    let seeds: HashMap<u32, TableRows> = prep
        .engine_tables
        .keys()
        .map(|&frep| {
            let f = FunctionId::new(frep);
            let rows = eg
                .by_key
                .get(&f)
                .map(|keys| {
                    keys.iter()
                        .map(|(key, entries)| {
                            let (vals, loc) = &entries[0];
                            let loc = match loc {
                                RowLocation::Live => LOC_LIVE,
                                RowLocation::Subsumed => LOC_SUBSUMED,
                            };
                            (key.to_vec(), (vals.to_vec(), loc))
                        })
                        .collect()
                })
                .unwrap_or_default();
            (frep, rows)
        })
        .collect();
    let cfg = EngineConfig {
        schedule: Schedule::build(&prep.tree),
        leaves: prep.engine_leaves.clone(),
        tables: prep.engine_tables.clone(),
        seeds,
        set_if_empty: prep.set_if_empty.clone(),
        view_proof: prep.view_proof.clone(),
        fresh_prims: prep.fresh_prims.clone(),
        db: eg.db_clone(),
        panic: eg.panic_channel(),
        unit_rep: eg.unit_rep(),
        first_id,
        channels: channels.clone(),
    };

    lap("seed-build");
    let read_funcs: Vec<FunctionId> = {
        let mut v: Vec<FunctionId> = prep.read_keys.iter().map(|r| r.func).collect();
        v.sort_unstable_by_key(|f| f.rep());
        v.dedup();
        v
    };

    let alloc = Allocator::Thread(Thread::default());
    let mut worker = Worker::new(
        WorkerConfig::default(),
        alloc,
        Some(std::time::Instant::now()),
    );
    let probe = ProbeHandle::new();
    let deltas: DeltaSink<WIDTH> = DeltaSink::<WIDTH>::default();
    let (mut table_sessions, mut boot_session, volumes) = {
        let probe = probe.clone();
        let deltas = Rc::clone(&deltas);
        let prep_ref = &prep;
        let read_funcs = &read_funcs;
        worker.dataflow::<u32, _, _>(move |scope| {
            // One (location, row) input per read table, plus the bootstrap
            // tick that wakes the engine at round 1 even when nothing
            // matches initially.
            let mut sessions = HashMap::new();
            let mut seeds_by_func: HashMap<FunctionId, VecCollection<'_, u32, (u8, RowN<WIDTH>)>> =
                HashMap::new();
            for &f in read_funcs {
                let (session, coll) = scope.new_collection::<(u8, RowN<WIDTH>), isize>();
                sessions.insert(f, session);
                seeds_by_func.insert(f, coll);
            }
            let (boot_session, bootstrap) = scope.new_collection::<MatchDelta<WIDTH>, isize>();

            // Feedback lives in the ROOT scope: rounds are raw u32 times, so
            // every batch carries a 4-byte timestamp and there is no nested
            // subgraph progress-tracking layer.
            let volumes: Rc<RefCell<HashMap<String, u64>>> = Rc::default();
            let (var, fed) = Variable::<_, Vec<(MatchDelta<WIDTH>, u32, isize)>>::new(scope, 1);
            {
                let out = engine(&fed, cfg);
                let data = out
                    .clone()
                    .flat_map(|(f, loc, row)| (loc != LOC_TICK).then_some((f, loc, row)));
                let ticks = out.flat_map(|(_, loc, _)| {
                    (loc == LOC_TICK).then_some((TICK, TICK, RowN::<WIDTH>::default()))
                });

                // Demux engine deltas ONCE by (func, loc): timely's Tee clones
                // every batch per subscriber, so per-view filters on the full
                // stream would copy each emission ~|views| times.
                let mut part_index: HashMap<(u32, u8), u64> = HashMap::new();
                for &read in &prep_ref.read_keys {
                    let locs: &[u8] = match read.mode {
                        ReadMode::Live => &[LOC_LIVE],
                        ReadMode::Subsumed => &[LOC_SUBSUMED],
                        ReadMode::All => &[LOC_LIVE, LOC_SUBSUMED],
                    };
                    for &loc in locs {
                        let next = part_index.len() as u64;
                        part_index.entry((read.func.rep(), loc)).or_insert(next);
                    }
                }
                // One extra part swallows deltas no view reads.
                let sink_part = part_index.len() as u64;
                let route = part_index.clone();
                let parts: Vec<VecCollection<'_, u32, RowN<WIDTH>>> = {
                    use differential_dataflow::AsCollection;
                    use timely::dataflow::operators::vec::Partition;
                    data.clone()
                        .inner
                        .partition(
                            sink_part + 1,
                            move |(d, t, r): (StateDelta<WIDTH>, u32, isize)| {
                                let (f, loc, row) = d;
                                let part = route.get(&(f, loc)).copied().unwrap_or(sink_part);
                                (part, (row, t, r))
                            },
                        )
                        .into_iter()
                        .map(|stream| stream.as_collection())
                        .collect()
                };

                // Per-read-view state collections: seeds ∪ engine deltas.
                let mut views: HashMap<ReadKey, Coll<'_, u32, WIDTH>> = HashMap::new();
                for &read in &prep_ref.read_keys {
                    let frep = read.func.rep();
                    let seed = seeds_by_func[&read.func].clone();
                    let seed_part = |loc: u8| {
                        seed.clone()
                            .flat_map(move |(l, row)| (l == loc).then_some(row))
                    };
                    let engine_part = |loc: u8| parts[part_index[&(frep, loc)] as usize].clone();
                    let coll = match read.mode {
                        ReadMode::Live => seed_part(LOC_LIVE).concat(engine_part(LOC_LIVE)),
                        ReadMode::Subsumed => {
                            seed_part(LOC_SUBSUMED).concat(engine_part(LOC_SUBSUMED))
                        }
                        ReadMode::All => seed_part(LOC_LIVE)
                            .concat(engine_part(LOC_LIVE))
                            .concat(seed_part(LOC_SUBSUMED))
                            .concat(engine_part(LOC_SUBSUMED)),
                    };
                    views.insert(read, coll);
                }

                // Per-rule join pipelines, tagged with (leaf, rule). One
                // SHARED arrangement per (view, key-column projection) serves
                // every join call site: the right side of every stage and
                // both sides of each rule's first join (bind/remap slot
                // programs run inside the join closure; bind is injective on
                // surviving rows, so multiplicities are unchanged).
                let mut arranged = HashMap::new();
                let count_volumes = std::env::var("EGGLOG_DD_VOLUMES").is_ok();
                let mut arrange = |read: ReadKey, cols: Vec<usize>| {
                    let volumes = Rc::clone(&volumes);
                    arranged
                        .entry((read, cols.clone()))
                        .or_insert_with(|| {
                            let tag = format!("shared f{}@{:?}", read.func.rep(), cols);
                            let mut keyed = views[&read]
                                .clone()
                                .map(move |r: RowN<WIDTH>| (pack_key128(&r, &cols), r));
                            if count_volumes {
                                keyed = keyed.inspect_batch(move |_t, b| {
                                    *volumes.borrow_mut().entry(tag.clone()).or_default() +=
                                        b.len() as u64;
                                });
                            }
                            keyed.arrange_by_key()
                        })
                        .clone()
                };
                let mut matches: Vec<VecCollection<'_, u32, MatchDelta<WIDTH>>> =
                    vec![bootstrap, ticks];
                for (leaf_idx, leaf) in prep_ref.leaves.iter().enumerate() {
                    for (rule_idx, pipe) in leaf.rules.iter().enumerate() {
                        let ops0 = pipe.first_ops.clone();
                        let mut cur = if pipe.stages.is_empty() {
                            views[&pipe.first].clone().flat_map(move |r: RowN<WIDTH>| {
                                ops0.apply(&RowN::<WIDTH>::default(), &r)
                            })
                        } else {
                            let first_stage = &pipe.stages[0];
                            let left = arrange(pipe.first, pipe.first_left_cols.clone());
                            let right = arrange(first_stage.read, first_stage.right_cols.clone());
                            let ops1 = first_stage.ops.clone();
                            left.join_core(
                                right,
                                move |_key, r0: &RowN<WIDTH>, r1: &RowN<WIDTH>| {
                                    ops0.apply(&RowN::<WIDTH>::default(), r0)
                                        .and_then(|b| ops1.apply(&b, r1))
                                },
                            )
                        };
                        for (si, stage) in pipe.stages.iter().enumerate().skip(1) {
                            let left_cols = stage.left_cols.clone();
                            let ops = stage.ops.clone();
                            let mut left =
                                cur.map(move |b: RowN<WIDTH>| (pack_key128(&b, &left_cols), b));
                            if count_volumes {
                                let volumes = Rc::clone(&volumes);
                                let tag = format!("inter l{leaf_idx}r{rule_idx}s{si}");
                                left = left.inspect_batch(move |_t, b| {
                                    *volumes.borrow_mut().entry(tag.clone()).or_default() +=
                                        b.len() as u64;
                                });
                            }
                            let right = arrange(stage.read, stage.right_cols.clone());
                            cur = left.join_core(right, move |_key, b, r| ops.apply(b, r));
                        }
                        let (lt, rt) = (leaf_idx as u32, rule_idx as u32);
                        let mut tagged = cur.map(move |b: RowN<WIDTH>| (lt, rt, b));
                        if count_volumes {
                            let volumes = Rc::clone(&volumes);
                            let tag = format!("match l{leaf_idx}r{rule_idx}");
                            tagged = tagged.inspect_batch(move |_t, b| {
                                *volumes.borrow_mut().entry(tag.clone()).or_default() +=
                                    b.len() as u64;
                            });
                        }
                        matches.push(tagged);
                    }
                }

                var.set(differential_dataflow::collection::concatenate(
                    scope, matches,
                ));
                data.inspect_batch(move |_t, batch| {
                    deltas
                        .borrow_mut()
                        .extend(batch.iter().map(|(d, _t, w)| (*d, *w)));
                })
                .probe_with(&probe);
            }
            (sessions, boot_session, volumes)
        })
    };

    lap("dataflow-build");
    for (&f, session) in table_sessions.iter_mut() {
        for (store, loc) in [(&eg.mirror, LOC_LIVE), (&eg.subsumed, LOC_SUBSUMED)] {
            if let Some(rows) = store.get(&f) {
                for row in rows.iter() {
                    session.insert((loc, pack_row::<WIDTH>(row)?));
                }
            }
        }
        session.advance_to(1);
        session.flush();
    }
    boot_session.insert((TICK, TICK, RowN::<WIDTH>::default()));
    boot_session.advance_to(1);
    boot_session.flush();
    drop(table_sessions);
    drop(boot_session);
    lap("seed-feed");
    #[cfg(feature = "pprof")]
    let guard = std::env::var("EGGLOG_DD_PROFILE").ok().map(|_| {
        pprof::ProfilerGuardBuilder::default()
            .frequency(500)
            .build()
            .unwrap()
    });
    worker.step_while(|| !probe.done());
    #[cfg(feature = "pprof")]
    if let Some(g) = guard {
        if let Ok(report) = g.report().build() {
            static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let n = N.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let path = format!("{}.{n}.svg", std::env::var("EGGLOG_DD_PROFILE").unwrap());
            let file = std::fs::File::create(&path).unwrap();
            report.flamegraph(file).ok();
            eprintln!("[profile] wrote {path}");
        }
    }
    lap("step");
    if std::env::var("EGGLOG_DD_VOLUMES").is_ok() {
        let volumes = volumes.borrow();
        let mut v: Vec<(&String, &u64)> = volumes.iter().collect();
        v.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
        let total: u64 = v.iter().map(|(_, n)| **n).sum();
        eprintln!("[volumes] total tuples into arrangements: {total}");
        for (tag, n) in v.iter().take(25) {
            eprintln!("[volumes]   {n:>10}  {tag}");
        }
    }
    drop(worker);
    lap("teardown");

    // Dynamic outcomes, checked BEFORE any host mutation.
    if let Some(id) = *channels.unsafe_prim.borrow() {
        eg.unsafe_prims.insert(id);
        return Ok(None);
    }
    if let Some(message) = channels.error.borrow_mut().take() {
        return Err(anyhow!(message));
    }

    // Consume the fresh ids the engine minted from the reserved range.
    let minted = *channels.minted.borrow() as usize;
    eg.advance_fresh_ids(minted);

    // Apply the engine's net row deltas to the host tables (sort + fold: the
    // sink holds millions of entries, and sorting beats hashing at that size).
    let mut sunk = std::mem::take(&mut *deltas.borrow_mut());
    sunk.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    let mut host_deltas: Vec<(FunctionId, u8, Box<[u32]>, isize)> = Vec::new();
    let mut i = 0;
    while i < sunk.len() {
        let key = sunk[i].0;
        let mut w = 0;
        while i < sunk.len() && sunk[i].0 == key {
            w += sunk[i].1;
            i += 1;
        }
        if w == 0 {
            continue;
        }
        let (frep, loc, row) = key;
        let f = FunctionId::new(frep);
        let arity = eg.info(f).arity;
        let full: Box<[u32]> = (0..arity).map(|i| row[i]).collect();
        host_deltas.push((f, loc, full, w.signum()));
    }
    let quiescent = host_deltas.is_empty() && minted == 0;
    eg.apply_compiled_deltas(host_deltas)?;
    lap("apply");

    // Reports: one entry per executed leaf turn, in execution order — the
    // interpreter's exact report stream.
    let reports = channels
        .turns
        .borrow()
        .iter()
        .map(|&(leaf, changed)| {
            let mut iteration = IterationReport::default();
            iteration.rule_set_report.changed = changed;
            ScheduleLeafReport {
                ruleset: prep.leaves[leaf].ruleset.clone(),
                iteration,
            }
        })
        .collect();
    Ok(Some((reports, quiescent)))
}
