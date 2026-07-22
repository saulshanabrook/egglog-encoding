//! Compile a backend [`ScheduleSpec`] tree into ONE DD dataflow and run it in
//! a single epoch — loops become in-dataflow fixpoints instead of host-driven
//! iterations (docs/rebuild-in-dataflow.md).
//!
//! Schedule nodes map to dataflow constructs: `Sequence` chains leaves;
//! `Saturate`/`Repeat(n)` open ONE nested iterative scope built around the
//! [`crate::merge_hub`]:
//!
//! ```text
//!   state(f) = entered seeds ∪ hub output deltas(f)
//!   bindings = rule joins over state          (round r = host iteration r)
//!   effects  = latched, tagged write ops      (rising_edge per stream)
//!   Variable(+1 round) feeds effects to the hub, which applies them with
//!   the host MergeTransaction's exact semantics (set-if-empty, deletes,
//!   then merge WAVES to fixpoint) at round r+1.
//! ```
//!
//! Effects produced at round r land at round r+1, so matches always see the
//! previous iteration's state — egglog's match-then-apply model — while merge
//! waves run inside one hub timestamp and never consume a `Repeat` budget.
//! The gate filters fed effects to rounds `< n`, so `Repeat(0)` is a no-op
//! and `Repeat(n)` applies exactly n iterations, converging early for free.
//!
//! Head actions: `(get-fresh! "sort")` lowers to a [`memoizing_mint`] stage
//! keyed by `(rule, binding)` — replay-stable ids from a reserved host
//! counter range; `set-if-empty-<view>!` and `delete` lower to hub ops.
//!
//! This compiles a SUBSET and falls back to the interpreter with an
//! env-gated reason (`EGGLOG_DD_DUMP_PLANS=1`) otherwise: bodies are pure
//! `Live` table atoms; every write happens inside ONE loop with ONE
//! write-bearing leaf (multi-leaf sequences need per-leaf phasing, and
//! same-scope writes at the epoch level would need a cycle timely cannot
//! express outside a loop); merges may use column ops and primitives but not
//! table lookups; at most one minting leaf. Primitive evaluation inside the
//! dataflow uses a cloned `Database`, guarded dynamically: a result that is
//! not an argument echo or unit aborts the run BEFORE any host mutation,
//! caches the primitive as uncompilable, and falls back to the interpreter.
//!
//! Compiled leaves report `changed` per leaf (net row deltas plus mints); a
//! loop's changes are attributed to its leaves collectively (OR-preserving;
//! per-leaf flags do not appear in printed outputs).

use std::rc::Rc;

use anyhow::{anyhow, Result};
use differential_dataflow::input::Input;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::operators::iterate::Variable;
use differential_dataflow::{AsCollection, VecCollection};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_backend_trait::{
    FunctionId, IterationReport, MergeAction, MergeFn, ReadMode, RuleActionCall, RuleBodyCall,
    ScheduleLeafReport, ScheduleSpec,
};
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};
use timely::dataflow::operators::probe::Handle as ProbeHandle;
use timely::dataflow::operators::vec::Filter;
use timely::dataflow::Scope;
use timely::order::Product;
use timely::progress::Timestamp;

use crate::compile::Slot;
use crate::dd_native::{atom_vars, pack_key128, pack_row, plan_join, AtomOps, RowN, W};
use crate::merge_hub::{merge_hub, HubChannels, HubOp, HubTable, OP_DELETE, OP_SET, OP_SIE};
use crate::monotone::{memoizing_mint, rising_edge};
use crate::EGraph;

/// Compiled-region rows run at the planner cap width; per-region ladder
/// selection (as the fused join does) is a later optimization.
type Row = RowN<W>;
type Coll<'s, T> = VecCollection<'s, T, Row>;
/// Net row deltas per (table, row); nonzero anywhere = changed.
type DeltaSink = Rc<std::cell::RefCell<HashMap<(u32, Row), isize>>>;
type CountSink = Rc<std::cell::RefCell<isize>>;

/// A column of an effect row: copied from a binding column, a constant, or
/// this rule's minted fresh id.
#[derive(Clone)]
enum Src {
    Col(usize),
    Const(u32),
    Mint,
}

/// One join stage of a compiled rule (atoms 1..).
struct StagePlan {
    func: FunctionId,
    left_cols: Vec<usize>,
    right_cols: Vec<usize>,
    ops: AtomOps,
}

/// A lowered write: the hub op kind, target table, and per-column sources
/// (full row for sets/sie; key columns for deletes).
struct WriteEffect {
    op: u8,
    func: FunctionId,
    srcs: Vec<Src>,
}

struct CompiledRule {
    first_func: FunctionId,
    first_ops: AtomOps,
    stages: Vec<StagePlan>,
    needs_mint: bool,
    writes: Vec<WriteEffect>,
}

struct LeafPlan {
    ruleset: String,
    rules: Vec<CompiledRule>,
}

/// Validated schedule shape: exactly one loop carries every write, loops do
/// not nest, and the writing loop has one write-bearing leaf.
enum Region {
    Leaf(usize),
    Seq(Vec<Region>),
    /// `Some(n)` = Repeat(n), `None` = Saturate.
    Loop(Option<u64>, Box<Region>),
}

struct Prep {
    region: Region,
    leaves: Vec<LeafPlan>,
    /// All tables read or written anywhere in the schedule.
    involved: Vec<FunctionId>,
    /// Tables the hub owns: written by rules or (transitively) by merge-block
    /// side effects.
    hub_tables: HashSet<FunctionId>,
    minting_leaf: Option<usize>,
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
    let prep = prepare(eg, spec)?;
    if std::env::var("EGGLOG_DD_DUMP_PLANS").is_ok() {
        eprintln!(
            "[dd-compile] compiled schedule: {} leaves, {} tables ({} hub-owned)",
            prep.leaves.len(),
            prep.involved.len(),
            prep.hub_tables.len(),
        );
    }
    match run_compiled(eg, prep) {
        Ok(Some(leaves)) => Some(Ok(leaves)),
        Ok(None) => fallback("a primitive proved unsafe to evaluate off-host (cached)"),
        Err(e) => Some(Err(e)),
    }
}

// ---------------------------------------------------------------------------
// Preparation: validate the subset and lower rules to join/effect plans.
// ---------------------------------------------------------------------------

fn prepare(eg: &EGraph, spec: &ScheduleSpec) -> Option<Prep> {
    let mut leaves = Vec::new();
    let region = shape(eg, spec, false, &mut leaves)?;

    // Involved tables and directly-written tables.
    let mut involved: Vec<FunctionId> = Vec::new();
    let mut seen: HashSet<FunctionId> = HashSet::new();
    let mut written: HashSet<FunctionId> = HashSet::new();
    for leaf in &leaves {
        for rule in &leaf.rules {
            for f in std::iter::once(rule.first_func).chain(rule.stages.iter().map(|s| s.func)) {
                if seen.insert(f) {
                    involved.push(f);
                }
            }
            for w in &rule.writes {
                written.insert(w.func);
                if seen.insert(w.func) {
                    involved.push(w.func);
                }
            }
        }
    }

    // Close the hub set over merge-block side-effect targets (e.g. a view's
    // merge writes the union-find), validating merge shapes as we go.
    let mut hub_tables = written.clone();
    let mut frontier: Vec<FunctionId> = hub_tables.iter().copied().collect();
    while let Some(f) = frontier.pop() {
        let (_, merge, _, _) = eg.function_spec(f);
        let mut targets = Vec::new();
        if !merge_supported(eg, &merge, &mut targets) {
            return fallback("a written table's merge is not compiled (table lookup or nested program)");
        }
        for t in targets {
            if hub_tables.insert(t) {
                frontier.push(t);
                if seen.insert(t) {
                    involved.push(t);
                }
            }
        }
    }

    // Structural gates.
    let mut minting_leaf = None;
    for (i, leaf) in leaves.iter().enumerate() {
        if leaf.rules.iter().any(|r| r.needs_mint) {
            if minting_leaf.is_some() {
                return fallback("more than one minting leaf per schedule");
            }
            minting_leaf = Some(i);
        }
    }
    validate_write_placement(&region, &leaves)?;

    // Table gates.
    for &f in &involved {
        let arity = eg.info(f).arity;
        if arity > W {
            return fallback("table arity exceeds the row width cap");
        }
        if eg.subsumed.get(&f).is_some_and(|s| !s.is_empty()) {
            return fallback("an involved table has subsumed rows");
        }
        if let Some(rows) = eg.mirror.get(&f) {
            if rows.iter().any(|r| r.len() != arity) {
                return fallback("an involved table stores rows wider than its arity");
            }
        }
        if hub_tables.contains(&f) {
            if let Some(keys) = eg.by_key.get(&f) {
                if keys.values().any(|entries| entries.len() != 1) {
                    return fallback("a hub table transiently holds multiple rows per key");
                }
            }
        }
    }

    Some(Prep {
        region,
        leaves,
        involved,
        hub_tables,
        minting_leaf,
    })
}

/// Merge programs the hub can fold: column ops, constants, primitives not
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

/// Writes must all live inside exactly ONE loop, in ONE write-bearing leaf:
/// the hub's effects-through-a-round-Variable cycle needs a loop scope, and a
/// second write leaf in the same round would see its sibling's writes a round
/// late (the host applies per leaf).
fn validate_write_placement(region: &Region, leaves: &[LeafPlan]) -> Option<()> {
    fn write_leaves(region: &Region, leaves: &[LeafPlan], out: &mut Vec<usize>) {
        match region {
            Region::Leaf(i) => {
                if leaves[*i].rules.iter().any(|r| !r.writes.is_empty() || r.needs_mint) {
                    out.push(*i);
                }
            }
            Region::Seq(children) => {
                for child in children {
                    write_leaves(child, leaves, out);
                }
            }
            Region::Loop(_, inner) => write_leaves(inner, leaves, out),
        }
    }
    fn check(region: &Region, leaves: &[LeafPlan], in_loop: bool) -> Option<()> {
        match region {
            Region::Leaf(i) => {
                let writes = leaves[*i]
                    .rules
                    .iter()
                    .any(|r| !r.writes.is_empty() || r.needs_mint);
                if writes && !in_loop {
                    return fallback("writes outside a loop are not compiled yet");
                }
                Some(())
            }
            Region::Seq(children) => {
                for child in children {
                    check(child, leaves, in_loop)?;
                }
                Some(())
            }
            Region::Loop(_, inner) => {
                let mut writers = Vec::new();
                write_leaves(inner, leaves, &mut writers);
                if writers.len() > 1 {
                    return fallback("more than one write-bearing leaf in a loop");
                }
                check(inner, leaves, true)
            }
        }
    }
    check(region, leaves, false)
}

fn shape(
    eg: &EGraph,
    spec: &ScheduleSpec,
    in_loop: bool,
    leaves: &mut Vec<LeafPlan>,
) -> Option<Region> {
    match spec {
        ScheduleSpec::Run { ruleset, rules } => {
            let leaf = prepare_leaf(eg, ruleset, rules)?;
            leaves.push(leaf);
            Some(Region::Leaf(leaves.len() - 1))
        }
        ScheduleSpec::Sequence(inners) => Some(Region::Seq(
            inners
                .iter()
                .map(|s| shape(eg, s, in_loop, leaves))
                .collect::<Option<Vec<_>>>()?,
        )),
        ScheduleSpec::Repeat(_, _) | ScheduleSpec::Saturate(_) if in_loop => {
            fallback("nested loops are not compiled yet")
        }
        ScheduleSpec::Repeat(limit, inner) => Some(Region::Loop(
            Some(*limit as u64),
            Box::new(shape(eg, inner, true, leaves)?),
        )),
        ScheduleSpec::Saturate(inner) => {
            Some(Region::Loop(None, Box::new(shape(eg, inner, true, leaves)?)))
        }
    }
}

/// What a head-local variable resolves to while interpreting the action list.
#[derive(Clone)]
enum HeadVal {
    Col(usize),
    Const(u32),
    Mint,
    /// A hash-cons result: reading it is not compiled yet (constructors).
    SieResult,
}

fn prepare_leaf(
    eg: &EGraph,
    ruleset: &str,
    rules: &[egglog_backend_trait::RuleId],
) -> Option<LeafPlan> {
    let mut compiled = Vec::new();
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

        // Body: pure Live table atoms only.
        for atom in &rule.core.body.atoms {
            match atom.head {
                RuleBodyCall::Table {
                    read: ReadMode::Live,
                    ..
                } => {}
                RuleBodyCall::Table { .. } => {
                    return fallback("a body atom reads a non-Live view");
                }
                RuleBodyCall::Primitive { .. } => {
                    return fallback("a body primitive is not compiled yet");
                }
            }
        }
        let Ok(plan) = plan_join(rule) else {
            return fallback("the body does not plan (atom-less or too wide)");
        };
        let step_col = &plan.projection.step_col;
        let first_ops = AtomOps::bind_stage(&plan.atoms[0].slots, &step_col[0]);
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
            stages.push(StagePlan {
                func: plan.atoms[i].read_key.func,
                left_cols,
                right_cols,
                ops: AtomOps::join_stage(slots, prev, next),
            });
        }
        let last_layout = step_col.last().expect("plans have at least one atom");

        // Head: interpret the action list, tracking head-local bindings.
        let mut alias: HashMap<u32, HeadVal> = HashMap::new();
        let resolve = |alias: &HashMap<u32, HeadVal>,
                       term: &GenericAtomTerm<
            egglog_backend_trait::RuleVar,
            egglog_backend_trait::RuleValue,
        >|
         -> Option<HeadVal> {
            match term {
                GenericAtomTerm::Var(_, v) => match alias.get(&v.id) {
                    Some(val) => Some(val.clone()),
                    None => last_layout.get(&v.id).map(|c| HeadVal::Col(*c)),
                },
                GenericAtomTerm::Literal(_, c) => Some(HeadVal::Const(c.value.rep())),
                GenericAtomTerm::Global(..) => None,
            }
        };
        let as_src = |val: HeadVal| -> Option<Src> {
            match val {
                HeadVal::Col(c) => Some(Src::Col(c)),
                HeadVal::Const(v) => Some(Src::Const(v)),
                HeadVal::Mint => Some(Src::Mint),
                HeadVal::SieResult => None,
            }
        };

        let mut needs_mint = false;
        let mut writes = Vec::new();
        for action in &rule.core.head.0 {
            match action {
                GenericCoreAction::Let(_, var, RuleActionCall::Primitive { id, name, .. }, args) => {
                    if &**name == "get-fresh!" {
                        if needs_mint {
                            return fallback("more than one mint per rule is not compiled yet");
                        }
                        needs_mint = true;
                        alias.insert(var.id, HeadVal::Mint);
                    } else if let Some(op) = eg.set_if_empty_ops.get(id) {
                        let view = *eg.table_ids.get(&op.view_name)?;
                        if args.len() != op.n_keys + op.out_arity
                            || eg.info(view).arity != op.n_keys + op.out_arity
                        {
                            return fallback("a hash-cons arity mismatch");
                        }
                        let srcs: Option<Vec<Src>> = args
                            .iter()
                            .map(|t| resolve(&alias, t).and_then(&as_src))
                            .collect();
                        let Some(srcs) = srcs else {
                            return fallback("a hash-cons argument is not compiled yet");
                        };
                        writes.push(WriteEffect {
                            op: OP_SIE,
                            func: view,
                            srcs,
                        });
                        alias.insert(var.id, HeadVal::SieResult);
                    } else {
                        return fallback("a head primitive is not compiled yet");
                    }
                }
                GenericCoreAction::Let(_, _, RuleActionCall::Table { .. }, _) => {
                    return fallback("a head table lookup (constructor) is not compiled yet");
                }
                GenericCoreAction::LetAtomTerm(_, var, term) => {
                    let Some(val) = resolve(&alias, term) else {
                        return fallback("a head alias reads an unbound term");
                    };
                    alias.insert(var.id, val);
                }
                GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, args, values) => {
                    let srcs: Option<Vec<Src>> = args
                        .iter()
                        .chain(values.iter())
                        .map(|t| resolve(&alias, t).and_then(&as_src))
                        .collect();
                    let Some(srcs) = srcs else {
                        return fallback("a Set reads a value that is not compiled yet");
                    };
                    if srcs.len() != eg.info(*id).arity {
                        return fallback("a Set's column count differs from the table arity");
                    }
                    writes.push(WriteEffect {
                        op: OP_SET,
                        func: *id,
                        srcs,
                    });
                }
                GenericCoreAction::Set(..) => {
                    return fallback("a Set on a primitive is not compiled");
                }
                GenericCoreAction::Change(_, change, RuleActionCall::Table { id, .. }, args) => {
                    if !matches!(change, egglog_ast::generic_ast::Change::Delete) {
                        return fallback("subsume is not compiled yet");
                    }
                    if args.len() != eg.n_keys(*id) {
                        return fallback("a delete does not address exactly the key columns");
                    }
                    let srcs: Option<Vec<Src>> = args
                        .iter()
                        .map(|t| resolve(&alias, t).and_then(&as_src))
                        .collect();
                    let Some(srcs) = srcs else {
                        return fallback("a delete reads a value that is not compiled yet");
                    };
                    writes.push(WriteEffect {
                        op: OP_DELETE,
                        func: *id,
                        srcs,
                    });
                }
                GenericCoreAction::Change(..)
                | GenericCoreAction::Union(..)
                | GenericCoreAction::Panic(..) => {
                    return fallback("a head action other than Set/Let/delete is not compiled yet");
                }
            }
        }

        compiled.push(CompiledRule {
            first_func: plan.atoms[0].read_key.func,
            first_ops,
            stages,
            needs_mint,
            writes,
        });
    }
    Some(LeafPlan {
        ruleset: ruleset.to_string(),
        rules: compiled,
    })
}

// ---------------------------------------------------------------------------
// Execution: build the dataflow, run one epoch, drain into the host tables.
// ---------------------------------------------------------------------------

struct RunCtx {
    first_id: u32,
    mint_count: CountSink,
    deltas: DeltaSink,
    channels: HubChannels,
}

/// `Ok(None)` = a primitive proved unsafe off-host: nothing was mutated, the
/// primitive is cached, and the caller must interpret instead.
fn run_compiled(eg: &mut EGraph, prep: Prep) -> Result<Option<Vec<ScheduleLeafReport>>> {
    use timely::communication::allocator::thread::Thread;
    use timely::communication::allocator::Allocator;
    use timely::worker::Worker;
    use timely::WorkerConfig;

    if let Some(message) = eg.take_panic_message() {
        return Err(anyhow!(message));
    }

    let ctx = RunCtx {
        first_id: eg.peek_fresh_id(),
        mint_count: CountSink::default(),
        deltas: DeltaSink::default(),
        channels: HubChannels::default(),
    };
    let hub_specs: HashMap<u32, HubTable> = prep
        .hub_tables
        .iter()
        .map(|&f| {
            let (n_keys, merge, _, n_identity_vals) = eg.function_spec(f);
            (
                f.rep(),
                HubTable {
                    n_keys,
                    arity: eg.info(f).arity,
                    merge,
                    n_identity_vals,
                    level: eg.merge_level(f),
                    name: eg.relation_name(f).to_string(),
                },
            )
        })
        .collect();
    let hub_seeds: HashMap<u32, HashMap<Vec<u32>, Vec<u32>>> = prep
        .hub_tables
        .iter()
        .map(|&f| {
            let n_keys = eg.n_keys(f);
            let rows = eg
                .mirror
                .get(&f)
                .map(|rows| {
                    rows.iter()
                        .map(|r| (r[..n_keys].to_vec(), r[n_keys..].to_vec()))
                        .collect()
                })
                .unwrap_or_default();
            (f.rep(), rows)
        })
        .collect();

    if prep.involved.is_empty() {
        return Ok(Some(reports(&prep, false)));
    }

    let alloc = Allocator::Thread(Thread::default());
    let mut worker = Worker::new(
        WorkerConfig::default(),
        alloc,
        Some(std::time::Instant::now()),
    );
    let probe = ProbeHandle::new();
    let mut sessions = {
        let probe = probe.clone();
        let prep_ref = &prep;
        let ctx_ref = &ctx;
        let db = eg.db_clone();
        let unit_rep = eg.unit_rep();
        worker.dataflow::<u32, _, _>(move |scope| {
            let mut sessions = HashMap::new();
            let mut state: HashMap<FunctionId, Coll<'_, u32>> = HashMap::new();
            for &f in &prep_ref.involved {
                let (session, coll) = scope.new_collection::<Row, isize>();
                sessions.insert(f, session);
                state.insert(f, coll);
            }
            let seeds = state.clone();

            walk_outer(
                prep_ref,
                &prep_ref.region,
                ctx_ref,
                (db, unit_rep, hub_specs, hub_seeds),
                scope,
                &mut state,
            );

            for (&f, seed) in &seeds {
                if !prep_ref.hub_tables.contains(&f) {
                    continue;
                }
                let sink = Rc::clone(&ctx_ref.deltas);
                let frep = f.rep();
                state[&f]
                    .clone()
                    .concat(seed.clone().negate())
                    .inspect_batch(move |_t, batch| {
                        let mut sink = sink.borrow_mut();
                        for (row, _t, w) in batch.iter() {
                            *sink.entry((frep, *row)).or_insert(0) += w;
                        }
                    })
                    .probe_with(&probe);
            }
            sessions
        })
    };

    for (&f, session) in sessions.iter_mut() {
        if let Some(rows) = eg.mirror.get(&f) {
            for row in rows.iter() {
                session.insert(pack_row::<W>(row)?);
            }
        }
        session.advance_to(1);
        session.flush();
    }
    worker.step_while(|| probe.less_than(&1));
    drop(sessions);
    drop(worker);

    // Dynamic outcomes, checked BEFORE any host mutation.
    if let Some(id) = *ctx.channels.unsafe_prim.borrow() {
        eg.unsafe_prims.insert(id);
        return Ok(None);
    }
    if let Some(message) = ctx.channels.error.borrow_mut().take() {
        return Err(anyhow!(message));
    }

    // Consume the fresh ids the mint stage assigned from the reserved range.
    let minted = *ctx.mint_count.borrow();
    if minted < 0 {
        return Err(anyhow!("compiled schedule retracted minted ids"));
    }
    eg.advance_fresh_ids(minted as usize);

    // Apply net deltas: removals first, then inserts.
    let deltas = std::mem::take(&mut *ctx.deltas.borrow_mut());
    let changed = deltas.values().any(|w| *w != 0) || minted > 0;
    let mut removes: Vec<(FunctionId, Row)> = Vec::new();
    let mut inserts: Vec<(FunctionId, Row)> = Vec::new();
    for ((frep, row), w) in &deltas {
        let f = FunctionId::new(*frep);
        match w.cmp(&0) {
            std::cmp::Ordering::Less => removes.push((f, *row)),
            std::cmp::Ordering::Greater => inserts.push((f, *row)),
            std::cmp::Ordering::Equal => {}
        }
    }
    for (f, row) in removes {
        let n_keys = eg.n_keys(f);
        let key: Box<[u32]> = (0..n_keys).map(|i| row[i]).collect();
        let keys: HashSet<Box<[u32]>> = [key].into_iter().collect();
        eg.remove_matching_keys(f, n_keys, &keys);
    }
    for (f, row) in inserts {
        let arity = eg.info(f).arity;
        let full: Vec<u32> = (0..arity).map(|i| row[i]).collect();
        eg.insert_live_row(f, full.into_boxed_slice());
    }

    Ok(Some(reports(&prep, changed)))
}

fn reports(prep: &Prep, changed: bool) -> Vec<ScheduleLeafReport> {
    prep.leaves
        .iter()
        .enumerate()
        .map(|(i, leaf)| {
            let mut iteration = IterationReport::default();
            // Changes are attributed to write-bearing leaves (an OR-preserving
            // attribution; per-leaf flags do not appear in printed outputs).
            let leaf_writes = leaf
                .rules
                .iter()
                .any(|r| !r.writes.is_empty() || r.needs_mint);
            iteration.rule_set_report.changed =
                changed && (leaf_writes || prep.minting_leaf == Some(i));
            ScheduleLeafReport {
                ruleset: leaf.ruleset.clone(),
                iteration,
            }
        })
        .collect()
}

type HubWiring = (
    egglog_core_relations::Database,
    u32,
    HashMap<u32, HubTable>,
    HashMap<u32, HashMap<Vec<u32>, Vec<u32>>>,
);

/// Walk at the epoch scope. Read-only leaves/sequences evaluate against the
/// current state (which never changes at this scope: all writes live inside
/// the single writing loop); the writing loop opens the hub scope.
fn walk_outer<'s>(
    prep: &Prep,
    region: &Region,
    ctx: &RunCtx,
    hub: HubWiring,
    scope: Scope<'s, u32>,
    state: &mut HashMap<FunctionId, Coll<'s, u32>>,
) {
    match region {
        // Read-only at this scope (validated): nothing to do.
        Region::Leaf(_) => {}
        Region::Seq(children) => {
            for child in children {
                walk_outer(prep, child, ctx, hub.clone(), scope, state);
            }
        }
        Region::Loop(bound, inner) => {
            let (db, unit_rep, hub_specs, hub_seeds) = hub;
            let bound = *bound;
            let finals = scope.scoped::<Product<u32, u64>, _, _>("CompiledRegion", |inner_scope| {
                let step = Product::new(Default::default(), 1);
                let mut inner_state: HashMap<FunctionId, Coll<'_, Product<u32, u64>>> =
                    HashMap::new();
                for (&f, coll) in state.iter() {
                    inner_state.insert(f, coll.clone().enter(inner_scope));
                }

                // The hub cycle: effects (round r) → Variable(+1) → hub
                // (applied at r+1) → state deltas → next round's matches.
                let (ops_var, ops_fed) =
                    Variable::<_, Vec<(HubOp, _, isize)>>::new(inner_scope, step);
                let hub_out = merge_hub(
                    &ops_fed,
                    hub_specs,
                    hub_seeds,
                    db,
                    unit_rep,
                    ctx.channels.clone(),
                );
                for &f in &prep.hub_tables {
                    let frep = f.rep();
                    let deltas = hub_out
                        .clone()
                        .flat_map(move |(t, row)| (t == frep).then_some(row));
                    let base = inner_state[&f].clone().concat(deltas);
                    inner_state.insert(f, base);
                }

                let effects = walk_region_effects(prep, inner, ctx, &mut inner_state);
                let fed = match (effects, bound) {
                    (Some(effects), Some(n)) => effects
                        .inner
                        .clone()
                        .filter(move |(_, t, _)| t.inner < n)
                        .as_collection(),
                    (Some(effects), None) => effects,
                    (None, _) => {
                        // A read-only loop never changes state: feed nothing.
                        ops_fed.clone().filter(|_| false)
                    }
                };
                ops_var.set(fed);

                prep.hub_tables
                    .iter()
                    .map(|&f| (f, inner_state[&f].clone().leave(scope)))
                    .collect::<Vec<_>>()
            });
            for (f, final_state) in finals {
                state.insert(f, final_state);
            }
        }
    }
}

/// Build a loop body's binding joins and latched, tagged write-op stream.
fn walk_region_effects<'s, T>(
    prep: &Prep,
    region: &Region,
    ctx: &RunCtx,
    state: &mut HashMap<FunctionId, Coll<'s, T>>,
) -> Option<VecCollection<'s, T, HubOp>>
where
    T: Timestamp + Lattice + Ord,
{
    match region {
        Region::Leaf(i) => apply_leaf(&prep.leaves[*i], ctx, state),
        Region::Seq(children) => {
            let mut out: Option<VecCollection<'s, T, HubOp>> = None;
            for child in children {
                if let Some(effects) = walk_region_effects(prep, child, ctx, state) {
                    out = Some(match out {
                        None => effects,
                        Some(prior) => prior.concat(effects),
                    });
                }
            }
            out
        }
        Region::Loop(..) => unreachable!("shape() rejects nested loops"),
    }
}

/// One leaf: rule joins against the incoming state, the mint stage, and the
/// latched tagged write ops (fed to the hub by the enclosing loop).
fn apply_leaf<'s, T>(
    leaf: &LeafPlan,
    ctx: &RunCtx,
    state: &mut HashMap<FunctionId, Coll<'s, T>>,
) -> Option<VecCollection<'s, T, HubOp>>
where
    T: Timestamp + Lattice + Ord,
{
    // Every rule's binding collection against the same incoming state.
    let mut bindings: Vec<Coll<'s, T>> = Vec::new();
    for rule in &leaf.rules {
        let ops0 = rule.first_ops.clone();
        let mut cur = state[&rule.first_func]
            .clone()
            .flat_map(move |r: Row| ops0.apply(&Row::default(), &r));
        for stage in &rule.stages {
            let left_cols = stage.left_cols.clone();
            let right_cols = stage.right_cols.clone();
            let ops = stage.ops.clone();
            let left = cur.map(move |b: Row| (pack_key128(&b, &left_cols), b));
            let right = state[&stage.func]
                .clone()
                .map(move |r: Row| (pack_key128(&r, &right_cols), r));
            cur = left
                .join_map(right, move |_key, b, r| ops.apply(b, r))
                .flat_map(|opt| opt);
        }
        bindings.push(cur);
    }

    // The leaf's shared mint stage: one replay-stable id per (rule, binding).
    let minted = if leaf.rules.iter().any(|r| r.needs_mint) {
        let mut demands: Option<VecCollection<'s, T, (u32, Row)>> = None;
        for (tag, (rule, cur)) in leaf.rules.iter().zip(&bindings).enumerate() {
            if !rule.needs_mint {
                continue;
            }
            let tag = tag as u32;
            let tagged = cur.clone().map(move |b: Row| (tag, b));
            demands = Some(match demands {
                None => tagged,
                Some(d) => d.concat(tagged),
            });
        }
        let minted = memoizing_mint(&demands.expect("a minting rule exists"), ctx.first_id);
        let count = Rc::clone(&ctx.mint_count);
        minted.clone().inspect_batch(move |_t, batch| {
            *count.borrow_mut() += batch.iter().map(|(_, _, w)| *w).sum::<isize>();
        });
        Some(minted)
    } else {
        None
    };

    // Tagged write ops from every rule, latched so retracted bindings never
    // retract an applied effect (monotone-fire).
    let mut all_ops: Option<VecCollection<'s, T, HubOp>> = None;
    for (tag, (rule, cur)) in leaf.rules.iter().zip(&bindings).enumerate() {
        if rule.writes.is_empty() {
            continue;
        }
        let enriched: VecCollection<'s, T, (Row, u32)> = if rule.needs_mint {
            let tag = tag as u32;
            minted
                .as_ref()
                .expect("the mint stage exists when a rule mints")
                .clone()
                .flat_map(move |((t, b), id)| (t == tag).then_some((b, id)))
        } else {
            cur.clone().map(|b: Row| (b, 0u32))
        };
        for write in &rule.writes {
            let srcs = write.srcs.clone();
            let op = write.op;
            let frep = write.func.rep();
            let stream = enriched
                .clone()
                .map(move |(b, id)| (op, frep, build_row(&srcs, &b, id)));
            let latched = rising_edge(&stream);
            all_ops = Some(match all_ops {
                None => latched,
                Some(prior) => prior.concat(latched),
            });
        }
    }
    all_ops
}

/// Materialize an effect row from its column sources.
fn build_row(srcs: &[Src], binding: &Row, minted: u32) -> Row {
    let mut row = Row::default();
    for (i, src) in srcs.iter().enumerate() {
        row[i] = match src {
            Src::Col(c) => binding[*c],
            Src::Const(v) => *v,
            Src::Mint => minted,
        };
    }
    row
}

#[cfg(test)]
mod tests {
    use super::*;
    use egglog_backend_trait::{Backend, ColumnTy, DefaultVal, FunctionConfig};

    fn row(vals: &[u32]) -> Box<[u32]> {
        vals.to_vec().into_boxed_slice()
    }

    fn table(
        eg: &mut EGraph,
        name: &str,
        schema: Vec<ColumnTy>,
        n_vals: usize,
        merge: MergeFn,
    ) -> FunctionId {
        Backend::add_table(
            eg,
            FunctionConfig {
                schema,
                n_vals,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge,
                name: name.to_string(),
                can_subsume: false,
            },
        )
    }

    /// Tables for `A(x, v) => B(x, fresh!) ; V[x] sie (fresh!, ()) ; set F(x)=v`.
    fn fixture(eg: &mut EGraph) -> (FunctionId, FunctionId, FunctionId, FunctionId) {
        let unit_ty = Backend::base_values(eg).get_ty::<()>();
        let unit = ColumnTy::Base(unit_ty);
        let a = table(eg, "A", vec![ColumnTy::Id, ColumnTy::Id, unit], 1, MergeFn::Old);
        let b = table(
            eg,
            "B",
            vec![ColumnTy::Id, ColumnTy::Id, unit],
            1,
            MergeFn::Old,
        );
        // The view maps key -> (eclass, unit): two value columns.
        let v = table(
            eg,
            "V",
            vec![ColumnTy::Id, ColumnTy::Id, unit],
            2,
            MergeFn::Columns(vec![MergeFn::Old, MergeFn::Old]),
        );
        // F folds same-key writes with UnionId (min) — a genuine merge.
        let f = table(
            eg,
            "F",
            vec![ColumnTy::Id, ColumnTy::Id, unit],
            2,
            MergeFn::Columns(vec![MergeFn::UnionId, MergeFn::Old]),
        );
        (a, b, v, f)
    }

    fn leaf_rule(
        a: FunctionId,
        b: FunctionId,
        v: FunctionId,
        f: FunctionId,
        needs_mint: bool,
    ) -> CompiledRule {
        let mut layout = HashMap::new();
        layout.insert(0u32, 0usize);
        layout.insert(1u32, 1usize);
        layout.insert(2u32, 2usize);
        let mut writes = vec![WriteEffect {
            op: OP_SET,
            func: f,
            srcs: vec![Src::Col(0), Src::Col(1), Src::Const(0)],
        }];
        if needs_mint {
            writes.push(WriteEffect {
                op: OP_SET,
                func: b,
                srcs: vec![Src::Col(0), Src::Mint, Src::Const(0)],
            });
            writes.push(WriteEffect {
                op: OP_SIE,
                func: v,
                srcs: vec![Src::Col(0), Src::Mint, Src::Const(0)],
            });
        }
        CompiledRule {
            first_func: a,
            first_ops: AtomOps::bind_stage(
                &[Slot::Var(0), Slot::Var(1), Slot::Var(2)],
                &layout,
            ),
            stages: Vec::new(),
            needs_mint,
            writes,
        }
    }

    fn prep_for(
        eg: &EGraph,
        rule: CompiledRule,
        involved: Vec<FunctionId>,
        hub: Vec<FunctionId>,
        minting: bool,
    ) -> Prep {
        let _ = eg;
        Prep {
            region: Region::Loop(None, Box::new(Region::Leaf(0))),
            leaves: vec![LeafPlan {
                ruleset: "t".to_string(),
                rules: vec![rule],
            }],
            involved,
            hub_tables: hub.into_iter().collect(),
            minting_leaf: minting.then_some(0),
        }
    }

    /// Mint + hash-cons + merge fold end to end: one replay-stable id per
    /// binding; one view row per key; UnionId folds colliding F writes to the
    /// minimum; the counter advances past the minted range.
    #[test]
    fn hub_folds_mints_and_hash_cons() {
        let mut eg = EGraph::new();
        let (a, b, v, f) = fixture(&mut eg);
        // Two rows sharing F-key 1 (values 7 and 5 -> min 5), one row key 2.
        eg.insert_live_row(a, row(&[1, 7, 0]));
        eg.insert_live_row(a, row(&[1, 5, 0]));
        eg.insert_live_row(a, row(&[2, 9, 0]));
        let first = eg.peek_fresh_id();

        let prep = prep_for(
            &eg,
            leaf_rule(a, b, v, f, true),
            vec![a, b, v, f],
            vec![b, v, f],
            true,
        );
        let leaves = run_compiled(&mut eg, prep)
            .expect("compiled run succeeds")
            .expect("no unsafe primitives here");
        assert!(leaves[0].iteration.changed());

        // Bindings sort as (1,5,_) < (1,7,_) < (2,9,_): ids in that order.
        let expected_b: crate::HashSet<Box<[u32]>> = [
            row(&[1, first, 0]),
            row(&[1, first + 1, 0]),
            row(&[2, first + 2, 0]),
        ]
        .into_iter()
        .collect();
        assert_eq!(eg.mirror[&b], expected_b);
        // One view row per key; the minimum candidate row wins deterministically.
        let expected_v: crate::HashSet<Box<[u32]>> =
            [row(&[1, first, 0]), row(&[2, first + 2, 0])]
                .into_iter()
                .collect();
        assert_eq!(eg.mirror[&v], expected_v);
        // UnionId merge folded key 1 to min(7, 5) = 5.
        let expected_f: crate::HashSet<Box<[u32]>> = [row(&[1, 5, 0]), row(&[2, 9, 0])]
            .into_iter()
            .collect();
        assert_eq!(eg.mirror[&f], expected_f);
        assert_eq!(eg.peek_fresh_id(), first + 3);
    }

    /// A pre-existing view key wins set-if-empty; a pre-existing F row folds
    /// with incoming writes through the merge.
    #[test]
    fn hub_respects_existing_rows() {
        let mut eg = EGraph::new();
        let (a, b, v, f) = fixture(&mut eg);
        eg.insert_live_row(a, row(&[1, 7, 0]));
        eg.insert_live_row(v, row(&[1, 99, 0]));
        eg.insert_live_row(f, row(&[1, 3, 0]));
        let first = eg.peek_fresh_id();

        let prep = prep_for(
            &eg,
            leaf_rule(a, b, v, f, true),
            vec![a, b, v, f],
            vec![b, v, f],
            true,
        );
        run_compiled(&mut eg, prep)
            .expect("compiled run succeeds")
            .expect("no unsafe primitives here");

        let expected_v: crate::HashSet<Box<[u32]>> = [row(&[1, 99, 0])].into_iter().collect();
        assert_eq!(eg.mirror[&v], expected_v);
        // min(3, 7) = 3: the merge kept the existing row (no drain delta).
        let expected_f: crate::HashSet<Box<[u32]>> = [row(&[1, 3, 0])].into_iter().collect();
        assert_eq!(eg.mirror[&f], expected_f);
        assert_eq!(eg.peek_fresh_id(), first + 1);
    }

    /// An AssertEq merge violation surfaces as the host's error message.
    #[test]
    fn hub_surfaces_merge_errors() {
        let mut eg = EGraph::new();
        let (a, b, v, f) = fixture(&mut eg);
        let unit_ty = Backend::base_values(&eg).get_ty::<()>();
        let strict = table(
            &mut eg,
            "S",
            vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
            2,
            MergeFn::Columns(vec![MergeFn::AssertEq, MergeFn::Old]),
        );
        let _ = (b, v, f);
        eg.insert_live_row(a, row(&[1, 7, 0]));
        eg.insert_live_row(strict, row(&[1, 3, 0]));

        let rule = CompiledRule {
            first_func: a,
            first_ops: AtomOps::bind_stage(
                &[Slot::Var(0), Slot::Var(1), Slot::Var(2)],
                &{
                    let mut l = HashMap::new();
                    l.insert(0u32, 0usize);
                    l.insert(1u32, 1usize);
                    l.insert(2u32, 2usize);
                    l
                },
            ),
            stages: Vec::new(),
            needs_mint: false,
            writes: vec![WriteEffect {
                op: OP_SET,
                func: strict,
                srcs: vec![Src::Col(0), Src::Col(1), Src::Const(0)],
            }],
        };
        let prep = prep_for(&eg, rule, vec![a, strict], vec![strict], false);
        let err = run_compiled(&mut eg, prep)
            .expect_err("conflicting AssertEq write must error");
        assert!(err.to_string().contains("illegal merge attempted"));
        // Nothing landed on the host.
        assert_eq!(eg.mirror[&strict].len(), 1);
    }
}
