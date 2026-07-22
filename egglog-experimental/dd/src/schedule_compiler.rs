//! Compile a backend [`ScheduleSpec`] tree into ONE DD dataflow and run it in
//! a single epoch — loops become in-dataflow fixpoints instead of host-driven
//! iterations (docs/rebuild-in-dataflow.md).
//!
//! Schedule nodes map to dataflow constructs: `Sequence` chains table states
//! through leaves; `Saturate` opens a nested scope whose feedback `Variable`s
//! carry each written table to fixpoint; `Repeat(n)` is the same scope with
//! feedback gated to rounds `< n` (at most n bounded hops, early convergence
//! free); a `Run` leaf joins rule bodies against the incoming state and merges
//! each rule's effects into the outgoing state.
//!
//! Head actions compile onto the monotone-fire toolkit ([`crate::monotone`]):
//!
//! - `(get-fresh! "sort")` lowers to a [`memoizing_mint`] stage keyed by
//!   `(rule, binding)` — replay-stable fresh ids, one per firing, drawn from
//!   a range reserved on the host counter and consumed after the run.
//! - `set-if-empty-<view>!` (the term encoder's hash-cons) lowers to a
//!   [`first_per_key`] latch per (leaf, view): candidates race per key, the
//!   earliest round's minimum wins ONCE, and pre-existing view keys are
//!   primed as zero-priority sentinels so they always win. The latched
//!   output is append-only, so loop feedback stays monotone.
//! - Plain `Set`s are idempotent set-union inserts (`distinct`).
//!
//! This still compiles a SUBSET and falls back to the interpreter with an
//! env-gated reason (`EGGLOG_DD_DUMP_PLANS=1`) otherwise: rule bodies must be
//! pure `Live` table atoms; heads may mint (at most one minting leaf per
//! schedule — each mint stage owns an id range — and one mint per rule),
//! write tables whose value columns are agreed constants, and hash-cons into
//! views whose result is unused; loops must not nest. General merges, body
//! primitives, deletes/subsumes, used hash-cons results (constructors), and
//! nested loops arrive next.
//!
//! Faithfulness: a leaf computes every rule's matches against the SAME
//! pre-leaf state before any effect lands (egglog's match-then-apply model);
//! loop rounds see round-boundary snapshots exactly like host iterations; a
//! table's final state leaves a loop as `seed ∪ gated feedback`, so
//! `Repeat(0)` is a no-op and `Repeat(n)` applies exactly n passes. Fresh-id
//! VALUES are implementation-defined in the reference backend too (host
//! HashMap iteration order), so the compiled deterministic assignment is
//! observably equivalent. Compiled leaves report `changed` per leaf at the
//! top level and per enclosing loop inside one (an OR-preserving attribution;
//! per-leaf flags do not appear in printed outputs).

use std::cell::RefCell;
use std::rc::Rc;

use anyhow::{anyhow, Result};
use differential_dataflow::input::Input;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::operators::iterate::Variable;
use differential_dataflow::{AsCollection, VecCollection};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_backend_trait::{
    FunctionId, IterationReport, ReadMode, RuleActionCall, RuleBodyCall, ScheduleLeafReport,
    ScheduleSpec,
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
use crate::monotone::{first_per_key, memoizing_mint};
use crate::EGraph;

/// Compiled-region rows run at the planner cap width; per-region ladder
/// selection (as the fused join does) is a later optimization.
type Row = RowN<W>;
type Coll<'s, T> = VecCollection<'s, T, Row>;
/// Accumulated net weight of a region's new-row stream (`> 0` = changed).
type ChangeSink = Rc<RefCell<isize>>;
/// Final-state minus seed deltas for one table, drained into the host.
type DrainSink = Rc<RefCell<Vec<(Row, isize)>>>;

/// A column of an effect row: copied from a binding column, a constant, or
/// this rule's minted fresh id.
#[derive(Clone)]
enum Src {
    Col(usize),
    Const(u32),
    Mint,
}

/// One join stage of a compiled rule (atoms 1..): the joined table, the
/// binding/atom key columns, and the compiled remap program.
struct StagePlan {
    func: FunctionId,
    left_cols: Vec<usize>,
    right_cols: Vec<usize>,
    ops: AtomOps,
}

/// A lowered `set-if-empty-<view>!` hash-cons: insert `srcs` (keys then
/// outputs) into `view` only if the key prefix is absent, first writer wins.
struct SieEffect {
    view: FunctionId,
    n_keys: usize,
    srcs: Vec<Src>,
}

struct CompiledRule {
    first_func: FunctionId,
    first_ops: AtomOps,
    stages: Vec<StagePlan>,
    needs_mint: bool,
    /// Plain table `Set`s: target and per-column sources (arity wide).
    sets: Vec<(FunctionId, Vec<Src>)>,
    sies: Vec<SieEffect>,
}

struct LeafPlan {
    ruleset: String,
    rules: Vec<CompiledRule>,
}

/// Validated schedule shape: loops (`Repeat`/`Saturate`) contain no nested
/// loops, so the dataflow needs exactly one nested-scope level.
enum Region {
    Leaf(usize),
    Seq(Vec<Region>),
    /// `Some(n)` = Repeat(n), `None` = Saturate.
    Loop(Option<u64>, Box<Region>),
}

struct Prep {
    region: Region,
    leaves: Vec<LeafPlan>,
    involved: Vec<FunctionId>,
    written: HashSet<FunctionId>,
    /// The single leaf allowed to mint, if any.
    minting_leaf: Option<usize>,
}

/// Shared per-run context for leaf lowering.
struct LeafCtx {
    /// First fresh id the (single) mint stage may assign.
    first_id: u32,
    /// Net count of ids the mint stage assigned.
    mint_count: ChangeSink,
}

/// Log (env-gated) why a schedule fell back to the interpreter, then `None`.
fn fallback<T>(reason: &str) -> Option<T> {
    if std::env::var("EGGLOG_DD_DUMP_PLANS").is_ok() {
        eprintln!("[dd-compile] fallback: {reason}");
    }
    None
}

/// Compile and run `spec`, or `None` when any part of it is outside the
/// supported subset (the caller falls back to the interpreter).
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
            "[dd-compile] compiled schedule: {} leaves, {} tables ({} written)",
            prep.leaves.len(),
            prep.involved.len(),
            prep.written.len(),
        );
    }
    Some(run_compiled(eg, prep))
}

// ---------------------------------------------------------------------------
// Preparation: validate the subset and lower rules to join/effect plans.
// ---------------------------------------------------------------------------

fn prepare(eg: &EGraph, spec: &ScheduleSpec) -> Option<Prep> {
    let mut leaves = Vec::new();
    let region = shape(eg, spec, false, &mut leaves)?;

    let mut involved: Vec<FunctionId> = Vec::new();
    let mut set_written: HashSet<FunctionId> = HashSet::new();
    let mut sie_written: HashSet<FunctionId> = HashSet::new();
    let mut seen: HashSet<FunctionId> = HashSet::new();
    for leaf in &leaves {
        for rule in &leaf.rules {
            for f in std::iter::once(rule.first_func).chain(rule.stages.iter().map(|s| s.func)) {
                if seen.insert(f) {
                    involved.push(f);
                }
            }
            for (f, _) in &rule.sets {
                set_written.insert(*f);
                if seen.insert(*f) {
                    involved.push(*f);
                }
            }
            for sie in &rule.sies {
                sie_written.insert(sie.view);
                if seen.insert(sie.view) {
                    involved.push(sie.view);
                }
            }
        }
    }
    if set_written.intersection(&sie_written).next().is_some() {
        return fallback("a table is both Set-written and hash-cons-written");
    }

    // At most ONE minting leaf: each minting leaf owns a mint-stage operator
    // instance, and multiple instances would need disjoint id ranges.
    let mut minting_leaf = None;
    for (i, leaf) in leaves.iter().enumerate() {
        if leaf.rules.iter().any(|r| r.needs_mint) {
            if minting_leaf.is_some() {
                return fallback("more than one minting leaf per schedule");
            }
            minting_leaf = Some(i);
        }
    }

    // Table gates: bounded arity, no subsumed side-set, stored rows exactly
    // arity wide, and every plain-Set writer agrees with the seeds on the
    // (constant) value columns so set-union insertion never needs a merge.
    // Hash-cons targets are exempt: their per-key race is decided by the
    // first_per_key latch instead.
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
    }
    for &f in &set_written {
        let arity = eg.info(f).arity;
        let n_keys = eg.n_keys(f);
        let mut value_consts: Option<Vec<u32>> = None;
        for leaf in &leaves {
            for rule in &leaf.rules {
                for (target, srcs) in &rule.sets {
                    if *target != f {
                        continue;
                    }
                    let vals: Option<Vec<u32>> = srcs[n_keys..arity]
                        .iter()
                        .map(|s| match s {
                            Src::Const(v) => Some(*v),
                            Src::Col(_) | Src::Mint => None,
                        })
                        .collect();
                    let Some(vals) = vals else {
                        return fallback("a Set writes non-constant value columns");
                    };
                    match &value_consts {
                        None => value_consts = Some(vals),
                        Some(prior) if *prior == vals => {}
                        Some(_) => {
                            return fallback("writers disagree on a table's value constants")
                        }
                    }
                }
            }
        }
        if let (Some(vals), Some(rows)) = (&value_consts, eg.mirror.get(&f)) {
            if rows
                .iter()
                .any(|r| r[n_keys..arity] != vals[..arity - n_keys])
            {
                return fallback("seed rows disagree with the written value constants");
            }
        }
    }

    let written: HashSet<FunctionId> = set_written.union(&sie_written).copied().collect();
    Some(Prep {
        region,
        leaves,
        involved,
        written,
        minting_leaf,
    })
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
        let mut sets = Vec::new();
        let mut sies = Vec::new();
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
                        sies.push(SieEffect {
                            view,
                            n_keys: op.n_keys,
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
                    sets.push((*id, srcs));
                }
                GenericCoreAction::Set(..) => {
                    return fallback("a Set on a primitive is not compiled");
                }
                GenericCoreAction::Change(..)
                | GenericCoreAction::Union(..)
                | GenericCoreAction::Panic(..) => {
                    return fallback("a head action other than Set/Let is not compiled yet");
                }
            }
        }

        compiled.push(CompiledRule {
            first_func: plan.atoms[0].read_key.func,
            first_ops,
            stages,
            needs_mint,
            sets,
            sies,
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

fn run_compiled(eg: &mut EGraph, prep: Prep) -> Result<Vec<ScheduleLeafReport>> {
    use timely::communication::allocator::thread::Thread;
    use timely::communication::allocator::Allocator;
    use timely::worker::Worker;
    use timely::WorkerConfig;

    if let Some(message) = eg.take_panic_message() {
        return Err(anyhow!(message));
    }

    let leaf_sinks: Vec<ChangeSink> = prep.leaves.iter().map(|_| ChangeSink::default()).collect();
    let ctx = LeafCtx {
        first_id: eg.peek_fresh_id(),
        mint_count: ChangeSink::default(),
    };
    let reports = |sinks: &[ChangeSink], minted: isize| -> Vec<ScheduleLeafReport> {
        prep.leaves
            .iter()
            .enumerate()
            .zip(sinks)
            .map(|((i, leaf), sink)| {
                let mut iteration = IterationReport::default();
                // A mint alone is a database change (the reference counts any
                // fresh-id advance as one).
                iteration.rule_set_report.changed =
                    *sink.borrow() > 0 || (prep.minting_leaf == Some(i) && minted > 0);
                ScheduleLeafReport {
                    ruleset: leaf.ruleset.clone(),
                    iteration,
                }
            })
            .collect()
    };
    if prep.involved.is_empty() {
        return Ok(reports(&leaf_sinks, 0));
    }

    let drain_sinks: HashMap<FunctionId, DrainSink> = prep
        .written
        .iter()
        .map(|&f| (f, DrainSink::default()))
        .collect();

    let alloc = Allocator::Thread(Thread::default());
    let mut worker = Worker::new(
        WorkerConfig::default(),
        alloc,
        Some(std::time::Instant::now()),
    );
    let probe = ProbeHandle::new();
    let mut sessions = {
        let probe = probe.clone();
        let leaf_sinks = leaf_sinks.clone();
        let drain_sinks = drain_sinks.clone();
        let prep_ref = &prep;
        let ctx_ref = &ctx;
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
                &prep_ref.region,
                &prep_ref.leaves,
                &leaf_sinks,
                ctx_ref,
                scope,
                &mut state,
            );

            for (&f, sink) in &drain_sinks {
                let sink = Rc::clone(sink);
                state[&f]
                    .clone()
                    .concat(seeds[&f].clone().negate())
                    .inspect_batch(move |_t, batch| {
                        sink.borrow_mut()
                            .extend(batch.iter().map(|(d, _t, w)| (*d, *w)));
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

    // Consume the fresh ids the mint stage assigned from the reserved range.
    let minted = *ctx.mint_count.borrow();
    if minted < 0 {
        return Err(anyhow!("compiled schedule retracted minted ids"));
    }
    eg.advance_fresh_ids(minted as usize);

    for (f, sink) in drain_sinks {
        let arity = eg.info(f).arity;
        let mut net: HashMap<Row, isize> = HashMap::new();
        for (row, w) in sink.borrow_mut().drain(..) {
            *net.entry(row).or_insert(0) += w;
        }
        for (row, w) in net {
            if w == 0 {
                continue;
            }
            if w < 0 {
                return Err(anyhow!(
                    "compiled schedule produced a retraction for `{}`; the compiled subset must be insert-only",
                    eg.relation_name(f)
                ));
            }
            let full: Vec<u32> = (0..arity).map(|i| row[i]).collect();
            eg.insert_live_row(f, full.into_boxed_slice());
        }
    }

    Ok(reports(&leaf_sinks, minted))
}

/// Walk at the epoch scope: leaves/sequences apply directly; each loop opens
/// ONE nested iterative scope.
fn walk_outer<'s>(
    region: &Region,
    leaves: &[LeafPlan],
    sinks: &[ChangeSink],
    ctx: &LeafCtx,
    scope: Scope<'s, u32>,
    state: &mut HashMap<FunctionId, Coll<'s, u32>>,
) {
    match region {
        Region::Leaf(i) => {
            let written = apply_leaf(&leaves[*i], ctx, state);
            for (f, prev) in written {
                observe_additions(&state[&f], &prev, std::slice::from_ref(&sinks[*i]));
            }
        }
        Region::Seq(children) => {
            for child in children {
                walk_outer(child, leaves, sinks, ctx, scope, state);
            }
        }
        Region::Loop(bound, inner) => {
            let written = written_tables(inner, leaves);
            let inner_sinks: Vec<ChangeSink> = leaf_indices(inner)
                .into_iter()
                .map(|i| Rc::clone(&sinks[i]))
                .collect();
            let prev_state: HashMap<FunctionId, Coll<'s, u32>> = written
                .iter()
                .map(|&f| (f, state[&f].clone()))
                .collect();
            let bound = *bound;
            let finals = scope.scoped::<Product<u32, u64>, _, _>("CompiledRegion", |inner_scope| {
                let step = Product::new(Default::default(), 1);
                let mut inner_state: HashMap<FunctionId, Coll<'_, Product<u32, u64>>> =
                    HashMap::new();
                let mut vars = Vec::new();
                let mut bases = HashMap::new();
                for (&f, coll) in state.iter() {
                    let entered = coll.clone().enter(inner_scope);
                    if written.contains(&f) {
                        // `base = seed ∪ fed` is the round-boundary state: it
                        // is what leaves read, what leaves the loop (so
                        // Repeat(0) is a no-op), and the fixpoint value.
                        let (var, fed) = Variable::new(inner_scope, step);
                        let base = entered.concat(fed).distinct();
                        vars.push((f, var));
                        bases.insert(f, base.clone());
                        inner_state.insert(f, base);
                    } else {
                        inner_state.insert(f, entered);
                    }
                }

                walk_flat(inner, leaves, ctx, &mut inner_state);

                let mut finals = Vec::new();
                for (f, var) in vars {
                    let updated = inner_state[&f].clone();
                    let fed_back = match bound {
                        Some(n) => updated
                            .inner
                            .clone()
                            .filter(move |(_, t, _)| t.inner < n)
                            .as_collection(),
                        None => updated,
                    };
                    var.set(fed_back);
                    finals.push((f, bases[&f].clone().leave(scope)));
                }
                finals
            });
            for (f, final_state) in finals {
                observe_additions(&final_state, &prev_state[&f], &inner_sinks);
                state.insert(f, final_state);
            }
        }
    }
}

/// Walk inside a loop scope: validation guarantees no nested loops here.
fn walk_flat<'s, T>(
    region: &Region,
    leaves: &[LeafPlan],
    ctx: &LeafCtx,
    state: &mut HashMap<FunctionId, Coll<'s, T>>,
) where
    T: Timestamp + Lattice + Ord,
{
    match region {
        Region::Leaf(i) => {
            apply_leaf(&leaves[*i], ctx, state);
        }
        Region::Seq(children) => {
            for child in children {
                walk_flat(child, leaves, ctx, state);
            }
        }
        Region::Loop(..) => unreachable!("shape() rejects nested loops"),
    }
}

/// One bounded hop of a leaf: every rule's matches are computed against the
/// SAME incoming state, then all effects land at once. Returns each written
/// table's pre-leaf state for change observation.
fn apply_leaf<'s, T>(
    leaf: &LeafPlan,
    ctx: &LeafCtx,
    state: &mut HashMap<FunctionId, Coll<'s, T>>,
) -> Vec<(FunctionId, Coll<'s, T>)>
where
    T: Timestamp + Lattice + Ord,
{
    // Pass 1: every rule's binding collection against the pre-leaf state.
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

    // Pass 2: build effect rows from (binding, minted id) per rule.
    let mut set_effects: HashMap<FunctionId, Vec<Coll<'s, T>>> = HashMap::new();
    type SieCandidates<'s, T> = (usize, Vec<VecCollection<'s, T, (Row, (u8, Row))>>);
    let mut sie_candidates: HashMap<FunctionId, SieCandidates<'s, T>> = HashMap::new();
    for (tag, (rule, cur)) in leaf.rules.iter().zip(&bindings).enumerate() {
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
        for (f, srcs) in &rule.sets {
            let srcs = srcs.clone();
            let effect = enriched.clone().map(move |(b, id)| build_row(&srcs, &b, id));
            set_effects.entry(*f).or_default().push(effect);
        }
        for sie in &rule.sies {
            let srcs = sie.srcs.clone();
            let n_keys = sie.n_keys;
            let candidate = enriched.clone().map(move |(b, id)| {
                let full = build_row(&srcs, &b, id);
                let mut key = Row::default();
                for i in 0..n_keys {
                    key[i] = full[i];
                }
                (key, (1u8, full))
            });
            sie_candidates
                .entry(sie.view)
                .or_insert_with(|| (n_keys, Vec::new()))
                .1
                .push(candidate);
        }
    }

    let mut written = Vec::new();
    for (f, effects) in set_effects {
        let prev = state[&f].clone();
        let mut all = prev.clone();
        for effect in effects {
            all = all.concat(effect);
        }
        state.insert(f, all.distinct());
        written.push((f, prev));
    }
    for (view, (n_keys, candidates)) in sie_candidates {
        let prev = state[&view].clone();
        // Pre-existing keys are primed as zero-priority sentinels: they win
        // the latch race, so only genuinely-new keys produce inserts.
        let mut race = prev.clone().map(move |r: Row| {
            let mut key = Row::default();
            for i in 0..n_keys {
                key[i] = r[i];
            }
            (key, (0u8, Row::default()))
        });
        for candidate in candidates {
            race = race.concat(candidate);
        }
        let inserts = first_per_key(&race)
            .flat_map(|(_key, (priority, full))| (priority == 1).then_some(full));
        state.insert(view, prev.clone().concat(inserts));
        written.push((view, prev));
    }
    written
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

/// Accumulate the net weight of `updated \ prev` into every sink (the streams
/// are insert-only, so a positive net means new rows landed).
fn observe_additions<'s, T>(updated: &Coll<'s, T>, prev: &Coll<'s, T>, sinks: &[ChangeSink])
where
    T: Timestamp + Lattice + Ord,
{
    let sinks: Vec<ChangeSink> = sinks.iter().map(Rc::clone).collect();
    updated
        .clone()
        .concat(prev.clone().negate())
        .inspect_batch(move |_t, batch| {
            let net: isize = batch.iter().map(|(_, _, w)| *w).sum();
            for sink in &sinks {
                *sink.borrow_mut() += net;
            }
        });
}

fn written_tables(region: &Region, leaves: &[LeafPlan]) -> HashSet<FunctionId> {
    let mut out = HashSet::new();
    let mut visit = vec![region];
    while let Some(r) = visit.pop() {
        match r {
            Region::Leaf(i) => {
                for rule in &leaves[*i].rules {
                    for (f, _) in &rule.sets {
                        out.insert(*f);
                    }
                    for sie in &rule.sies {
                        out.insert(sie.view);
                    }
                }
            }
            Region::Seq(children) => visit.extend(children.iter()),
            Region::Loop(_, inner) => visit.push(inner),
        }
    }
    out
}

fn leaf_indices(region: &Region) -> Vec<usize> {
    let mut out = Vec::new();
    let mut visit = vec![region];
    while let Some(r) = visit.pop() {
        match r {
            Region::Leaf(i) => out.push(*i),
            Region::Seq(children) => visit.extend(children.iter()),
            Region::Loop(_, inner) => visit.push(inner),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use egglog_backend_trait::{Backend, ColumnTy, DefaultVal, FunctionConfig, MergeFn};

    fn row(vals: &[u32]) -> Box<[u32]> {
        vals.to_vec().into_boxed_slice()
    }

    /// Tables for `A(x) => B(x, fresh!); V[x] set-if-empty (fresh!, ())`.
    fn mint_fixture(eg: &mut EGraph) -> (FunctionId, FunctionId, FunctionId) {
        let unit_ty = Backend::base_values(eg).get_ty::<()>();
        let table = |eg: &mut EGraph, name: &str, schema: Vec<ColumnTy>| {
            Backend::add_table(
                eg,
                FunctionConfig {
                    schema,
                    n_vals: 1,
                    n_identity_vals: None,
                    default: DefaultVal::Fail,
                    merge: MergeFn::Old,
                    name: name.to_string(),
                    can_subsume: false,
                },
            )
        };
        let a = table(eg, "A", vec![ColumnTy::Id, ColumnTy::Base(unit_ty)]);
        let b = table(
            eg,
            "B",
            vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
        );
        let v = table(
            eg,
            "V",
            vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit_ty)],
        );
        eg.insert_live_row(a, row(&[1, 0]));
        eg.insert_live_row(a, row(&[2, 0]));
        (a, b, v)
    }

    fn mint_prep(a: FunctionId, b: FunctionId, v: FunctionId) -> Prep {
        let mut layout = HashMap::new();
        layout.insert(0u32, 0usize);
        layout.insert(1u32, 1usize);
        let rule = CompiledRule {
            first_func: a,
            first_ops: AtomOps::bind_stage(&[Slot::Var(0), Slot::Var(1)], &layout),
            stages: Vec::new(),
            needs_mint: true,
            sets: vec![(b, vec![Src::Col(0), Src::Mint, Src::Const(0)])],
            sies: vec![SieEffect {
                view: v,
                n_keys: 1,
                srcs: vec![Src::Col(0), Src::Mint, Src::Const(0)],
            }],
        };
        Prep {
            region: Region::Loop(None, Box::new(Region::Leaf(0))),
            leaves: vec![LeafPlan {
                ruleset: "t".to_string(),
                rules: vec![rule],
            }],
            involved: vec![a, b, v],
            written: [b, v].into_iter().collect(),
            minting_leaf: Some(0),
        }
    }

    /// One replay-stable id per binding, assigned in binding order from the
    /// reserved counter range; the hash-cons view gets one row per key; the
    /// host counter advances past the minted range.
    #[test]
    fn minting_and_hash_cons_compile() {
        let mut eg = EGraph::new();
        let (a, b, v) = mint_fixture(&mut eg);
        let first = eg.peek_fresh_id();

        let leaves = run_compiled(&mut eg, mint_prep(a, b, v)).expect("compiled run succeeds");
        assert!(leaves[0].iteration.changed());

        let expected_b: crate::HashSet<Box<[u32]>> =
            [row(&[1, first, 0]), row(&[2, first + 1, 0])]
                .into_iter()
                .collect();
        assert_eq!(eg.mirror[&b], expected_b);
        assert_eq!(eg.mirror[&v], expected_b);
        assert_eq!(eg.peek_fresh_id(), first + 2);
    }

    /// A pre-existing view key wins the set-if-empty race: no second row for
    /// that key, while fresh keys still land.
    #[test]
    fn hash_cons_respects_existing_keys() {
        let mut eg = EGraph::new();
        let (a, b, v) = mint_fixture(&mut eg);
        eg.insert_live_row(v, row(&[1, 99, 0]));
        let first = eg.peek_fresh_id();

        run_compiled(&mut eg, mint_prep(a, b, v)).expect("compiled run succeeds");

        let expected_v: crate::HashSet<Box<[u32]>> =
            [row(&[1, 99, 0]), row(&[2, first + 1, 0])]
                .into_iter()
                .collect();
        assert_eq!(eg.mirror[&v], expected_v);
        // B still gets one row per firing, minted ids unaffected by the race.
        assert_eq!(eg.mirror[&b].len(), 2);
        assert_eq!(eg.peek_fresh_id(), first + 2);
    }
}
