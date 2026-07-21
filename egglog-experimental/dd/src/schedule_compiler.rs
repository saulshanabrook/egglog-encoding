//! Compile a backend [`ScheduleSpec`] tree into ONE DD dataflow and run it in
//! a single epoch — loops become in-dataflow fixpoints instead of host-driven
//! iterations (docs/rebuild-in-dataflow.md).
//!
//! Schedule nodes map to dataflow constructs: `Sequence` chains table states
//! through leaves; `Saturate` opens a nested scope whose feedback `Variable`s
//! carry each written table to fixpoint; `Repeat(n)` is the same scope with
//! feedback gated to rounds `< n` (at most n bounded hops, early convergence
//! free); a `Run` leaf joins rule bodies against the incoming state and merges
//! each rule's `Set` effects into the outgoing state.
//!
//! This v1 compiles the DATALOG SUBSET and falls back to the interpreter for
//! everything else (`prepare` returns `None`): rule bodies must be pure
//! `Live` table atoms, heads only `Set` actions whose value columns are
//! constants agreed across all writers of a table (relations fit: the value
//! is the unit constant), and loops must not nest (one scope level). Mints,
//! merges, primitives, deletes/subsumes, and nested loops arrive next — the
//! monotone-fire toolkit for them is in [`crate::monotone`].
//!
//! Faithfulness: a leaf computes every rule's matches against the SAME
//! pre-leaf state before any effect lands (egglog's match-then-apply model);
//! loop rounds see round-boundary snapshots exactly like host iterations; a
//! table's final state leaves a loop as `seed ∪ gated feedback`, so
//! `Repeat(0)` is a no-op and `Repeat(n)` applies exactly n passes. Insert
//! effects are idempotent set-union (`distinct`), matching `:merge`-irrelevant
//! relation writes. Compiled leaves report `changed` per leaf at the top
//! level and per enclosing loop inside one (an OR-preserving attribution;
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
use crate::EGraph;

/// Compiled-region rows run at the planner cap width; per-region ladder
/// selection (as the fused join does) is a later optimization.
type Row = RowN<W>;
type Coll<'s, T> = VecCollection<'s, T, Row>;
/// Accumulated net weight of a region's new-row stream (`> 0` = changed).
type ChangeSink = Rc<RefCell<isize>>;
/// Final-state minus seed deltas for one table, drained into the host.
type DrainSink = Rc<RefCell<Vec<(Row, isize)>>>;

/// A column of an effect row: copied from a binding column or a constant.
#[derive(Clone)]
enum Src {
    Col(usize),
    Const(u32),
}

/// One join stage of a compiled rule (atoms 1..): the joined table, the
/// binding/atom key columns, and the compiled remap program.
struct StagePlan {
    func: FunctionId,
    left_cols: Vec<usize>,
    right_cols: Vec<usize>,
    ops: AtomOps,
}

struct CompiledRule {
    first_func: FunctionId,
    first_ops: AtomOps,
    stages: Vec<StagePlan>,
    /// Per `Set` action: target table and per-column sources (arity wide).
    effects: Vec<(FunctionId, Vec<Src>)>,
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
    let mut written: HashSet<FunctionId> = HashSet::new();
    let mut reads: HashSet<FunctionId> = HashSet::new();
    for leaf in &leaves {
        for rule in &leaf.rules {
            for f in std::iter::once(rule.first_func).chain(rule.stages.iter().map(|s| s.func)) {
                if reads.insert(f) && !involved.contains(&f) {
                    involved.push(f);
                }
            }
            for (f, _) in &rule.effects {
                if written.insert(*f) && !involved.contains(f) {
                    involved.push(*f);
                }
            }
        }
    }

    // Table gates: bounded arity, no subsumed side-set, stored rows exactly
    // arity wide, and every writer agrees with the seeds on the (constant)
    // value columns so set-union insertion never needs a merge.
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
    for &f in &written {
        let arity = eg.info(f).arity;
        let n_keys = eg.n_keys(f);
        let mut value_consts: Option<Vec<u32>> = None;
        for leaf in &leaves {
            for rule in &leaf.rules {
                for (target, srcs) in &rule.effects {
                    if *target != f {
                        continue;
                    }
                    let vals: Option<Vec<u32>> = srcs[n_keys..arity]
                        .iter()
                        .map(|s| match s {
                            Src::Const(v) => Some(*v),
                            Src::Col(_) => None,
                        })
                        .collect();
                    let Some(vals) = vals else {
                        return fallback("a Set writes non-constant value columns");
                    };
                    match &value_consts {
                        None => value_consts = Some(vals),
                        Some(seen) if *seen == vals => {}
                        Some(_) => return fallback("writers disagree on a table's value constants"),
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

    Some(Prep {
        region,
        leaves,
        involved,
        written,
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

        // Head: only `Set` actions onto tables, columns from bound vars or
        // constants.
        let mut effects = Vec::new();
        for action in &rule.core.head.0 {
            let GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, args, values) = action
            else {
                return fallback(&format!(
                    "a head action other than a table Set is not compiled yet: {action:?}"
                ));
            };
            let mut srcs = Vec::with_capacity(args.len() + values.len());
            for term in args.iter().chain(values.iter()) {
                match term {
                    GenericAtomTerm::Var(_, v) => match last_layout.get(&v.id) {
                        Some(col) => srcs.push(Src::Col(*col)),
                        None => return fallback("a Set reads a variable outside the final layout"),
                    },
                    GenericAtomTerm::Literal(_, c) => srcs.push(Src::Const(c.value.rep())),
                    GenericAtomTerm::Global(..) => {
                        return fallback("a Set reads a residual global")
                    }
                }
            }
            if srcs.len() != eg.info(*id).arity {
                return fallback("a Set's column count differs from the table arity");
            }
            effects.push((*id, srcs));
        }

        compiled.push(CompiledRule {
            first_func: plan.atoms[0].read_key.func,
            first_ops,
            stages,
            effects,
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
    let reports = |sinks: &[ChangeSink]| -> Vec<ScheduleLeafReport> {
        prep.leaves
            .iter()
            .zip(sinks)
            .map(|(leaf, sink)| {
                let mut iteration = IterationReport::default();
                iteration.rule_set_report.changed = *sink.borrow() > 0;
                ScheduleLeafReport {
                    ruleset: leaf.ruleset.clone(),
                    iteration,
                }
            })
            .collect()
    };
    if prep.involved.is_empty() {
        return Ok(reports(&leaf_sinks));
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
        worker.dataflow::<u32, _, _>(move |scope| {
            let mut sessions = HashMap::new();
            let mut state: HashMap<FunctionId, Coll<'_, u32>> = HashMap::new();
            for &f in &prep_ref.involved {
                let (session, coll) = scope.new_collection::<Row, isize>();
                sessions.insert(f, session);
                state.insert(f, coll);
            }
            let seeds = state.clone();

            walk_outer(&prep_ref.region, &prep_ref.leaves, &leaf_sinks, scope, &mut state);

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
                    "compiled schedule produced a retraction for `{}`; the datalog subset must be insert-only",
                    eg.relation_name(f)
                ));
            }
            let full: Vec<u32> = (0..arity).map(|i| row[i]).collect();
            eg.insert_live_row(f, full.into_boxed_slice());
        }
    }

    Ok(reports(&leaf_sinks))
}

/// Walk at the epoch scope: leaves/sequences apply directly; each loop opens
/// ONE nested iterative scope.
fn walk_outer<'s>(
    region: &Region,
    leaves: &[LeafPlan],
    sinks: &[ChangeSink],
    scope: Scope<'s, u32>,
    state: &mut HashMap<FunctionId, Coll<'s, u32>>,
) {
    match region {
        Region::Leaf(i) => {
            let written = apply_leaf(&leaves[*i], state);
            for (f, prev) in written {
                observe_additions(&state[&f], &prev, std::slice::from_ref(&sinks[*i]));
            }
        }
        Region::Seq(children) => {
            for child in children {
                walk_outer(child, leaves, sinks, scope, state);
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

                walk_flat(inner, leaves, &mut inner_state);

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
    state: &mut HashMap<FunctionId, Coll<'s, T>>,
) where
    T: Timestamp + Lattice + Ord,
{
    match region {
        Region::Leaf(i) => {
            apply_leaf(&leaves[*i], state);
        }
        Region::Seq(children) => {
            for child in children {
                walk_flat(child, leaves, state);
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
    state: &mut HashMap<FunctionId, Coll<'s, T>>,
) -> Vec<(FunctionId, Coll<'s, T>)>
where
    T: Timestamp + Lattice + Ord,
{
    let mut effects_by_table: HashMap<FunctionId, Vec<Coll<'s, T>>> = HashMap::new();
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
        for (f, srcs) in &rule.effects {
            let srcs = srcs.clone();
            let effect = cur.clone().map(move |b: Row| {
                let mut row = Row::default();
                for (i, src) in srcs.iter().enumerate() {
                    row[i] = match src {
                        Src::Col(c) => b[*c],
                        Src::Const(v) => *v,
                    };
                }
                row
            });
            effects_by_table.entry(*f).or_default().push(effect);
        }
    }

    let mut written = Vec::new();
    for (f, effects) in effects_by_table {
        let prev = state[&f].clone();
        let mut all = prev.clone();
        for effect in effects {
            all = all.concat(effect);
        }
        state.insert(f, all.distinct());
        written.push((f, prev));
    }
    written
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
                    for (f, _) in &rule.effects {
                        out.insert(*f);
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
