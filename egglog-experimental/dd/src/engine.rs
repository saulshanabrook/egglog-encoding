//! The schedule engine: ONE stateful operator that executes an entire
//! egglog schedule inside a single iterative dataflow scope
//! (docs/rebuild-in-dataflow.md).
//!
//! Division of labor: DD computes rule-body JOINS incrementally; the engine
//! does everything the host interpreter did, fed by match deltas instead of
//! scanning tables. Its input is `±(leaf, rule, binding)` deltas from the
//! join pipelines (plus its own tick, looped through the scope's
//! round-incrementing `Variable`); its output is `±(table, location, row)`
//! deltas of every table's authoritative contents, which the dataflow folds
//! into the per-(table, location) state collections the joins read.
//!
//! ## Control flow as a program counter
//!
//! The schedule tree runs as a stack machine inside the engine: ONE leaf
//! execution per timestamp ("turn"). `Seq` frames step children in order;
//! `Repeat`/`Saturate` frames re-enter their body until a full pass changes
//! nothing (or the bound is hit) — the frontend interpreter's exact control
//! flow, at any nesting depth, with no nested dataflow scopes. A tick record
//! emitted while the schedule is unfinished (plus a bootstrap tick at round
//! 0) keeps the loop advancing even when a turn changes nothing; when the
//! schedule completes, no tick is emitted and the scope quiesces.
//!
//! Because effects flow back to the joins through the `Variable(+1)`, the
//! match deltas caused by turn r arrive at turn r+1 — every leaf matches
//! against the state left by the previous leaf execution, exactly the host's
//! match-then-apply sequencing (leaf B in a sequence sees leaf A's writes).
//!
//! ## Firing semantics
//!
//! Per (leaf, rule) the engine keeps the current match set with a fired
//! marker: a turn fires the present-and-unfired bindings (all present ones
//! for `:naive` rules); a binding retracted by canonicalization is dropped,
//! so its re-derivation refires (the host's version-bump semantics), and
//! effects once applied are never un-applied (monotone-fire: deletes are
//! data, not view retraction). Firing runs the host interpreter's
//! per-binding program: body primitives (prune/extend the env), then head
//! actions — `get-fresh!` mints from a reserved counter range, constructor
//! lookups and `set-if-empty` hash-cons read/write engine state immediately
//! (results feed later actions), `set`/`delete`/`subsume` are staged. After
//! all firings: staged removes, then merge-aware sets in WAVES to a fixed
//! point (merge-block side effects join the next wave), then subsumes — the
//! host `run_iteration`/`MergeTransaction` order.
//!
//! ## Primitive safety off-host
//!
//! Primitives evaluate against a CLONED `Database`; that is sound only for
//! results that intern nothing new. The engine enforces it dynamically: a
//! result that is neither an argument echo nor the unit rep records the
//! primitive as unsafe and poisons the run — checked by the caller BEFORE
//! any host mutation, which then falls back to the interpreter and caches
//! the primitive id.

use std::cell::{Cell, RefCell};
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::rc::Rc;
use std::sync::Arc;

use differential_dataflow::lattice::Lattice;
use differential_dataflow::{AsCollection, VecCollection};
use egglog_ast::core::{GenericAtom, GenericAtomTerm, GenericCoreAction};
use egglog_ast::generic_ast::Change;
use egglog_backend_trait::{
    ExternalFunctionId, MergeAction, MergeFn, RuleActionCall, RuleBodyCall, RuleValue, RuleVar,
    Value,
};
use egglog_core_relations::Database;
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};
use timely::dataflow::channels::pact::Pipeline;
use timely::dataflow::operators::generic::operator::Operator;
use timely::dataflow::operators::CapabilitySet;
use timely::progress::Timestamp;

use crate::dd_native::RowN;
use crate::TableDefault;

/// Engine input: `(leaf, rule, binding)` match deltas; `(TICK, TICK, zero)`
/// is the self-scheduling tick.
pub(crate) type MatchDelta<const WIDTH: usize> = (u32, u32, RowN<WIDTH>);
pub(crate) const TICK: u32 = u32::MAX;

/// Rule-slot marker distinguishing a host BOOT delta `(TICK, BOOT, _)` — which
/// starts a new schedule pass — from the engine's own self-ticks
/// `(TICK, TICK, _)`.
pub(crate) const BOOT: u32 = u32::MAX - 1;

/// Engine output: `(table rep, location, row)` deltas. `LOC_TICK` rows are
/// control records routed back to the input, not table data.
pub(crate) type StateDelta<const WIDTH: usize> = (u32, u8, RowN<WIDTH>);
pub(crate) const LOC_LIVE: u8 = 0;
pub(crate) const LOC_SUBSUMED: u8 = 1;
pub(crate) const LOC_TICK: u8 = 2;
/// Seed-row locations: routed into the join views exactly like live/subsumed
/// deltas, but filtered from the host-apply sink (the host already has them).
pub(crate) const LOC_SEED_LIVE: u8 = 3;
pub(crate) const LOC_SEED_SUBSUMED: u8 = 4;

/// Authoritative rows of one table: `key -> (values, location)`.
pub(crate) type TableRows = HashMap<Vec<u32>, (Vec<u32>, u8)>;

/// The schedule, flattened into an arena so the stack machine holds indices
/// rather than borrows.
pub(crate) struct Schedule {
    nodes: Vec<FlatNode>,
    root: usize,
}

enum FlatNode {
    Leaf(usize),
    Seq(Vec<usize>),
    /// `None` bound = saturate.
    Loop(Option<u64>, usize),
}

/// Tree-shaped builder mirroring the backend `ScheduleSpec`.
pub(crate) enum ScheduleNode {
    Leaf(usize),
    Seq(Vec<ScheduleNode>),
    Repeat(u64, Box<ScheduleNode>),
    Saturate(Box<ScheduleNode>),
}

impl Schedule {
    pub(crate) fn build(tree: &ScheduleNode) -> Schedule {
        fn go(tree: &ScheduleNode, nodes: &mut Vec<FlatNode>) -> usize {
            let node = match tree {
                ScheduleNode::Leaf(i) => FlatNode::Leaf(*i),
                ScheduleNode::Seq(children) => {
                    FlatNode::Seq(children.iter().map(|c| go(c, nodes)).collect())
                }
                ScheduleNode::Repeat(bound, body) => FlatNode::Loop(Some(*bound), go(body, nodes)),
                ScheduleNode::Saturate(body) => FlatNode::Loop(None, go(body, nodes)),
            };
            nodes.push(node);
            nodes.len() - 1
        }
        let mut nodes = Vec::new();
        let root = go(tree, &mut nodes);
        Schedule { nodes, root }
    }
}

/// A frame of the running schedule: which node, plus its progress state.
struct Frame {
    node: usize,
    /// Seq: next child index. Loop: completed iterations.
    progress: u64,
    /// Loop: whether the current pass changed anything.
    pass_changed: bool,
    /// Loop: whether the current pass has started (distinguishes "about to
    /// start pass 1" from "pass `progress` just completed").
    in_pass: bool,
}

/// Yields leaf indices in the frontend interpreter's exact order, consuming
/// each executed leaf's `changed` flag to drive loop exits.
struct Scheduler {
    stack: Vec<Frame>,
    done: bool,
}

impl Scheduler {
    fn new(schedule: &Schedule) -> Scheduler {
        let mut s = Scheduler {
            stack: Vec::new(),
            done: false,
        };
        s.stack.push(Frame {
            node: schedule.root,
            progress: 0,
            pass_changed: false,
            in_pass: false,
        });
        s.descend(schedule);
        s
    }

    /// Advance until the top of the stack is the next leaf to execute (or the
    /// schedule is done). Never blocks: empty sequences and zero-bound
    /// repeats unwind immediately.
    fn descend(&mut self, schedule: &Schedule) {
        loop {
            let Some(top) = self.stack.last_mut() else {
                self.done = true;
                return;
            };
            match &schedule.nodes[top.node] {
                FlatNode::Leaf(_) => return,
                FlatNode::Seq(children) => {
                    let next = top.progress as usize;
                    if next < children.len() {
                        top.progress += 1;
                        let child = children[next];
                        self.stack.push(Frame {
                            node: child,
                            progress: 0,
                            pass_changed: false,
                            in_pass: false,
                        });
                    } else {
                        self.stack.pop();
                    }
                }
                FlatNode::Loop(bound, body) => {
                    // Reached on entry (`!in_pass`, progress passes done) or
                    // when a body pass just completed (`in_pass`).
                    if top.in_pass {
                        top.in_pass = false;
                        top.progress += 1;
                        if !top.pass_changed {
                            self.stack.pop();
                            continue;
                        }
                    }
                    let start_another = match bound {
                        Some(n) => top.progress < *n,
                        None => true,
                    };
                    if start_another {
                        top.in_pass = true;
                        top.pass_changed = false;
                        let body = *body;
                        self.stack.push(Frame {
                            node: body,
                            progress: 0,
                            pass_changed: false,
                            in_pass: false,
                        });
                    } else {
                        self.stack.pop();
                    }
                }
            }
        }
    }

    /// The leaf to execute this turn, if any.
    fn current(&self, schedule: &Schedule) -> Option<usize> {
        match self.stack.last() {
            Some(frame) => match schedule.nodes[frame.node] {
                FlatNode::Leaf(i) => Some(i),
                _ => None,
            },
            None => None,
        }
    }

    /// Record the executed leaf's outcome and advance to the next leaf.
    fn report(&mut self, schedule: &Schedule, changed: bool) {
        self.stack.pop();
        if changed {
            for frame in self.stack.iter_mut() {
                if matches!(schedule.nodes[frame.node], FlatNode::Loop(..)) {
                    frame.pass_changed = true;
                }
            }
        }
        self.descend(schedule);
    }
}

// ---------------------------------------------------------------------------
// Engine configuration and channels.
// ---------------------------------------------------------------------------

/// Per-table metadata (the host's `RelationInfo` subset the engine needs).
#[derive(Clone)]
pub(crate) struct EngineTable {
    pub(crate) n_keys: usize,
    pub(crate) arity: usize,
    pub(crate) merge: Arc<MergeFn>,
    pub(crate) n_identity_vals: Option<usize>,
    /// Wave ordering: readable merge targets before their readers.
    pub(crate) level: usize,
    pub(crate) default: TableDefault,
    pub(crate) name: String,
}

/// One rule inside a leaf: the final join layout plus the UNlowered body
/// primitives and head actions, interpreted per firing exactly like the host.
pub(crate) struct EngineRule {
    /// Variable id -> binding-row column (the join plan's final layout).
    pub(crate) layout: HashMap<u32, usize>,
    /// Body primitive atoms, in body order.
    pub(crate) prims: Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>>,
    /// Head actions, in order.
    pub(crate) head: Vec<GenericCoreAction<RuleActionCall, RuleVar, RuleValue>>,
    /// `false` for `:naive` rules: fire every present binding each turn.
    pub(crate) seminaive: bool,
}

pub(crate) struct EngineLeaf {
    pub(crate) rules: Vec<EngineRule>,
}

/// Leaves are shared with the turn loop through `Rc` so firing can call
/// `&mut self` interpretation methods while iterating a leaf's rules.
pub(crate) type SharedLeaf = Rc<EngineLeaf>;

/// A `set-if-empty-<view>!` / view-proof op resolved to its view table.
#[derive(Clone, Copy)]
pub(crate) struct ViewOpSpec {
    pub(crate) view: u32,
    pub(crate) n_keys: usize,
}

/// Host-visible outcome channels, checked after the worker run.
#[derive(Clone, Default)]
pub(crate) struct EngineChannels {
    /// A rule/merge error, with the host's message.
    pub(crate) error: Rc<RefCell<Option<String>>>,
    /// A primitive whose result was neither an argument echo nor unit.
    pub(crate) unsafe_prim: Rc<RefCell<Option<ExternalFunctionId>>>,
    /// `(leaf index, changed)` per executed leaf turn, in execution order.
    pub(crate) turns: Rc<RefCell<Vec<(usize, bool)>>>,
    /// Ids minted from the reserved counter range (this pass only).
    pub(crate) minted: Rc<RefCell<u32>>,
    /// Set when the current pass finishes (schedule done or poisoned); the
    /// host's stepping loop watches it.
    pub(crate) done: Rc<Cell<bool>>,
}

impl EngineChannels {
    fn poisoned(&self) -> bool {
        self.error.borrow().is_some() || self.unsafe_prim.borrow().is_some()
    }
}

/// Everything the engine needs at construction.
pub(crate) struct EngineConfig {
    pub(crate) schedule: Schedule,
    pub(crate) leaves: Vec<SharedLeaf>,
    pub(crate) tables: HashMap<u32, EngineTable>,
    /// Seed rows per engine-owned table: `key -> (values, location)`.
    pub(crate) seeds: HashMap<u32, TableRows>,
    /// One-shot seed rows for read-only tables (full row + location): emitted
    /// into the dataflow on the first pass, never part of engine state.
    pub(crate) extra_seeds: Vec<(u32, u8, Vec<u32>)>,
    pub(crate) set_if_empty: HashMap<ExternalFunctionId, ViewOpSpec>,
    pub(crate) view_proof: HashMap<ExternalFunctionId, ViewOpSpec>,
    /// Primitive ids that are `get-fresh!` (mint from the reserved range).
    pub(crate) fresh_prims: HashSet<ExternalFunctionId>,
    pub(crate) db: Database,
    /// The host's deferred-panic side channel (shared by database clones);
    /// drained after every primitive invocation, like `eval_prim_internal`.
    pub(crate) panic: std::sync::Arc<std::sync::Mutex<Option<String>>>,
    pub(crate) unit_rep: u32,
    pub(crate) first_id: u32,
    pub(crate) channels: EngineChannels,
}

/// Build the engine over the match-delta stream.
pub(crate) fn engine<'s, T, const WIDTH: usize>(
    input: &VecCollection<'s, T, MatchDelta<WIDTH>>,
    cfg: EngineConfig,
) -> VecCollection<'s, T, StateDelta<WIDTH>>
where
    T: Timestamp + Lattice + Ord + std::hash::Hash,
{
    let stream = input
        .inner
        .clone()
        .unary_frontier(Pipeline, "ScheduleEngine", move |_default_cap, _info| {
            // Pending-data-only capabilities: a capability parked at the
            // frontier would keep the loop's rounds advancing forever.
            let mut caps: CapabilitySet<T> = CapabilitySet::new();
            // Pending deltas bucketed per timestamp: heap traffic scales with
            // distinct rounds, not with tuples (which reach tens of millions).
            let mut queue: HashMap<T, Vec<(MatchDelta<WIDTH>, isize)>> = HashMap::new();
            let mut times: BinaryHeap<Reverse<T>> = BinaryHeap::new();
            let mut state = EngineState::<WIDTH>::new(cfg);
            let debug = std::env::var("EGGLOG_DD_ENGINE_DEBUG").is_ok();
            let mut turns = 0u64;
            let mut engine_time = std::time::Duration::ZERO;
            let mut ingested = 0u64;
            let mut raw = 0u64;
            let mut emitted = 0u64;
            let mut last_turn = std::time::Instant::now();
            let mut turn_gaps: Vec<(u64, f64, u64)> = Vec::new();
            // Debug: per-table (new, removed, rewritten) row counts, where a
            // -/+ pair on the same key within one turn is a rewrite.
            let classify = std::env::var("EGGLOG_DD_VOLUMES").is_ok();
            let mut emit_classes: HashMap<u32, (u64, u64, u64)> = HashMap::new();
            move |(input, frontier), output| {
                input.for_each(|cap, data| {
                    caps.insert(cap.retain(0));
                    raw += data.len() as u64;
                    for (d, t, r) in data.drain(..) {
                        queue
                            .entry(t.clone())
                            .or_insert_with(|| {
                                times.push(Reverse(t));
                                Vec::new()
                            })
                            .push((d, r));
                    }
                });
                while times
                    .peek()
                    .is_some_and(|Reverse(t)| !frontier.frontier().less_equal(t))
                {
                    let Reverse(time) = times.pop().expect("peeked above");
                    let mut bucket = queue.remove(&time).expect("bucket exists");
                    let started = std::time::Instant::now();
                    let gap_ms = last_turn.elapsed().as_secs_f64() * 1e3;
                    // Sort raw deltas and fold equal-binding runs: netting by
                    // sequential scan beats a hash map at tens of millions of
                    // 72-byte keys, and groups amortize the per-rule lookup.
                    bucket.sort_unstable_by(|a, b| a.0.cmp(&b.0));
                    let (distinct, boot) = state.ingest(&bucket);
                    ingested += distinct;
                    if debug {
                        turn_gaps.push((turns, gap_ms, distinct));
                    }

                    let mut emits: Vec<(StateDelta<WIDTH>, isize)> = Vec::new();
                    if boot {
                        state.begin_pass(&mut emits);
                    } else {
                        state.turn(&mut emits);
                    }
                    if state.scheduler.done || state.cfg.channels.poisoned() {
                        state.cfg.channels.done.set(true);
                    }
                    turns += 1;
                    emitted += emits.len() as u64;
                    if classify {
                        let mut per_key: HashMap<(u32, Vec<u32>), (u64, u64)> = HashMap::new();
                        for ((f, loc, row), w) in &emits {
                            if *loc == LOC_TICK || *loc >= LOC_SEED_LIVE {
                                continue;
                            }
                            let Some(table) = state.cfg.tables.get(f) else {
                                continue;
                            };
                            let key: Vec<u32> = (0..table.n_keys).map(|i| row[i]).collect();
                            let e = per_key.entry((*f, key)).or_default();
                            if *w > 0 {
                                e.0 += 1;
                            } else {
                                e.1 += 1;
                            }
                        }
                        for ((f, _), (pos, neg)) in per_key {
                            let c = emit_classes.entry(f).or_default();
                            let rewrites = pos.min(neg);
                            c.2 += rewrites;
                            c.0 += pos - rewrites;
                            c.1 += neg - rewrites;
                        }
                    }
                    engine_time += started.elapsed();
                    if debug {
                        last_turn = std::time::Instant::now();
                    }
                    if debug && state.scheduler.done {
                        if let Some(traffic) = &state.debug_traffic {
                            let mut v: Vec<_> = traffic.iter().collect();
                            v.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
                            let total: u64 = v.iter().map(|(_, n)| **n).sum();
                            eprintln!("[engine] match traffic total={total}");
                            for ((leaf, rule), n) in v.iter().take(12) {
                                eprintln!("[engine]   {n:>10}  l{leaf}r{rule}");
                            }
                        }
                        let mut classes: Vec<_> = emit_classes.iter().collect();
                        classes.sort_by_key(|(_, (n, r, w))| std::cmp::Reverse(n + r + w));
                        for (f, (new, removed, rewritten)) in classes.iter().take(8) {
                            eprintln!(
                                "[engine] table f{f}: new={new} removed={removed} rewritten={rewritten}"
                            );
                        }
                        let present: usize =
                            state.matches.values().map(|m| m.present.len()).sum();
                        eprintln!("[engine] distinct present matches at done: {present}");
                        let gaps: String = turn_gaps
                            .iter()
                            .map(|(t, ms, n)| format!("{t}:{ms:.0}ms/{n}"))
                            .collect::<Vec<_>>()
                            .join(" ");
                        eprintln!("[engine] turn gaps (turn:dataflow_ms/deltas): {gaps}");
                        eprintln!(
                            "[engine] turns={turns} raw={raw} ingested={ingested} emitted={emitted} engine_time={:.1}ms",
                            engine_time.as_secs_f64() * 1e3
                        );
                    }

                    let cap = caps.delayed(&time);
                    let mut session = output.session(&cap);
                    for (data, weight) in emits {
                        session.give((data, time.clone(), weight));
                    }
                }
                match times.peek() {
                    Some(Reverse(t)) => {
                        let t = t.clone();
                        caps.downgrade([t]);
                    }
                    None => caps.downgrade(Vec::<T>::new()),
                }
            }
        });
    stream.as_collection()
}

// ---------------------------------------------------------------------------
// Engine state: match bookkeeping, table state, the per-turn interpreter.
// ---------------------------------------------------------------------------

/// Match bookkeeping for one (leaf, rule): `(count, fired)` per present
/// binding, plus a queue of bindings that crossed 0 -> positive since the
/// rule last fired — so a turn touches O(new matches), not O(all matches).
#[derive(Default)]
struct RuleMatches<const WIDTH: usize> {
    present: HashMap<RowN<WIDTH>, (isize, bool)>,
    pending: Vec<RowN<WIDTH>>,
}

type MatchSets<const WIDTH: usize> = HashMap<(u32, u32), RuleMatches<WIDTH>>;

/// Staged writes collected while firing one turn's bindings.
#[derive(Default)]
struct Staged {
    removes: Vec<(u32, Vec<u32>)>,
    sets: Vec<(u32, Vec<u32>)>,
    subsumes: Vec<(u32, Vec<u32>)>,
}

struct EngineState<const WIDTH: usize> {
    /// When engine debugging is on: match-delta traffic per (leaf, rule).
    debug_traffic: Option<HashMap<(u32, u32), u64>>,
    cfg: EngineConfig,
    scheduler: Scheduler,
    matches: MatchSets<WIDTH>,
    /// Authoritative rows: table -> key -> (values, location).
    tables: HashMap<u32, TableRows>,
    counter: u32,
    /// Counter value when the current pass began; `minted` reports the
    /// difference so each invocation's reservation is exact.
    pass_start: u32,
    /// Whether the initial table rows have been emitted into the dataflow
    /// (first BOOT only; afterwards the views incrementally track state).
    seeded: bool,
}

impl<const WIDTH: usize> EngineState<WIDTH> {
    fn new(mut cfg: EngineConfig) -> EngineState<WIDTH> {
        let scheduler = Scheduler::new(&cfg.schedule);
        let tables = std::mem::take(&mut cfg.seeds);
        let counter = cfg.first_id;
        EngineState {
            debug_traffic: std::env::var("EGGLOG_DD_ENGINE_DEBUG")
                .is_ok()
                .then(HashMap::new),
            cfg,
            scheduler,
            matches: MatchSets::default(),
            tables,
            counter,
            pass_start: counter,
            seeded: false,
        }
    }

    /// Start a schedule pass: reset the program counter, emit the seed rows
    /// on the first pass ever, and self-schedule the first turn one round
    /// later (so it observes matches derived from current state).
    fn begin_pass(&mut self, emits: &mut Vec<(StateDelta<WIDTH>, isize)>) {
        if std::env::var("EGGLOG_DD_ENGINE_DEBUG").is_ok() {
            let pending: usize = self.matches.values().map(|m| m.pending.len()).sum();
            let unfired: usize = self
                .matches
                .values()
                .flat_map(|m| m.present.values())
                .filter(|(c, fired)| *c > 0 && !fired)
                .count();
            eprintln!("[engine] begin_pass pending={pending} present-unfired={unfired}");
        }
        self.scheduler = Scheduler::new(&self.cfg.schedule);
        self.pass_start = self.counter;
        *self.cfg.channels.minted.borrow_mut() = 0;
        // Delete/subsume-capable rules start each pass with a clean slate of
        // fired flags: a fired delete whose row was re-added in the SAME
        // round never sees its match retract (the -/+ pair cancels in the
        // dataflow, where the interpreter's physical row timestamps would
        // re-trigger it), so its flag can go stale. Refiring such rules is
        // idempotent on table state. Pure writers keep their flags: their
        // inputs are untouched, and the interpreter's seminaive would not
        // re-search them either.
        for ((leaf, rule), per_rule) in self.matches.iter_mut() {
            let head = &self.cfg.leaves[*leaf as usize].rules[*rule as usize].head;
            let undoes = head.iter().any(|a| {
                matches!(
                    a,
                    GenericCoreAction::Change(_, Change::Delete | Change::Subsume, ..)
                )
            });
            if !undoes {
                continue;
            }
            per_rule.pending.clear();
            for (binding, (count, fired)) in per_rule.present.iter_mut() {
                *fired = false;
                if *count > 0 {
                    per_rule.pending.push(*binding);
                }
            }
        }
        if !self.seeded {
            self.seeded = true;
            let seed_loc = |loc: u8| {
                if loc == LOC_LIVE {
                    LOC_SEED_LIVE
                } else {
                    LOC_SEED_SUBSUMED
                }
            };
            for (&frep, rows) in &self.tables {
                for (key, (vals, loc)) in rows {
                    emits.push(((frep, seed_loc(*loc), pack2(key, vals)), 1));
                }
            }
            for (frep, loc, row) in std::mem::take(&mut self.cfg.extra_seeds) {
                emits.push(((frep, seed_loc(loc), pack2(&row, &[])), 1));
            }
        }
        if !self.scheduler.done && !self.cfg.channels.poisoned() {
            emits.push(((TICK, LOC_TICK, RowN::<WIDTH>::default()), 1));
        }
    }

    /// Apply one round's SORTED raw deltas: equal bindings net by run-fold,
    /// per-(leaf, rule) state is fetched once per group. Returns the distinct
    /// netted-delta count and whether a BOOT marker was present.
    fn ingest(&mut self, sorted: &[(MatchDelta<WIDTH>, isize)]) -> (u64, bool) {
        let mut distinct = 0u64;
        let mut boot = false;
        let mut i = 0;
        while i < sorted.len() {
            let (leaf, rule, _) = sorted[i].0;
            if leaf == TICK {
                boot |= rule == BOOT;
                i += 1;
                continue;
            }
            let per_rule = self.matches.entry((leaf, rule)).or_default();
            let mut group_traffic = 0u64;
            while i < sorted.len() {
                let (l, r, binding) = sorted[i].0;
                if (l, r) != (leaf, rule) {
                    break;
                }
                let mut delta = 0isize;
                while i < sorted.len() && sorted[i].0 == (l, r, binding) {
                    delta += sorted[i].1;
                    i += 1;
                }
                if delta == 0 {
                    continue;
                }
                distinct += 1;
                group_traffic += 1;
                let (count, fired) = per_rule
                    .present
                    .get(&binding)
                    .copied()
                    .unwrap_or((0, false));
                let updated = count + delta;
                if updated <= 0 {
                    // Retracted: forget it entirely so a re-derivation
                    // refires.
                    per_rule.present.remove(&binding);
                } else {
                    // A 0 -> positive transition is fresh (unfired) even if
                    // the binding had fired in an earlier incarnation.
                    let fired = if count <= 0 { false } else { fired };
                    if count <= 0 {
                        per_rule.pending.push(binding);
                    }
                    per_rule.present.insert(binding, (updated, fired));
                }
            }
            if let Some(traffic) = self.debug_traffic.as_mut() {
                *traffic.entry((leaf, rule)).or_default() += group_traffic;
            }
        }
        (distinct, boot)
    }

    /// Execute one leaf turn (if the schedule is unfinished), emitting table
    /// deltas plus the next tick.
    fn turn(&mut self, emits: &mut Vec<(StateDelta<WIDTH>, isize)>) {
        if self.scheduler.done || self.cfg.channels.poisoned() {
            return;
        }
        let leaf_idx = self
            .scheduler
            .current(&self.cfg.schedule)
            .expect("an unfinished schedule is positioned at a leaf");

        let minted_before = self.counter;
        let mut staged = Staged::default();
        let mut changed = false;

        let leaf = Rc::clone(&self.cfg.leaves[leaf_idx]);
        for (rule_idx, rule) in leaf.rules.iter().enumerate() {
            // Fire present-and-unfired bindings (all present ones for
            // :naive), in deterministic order.
            let key = (leaf_idx as u32, rule_idx as u32);
            let mut to_fire: Vec<RowN<WIDTH>> = match self.matches.get_mut(&key) {
                Some(per_rule) if rule.seminaive => {
                    // Only bindings that appeared since the last firing are
                    // candidates; the present+unfired check drops stale queue
                    // entries from retract/re-derive churn.
                    let mut out = Vec::new();
                    for b in per_rule.pending.drain(..) {
                        if let Some(entry) = per_rule.present.get_mut(&b) {
                            if entry.0 > 0 && !entry.1 {
                                entry.1 = true;
                                out.push(b);
                            }
                        }
                    }
                    out
                }
                // :naive rules refire every present binding each turn.
                Some(per_rule) => per_rule.present.keys().copied().collect(),
                None => Vec::new(),
            };
            to_fire.sort_unstable();
            for binding in to_fire {
                // Body primitives can fan one binding out to several envs.
                let envs = self.run_body_prims(rule, &binding);
                for mut env in envs {
                    if self.cfg.channels.poisoned() {
                        return;
                    }
                    self.apply_head(rule, &binding, &mut env, &mut staged, emits, &mut changed);
                }
            }
            if self.cfg.channels.poisoned() {
                return;
            }
        }

        changed |= self.apply_staged(staged, emits);
        changed |= self.counter != minted_before;
        *self.cfg.channels.minted.borrow_mut() = self.counter - self.pass_start;
        if std::env::var("EGGLOG_DD_TURN_TRACE").is_ok() {
            eprintln!(
                "[turn] leaf={leaf_idx} changed={changed} minted={}",
                self.counter
            );
        }
        self.cfg
            .channels
            .turns
            .borrow_mut()
            .push((leaf_idx, changed));

        self.scheduler.report(&self.cfg.schedule, changed);
        if !self.scheduler.done && !self.cfg.channels.poisoned() {
            emits.push(((TICK, LOC_TICK, RowN::<WIDTH>::default()), 1));
        }
    }

    // -- per-binding interpretation (ports of interpret.rs) -----------------

    /// The host `step_prim` over one binding: each primitive prunes or
    /// extends the env; value-computing primitives may bind new variables.
    fn run_body_prims(&mut self, rule: &EngineRule, binding: &RowN<WIDTH>) -> Vec<Env> {
        let mut envs = vec![Env::new()];
        for atom in &rule.prims {
            let RuleBodyCall::Primitive { id, .. } = atom.head else {
                unreachable!("prims list contains only primitive atoms");
            };
            let Some((ret, args)) = atom.args.split_last() else {
                self.fail("body primitive has no return term");
                return Vec::new();
            };
            let mut out = Vec::new();
            for env in envs {
                let resolved: Option<Vec<u32>> = args
                    .iter()
                    .map(|t| term_value(t, rule, binding, &env))
                    .collect();
                let Some(argv) = resolved else { continue };
                let Some(result) = self.eval_prim(id, &argv) else {
                    if self.cfg.channels.poisoned() {
                        return Vec::new();
                    }
                    // Primitive failed (e.g. `!=` of equal args) — prune.
                    continue;
                };
                match ret {
                    GenericAtomTerm::Var(_, variable) => {
                        match resolve_env(&env, rule, binding, variable.id) {
                            Some(existing) if existing != result => continue,
                            Some(_) => out.push(env.clone()),
                            None => {
                                let mut next = env.clone();
                                next.insert(variable.id, result);
                                out.push(next);
                            }
                        }
                    }
                    GenericAtomTerm::Literal(_, constant) => {
                        if constant.value.rep() == result {
                            out.push(env.clone());
                        }
                    }
                    GenericAtomTerm::Global(..) => {
                        self.fail("residual global in a body primitive");
                        return Vec::new();
                    }
                }
            }
            envs = out;
            if envs.is_empty() {
                break;
            }
        }
        envs
    }

    /// The host `apply_head` over one binding+env.
    #[allow(clippy::too_many_arguments)]
    fn apply_head(
        &mut self,
        rule: &EngineRule,
        binding: &RowN<WIDTH>,
        env: &mut Env,
        staged: &mut Staged,
        emits: &mut Vec<(StateDelta<WIDTH>, isize)>,
        changed: &mut bool,
    ) {
        for action in &rule.head {
            match action {
                GenericCoreAction::Let(_, var, call, arguments) => {
                    let Some(args) = resolve_terms(arguments, rule, binding, env) else {
                        self.fail("unbound term in rule head");
                        return;
                    };
                    let result = match call {
                        RuleActionCall::Table { id, .. } => {
                            self.lookup_or_create(id.rep(), &args, emits, changed)
                        }
                        RuleActionCall::Primitive { id, .. } => {
                            if self.cfg.fresh_prims.contains(id) {
                                Some(self.mint())
                            } else if let Some(op) = self.cfg.set_if_empty.get(id).copied() {
                                self.set_if_empty(op, &args, emits, changed)
                            } else if let Some(op) = self.cfg.view_proof.get(id).copied() {
                                Some(self.view_proof(op, &args))
                            } else {
                                self.eval_prim(*id, &args)
                            }
                        }
                    };
                    if self.cfg.channels.poisoned() {
                        return;
                    }
                    if let Some(result) = result {
                        env.insert(var.id, result);
                    }
                }
                GenericCoreAction::LetAtomTerm(_, var, term) => {
                    let Some(value) = term_value(term, rule, binding, env) else {
                        self.fail("unbound term in rule head");
                        return;
                    };
                    env.insert(var.id, value);
                }
                GenericCoreAction::Set(_, call, arguments, values) => {
                    let RuleActionCall::Table { id, .. } = call else {
                        self.fail("cannot set a primitive");
                        return;
                    };
                    let Some(mut row) = resolve_terms(arguments, rule, binding, env) else {
                        self.fail("unbound term in rule head");
                        return;
                    };
                    let Some(vals) = resolve_terms(values, rule, binding, env) else {
                        self.fail("unbound term in rule head");
                        return;
                    };
                    row.extend(vals);
                    staged.sets.push((id.rep(), row));
                }
                GenericCoreAction::Change(_, change, call, arguments) => {
                    let RuleActionCall::Table { id, .. } = call else {
                        self.fail("cannot delete or subsume a primitive");
                        return;
                    };
                    let Some(args) = resolve_terms(arguments, rule, binding, env) else {
                        self.fail("unbound term in rule head");
                        return;
                    };
                    match change {
                        Change::Delete => staged.removes.push((id.rep(), args)),
                        Change::Subsume => staged.subsumes.push((id.rep(), args)),
                    }
                }
                GenericCoreAction::Union(..) => {
                    self.fail("native union reached the engine; term encoding must lower unions");
                    return;
                }
                GenericCoreAction::Panic(_, message) => {
                    self.fail(message.clone());
                    return;
                }
            }
        }
    }

    // -- staged write application (port of run_iteration's tail) ------------

    fn apply_staged(
        &mut self,
        staged: Staged,
        emits: &mut Vec<(StateDelta<WIDTH>, isize)>,
    ) -> bool {
        let mut changed = false;

        // Removes first, batched and deduplicated.
        let mut removes = staged.removes;
        removes.sort_unstable();
        removes.dedup();
        for (func, key) in removes {
            changed |= self.remove_row(func, &key, emits);
        }

        // Merge-aware sets, in waves to a fixed point.
        let mut wave = staged.sets;
        while !wave.is_empty() && !self.cfg.channels.poisoned() {
            let mut current = std::mem::take(&mut wave);
            current.sort_by(|(fa, ra), (fb, rb)| {
                let la = self.cfg.tables[fa].level;
                let lb = self.cfg.tables[fb].level;
                (la, fa, ra).cmp(&(lb, fb, rb))
            });
            for (func, row) in current {
                changed |= self.apply_set(func, &row, emits, &mut wave);
                if self.cfg.channels.poisoned() {
                    return changed;
                }
            }
        }

        // Subsumes last, reading the just-updated rows.
        let mut subsumes = staged.subsumes;
        subsumes.sort_unstable();
        subsumes.dedup();
        for (func, prefix) in subsumes {
            changed |= self.subsume_rows(func, &prefix, emits);
        }
        changed
    }

    fn remove_row(
        &mut self,
        func: u32,
        key: &[u32],
        emits: &mut Vec<(StateDelta<WIDTH>, isize)>,
    ) -> bool {
        let table = &self.cfg.tables[&func];
        if key.len() != table.n_keys {
            self.fail(format!(
                "a delete on `{}` does not address exactly the key columns",
                table.name
            ));
            return false;
        }
        let rows = self.tables.entry(func).or_default();
        if let Some((vals, loc)) = rows.remove(key) {
            emits.push(((func, loc, pack2(key, &vals)), -1));
            true
        } else {
            false
        }
    }

    fn apply_set(
        &mut self,
        func: u32,
        row: &[u32],
        emits: &mut Vec<(StateDelta<WIDTH>, isize)>,
        next_wave: &mut Vec<(u32, Vec<u32>)>,
    ) -> bool {
        let table = self.cfg.tables[&func].clone();
        if row.len() != table.arity {
            self.fail(format!(
                "set on `{}` has {} columns, expected {}",
                table.name,
                row.len(),
                table.arity
            ));
            return false;
        }
        let key: Vec<u32> = (0..table.n_keys).map(|i| row[i]).collect();
        let incoming = row[table.n_keys..].to_vec();
        let rows = self.tables.entry(func).or_default();
        let Some((old, loc)) = rows.get(&key).cloned() else {
            rows.insert(key.clone(), (incoming.clone(), LOC_LIVE));
            emits.push(((func, LOC_LIVE, pack2(&key, &incoming)), 1));
            return true;
        };

        let values_unchanged = old == incoming;
        let identity_unchanged = table
            .n_identity_vals
            .is_some_and(|count| old[..count] == incoming[..count]);
        if values_unchanged || identity_unchanged {
            return false;
        }

        let (actions, result) = match table.merge.as_ref() {
            MergeFn::Block { actions, result } => (actions.as_slice(), result.as_ref()),
            result => (&[][..], result),
        };
        let mut menv: Vec<u32> = Vec::new();
        for action in actions {
            match action {
                MergeAction::Set(target, arguments) => {
                    let Some(vals) =
                        self.eval_merge_args(arguments, &old, &incoming, 0, &menv, &table.name)
                    else {
                        return false;
                    };
                    next_wave.push((target.rep(), vals));
                }
                MergeAction::Let { value, .. } => {
                    let Some(v) = self.eval_merge(value, &old, &incoming, 0, &menv, &table.name)
                    else {
                        return false;
                    };
                    menv.push(v);
                }
                MergeAction::Union(..) => {
                    self.fail("native merge unions are rejected at table registration");
                    return false;
                }
            }
        }
        let merged: Option<Vec<u32>> = match result {
            MergeFn::Columns(results) => results
                .iter()
                .enumerate()
                .map(|(col, expr)| self.eval_merge(expr, &old, &incoming, col, &menv, &table.name))
                .collect(),
            expr => self
                .eval_merge(expr, &old, &incoming, 0, &menv, &table.name)
                .map(|v| vec![v]),
        };
        let Some(merged) = merged else {
            return false;
        };

        if merged != old {
            emits.push(((func, loc, pack2(&key, &old)), -1));
            emits.push(((func, loc, pack2(&key, &merged)), 1));
            self.tables
                .entry(func)
                .or_default()
                .insert(key, (merged, loc));
            true
        } else {
            false
        }
    }

    /// Move live rows whose leading columns match `prefix` to the subsumed
    /// side (still present, hidden from Live reads).
    fn subsume_rows(
        &mut self,
        func: u32,
        prefix: &[u32],
        emits: &mut Vec<(StateDelta<WIDTH>, isize)>,
    ) -> bool {
        let table = &self.cfg.tables[&func];
        let n_keys = table.n_keys;
        let rows = self.tables.entry(func).or_default();
        let mut moved = false;
        if prefix.len() >= n_keys {
            // Key fully determined: one lookup plus a value-prefix check.
            let key = prefix[..n_keys].to_vec();
            if let Some((vals, loc)) = rows.get_mut(&key) {
                let vals_prefix = &prefix[n_keys..];
                if *loc == LOC_LIVE
                    && vals.len() >= vals_prefix.len()
                    && vals[..vals_prefix.len()] == *vals_prefix
                {
                    *loc = LOC_SUBSUMED;
                    let row = pack2(&key, vals);
                    emits.push(((func, LOC_LIVE, row), -1));
                    emits.push(((func, LOC_SUBSUMED, row), 1));
                    moved = true;
                }
            }
        } else {
            // Shorter prefix: scan (rare; mirrors the host's prefix scan).
            let mut to_move = Vec::new();
            for (key, (vals, loc)) in rows.iter() {
                if *loc == LOC_LIVE && key.len() >= prefix.len() && key[..prefix.len()] == *prefix {
                    to_move.push((key.clone(), vals.clone()));
                }
            }
            for (key, vals) in to_move {
                rows.insert(key.clone(), (vals.clone(), LOC_SUBSUMED));
                let row = pack2(&key, &vals);
                emits.push(((func, LOC_LIVE, row), -1));
                emits.push(((func, LOC_SUBSUMED, row), 1));
                moved = true;
            }
        }
        moved
    }

    // -- constructor lookups, hash-cons, minting -----------------------------

    fn mint(&mut self) -> u32 {
        let id = self.counter;
        self.counter += 1;
        id
    }

    /// The host `lookup_or_create`: return the output of `func` for `key`,
    /// creating the row (with the table default) on a miss. Writes land
    /// immediately so later lookups in the same firing see them.
    fn lookup_or_create(
        &mut self,
        func: u32,
        key: &[u32],
        emits: &mut Vec<(StateDelta<WIDTH>, isize)>,
        changed: &mut bool,
    ) -> Option<u32> {
        let table = self.cfg.tables[&func].clone();
        if key.len() != table.n_keys {
            self.fail(format!(
                "lookup on `{}` has {} keys, expected {}",
                table.name,
                key.len(),
                table.n_keys
            ));
            return None;
        }
        if let Some((vals, _)) = self.tables.entry(func).or_default().get(key) {
            return Some(vals[0]);
        }
        if table.arity - table.n_keys != 1 {
            self.fail(format!(
                "lookup on tuple-output function `{}` cannot bind one value",
                table.name
            ));
            return None;
        }
        let value = match table.default {
            TableDefault::FreshId => self.mint(),
            TableDefault::Const(v) => v,
            TableDefault::Fail => {
                self.fail(format!("lookup on `{}` failed in rule action", table.name));
                return None;
            }
        };
        self.tables
            .entry(func)
            .or_default()
            .insert(key.to_vec(), (vec![value], LOC_LIVE));
        emits.push(((func, LOC_LIVE, pack2(key, &[value])), 1));
        *changed = true;
        Some(value)
    }

    /// The term encoder's `set-if-empty`: the e-class of the existing view
    /// row, or insert `(keys, default vals)` and return the default e-class.
    fn set_if_empty(
        &mut self,
        op: ViewOpSpec,
        args: &[u32],
        emits: &mut Vec<(StateDelta<WIDTH>, isize)>,
        changed: &mut bool,
    ) -> Option<u32> {
        let key = &args[..op.n_keys];
        if let Some((vals, _)) = self.tables.entry(op.view).or_default().get(key) {
            return Some(vals[0]);
        }
        let vals = args[op.n_keys..].to_vec();
        let eclass = vals[0];
        self.tables
            .entry(op.view)
            .or_default()
            .insert(key.to_vec(), (vals.clone(), LOC_LIVE));
        emits.push(((op.view, LOC_LIVE, pack2(key, &vals)), 1));
        *changed = true;
        Some(eclass)
    }

    /// The term encoder's view-proof read: output column 1 of the existing
    /// view row, or the fallback argument.
    fn view_proof(&mut self, op: ViewOpSpec, args: &[u32]) -> u32 {
        let key = &args[..op.n_keys];
        let fallback = args[op.n_keys];
        match self.tables.entry(op.view).or_default().get(key) {
            Some((vals, _)) => vals[1],
            None => fallback,
        }
    }

    // -- primitive + merge evaluation ----------------------------------------

    /// Evaluate a primitive off-host, guarded: the result must be an argument
    /// echo or the unit rep, else the primitive is recorded unsafe and the
    /// run poisons. `None` = the primitive itself returned none (prune) OR
    /// the run poisoned (checked by callers via `poisoned()`).
    fn eval_prim(&mut self, id: ExternalFunctionId, args: &[u32]) -> Option<u32> {
        let values: Vec<Value> = args.iter().copied().map(Value::new).collect();
        let result = self
            .cfg
            .db
            .with_execution_state(|st| st.call_external_func(id, &values));
        if let Some(message) = self
            .cfg
            .panic
            .lock()
            .expect("panic side channel must not be poisoned")
            .take()
        {
            self.fail(message);
            return None;
        }
        let result = result?;
        let rep = result.rep();
        if !args.contains(&rep) && rep != self.cfg.unit_rep {
            let mut slot = self.cfg.channels.unsafe_prim.borrow_mut();
            if slot.is_none() {
                *slot = Some(id);
            }
            return None;
        }
        Some(rep)
    }

    fn eval_merge_args(
        &mut self,
        arguments: &[MergeFn],
        old: &[u32],
        new: &[u32],
        self_col: usize,
        menv: &[u32],
        name: &str,
    ) -> Option<Vec<u32>> {
        arguments
            .iter()
            .map(|a| self.eval_merge(a, old, new, self_col, menv, name))
            .collect()
    }

    /// The host `MergeTransaction::eval`, minus table lookups (gated out at
    /// compile time).
    fn eval_merge(
        &mut self,
        expression: &MergeFn,
        old: &[u32],
        new: &[u32],
        self_col: usize,
        menv: &[u32],
        name: &str,
    ) -> Option<u32> {
        match expression {
            MergeFn::AssertEq => {
                if old[self_col] != new[self_col] {
                    self.fail(format!("illegal merge attempted for function `{name}`"));
                    return None;
                }
                Some(old[self_col])
            }
            MergeFn::UnionId => Some(old[self_col].min(new[self_col])),
            MergeFn::Old => Some(old[self_col]),
            MergeFn::New => Some(new[self_col]),
            MergeFn::OldCol(index) => Some(old[*index]),
            MergeFn::NewCol(index) => Some(new[*index]),
            MergeFn::LetVar(slot) => match menv.get(*slot) {
                Some(v) => Some(*v),
                None => {
                    self.fail(format!("merge for `{name}` references an unbound let slot"));
                    None
                }
            },
            MergeFn::Const(value) => Some(value.rep()),
            MergeFn::Primitive(id, arguments) => {
                let args = self.eval_merge_args(arguments, old, new, self_col, menv, name)?;
                let result = self.eval_prim(*id, &args);
                if result.is_none() && !self.cfg.channels.poisoned() {
                    self.fail(format!("merge primitive failed for function `{name}`"));
                }
                result
            }
            MergeFn::Function(..) | MergeFn::Lookup(..) => {
                self.fail(format!(
                    "merge table lookups for `{name}` are gated out of compiled schedules"
                ));
                None
            }
            MergeFn::Columns(_) | MergeFn::Block { .. } => {
                self.fail(format!(
                    "nested merge programs for `{name}` are rejected at registration"
                ));
                None
            }
        }
    }

    fn fail(&self, message: impl Into<String>) {
        let mut slot = self.cfg.channels.error.borrow_mut();
        if slot.is_none() {
            *slot = Some(message.into());
        }
    }
}

// ---------------------------------------------------------------------------
// Per-firing environments.
// ---------------------------------------------------------------------------

/// Variables bound beyond the join layout (primitive returns, head lets).
type Env = HashMap<u32, u32>;

fn resolve_env<const WIDTH: usize>(
    env: &Env,
    rule: &EngineRule,
    binding: &RowN<WIDTH>,
    var: u32,
) -> Option<u32> {
    env.get(&var)
        .copied()
        .or_else(|| rule.layout.get(&var).map(|col| binding[*col]))
}

fn term_value<const WIDTH: usize>(
    term: &GenericAtomTerm<RuleVar, RuleValue>,
    rule: &EngineRule,
    binding: &RowN<WIDTH>,
    env: &Env,
) -> Option<u32> {
    match term {
        GenericAtomTerm::Var(_, v) => resolve_env(env, rule, binding, v.id),
        GenericAtomTerm::Literal(_, c) => Some(c.value.rep()),
        GenericAtomTerm::Global(..) => None,
    }
}

fn resolve_terms<const WIDTH: usize>(
    terms: &[GenericAtomTerm<RuleVar, RuleValue>],
    rule: &EngineRule,
    binding: &RowN<WIDTH>,
    env: &Env,
) -> Option<Vec<u32>> {
    terms
        .iter()
        .map(|t| term_value(t, rule, binding, env))
        .collect()
}

fn pack2<const WIDTH: usize>(key: &[u32], vals: &[u32]) -> RowN<WIDTH> {
    let mut row = RowN::<WIDTH>::default();
    for (i, v) in key.iter().chain(vals.iter()).enumerate() {
        row[i] = *v;
    }
    row
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(i: usize) -> ScheduleNode {
        ScheduleNode::Leaf(i)
    }

    /// Drive a schedule against scripted per-leaf `changed` outcomes and
    /// return the executed leaf order — must match the frontend interpreter.
    fn run(tree: ScheduleNode, mut outcomes: impl FnMut(usize, usize) -> bool) -> Vec<usize> {
        let schedule = Schedule::build(&tree);
        let mut s = Scheduler::new(&schedule);
        let mut order = Vec::new();
        let mut turn = 0;
        while let Some(leaf) = s.current(&schedule) {
            order.push(leaf);
            let changed = outcomes(turn, leaf);
            turn += 1;
            s.report(&schedule, changed);
            assert!(turn < 10_000, "runaway schedule");
        }
        assert!(s.done);
        order
    }

    #[test]
    fn scheduler_matches_interpreter_control_flow() {
        // (seq A B): both leaves once, in order.
        let order = run(ScheduleNode::Seq(vec![leaf(0), leaf(1)]), |_, _| false);
        assert_eq!(order, vec![0, 1]);

        // Repeat(0, A): never executes.
        let order = run(ScheduleNode::Repeat(0, Box::new(leaf(0))), |_, _| true);
        assert_eq!(order, Vec::<usize>::new());

        // Repeat(3, A) always changing: exactly 3 passes.
        let order = run(ScheduleNode::Repeat(3, Box::new(leaf(0))), |_, _| true);
        assert_eq!(order, vec![0, 0, 0]);

        // Repeat(5, A) that stops changing after pass 2: 3 passes total (the
        // frontend runs a pass, sees no change, and breaks).
        let order = run(ScheduleNode::Repeat(5, Box::new(leaf(0))), |turn, _| {
            turn < 2
        });
        assert_eq!(order, vec![0, 0, 0]);

        // Saturate over a two-leaf sequence: exits after the first pass in
        // which NEITHER leaf changed.
        let order = run(
            ScheduleNode::Saturate(Box::new(ScheduleNode::Seq(vec![leaf(0), leaf(1)]))),
            |turn, _| turn < 3,
        );
        // Pass 1 (turns 0,1: changed) -> pass 2 (turn 2 changed, turn 3 not:
        // pass changed) -> pass 3 (turns 4,5 unchanged) -> exit.
        assert_eq!(order, vec![0, 1, 0, 1, 0, 1]);

        // The real spliced shape: Repeat(2, Seq(user, Saturate(Seq(cleanup,
        // Saturate(parent), rebuild)))) with nothing ever changing: one pass
        // of everything, each inner saturate runs its body once.
        let tree = ScheduleNode::Repeat(
            2,
            Box::new(ScheduleNode::Seq(vec![
                leaf(0),
                ScheduleNode::Saturate(Box::new(ScheduleNode::Seq(vec![
                    leaf(1),
                    ScheduleNode::Saturate(Box::new(leaf(2))),
                    leaf(3),
                ]))),
            ])),
        );
        let order = run(tree, |_, _| false);
        assert_eq!(order, vec![0, 1, 2, 3]);
    }
}
