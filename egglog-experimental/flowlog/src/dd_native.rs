//! In-process, build-once, epoch-driven incremental body join on RAW
//! `differential-dataflow` + `timely`.
//!
//! This is the ONLY join path for the FlowLog backend (driven by
//! [`crate::interpret::run_iteration`]); there is no host nested-loop fallback.
//! It panics (via the caller) on shapes it does not support — see `plan_join`.
//!
//! ## The join: one fused worker per ruleset
//!
//! [`FusedDdJoin`] is the path the interpreter drives: ONE shared timely
//! `Worker` hosts ONE dataflow for a whole RULESET, every distinct body relation
//! is a single SHARED input `Collection`, and each rule is a join sub-stream
//! reading those shared collections. It feeds only signed DELTAS into
//! never-cleared InputSessions, so the arrangements persist across epochs =
//! incremental.
//!
//! ## The base architecture
//!
//! For each atom-bearing rule we build ONE differential-dataflow dataflow, ONCE,
//! inside a single-threaded timely `Worker` we OWN (so we can `step` it across
//! host calls). Each body atom occurrence is sourced from a
//! `differential_dataflow::input::InputSession`; the rule's body join is a
//! left-deep chain of DD `.join`s, with `!=` guards and value-prims inlined in
//! `.flat_map`/`.filter`; the head binding rows flow out through `.inspect_batch`
//! into a shared `CaptureBuf` capture buffer.
//!
//! Each egglog iteration (= one epoch) the host feeds ONLY the per-relation
//! signed DELTA into the InputSessions (`+1` insert, `-1` retract), advances the
//! timely timestamp, `step_while`s the worker to that epoch's fixpoint, and
//! drains the capture buffer to get the OUTPUT binding deltas. The
//! InputSessions are NEVER cleared — the DD arrangements persist across epochs,
//! which is what makes the join genuinely incremental (epoch K does only
//! delta·integral work, not a full recompute) — the whole point of the design.
//!
//! ## Fixpoint structure
//!
//! We use EXTERNAL epoch-drive (the host loop advances epochs and feeds head
//! outputs back as the next epoch's inputs), NOT an in-dataflow `iterate()`
//! scope. This matches egglog's bounded `(run N)` fire->rebuild->repeat model and
//! sidesteps DD `iterate()`'s monotonicity constraints under retraction (a
//! rebuild RETRACTS non-canonical rows, which `iterate()` cannot express
//! cleanly). The dataflow itself is NON-recursive: one epoch = one bounded hop.

use std::cell::RefCell;
use std::rc::Rc;

use anyhow::Result;
use differential_dataflow::input::InputSession;
use hashbrown::HashMap;
use timely::communication::allocator::thread::Thread;
use timely::communication::allocator::Allocator;
use timely::dataflow::operators::probe::Handle as ProbeHandle;
use timely::dataflow::operators::{Inspect, Probe};
use timely::worker::Worker;
use timely::WorkerConfig;

use crate::compile::{BodyOp, ReadKey, RuleIr, Slot};

/// A signed `(row, weight)` delta for one relation (`+1` inserted, `-1`
/// retracted), with rows as plain `Vec<u32>`.
type SignedDelta = Vec<(Vec<u32>, isize)>;
/// Per-relation-view input deltas fed into one [`FusedDdJoin::step`].
type DeltaMap = HashMap<ReadKey, SignedDelta>;
/// One `step`'s captured output deltas, parallel to the fused join's rule list.
type StepOutput = Vec<SignedDelta>;
/// A per-rule output-capture buffer shared with the DD closure (fixed-width
/// [`Row`] rows).
type CaptureBuf = Rc<RefCell<Vec<(Row, isize)>>>;

/// Fixed binding-row width (DD `Data` needs a `Sized + Ord + Hash` type; an
/// array gives us that). Set to 48 to cover the widest rebuild rule the flowlog
/// test corpus generates: `luminal-llama`'s `@rebuild_rule34` uses 35 distinct
/// body vars (a wide-arity congruence-closure rebuild). 48 covers every
/// reachable program with headroom; a rule exceeding this is reported as a
/// row-width-cap wall (raise `W` to extend coverage — it is purely a fixed
/// array size, costing `W * 4` bytes per binding row).
pub const W: usize = 48;

/// A fixed-width binding / relation row flowing through the DD dataflow:
/// `row[i]` is the value of canonical body variable `i` (0 if not yet bound).
///
/// A NEWTYPE over `[u32; W]` (rather than the bare array) because timely's
/// `ExchangeData` bound — required by DD `.join`/`.distinct` — is
/// `Serialize + Deserialize`, and `serde` only derives those for arrays up to
/// length 32. The hand-written serde impl (serialize as a fixed-length seq of
/// `W` `u32`s) lifts that cap so `W` can exceed 32 (the corpus needs 35). All
/// other derives (`Ord`/`Hash`/`Clone`/`Copy`) are auto for any array size.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Row([u32; W]);

/// The join key carried between DD `.join` stages: the shared bound columns
/// packed into a fixed-width array (others 0). Same newtype as [`Row`].
type Key = Row;

impl std::ops::Index<usize> for Row {
    type Output = u32;
    #[inline]
    fn index(&self, i: usize) -> &u32 {
        &self.0[i]
    }
}

impl std::ops::IndexMut<usize> for Row {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut u32 {
        &mut self.0[i]
    }
}

impl serde::Serialize for Row {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        // Fixed-length tuple of W u32s — bincode-friendly, no length prefix
        // needed (the deserializer knows W). Sidesteps serde's 32-array cap.
        let mut t = s.serialize_tuple(W)?;
        for v in &self.0 {
            t.serialize_element(v)?;
        }
        t.end()
    }
}

impl<'de> serde::Deserialize<'de> for Row {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Row, D::Error> {
        struct RowVisitor;
        impl<'de> serde::de::Visitor<'de> for RowVisitor {
            type Value = Row;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "a tuple of {W} u32s")
            }
            fn visit_seq<A: serde::de::SeqAccess<'de>>(self, mut seq: A) -> Result<Row, A::Error> {
                let mut a = [0u32; W];
                for (i, slot) in a.iter_mut().enumerate() {
                    *slot = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
                }
                Ok(Row(a))
            }
        }
        d.deserialize_tuple(W, RowVisitor)
    }
}

fn empty_row() -> Row {
    Row([0u32; W])
}

impl Default for Row {
    #[inline]
    fn default() -> Self {
        empty_row()
    }
}

/// A planned DD join: canonical body-variable order + the table atoms.
pub struct JoinPlan {
    /// `var_order[i]` is the variable id at binding-row column `i`.
    var_order: Vec<u32>,
    /// var id -> binding-row column index.
    var_col: HashMap<u32, usize>,
    /// Body table atoms in emission order.
    atoms: Vec<PlanAtom>,
    /// `Some` ⇒ row projection found a column-reusing layout that fits `W`
    /// though the static var count does not; the binary chain uses the per-step
    /// columns instead of `var_col`. `None` ⇒ the static layout (every distinct
    /// var gets a permanent column).
    projection: Option<ProjectionPlan>,
}

struct PlanAtom {
    read_key: ReadKey,
    slots: Vec<Slot>,
}

impl JoinPlan {
    /// The variable id at each CAPTURED binding-row column, in column order. With
    /// projection this is the reduced surviving-var set (the build packs them into
    /// columns `0..head_vars.len()`); without, it is the full static var order.
    /// Either way the head scatter reads captured-row column `i` for var
    /// `var_order()[i]`, so it stays correct.
    pub fn var_order(&self) -> Vec<u32> {
        match &self.projection {
            Some(p) => p.head_vars.clone(),
            None => self.var_order.clone(),
        }
    }
}

/// Build the join plan for `rule`, or `Err(reason)` if the DD dataflow cannot
/// support its shape (the caller PANICS — there is no host fallback). Supported:
/// one or more table atoms, at most [`W`] distinct body vars, atom arity at most
/// [`W`]. Body prims (`!=` guards, value prims like `+`) are re-run host-side
/// over the bindings by the caller (the table-join-on-engine /
/// prim-tail-host-side split), so we accept them by leaving them to the host tail.
pub fn plan_join(rule: &RuleIr) -> Result<JoinPlan, String> {
    let mut var_order: Vec<u32> = Vec::new();
    let mut var_col: HashMap<u32, usize> = HashMap::new();
    let mut atoms: Vec<PlanAtom> = Vec::new();

    let see = |v: u32, var_order: &mut Vec<u32>, var_col: &mut HashMap<u32, usize>| {
        if !var_col.contains_key(&v) {
            var_col.insert(v, var_order.len());
            var_order.push(v);
        }
    };

    for op in &rule.body {
        match op {
            BodyOp::Atom(atom) => {
                if atom.slots.len() > W {
                    return Err(format!("atom arity {} > W {}", atom.slots.len(), W));
                }
                for s in &atom.slots {
                    if let Slot::Var(v) = s {
                        see(*v, &mut var_order, &mut var_col);
                    }
                }
                atoms.push(PlanAtom {
                    read_key: atom.read_key(),
                    slots: atom.slots.clone(),
                });
            }
            // Body prims (e.g. `!=` guards, value prims like `+`) are re-run
            // host-side over the join bindings by the caller (the table-join-on-
            // engine / prim-tail-host-side split). They do not affect join
            // planning; a value prim may bind a fresh var the head reads.
            BodyOp::Prim { .. } => {}
        }
    }

    if atoms.is_empty() {
        return Err("no body table atoms (atom-less rule)".to_string());
    }
    // When the static layout exceeds `W`, attempt a per-step register allocation
    // that reuses binding-row columns for variables whose liveness intervals do
    // not overlap. If the reused-column frontier fits `W`, the binary chain can
    // still run the rule on the fixed-width `Row`.
    if let Some(proj) = build_projection(&atoms, &rule.head, &rule.body) {
        return Ok(JoinPlan {
            var_order,
            var_col,
            atoms,
            projection: Some(proj),
        });
    }

    if var_order.len() > W {
        return Err(format!("too many body vars {} > W {}", var_order.len(), W));
    }

    Ok(JoinPlan {
        var_order,
        var_col,
        atoms,
        projection: None,
    })
}

/// A per-step binding-row column layout produced by [`build_projection`]: column
/// reuse (linear-scan register allocation over body-atom liveness) that keeps the
/// frontier within [`W`] so a rule whose STATIC var count exceeds `W` can still
/// run on the fixed-width `Row`. See the call site in [`plan_join`].
#[derive(Clone, Debug)]
pub(crate) struct ProjectionPlan {
    /// `step_col[i]` maps each variable LIVE during step `i` (atom `i`'s join) to
    /// its binding-row column at that step. A var's column is stable from its
    /// birth step to its death step but may differ across non-overlapping vars.
    pub step_col: Vec<HashMap<u32, usize>>,
    /// The surviving (head/body-prim-relevant) variables and their FINAL columns,
    /// in a deterministic order. Drives the reduced head-scatter `var_order`.
    pub head_vars: Vec<u32>,
    /// Final column of each surviving var (parallel to `head_vars`).
    pub head_cols: Vec<usize>,
}

/// Build a column-reusing layout for the body atoms, or `None` if the reused
/// frontier still exceeds `W`. Liveness is first-use..last-use over the EMITTED
/// atom order, EXTENDED so any variable read by the head or a body prim stays
/// live to the end (it must survive into the captured row). Linear-scan slot
/// assignment: a column freed by a dead var is reused by a later var's birth.
fn build_projection(
    atoms: &[PlanAtom],
    head: &[crate::compile::HeadOp],
    body: &[BodyOp],
) -> Option<ProjectionPlan> {
    use hashbrown::HashSet;
    let n = atoms.len();

    // Variables the head / body prims read: these must survive to the end.
    let mut survivor: HashSet<u32> = HashSet::new();
    collect_head_vars(head, &mut survivor);
    for op in body {
        if let BodyOp::Prim { args, ret, .. } = op {
            for s in args {
                if let Slot::Var(v) = s {
                    survivor.insert(*v);
                }
            }
            if let Slot::Var(v) = ret {
                survivor.insert(*v);
            }
        }
    }

    // first[v]/last[v] = first/last atom index where v appears. Survivors get
    // last = n-1 (live to the final step) so they are never freed mid-chain.
    let mut first: HashMap<u32, usize> = HashMap::new();
    let mut last: HashMap<u32, usize> = HashMap::new();
    for (i, a) in atoms.iter().enumerate() {
        for s in &a.slots {
            if let Slot::Var(v) = s {
                first.entry(*v).or_insert(i);
                last.insert(*v, i);
            }
        }
    }
    for v in &survivor {
        if let Some(l) = last.get_mut(v) {
            *l = n - 1;
        }
    }

    // Vars born / dying at each step (in deterministic var-id order so the layout
    // is reproducible).
    let mut births: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut deaths: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut vars: Vec<u32> = first.keys().copied().collect();
    vars.sort_unstable();
    for v in vars {
        births[first[&v]].push(v);
        deaths[last[&v]].push(v);
    }

    // Linear-scan register allocation. `col_of` is the current column of each
    // live var; `free` is a stack of reusable columns (lowest first, so the
    // layout is deterministic); `next` is the high-water column allocator.
    let mut col_of: HashMap<u32, usize> = HashMap::new();
    let mut free: Vec<usize> = Vec::new();
    let mut next: usize = 0;
    let mut step_col: Vec<HashMap<u32, usize>> = Vec::with_capacity(n);
    let mut peak = 0usize;
    for i in 0..n {
        // Births first (so this atom's fresh vars get columns before we snapshot).
        for &v in &births[i] {
            let c = if let Some(c) = free.pop() {
                c
            } else {
                let c = next;
                next += 1;
                c
            };
            col_of.insert(v, c);
        }
        peak = peak.max(col_of.len());
        if peak > W {
            return None;
        }
        // Snapshot the layout AT this step (after births, before deaths) — every
        // var the atom touches plus all still-live carried vars are present.
        step_col.push(col_of.clone());
        // Deaths free their columns for reuse by later births.
        for &v in &deaths[i] {
            if let Some(c) = col_of.remove(&v) {
                free.push(c);
            }
            // freeing low-first keeps assignment deterministic
            free.sort_unstable_by(|a, b| b.cmp(a));
        }
    }

    // Surviving vars + their FINAL columns (the columns they hold at the last
    // step, where they are guaranteed live). Deterministic order by var id.
    let final_layout = &step_col[n - 1];
    let mut head_vars: Vec<u32> = survivor
        .into_iter()
        .filter(|v| final_layout.contains_key(v))
        .collect();
    head_vars.sort_unstable();
    let head_cols: Vec<usize> = head_vars.iter().map(|v| final_layout[v]).collect();

    Some(ProjectionPlan {
        step_col,
        head_vars,
        head_cols,
    })
}

/// Collect every variable a head op references into `out`.
fn collect_head_vars(head: &[crate::compile::HeadOp], out: &mut hashbrown::HashSet<u32>) {
    use crate::compile::HeadOp;
    let add = |s: &Slot, out: &mut hashbrown::HashSet<u32>| {
        if let Slot::Var(v) = s {
            out.insert(*v);
        }
    };
    for op in head {
        match op {
            HeadOp::Set { slots, .. }
            | HeadOp::Remove { slots, .. }
            | HeadOp::Subsume { slots, .. } => {
                for s in slots {
                    add(s, out);
                }
            }
            HeadOp::Lookup { args, ret, .. } => {
                for s in args {
                    add(s, out);
                }
                out.insert(*ret);
            }
            HeadOp::Call { args, ret, .. } => {
                for s in args {
                    add(s, out);
                }
                out.insert(*ret);
            }
            HeadOp::Union { l, r } => {
                add(l, out);
                add(r, out);
            }
            HeadOp::Panic(_) => {}
        }
    }
}

// ===========================================================================
// FusedDdJoin — ONE shared worker + ONE dataflow per RULESET
// ===========================================================================
//
// A per-RULE design would spin up one timely `Worker` per rule, and a body
// relation read by K rules would get K separate `InputSession`s (each fed the
// same delta) + K separate arrangements stepped to fixpoint separately. Fusing
// the whole ruleset into ONE worker + ONE dataflow with SHARED input
// collections avoids that duplication.
//
// `FusedDdJoin` collapses this to ONE worker hosting ONE `worker.dataflow(...)`
// scope for the whole ruleset (keyed by the sorted live rule-index list). Within
// that scope:
//   - every DISTINCT body relation across all rules gets ONE `InputSession` →
//     ONE base `Collection`, `.distinct()`'d ONCE and SHARED by every atom
//     occurrence (in every rule) that reads it. Cloning a DD collection is a
//     handle copy, so the shared `.distinct()` arrangement is built once, not K
//     times — the dedup win.
//   - each rule is a left-deep join sub-stream reading those shared collections,
//     with its OWN `inspect_batch` capture into a per-rule `Rc<RefCell<Vec>>`.
// Per epoch: feed each relation's delta ONCE into its shared input, advance +
// step the SINGLE worker once, then drain each rule's capture buffer. The
// host-side prim re-run + `apply_head` are unchanged (the caller does them).
//
// The NEVER-CLEAR / fed-only-deltas invariant is preserved (the InputSessions
// persist across epochs = genuinely incremental), as is the external epoch-drive.

/// A fused, delta-fed body join for a WHOLE ruleset on a single shared timely
/// `Worker`. Built once via [`FusedDdJoin::build`]; driven across epochs via
/// [`FusedDdJoin::step`] with a SINGLE `worker.step_while` per call.
pub struct FusedDdJoin {
    worker: Worker,
    /// One shared input session per DISTINCT body relation read view across all
    /// rules.
    inputs: HashMap<ReadKey, InputSession<u32, Row, isize>>,
    /// Single probe on all rule outputs (they share the dataflow scope, so one
    /// probe gates the whole epoch's fixpoint).
    probe: ProbeHandle<u32>,
    /// The fused rules, in build (= sorted rule-index) order. Each carries its
    /// own capture buffer + var width.
    rules: Vec<FusedRule>,
    /// Current epoch (monotonic; advanced once per [`step`]).
    epoch: u32,
}

/// One rule's lowering inside a [`FusedDdJoin`]: its rule index (for routing
/// bindings to its head), its per-epoch output capture buffer, and its width.
struct FusedRule {
    idx: usize,
    /// This rule's per-epoch output binding-delta capture (`inspect_batch`
    /// appends `(row, weight)`; drained by [`FusedDdJoin::step`]).
    captured: CaptureBuf,
    /// Number of canonical body variables (binding-row width in use).
    n_vars: usize,
    /// Distinct relation read views this rule reads. Self-join fan-out is
    /// handled at build time via the shared collection; this is only used by the
    /// host to know which input deltas to feed for the rule.
    body_reads: Vec<ReadKey>,
}

impl FusedDdJoin {
    /// Build ONE worker + ONE dataflow for the whole ruleset. `plans` pairs each
    /// rule's index with its [`JoinPlan`], in the order they should fire. Every
    /// rule — congruence, user, and canonicalization — runs through the same
    /// general fused join.
    pub fn build(plans: &[(usize, JoinPlan)]) -> Result<FusedDdJoin> {
        let alloc = Allocator::Thread(Thread::default());
        let mut worker = Worker::new(
            WorkerConfig::default(),
            alloc,
            Some(std::time::Instant::now()),
        );

        // Distinct body relation read views across all rules → one shared input
        // each.
        let mut reads: Vec<ReadKey> = Vec::new();
        for (_, plan) in plans {
            for a in &plan.atoms {
                if !reads.contains(&a.read_key) {
                    reads.push(a.read_key);
                }
            }
        }

        // Owned per-rule plan snapshots so the `move` dataflow closure is 'static.
        struct RulePlan {
            idx: usize,
            atoms: Vec<Vec<Slot>>,
            atom_reads: Vec<ReadKey>,
            var_col: HashMap<u32, usize>,
            n_vars: usize,
            body_reads: Vec<ReadKey>,
            /// Per-step column-reuse layout; `None` uses the static-column chain.
            projection: Option<ProjectionPlan>,
        }
        let rule_plans: Vec<RulePlan> = plans
            .iter()
            .map(|(idx, plan)| {
                let atom_reads: Vec<ReadKey> = plan.atoms.iter().map(|a| a.read_key).collect();
                let mut body_reads: Vec<ReadKey> = Vec::new();
                for &read in &atom_reads {
                    if !body_reads.contains(&read) {
                        body_reads.push(read);
                    }
                }
                // With projection the CAPTURED row is packed to the surviving
                // vars (columns `0..head_vars.len()`), so the capture/scatter
                // width is `head_vars.len()`, not the full static var count.
                let n_vars = match &plan.projection {
                    Some(p) => p.head_vars.len(),
                    None => plan.var_order.len(),
                };
                RulePlan {
                    idx: *idx,
                    atoms: plan.atoms.iter().map(|a| a.slots.clone()).collect(),
                    atom_reads,
                    var_col: plan.var_col.clone(),
                    n_vars,
                    body_reads,
                    projection: plan.projection.clone(),
                }
            })
            .collect();

        let probe: ProbeHandle<u32> = ProbeHandle::new();
        let probe_in = probe.clone();
        // Per-rule capture buffers, allocated outside the closure so we can keep a
        // clone here and route each rule's output to its head after `step`.
        let captures: Vec<CaptureBuf> = rule_plans
            .iter()
            .map(|_| Rc::new(RefCell::new(Vec::new())))
            .collect();
        let captures_in = captures.clone();
        let reads_in = reads.clone();
        // The per-rule metadata `FusedRule` needs (kept here; the closure consumes
        // `rule_plans` for the dataflow build).
        let rule_meta: Vec<(usize, usize, Vec<ReadKey>)> = rule_plans
            .iter()
            .map(|rp| (rp.idx, rp.n_vars, rp.body_reads.clone()))
            .collect();

        // The per-epoch input delta is already set-semantic — it is built
        // from a `HashSet` set-difference vs the fed view (`interpret::fused_bindings`),
        // so each row appears at most once with weight ±1. The input integral
        // therefore stays 0/1 per row WITHOUT `.distinct()`, making the input
        // distinct (a full integral + per-key consolidation every epoch, over
        // the large relation integrals) pure overhead.
        let inputs = worker.dataflow::<u32, _, _>(move |scope| {
            // ONE shared input + base collection per distinct relation, shared by
            // every atom occurrence (in every rule) that reads it.
            let mut inputs: HashMap<ReadKey, InputSession<u32, Row, isize>> = HashMap::new();
            let mut rel_coll: HashMap<ReadKey, _> = HashMap::new();
            for &read in &reads_in {
                let mut session: InputSession<u32, Row, isize> = InputSession::new();
                let coll = session.to_collection(scope);
                inputs.insert(read, session);
                rel_coll.insert(read, coll);
            }
            // A collection-level join arranges both inputs at every call site.
            // Share base-relation arrangements with the same key projection.
            let mut arranged_right = HashMap::new();

            for (rp, cap) in rule_plans.iter().zip(captures_in.iter()) {
                // This rule's per-atom collection vector, from the SHARED relation
                // collections (cloning a DD collection is just a handle copy).
                let n_atoms = rp.atoms.len();
                let atom_slots = &rp.atoms;
                let var_col = &rp.var_col;
                let n_vars = rp.n_vars;

                let cur = if let Some(proj) = &rp.projection {
                    // Projected binary chain: the binding row
                    // is laid out per-step with column REUSE (`proj.step_col`), so
                    // a rule whose static var count exceeds `W` still fits. The
                    // chain is otherwise identical to the static path below; the
                    // only differences are (a) every var's column is the per-step
                    // column instead of the static `var_col`, (b) each merge REMAPS
                    // carried-over vars whose column changed (reuse) and zeroes
                    // freed columns, and (c) a final `.map` packs the surviving
                    // vars into columns `0..head_vars.len()` for the capture.
                    let step_col = &proj.step_col;
                    let slots0 = atom_slots[0].clone();
                    let sc0 = step_col[0].clone();
                    let mut cur = rel_coll[&rp.atom_reads[0]]
                        .clone()
                        .flat_map(move |r: Row| bind_atom(&r, &slots0, &sc0));

                    for i in 1..n_atoms {
                        let slots = atom_slots[i].clone();
                        let prev = &step_col[i - 1];
                        let curl = &step_col[i];
                        // Shared = atom vars already live (present in `prev`).
                        let shared: Vec<u32> = atom_vars(&slots)
                            .into_iter()
                            .filter(|v| prev.contains_key(v))
                            .collect();
                        // Left key reads each shared var from its PREVIOUS column.
                        let shared_cols_left: Vec<usize> = shared.iter().map(|v| prev[v]).collect();
                        let shared_atom_cols: Vec<usize> = shared
                            .iter()
                            .map(|v| {
                                slots
                                    .iter()
                                    .position(|s| matches!(s, Slot::Var(x) if x == v))
                                    .expect("shared var present in atom")
                            })
                            .collect();

                        let scl = shared_cols_left.clone();
                        let left = cur.map(move |b: Row| (pack_key(&b, &scl), b));
                        let arrangement_key = (rp.atom_reads[i], shared_atom_cols.clone());
                        let right = arranged_right
                            .entry(arrangement_key)
                            .or_insert_with(|| {
                                let sac = shared_atom_cols.clone();
                                rel_coll[&rp.atom_reads[i]]
                                    .clone()
                                    .map(move |r: Row| (pack_key(&r, &sac), r))
                                    .arrange_by_key()
                            })
                            .clone();

                        // Carried vars: live at BOTH prev and cur but NOT produced
                        // by this atom — copy them from prev[v] to cur[v]. Atom
                        // vars: written/validated at cur[v]. (prev_col, cur_col,
                        // is_shared, atom_col) per relevant var, precomputed.
                        let slotsc = slots.clone();
                        let prevc = prev.clone();
                        let curc = curl.clone();
                        cur = left.join_core(right, move |_key, b, r| {
                            remap_merge_atom_into(b, r, &slotsc, &prevc, &curc)
                        });
                    }

                    // Final projection: pack the surviving vars (at their last-step
                    // columns `head_cols`) into the capture columns `0..k`, zeroing
                    // the rest, so the head scatter reads `bind[i]` for surviving
                    // var `i` exactly like the static path.
                    let head_cols = proj.head_cols.clone();
                    cur.map(move |b: Row| pack_key(&b, &head_cols))
                } else {
                    let mut bound = vec![false; n_vars];
                    let slots0 = atom_slots[0].clone();
                    let vc0 = var_col.clone();
                    let mut cur = rel_coll[&rp.atom_reads[0]]
                        .clone()
                        .flat_map(move |r: Row| bind_atom(&r, &slots0, &vc0));
                    mark_bound(&atom_slots[0], var_col, &mut bound);

                    for i in 1..n_atoms {
                        let slots = atom_slots[i].clone();
                        let shared: Vec<u32> = atom_vars(&slots)
                            .into_iter()
                            .filter(|v| var_col.get(v).map(|&c| bound[c]).unwrap_or(false))
                            .collect();
                        let shared_cols_left: Vec<usize> =
                            shared.iter().map(|v| var_col[v]).collect();
                        let shared_atom_cols: Vec<usize> = shared
                            .iter()
                            .map(|v| {
                                slots
                                    .iter()
                                    .position(|s| matches!(s, Slot::Var(x) if x == v))
                                    .expect("shared var present in atom")
                            })
                            .collect();

                        let scl = shared_cols_left.clone();
                        let left = cur.map(move |b: Row| (pack_key(&b, &scl), b));
                        let arrangement_key = (rp.atom_reads[i], shared_atom_cols.clone());
                        let right = arranged_right
                            .entry(arrangement_key)
                            .or_insert_with(|| {
                                let sac = shared_atom_cols.clone();
                                rel_coll[&rp.atom_reads[i]]
                                    .clone()
                                    .map(move |r: Row| (pack_key(&r, &sac), r))
                                    .arrange_by_key()
                            })
                            .clone();

                        let slotsc = slots.clone();
                        let vc = var_col.clone();
                        let bound_now = bound.clone();
                        cur = left.join_core(right, move |_key, b, r| {
                            merge_atom_into(b, r, &slotsc, &vc, &bound_now)
                        });
                        mark_bound(&slots, var_col, &mut bound);
                    }
                    cur
                };

                let cap = Rc::clone(cap);
                // `step` accumulates captured deltas by binding row before
                // interpreting their sign, so consolidating this stream in DD
                // would duplicate the same per-key aggregation.
                cur.inner
                    .inspect_batch(move |_t, batch| {
                        let mut buf = cap.borrow_mut();
                        for (row, _time, w) in batch.iter() {
                            buf.push((*row, *w));
                        }
                    })
                    .probe_with(&probe_in);
            }

            inputs
        });

        let rules: Vec<FusedRule> = rule_meta
            .into_iter()
            .zip(captures)
            .map(|((idx, n_vars, body_reads), captured)| FusedRule {
                idx,
                captured,
                n_vars,
                body_reads,
            })
            .collect();

        Ok(FusedDdJoin {
            worker,
            inputs,
            probe,
            rules,
            epoch: 0,
        })
    }

    /// The rule indices this fused worker serves (build order).
    pub fn rule_indices(&self) -> Vec<usize> {
        self.rules.iter().map(|r| r.idx).collect()
    }

    /// The body relations the fused rule at build position `pos` reads.
    pub fn rule_body_reads(&self, pos: usize) -> &[ReadKey] {
        &self.rules[pos].body_reads
    }

    /// Feed one epoch of signed relation deltas into the SHARED inputs, advance
    /// the timestamp, run the SINGLE worker to this epoch's fixpoint, and return
    /// per-rule binding deltas. The outer `Vec` is in [`rule_indices`] order; each
    /// inner `Vec` is `(binding_row_as_var_order_vec, weight)`.
    ///
    /// CRUCIAL: the InputSessions are NEVER cleared — only the delta is pushed, so
    /// the DD arrangements persist and the join is genuinely incremental.
    pub fn step(&mut self, deltas: &DeltaMap) -> Result<StepOutput> {
        // Every rule — congruence, user, and canonicalization — runs through the
        // SAME symmetric incremental join: feed ALL deltas, one sub-step, capture
        // every rule. No rule kind takes a special path.
        self.step_symmetric(deltas)
    }

    /// Step the SINGLE worker to `epoch`.
    fn drive_to(&mut self, epoch: u32) {
        for inp in self.inputs.values_mut() {
            inp.advance_to(epoch);
            inp.flush();
        }
        let probe = self.probe.clone();
        self.worker.step_while(|| probe.less_than(&epoch));
    }

    /// Drain each rule's capture buffer; keep a rule's output into `accs` only if
    /// `keep(rule)` (route a sub-step's output to the rules it is meant for).
    fn drain_into(&self, accs: &mut [HashMap<Vec<u32>, isize>], keep: impl Fn(&FusedRule) -> bool) {
        for (rule, acc) in self.rules.iter().zip(accs.iter_mut()) {
            let drained: Vec<(Row, isize)> = rule.captured.borrow_mut().drain(..).collect();
            if !keep(rule) {
                continue;
            }
            for (row, w) in drained {
                let key: Vec<u32> = (0..rule.n_vars).map(|i| row[i]).collect();
                *acc.entry(key).or_insert(0) += w;
            }
        }
    }

    /// The symmetric incremental join: feed ALL deltas, one sub-step, capture
    /// every rule.
    fn step_symmetric(&mut self, deltas: &DeltaMap) -> Result<StepOutput> {
        let mut pushed = false;
        for (func, rows) in deltas {
            if let Some(inp) = self.inputs.get_mut(func) {
                for (row, w) in rows {
                    inp.update(pack_row(row), *w);
                    pushed = true;
                }
            }
        }
        let next_epoch = self.epoch + 1;
        if !pushed {
            self.epoch = next_epoch;
            return Ok(vec![Vec::new(); self.rules.len()]);
        }

        for rule in &self.rules {
            rule.captured.borrow_mut().clear();
        }
        self.drive_to(next_epoch);
        self.epoch = next_epoch;

        let mut accs: Vec<HashMap<Vec<u32>, isize>> =
            (0..self.rules.len()).map(|_| HashMap::new()).collect();
        self.drain_into(&mut accs, |_| true);
        Ok(accs
            .into_iter()
            .map(|acc| acc.into_iter().filter(|(_, w)| *w != 0).collect())
            .collect())
    }
}

/// Pack a slice of column values into a fixed-width row (0-padded).
fn pack_row(vals: &[u32]) -> Row {
    let mut a = empty_row();
    for (i, v) in vals.iter().enumerate() {
        a[i] = *v;
    }
    a
}

/// Build a join key from selected columns (packed into the low slots).
fn pack_key(r: &Row, cols: &[usize]) -> Key {
    let mut a = empty_row();
    for (i, &c) in cols.iter().enumerate() {
        a[i] = r[c];
    }
    a
}

/// Distinct variables appearing in an atom (column order).
fn atom_vars(slots: &[Slot]) -> Vec<u32> {
    let mut out = Vec::new();
    for s in slots {
        if let Slot::Var(v) = s {
            if !out.contains(v) {
                out.push(*v);
            }
        }
    }
    out
}

/// Mark the canonical columns of an atom's variables as bound.
fn mark_bound(slots: &[Slot], var_col: &HashMap<u32, usize>, bound: &mut [bool]) {
    for s in slots {
        if let Slot::Var(v) = s {
            if let Some(&c) = var_col.get(v) {
                bound[c] = true;
            }
        }
    }
}

/// Match the first atom's relation row against its slots, producing the initial
/// canonical binding row (or empty vec if a const / repeated-var constraint
/// fails). Returns a `Vec` for `flat_map`.
fn bind_atom(r: &Row, slots: &[Slot], var_col: &HashMap<u32, usize>) -> Vec<Row> {
    let mut out = empty_row();
    let mut local: HashMap<u32, u32> = HashMap::new();
    for (i, s) in slots.iter().enumerate() {
        let val = r[i];
        match s {
            Slot::Const(c) => {
                if *c != val {
                    return Vec::new();
                }
            }
            Slot::Var(v) => {
                if let Some(&prev) = local.get(v) {
                    if prev != val {
                        return Vec::new();
                    }
                } else {
                    local.insert(*v, val);
                    out[var_col[v]] = val;
                }
            }
        }
    }
    vec![out]
}

/// Merge atom row `r` into binding `b`: already-bound columns must agree;
/// previously-unbound atom vars are written. Empty vec on constraint failure.
fn merge_atom_into(
    b: &Row,
    r: &Row,
    slots: &[Slot],
    var_col: &HashMap<u32, usize>,
    bound: &[bool],
) -> Vec<Row> {
    let mut out = *b;
    let mut local: HashMap<u32, u32> = HashMap::new();
    for (i, s) in slots.iter().enumerate() {
        let val = r[i];
        match s {
            Slot::Const(c) => {
                if *c != val {
                    return Vec::new();
                }
            }
            Slot::Var(v) => {
                if let Some(&prev) = local.get(v) {
                    if prev != val {
                        return Vec::new();
                    }
                    continue;
                }
                local.insert(*v, val);
                let c = var_col[v];
                if bound[c] {
                    if out[c] != val {
                        return Vec::new();
                    }
                } else {
                    out[c] = val;
                }
            }
        }
    }
    vec![out]
}

/// Projecting merge for the column-reusing chain. Like [`merge_atom_into`] but
/// rebuilds the row from scratch under a NEW column layout: `prev` is the
/// left-row layout (step `i-1`), `cur` is the output layout (step `i`). Carried
/// vars (live in both layouts but not produced here) are copied `prev[v]→cur[v]`;
/// the atom's vars are validated (shared) or written (fresh) at `cur[v]`; every
/// other output column is left zeroed. This is what reuses freed columns and so
/// keeps the frontier within `W`. Empty vec on a const / repeated-var / shared-
/// var constraint failure (same semantics as the static merge).
fn remap_merge_atom_into(
    b: &Row,
    r: &Row,
    slots: &[Slot],
    prev: &HashMap<u32, usize>,
    cur: &HashMap<u32, usize>,
) -> Vec<Row> {
    let mut out = empty_row();
    // Carry over every still-live var (present in `cur`) that the left row
    // already holds (present in `prev`). Atom-fresh vars are absent from `prev`,
    // so they are NOT copied here — they are written from `r` below.
    for (&v, &pc) in prev {
        if let Some(&cc) = cur.get(&v) {
            out[cc] = b[pc];
        }
    }
    let mut local: HashMap<u32, u32> = HashMap::new();
    for (i, s) in slots.iter().enumerate() {
        let val = r[i];
        match s {
            Slot::Const(c) => {
                if *c != val {
                    return Vec::new();
                }
            }
            Slot::Var(v) => {
                if let Some(&prior) = local.get(v) {
                    if prior != val {
                        return Vec::new();
                    }
                    continue;
                }
                local.insert(*v, val);
                // Every atom var is live at this step ⇒ present in `cur`.
                let cc = cur[v];
                if prev.contains_key(v) {
                    // Shared (already bound): the carried value must agree. (The
                    // join key already enforces this for the key columns; this
                    // also covers shared vars not in the key, if any.)
                    if out[cc] != val {
                        return Vec::new();
                    }
                } else {
                    // Fresh var born at this atom: write it.
                    out[cc] = val;
                }
            }
        }
    }
    vec![out]
}

#[cfg(test)]
mod tests {
    use super::*;
    use egglog_backend_trait::FunctionId;
    use egglog_numeric_id::NumericId;

    fn live(func: FunctionId) -> ReadKey {
        ReadKey {
            func,
            mode: crate::compile::ReadMode::Live,
        }
    }

    /// Build a `JoinPlan` directly from `(func, vars)` atoms.
    fn plan_of(atoms: &[(FunctionId, &[u32])]) -> JoinPlan {
        let mut var_order: Vec<u32> = Vec::new();
        let mut var_col: HashMap<u32, usize> = HashMap::new();
        let mut planned: Vec<PlanAtom> = Vec::new();
        for (func, vars) in atoms {
            for &v in *vars {
                if !var_col.contains_key(&v) {
                    var_col.insert(v, var_order.len());
                    var_order.push(v);
                }
            }
            planned.push(PlanAtom {
                read_key: live(*func),
                slots: vars.iter().map(|&v| Slot::Var(v)).collect(),
            });
        }
        JoinPlan {
            var_order,
            var_col,
            atoms: planned,
            projection: None,
        }
    }

    /// Feed one all-at-once delta of `rows` per func into a fresh
    /// `FusedDdJoin`, returning the rule's sorted output bindings.
    fn run_once(
        atoms: &[(FunctionId, &[u32])],
        rows: &HashMap<FunctionId, SignedDelta>,
    ) -> Vec<(Vec<u32>, isize)> {
        let plan = plan_of(atoms);
        let mut j = FusedDdJoin::build(&[(0usize, plan)]).unwrap();
        let deltas: DeltaMap = rows
            .iter()
            .map(|(&f, rows)| (live(f), rows.clone()))
            .collect();
        let mut out = j.step(&deltas).unwrap().remove(0);
        out.sort();
        out
    }

    #[test]
    fn binary_join_handles_multi_atom_self_join() {
        let f = FunctionId::new(0);
        let g = FunctionId::new(1);
        let atoms: &[(FunctionId, &[u32])] = &[(f, &[0, 1, 2]), (g, &[0, 3]), (g, &[1, 4])];
        let mut rows = HashMap::new();
        rows.insert(
            f,
            vec![
                (vec![1, 2, 100], 1),
                (vec![1, 3, 101], 1),
                (vec![4, 2, 102], 1),
            ],
        );
        rows.insert(
            g,
            vec![
                (vec![1, 10], 1),
                (vec![2, 20], 1),
                (vec![3, 21], 1),
                (vec![4, 40], 1),
            ],
        );

        assert_eq!(
            run_once(atoms, &rows),
            vec![
                (vec![1, 2, 100, 10, 20], 1),
                (vec![1, 3, 101, 10, 21], 1),
                (vec![4, 2, 102, 40, 20], 1),
            ]
        );
    }
}
