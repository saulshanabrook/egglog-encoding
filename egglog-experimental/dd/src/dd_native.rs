//! In-process, build-once, epoch-driven incremental body join on RAW
//! `differential-dataflow` + `timely`.
//!
//! This is the only join path for the Differential Dataflow backend (driven by
//! [`crate::interpret::run_iteration`]); there is no host nested-loop fallback.
//! Unsupported shapes are reported to the caller; see [`plan_join`].
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
//! Each ruleset owns one dataflow in a single-threaded timely [`Worker`] that is
//! stepped across host calls. Every body relation view has one shared
//! [`InputSession`], while each atom-bearing rule lowers to a left-deep join
//! subgraph. Table constraints run in the dataflow; body primitives run later
//! in the host interpreter. Binding deltas flow through `.inspect_batch` into
//! per-rule capture buffers.
//!
//! The host feeds only per-relation signed deltas (`+1` insert, `-1` retract)
//! into the input sessions, advances the timely timestamp for each nonempty
//! delta batch, drives the worker to that epoch's frontier, and drains the
//! output binding deltas. One egglog iteration may submit a removal batch and
//! then an insertion batch to preserve reinsertion freshness. The
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

use anyhow::{anyhow, bail, Result};
use differential_dataflow::input::InputSession;
use egglog_ast::core::{GenericAtom, GenericAtomTerm, GenericCoreAction};
use egglog_backend_trait::{RuleActionCall, RuleBodyCall, RuleSpec, RuleValue, RuleVar};
use hashbrown::HashMap;
use timely::communication::allocator::thread::Thread;
use timely::communication::allocator::Allocator;
use timely::dataflow::operators::probe::Handle as ProbeHandle;
use timely::dataflow::operators::{Inspect, Probe};
use timely::worker::Worker;
use timely::WorkerConfig;

use crate::compile::{ReadKey, Slot};

/// A signed `(row, weight)` delta for one relation (`+1` inserted, `-1`
/// retracted), with rows as plain `Vec<u32>`.
type SignedDelta = Vec<(Vec<u32>, isize)>;
/// Per-relation-view input deltas fed into one [`FusedDdJoin::step`].
type DeltaMap = HashMap<ReadKey, SignedDelta>;
/// One `step`'s captured output deltas, parallel to the fused join's rule list.
type StepOutput = Vec<SignedDelta>;
/// A per-rule output-capture buffer shared with the DD closure (fixed-width
/// [`RowN`] rows).
type CaptureBuf<const WIDTH: usize> = Rc<RefCell<Vec<(RowN<WIDTH>, isize)>>>;

/// Maximum binding-row width the planner accepts. Set to 48 to cover the
/// widest live-variable frontier in the backend corpus: `luminal-llama`'s
/// `@rebuild_rule34` uses 35 distinct body vars in a wide congruence-closure
/// rebuild. A larger live frontier is reported as a row-width-cap wall.
///
/// The dataflow itself does NOT run at this width: [`FusedDdJoin::build`]
/// selects the smallest width in [`WIDTH_LADDER`] that fits the ruleset's
/// plans, so arrangements store (and compare) only as many columns as the
/// widest rule in that ruleset actually needs.
pub const W: usize = 48;

/// Row widths the fused dataflow is monomorphized over. Every ruleset runs at
/// the smallest ladder width `>=` its widest plan ([`JoinPlan::width`]).
pub const WIDTH_LADDER: [usize; 4] = [8, 16, 32, 48];

/// A fixed-width relation or binding row flowing through the DD dataflow. Input
/// rows store relation columns in the low slots. Intermediate binding columns
/// are assigned by the current `ProjectionPlan` stage, and captured outputs
/// repack surviving variables into the low slots in [`JoinPlan::var_order`].
///
/// A NEWTYPE over `[u32; WIDTH]` (rather than the bare array) because timely's
/// `ExchangeData` bound required by DD joins is
/// `Serialize + Deserialize`, and `serde` only derives those for arrays up to
/// length 32. The hand-written serde impl (serialize as a fixed-length seq of
/// `WIDTH` `u32`s) lifts that cap so `WIDTH` can exceed 32 (the corpus needs
/// 35). All other derives (`Ord`/`Hash`/`Clone`/`Copy`) are auto for any array
/// size.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct RowN<const WIDTH: usize>([u32; WIDTH]);

impl<const WIDTH: usize> std::ops::Index<usize> for RowN<WIDTH> {
    type Output = u32;
    #[inline]
    fn index(&self, i: usize) -> &u32 {
        &self.0[i]
    }
}

impl<const WIDTH: usize> std::ops::IndexMut<usize> for RowN<WIDTH> {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut u32 {
        &mut self.0[i]
    }
}

impl<const WIDTH: usize> serde::Serialize for RowN<WIDTH> {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        // Fixed-length tuple of WIDTH u32s — bincode-friendly, no length prefix
        // needed (the deserializer knows WIDTH). Sidesteps serde's 32-array cap.
        let mut t = s.serialize_tuple(WIDTH)?;
        for v in &self.0 {
            t.serialize_element(v)?;
        }
        t.end()
    }
}

impl<'de, const WIDTH: usize> serde::Deserialize<'de> for RowN<WIDTH> {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<RowN<WIDTH>, D::Error> {
        struct RowVisitor<const WIDTH: usize>;
        impl<'de, const WIDTH: usize> serde::de::Visitor<'de> for RowVisitor<WIDTH> {
            type Value = RowN<WIDTH>;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "a tuple of {WIDTH} u32s")
            }
            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> Result<RowN<WIDTH>, A::Error> {
                let mut a = [0u32; WIDTH];
                for (i, slot) in a.iter_mut().enumerate() {
                    *slot = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
                }
                Ok(RowN(a))
            }
        }
        d.deserialize_tuple(WIDTH, RowVisitor)
    }
}

impl<const WIDTH: usize> Default for RowN<WIDTH> {
    fn default() -> Self {
        RowN([0; WIDTH])
    }
}

/// A planned DD join: table atoms plus a bounded live-variable layout.
pub struct JoinPlan {
    /// Body table atoms in emission order.
    atoms: Vec<PlanAtom>,
    /// Per-step column allocation for variables live at each join stage.
    projection: ProjectionPlan,
    /// Minimum row width this plan needs: the widest atom arity or live
    /// binding-column frontier. [`FusedDdJoin::build`] picks the smallest
    /// [`WIDTH_LADDER`] entry covering every plan in the ruleset.
    width: usize,
}

struct PlanAtom {
    read_key: ReadKey,
    slots: Vec<Slot>,
}

impl JoinPlan {
    /// The variable id at each captured binding-row column, in column order.
    #[cfg(test)]
    pub fn var_order(&self) -> Vec<u32> {
        self.projection.head_vars.clone()
    }
}

/// Build the join plan for `rule`, or `Err(reason)` if the DD dataflow cannot
/// support its shape.
/// Supported rules have one or more table atoms, atom arity at most [`W`], and
/// no more than [`W`] simultaneously live body variables. Body primitives are
/// evaluated later by the host interpreter, so they do not become DD operators.
pub fn plan_join(rule: &RuleSpec) -> Result<JoinPlan, String> {
    use hashbrown::HashSet;

    let mut body_vars = HashSet::new();
    let mut atoms: Vec<PlanAtom> = Vec::new();

    for atom in &rule.core.body.atoms {
        match atom.head {
            RuleBodyCall::Table { id, read } => {
                if atom.args.len() > W {
                    return Err(format!("atom arity {} > W {}", atom.args.len(), W));
                }
                let slots = atom
                    .args
                    .iter()
                    .map(Slot::from_term)
                    .collect::<Result<Vec<_>, _>>()?;
                for s in &slots {
                    if let Slot::Var(v) = s {
                        body_vars.insert(*v);
                    }
                }
                atoms.push(PlanAtom {
                    read_key: ReadKey {
                        func: id,
                        mode: read,
                    },
                    slots,
                });
            }
            // The host replays body primitives over each completed table
            // binding. Their variables remain live through the projection.
            RuleBodyCall::Primitive { .. } => {}
        }
    }

    if atoms.is_empty() {
        return Err("no body table atoms (atom-less rule)".to_string());
    }
    // Diagnostic: dump the emitted (naive, body-order) join sequence, flagging
    // any stage that joins with no shared variable (a cartesian product).
    if std::env::var("EGGLOG_DD_DUMP_PLANS").is_ok() {
        let mut bound: hashbrown::HashSet<u32> = hashbrown::HashSet::new();
        let mut desc: Vec<String> = Vec::new();
        for (i, atom) in atoms.iter().enumerate() {
            let vars = atom_vars(&atom.slots);
            let shared = vars.iter().filter(|v| bound.contains(*v)).count();
            let tag = if i > 0 && shared == 0 {
                " CARTESIAN"
            } else {
                ""
            };
            desc.push(format!(
                "{:?}/{}(arity {}, shared {}{tag})",
                atom.read_key.func,
                match atom.read_key.mode {
                    egglog_backend_trait::ReadMode::Live => "live",
                    egglog_backend_trait::ReadMode::Subsumed => "sub",
                    egglog_backend_trait::ReadMode::All => "all",
                },
                atom.slots.len(),
                shared,
            ));
            bound.extend(vars);
        }
        eprintln!("[dd-plan] rule {:?}: {}", rule.name, desc.join(" ⋈ "));
    }
    let projection = build_projection(&atoms, &rule.core.head.0, &rule.core.body.atoms)
        .ok_or_else(|| {
            format!(
                "live body-variable frontier exceeds W {W} ({} distinct body variables)",
                body_vars.len()
            )
        })?;
    let width = plan_width(&atoms, &projection);
    Ok(JoinPlan {
        atoms,
        projection,
        width,
    })
}

/// The narrowest row width that fits every atom's input columns and every
/// step's binding-column frontier (columns are allocated low-first, so the
/// frontier is `max column + 1`).
fn plan_width(atoms: &[PlanAtom], projection: &ProjectionPlan) -> usize {
    let arity = atoms.iter().map(|a| a.slots.len()).max().unwrap_or(0);
    let cols = projection
        .step_col
        .iter()
        .flat_map(|layout| layout.values().map(|&c| c + 1))
        .chain(projection.head_cols.iter().map(|&c| c + 1))
        .max()
        .unwrap_or(0);
    arity.max(cols).max(1)
}

/// Per-step binding columns produced by linear-scan allocation over body-atom
/// liveness. Reusing dead variables' columns lets some rules with more than
/// [`W`] total variables fit in a fixed-width [`Row`].
#[derive(Clone, Debug)]
struct ProjectionPlan {
    /// `step_col[i]` maps each variable LIVE during step `i` (atom `i`'s join) to
    /// its binding-row column at that step. A var's column is stable from its
    /// birth step to its death step but may differ across non-overlapping vars.
    step_col: Vec<HashMap<u32, usize>>,
    /// The surviving (head/body-prim-relevant) variables and their FINAL columns,
    /// in a deterministic order. Drives the reduced head-scatter `var_order`.
    head_vars: Vec<u32>,
    /// Final column of each surviving var (parallel to `head_vars`).
    head_cols: Vec<usize>,
}

/// Build a column-reusing layout for the body atoms, or `None` if the reused
/// frontier still exceeds `W`. Liveness is first-use..last-use over the EMITTED
/// atom order, EXTENDED so any variable read by the head or a body prim stays
/// live to the end (it must survive into the captured row). Linear-scan slot
/// assignment: a column freed by a dead var is reused by a later var's birth.
fn build_projection(
    atoms: &[PlanAtom],
    head: &[GenericCoreAction<RuleActionCall, RuleVar, RuleValue>],
    body: &[GenericAtom<RuleBodyCall, RuleVar, RuleValue>],
) -> Option<ProjectionPlan> {
    use hashbrown::HashSet;
    let n = atoms.len();

    // Variables the head / body prims read: these must survive to the end.
    let mut survivor: HashSet<u32> = HashSet::new();
    collect_head_vars(head, &mut survivor);
    for atom in body {
        if matches!(atom.head, RuleBodyCall::Primitive { .. }) {
            for term in &atom.args {
                if let GenericAtomTerm::Var(_, variable) = term {
                    survivor.insert(variable.id);
                }
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
        if col_of.len() > W {
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

/// Collect every variable a head action references into `out`.
fn collect_head_vars(
    head: &[GenericCoreAction<RuleActionCall, RuleVar, RuleValue>],
    out: &mut hashbrown::HashSet<u32>,
) {
    let add = |term: &GenericAtomTerm<RuleVar, RuleValue>, out: &mut hashbrown::HashSet<u32>| {
        if let GenericAtomTerm::Var(_, variable) = term {
            out.insert(variable.id);
        }
    };
    for action in head {
        match action {
            GenericCoreAction::Let(_, variable, _, arguments) => {
                for argument in arguments {
                    add(argument, out);
                }
                out.insert(variable.id);
            }
            GenericCoreAction::LetAtomTerm(_, variable, term) => {
                add(term, out);
                out.insert(variable.id);
            }
            GenericCoreAction::Set(_, _, arguments, values) => {
                for argument in arguments {
                    add(argument, out);
                }
                for value in values {
                    add(value, out);
                }
            }
            GenericCoreAction::Change(_, _, _, arguments) => {
                for argument in arguments {
                    add(argument, out);
                }
            }
            GenericCoreAction::Union(_, lhs, rhs) => {
                add(lhs, out);
                add(rhs, out);
            }
            GenericCoreAction::Panic(..) => {}
        }
    }
}

/// A fused, delta-fed body join for a WHOLE ruleset on a single shared timely
/// `Worker`. Built once via [`FusedDdJoin::build`]; driven across epochs via
/// [`FusedDdJoin::step`] with a SINGLE `worker.step_while` per call.
///
/// The variants are the [`WIDTH_LADDER`] monomorphizations of the same
/// dataflow: `build` picks the smallest width that fits the ruleset's plans, so
/// arrangement keys/values only pay for the columns the widest rule needs.
pub enum FusedDdJoin {
    W8(FusedDdJoinW<8>),
    W16(FusedDdJoinW<16>),
    W32(FusedDdJoinW<32>),
    W48(FusedDdJoinW<48>),
}

impl FusedDdJoin {
    /// Build ONE worker + ONE dataflow for the whole ruleset at the smallest
    /// ladder width covering every plan. `plans` pairs each rule's index with
    /// its [`JoinPlan`], in the order they should fire.
    pub fn build(plans: &[(usize, JoinPlan)]) -> Result<FusedDdJoin> {
        let need = plans.iter().map(|(_, p)| p.width).max().unwrap_or(1);
        match WIDTH_LADDER.iter().find(|&&w| w >= need) {
            Some(8) => Ok(FusedDdJoin::W8(FusedDdJoinW::build(plans)?)),
            Some(16) => Ok(FusedDdJoin::W16(FusedDdJoinW::build(plans)?)),
            Some(32) => Ok(FusedDdJoin::W32(FusedDdJoinW::build(plans)?)),
            Some(48) => Ok(FusedDdJoin::W48(FusedDdJoinW::build(plans)?)),
            Some(w) => bail!("DD width ladder entry {w} has no monomorphization"),
            None => bail!("plan width {need} exceeds the row-width cap {W}"),
        }
    }

    /// The rule indices this fused worker serves (build order).
    pub fn rule_indices(&self) -> Vec<usize> {
        self.dispatch(
            |j| j.rule_indices(),
            |j| j.rule_indices(),
            |j| j.rule_indices(),
            |j| j.rule_indices(),
        )
    }

    /// Distinct body relation read views across the ruleset, in first-use order.
    pub fn read_keys(&self) -> &[ReadKey] {
        self.dispatch(
            |j| j.read_keys(),
            |j| j.read_keys(),
            |j| j.read_keys(),
            |j| j.read_keys(),
        )
    }

    /// Captured variable order for the fused rule at build position `pos`.
    pub fn rule_var_order(&self, pos: usize) -> &[u32] {
        self.dispatch(
            |j| j.rule_var_order(pos),
            |j| j.rule_var_order(pos),
            |j| j.rule_var_order(pos),
            |j| j.rule_var_order(pos),
        )
    }

    /// Feed one epoch of signed relation deltas, advance the timestamp, run the
    /// worker to this epoch's fixpoint, and return per-rule binding deltas. See
    /// [`FusedDdJoinW::step`].
    pub fn step(&mut self, deltas: &DeltaMap) -> Result<StepOutput> {
        match self {
            FusedDdJoin::W8(j) => j.step(deltas),
            FusedDdJoin::W16(j) => j.step(deltas),
            FusedDdJoin::W32(j) => j.step(deltas),
            FusedDdJoin::W48(j) => j.step(deltas),
        }
    }

    fn dispatch<'a, T>(
        &'a self,
        f8: impl FnOnce(&'a FusedDdJoinW<8>) -> T,
        f16: impl FnOnce(&'a FusedDdJoinW<16>) -> T,
        f32: impl FnOnce(&'a FusedDdJoinW<32>) -> T,
        f48: impl FnOnce(&'a FusedDdJoinW<48>) -> T,
    ) -> T {
        match self {
            FusedDdJoin::W8(j) => f8(j),
            FusedDdJoin::W16(j) => f16(j),
            FusedDdJoin::W32(j) => f32(j),
            FusedDdJoin::W48(j) => f48(j),
        }
    }
}

/// One [`WIDTH_LADDER`] monomorphization of the fused join dataflow.
pub struct FusedDdJoinW<const WIDTH: usize> {
    worker: Worker,
    /// One shared input session per DISTINCT body relation read view across all
    /// rules.
    inputs: HashMap<ReadKey, InputSession<u32, RowN<WIDTH>, isize>>,
    /// Single probe on all rule outputs (they share the dataflow scope, so one
    /// probe gates the whole epoch's fixpoint).
    probe: ProbeHandle<u32>,
    /// Distinct relation read views across the whole ruleset, in first-use
    /// order. This is the authoritative host feed order for the fused worker.
    reads: Vec<ReadKey>,
    /// The fused rules in caller-supplied build order. The sorted rule-index list
    /// identifies the ruleset cache entry but does not reorder these outputs.
    rules: Vec<FusedRule<WIDTH>>,
    /// Current epoch (monotonic; advanced once per [`step`]).
    epoch: u32,
}

/// One rule's lowering inside a [`FusedDdJoinW`]: its rule index (for routing
/// bindings to its head), its per-epoch output capture buffer, and the variable
/// order used to unpack captured rows.
struct FusedRule<const WIDTH: usize> {
    idx: usize,
    /// This rule's per-epoch output binding-delta capture (`inspect_batch`
    /// appends `(row, weight)`; drained by [`FusedDdJoinW::step`]).
    captured: CaptureBuf<WIDTH>,
    /// Variable ids packed into each captured row, in capture-column order.
    var_order: Vec<u32>,
}

impl<const WIDTH: usize> FusedDdJoinW<WIDTH> {
    /// Build ONE worker + ONE dataflow for the whole ruleset. Every rule —
    /// congruence, user, and canonicalization — runs through the same general
    /// fused join.
    fn build(plans: &[(usize, JoinPlan)]) -> Result<FusedDdJoinW<WIDTH>> {
        if plans.is_empty() {
            bail!("cannot build a fused DD join without any rule plans");
        }
        debug_assert!(
            plans.iter().all(|(_, p)| p.width <= WIDTH),
            "DD width invariant: every plan must fit the selected row width"
        );
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
            var_order: Vec<u32>,
            projection: ProjectionPlan,
        }
        let rule_plans: Vec<RulePlan> = plans
            .iter()
            .map(|(idx, plan)| {
                let atom_reads: Vec<ReadKey> = plan.atoms.iter().map(|a| a.read_key).collect();
                RulePlan {
                    idx: *idx,
                    atoms: plan.atoms.iter().map(|a| a.slots.clone()).collect(),
                    atom_reads,
                    var_order: plan.projection.head_vars.clone(),
                    projection: plan.projection.clone(),
                }
            })
            .collect();

        let probe: ProbeHandle<u32> = ProbeHandle::new();
        let probe_in = probe.clone();
        // Per-rule capture buffers, allocated outside the closure so we can keep a
        // clone here and route each rule's output to its head after `step`.
        let captures: Vec<CaptureBuf<WIDTH>> = rule_plans
            .iter()
            .map(|_| Rc::new(RefCell::new(Vec::new())))
            .collect();
        let captures_in = captures.clone();
        let reads_in = reads.clone();
        // The per-rule metadata `FusedRule` needs (kept here; the closure consumes
        // `rule_plans` for the dataflow build).
        let rule_meta: Vec<(usize, Vec<u32>)> = rule_plans
            .iter()
            .map(|rp| (rp.idx, rp.var_order.clone()))
            .collect();

        // The per-epoch input delta is already set-semantic: it comes from the
        // versioned current-vs-fed map diff in `interpret::fused_bindings`, so
        // each row appears at most once with weight ±1. The input integral
        // therefore stays 0/1 per row without `.distinct()`. Adding that operator
        // would perform redundant consolidation over the large relation integrals.
        let inputs = worker.dataflow::<u32, _, _>(move |scope| {
            // ONE shared input + base collection per distinct relation, shared by
            // every atom occurrence (in every rule) that reads it.
            let mut inputs: HashMap<ReadKey, InputSession<u32, RowN<WIDTH>, isize>> =
                HashMap::new();
            let mut rel_coll: HashMap<ReadKey, _> = HashMap::new();
            for &read in &reads_in {
                let mut session: InputSession<u32, RowN<WIDTH>, isize> = InputSession::new();
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
                let proj = &rp.projection;
                let step_col = &proj.step_col;
                let ops0 = AtomOps::bind_stage(&atom_slots[0], &step_col[0]);
                let mut cur = rel_coll[&rp.atom_reads[0]]
                    .clone()
                    .flat_map(move |r: RowN<WIDTH>| ops0.apply(&RowN::default(), &r));

                for i in 1..n_atoms {
                    let slots = &atom_slots[i];
                    let prev = &step_col[i - 1];
                    let next = &step_col[i];
                    let shared: Vec<u32> = atom_vars(slots)
                        .into_iter()
                        .filter(|v| prev.contains_key(v))
                        .collect();
                    let shared_cols_left: Vec<usize> = shared.iter().map(|v| prev[v]).collect();
                    let shared_atom_cols: Vec<usize> = shared
                        .iter()
                        .map(|v| {
                            slots
                                .iter()
                                .position(|s| matches!(s, Slot::Var(x) if x == v))
                                .expect(
                                    "DD join invariant: a shared variable must occur in the joined atom",
                                )
                        })
                        .collect();

                    let left_cols = shared_cols_left.clone();
                    let left =
                        cur.map(move |b: RowN<WIDTH>| (pack_key128(&b, &left_cols), b));
                    let arrangement_key = (rp.atom_reads[i], shared_atom_cols.clone());
                    let right = arranged_right
                        .entry(arrangement_key)
                        .or_insert_with(|| {
                            let right_cols = shared_atom_cols.clone();
                            rel_coll[&rp.atom_reads[i]]
                                .clone()
                                .map(move |r: RowN<WIDTH>| (pack_key128(&r, &right_cols), r))
                                .arrange_by_key()
                        })
                        .clone();

                    // The compiled `checks` re-verify EVERY shared variable's
                    // equality, so a fold collision in a wide (>4-column) packed
                    // key is filtered here rather than producing a false match.
                    let ops = AtomOps::join_stage(slots, prev, next);
                    cur = left.join_core(right, move |_key, binding, row| {
                        ops.apply(binding, row)
                    });
                }

                // Pack the variables needed by body primitives and head actions
                // into the capture columns expected by `var_order()`.
                let head_cols = proj.head_cols.clone();
                let cur = cur.map(move |binding: RowN<WIDTH>| pack_cols(&binding, &head_cols));

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

            if std::env::var("EGGLOG_DD_DUMP_PLANS").is_ok() {
                let stages: usize = rule_plans.iter().map(|rp| rp.atoms.len() - 1).sum();
                eprintln!(
                    "[dd-arrange] width={WIDTH} rules={} join_stages={} left_arrangements={} shared_right_arrangements={} input_relations={}",
                    rule_plans.len(),
                    stages,
                    stages,
                    arranged_right.len(),
                    reads_in.len(),
                );
            }
            inputs
        });

        let rules: Vec<FusedRule<WIDTH>> = rule_meta
            .into_iter()
            .zip(captures)
            .map(|((idx, var_order), captured)| FusedRule {
                idx,
                captured,
                var_order,
            })
            .collect();

        Ok(FusedDdJoinW {
            worker,
            inputs,
            probe,
            reads,
            rules,
            epoch: 0,
        })
    }

    /// The rule indices this fused worker serves (build order).
    fn rule_indices(&self) -> Vec<usize> {
        self.rules.iter().map(|r| r.idx).collect()
    }

    /// Distinct body relation read views across the ruleset, in first-use order.
    fn read_keys(&self) -> &[ReadKey] {
        &self.reads
    }

    /// Captured variable order for the fused rule at build position `pos`.
    fn rule_var_order(&self, pos: usize) -> &[u32] {
        &self.rules[pos].var_order
    }

    /// Feed one epoch of signed relation deltas into the SHARED inputs, advance
    /// the timestamp, run the SINGLE worker to this epoch's fixpoint, and return
    /// per-rule binding deltas. The outer `Vec` is in [`Self::rule_indices`]
    /// order; each inner `Vec` is `(binding_row_as_var_order_vec, weight)`.
    ///
    /// CRUCIAL: the InputSessions are NEVER cleared — only the delta is pushed, so
    /// the DD arrangements persist and the join is genuinely incremental.
    fn step(&mut self, deltas: &DeltaMap) -> Result<StepOutput> {
        let mut pushed = false;
        for (read, rows) in deltas {
            let inp = self.inputs.get_mut(read).ok_or_else(|| {
                anyhow!("DD invariant: received deltas for unplanned read view {read:?}")
            })?;
            for (row, w) in rows {
                inp.update(pack_row(row)?, *w);
                pushed = true;
            }
        }
        let next_epoch = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| anyhow!("DD worker epoch overflow"))?;
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
        for (rule, acc) in self.rules.iter().zip(accs.iter_mut()) {
            for (row, weight) in rule.captured.borrow_mut().drain(..) {
                let key = (0..rule.var_order.len()).map(|i| row[i]).collect();
                *acc.entry(key).or_insert(0) += weight;
            }
        }
        Ok(accs
            .into_iter()
            .map(|acc| acc.into_iter().filter(|(_, w)| *w != 0).collect())
            .collect())
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
}

/// Pack a slice of column values into a fixed-width row (0-padded).
fn pack_row<const WIDTH: usize>(vals: &[u32]) -> Result<RowN<WIDTH>> {
    if vals.len() > WIDTH {
        bail!(
            "DD input row has {} columns, exceeding fixed row width {WIDTH}",
            vals.len()
        );
    }
    let mut a = RowN::default();
    for (i, v) in vals.iter().enumerate() {
        a[i] = *v;
    }
    Ok(a)
}

/// Repack selected columns into the low slots of a fresh row (0-padded).
fn pack_cols<const WIDTH: usize>(r: &RowN<WIDTH>, cols: &[usize]) -> RowN<WIDTH> {
    let mut a = RowN::default();
    for (i, &c) in cols.iter().enumerate() {
        a[i] = r[c];
    }
    a
}

/// Pack the selected columns into a single `u128` join key. Up to four columns
/// are packed exactly (one per 32-bit lane); wider key sets pack three exact
/// columns plus a fold of the rest into the top lane. A fold collision only
/// routes extra pairs into `join_core`'s output closure, where the compiled
/// [`AtomOps::checks`] on every shared variable filter them out.
fn pack_key128<const WIDTH: usize>(r: &RowN<WIDTH>, cols: &[usize]) -> u128 {
    let mut k = 0u128;
    if cols.len() <= 4 {
        for (i, &c) in cols.iter().enumerate() {
            k |= (r[c] as u128) << (32 * i);
        }
    } else {
        for (i, &c) in cols.iter().take(3).enumerate() {
            k |= (r[c] as u128) << (32 * i);
        }
        let mut h = 0x9E37_79B9u32;
        for &c in &cols[3..] {
            h = h.rotate_left(5) ^ r[c].wrapping_mul(0x85EB_CA6B);
        }
        k |= (h as u128) << 96;
    }
    k
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

/// A bind/remap slot program compiled once at dataflow-build time, so the
/// per-tuple closures do pure array reads/writes — no hashing, lookups, or
/// allocation per row.
///
/// Stage 0 ("bind") matches the first atom's relation row against its slots
/// and lays out its variables under the first-step layout. Later stages
/// ("join") merge an atom's row into the carried binding while changing column
/// layouts; reusing freed columns is what keeps the frontier within the row
/// width. `apply` returns `None` when any constraint fails.
#[derive(Clone, Default)]
struct AtomOps {
    /// `row[i]` must equal the constant.
    consts: Vec<(usize, u32)>,
    /// `row[i]` must equal `row[j]` (repeated variable; `j` is its first slot).
    dups: Vec<(usize, usize)>,
    /// Copy `binding[prev_col]` into `out[cur_col]` (still-live carried vars;
    /// empty at stage 0).
    carries: Vec<(usize, usize)>,
    /// `row[i]` must equal the carried `out[col]` (shared variable — covers
    /// every shared var, including any not in the packed join key).
    checks: Vec<(usize, usize)>,
    /// Write `row[i]` into `out[col]` (variable born at this atom).
    writes: Vec<(usize, usize)>,
}

impl AtomOps {
    /// Compile the first atom: every variable is born here.
    fn bind_stage(slots: &[Slot], layout: &HashMap<u32, usize>) -> AtomOps {
        Self::compile(slots, None, layout)
    }

    /// Compile a join stage: `prev` is the left-row layout (step `i-1`), `cur`
    /// the output layout (step `i`).
    fn join_stage(slots: &[Slot], prev: &HashMap<u32, usize>, cur: &HashMap<u32, usize>) -> AtomOps {
        Self::compile(slots, Some(prev), cur)
    }

    fn compile(slots: &[Slot], prev: Option<&HashMap<u32, usize>>, cur: &HashMap<u32, usize>) -> AtomOps {
        let mut ops = AtomOps::default();
        if let Some(prev) = prev {
            // Carry over every still-live var (present in `cur`) that the left
            // row already holds. Atom-fresh vars are absent from `prev`, so they
            // are written from the atom row below instead.
            for (&v, &pc) in prev {
                if let Some(&cc) = cur.get(&v) {
                    ops.carries.push((pc, cc));
                }
            }
        }
        let mut seen: Vec<(u32, usize)> = Vec::new();
        for (i, s) in slots.iter().enumerate() {
            match s {
                Slot::Const(c) => ops.consts.push((i, *c)),
                Slot::Var(v) => {
                    if let Some(&(_, j)) = seen.iter().find(|(sv, _)| sv == v) {
                        ops.dups.push((i, j));
                        continue;
                    }
                    seen.push((*v, i));
                    // Every atom var is live at this step ⇒ present in `cur`.
                    let cc = cur[v];
                    if prev.is_some_and(|p| p.contains_key(v)) {
                        ops.checks.push((i, cc));
                    } else {
                        ops.writes.push((i, cc));
                    }
                }
            }
        }
        // Deterministic carry order (prev iterates a HashMap).
        ops.carries.sort_unstable();
        ops
    }

    /// Run the compiled program over one (binding, atom-row) pair. Stage 0
    /// passes a zero binding (it has no carries or checks).
    #[inline]
    fn apply<const WIDTH: usize>(
        &self,
        b: &RowN<WIDTH>,
        r: &RowN<WIDTH>,
    ) -> Option<RowN<WIDTH>> {
        for &(i, c) in &self.consts {
            if r[i] != c {
                return None;
            }
        }
        for &(i, j) in &self.dups {
            if r[i] != r[j] {
                return None;
            }
        }
        let mut out = RowN::default();
        for &(pc, cc) in &self.carries {
            out[cc] = b[pc];
        }
        for &(i, cc) in &self.checks {
            if out[cc] != r[i] {
                return None;
            }
        }
        for &(i, cc) in &self.writes {
            out[cc] = r[i];
        }
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use egglog_ast::{
        core::{GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreRule, Query},
        span::Span,
    };
    use egglog_backend_trait::{
        ColumnTy, FunctionId, ReadMode, RuleActionCall, RuleBodyCall, RuleSpec, RuleVar,
    };
    use egglog_numeric_id::NumericId;

    fn live(func: FunctionId) -> ReadKey {
        ReadKey {
            func,
            mode: ReadMode::Live,
        }
    }

    fn variable(id: u32) -> GenericAtomTerm<RuleVar, RuleValue> {
        GenericAtomTerm::Var(
            Span::Panic,
            RuleVar {
                id,
                name: format!("v{id}").into_boxed_str(),
                ty: ColumnTy::Id,
            },
        )
    }

    fn body_atom(
        func: FunctionId,
        vars: impl IntoIterator<Item = u32>,
    ) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
        GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::Table {
                id: func,
                read: ReadMode::Live,
            },
            args: vars.into_iter().map(variable).collect(),
        }
    }

    fn test_rule(
        name: &str,
        body: Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>>,
        output: FunctionId,
        vars: impl IntoIterator<Item = u32>,
    ) -> RuleSpec {
        let mut terms = vars.into_iter().map(variable).collect::<Vec<_>>();
        let value = terms.pop().expect("test output includes a value");
        RuleSpec {
            name: name.to_owned(),
            seminaive: true,
            no_decomp: false,
            core: GenericCoreRule {
                span: Span::Panic,
                body: Query { atoms: body },
                head: egglog_ast::core::GenericCoreActions::new(vec![GenericCoreAction::Set(
                    Span::Panic,
                    RuleActionCall::Table {
                        id: output,
                        name: "output".into(),
                    },
                    terms,
                    vec![value],
                )]),
            },
        }
    }

    /// Build a `JoinPlan` from `(func, vars)` atoms, preserving every variable
    /// in the captured output through a synthetic head action.
    fn plan_of(atoms: &[(FunctionId, &[u32])]) -> JoinPlan {
        let body = atoms
            .iter()
            .map(|(func, vars)| body_atom(*func, vars.iter().copied()))
            .collect();
        let mut vars: Vec<u32> = atoms
            .iter()
            .flat_map(|(_, vars)| vars.iter().copied())
            .collect();
        vars.sort_unstable();
        vars.dedup();
        plan_join(&test_rule(
            "test join",
            body,
            FunctionId::new(u32::MAX),
            vars,
        ))
        .unwrap()
    }

    #[test]
    fn pack_row_checks_the_fixed_width_boundary() {
        let values = (0..W as u32).collect::<Vec<_>>();
        let packed = pack_row::<W>(&values).expect("a width-W row must fit");
        assert_eq!(&packed.0[..], values.as_slice());

        let error = pack_row::<W>(&[0; W + 1]).unwrap_err();
        assert!(error.to_string().contains(&format!("{} columns", W + 1)));
        assert!(error.to_string().contains(&format!("fixed row width {W}")));
    }

    #[test]
    fn plans_pick_the_narrowest_ladder_width() {
        let f = FunctionId::new(0);
        // Two ternary atoms sharing one var: frontier of 5 vars → width 8.
        let plan = plan_of(&[(f, &[0, 1, 2]), (f, &[2, 3, 4])]);
        assert!(plan.width <= 8);
        let fused = FusedDdJoin::build(&[(0, plan)]).unwrap();
        assert!(matches!(fused, FusedDdJoin::W8(_)));
    }

    #[test]
    fn wide_key_fold_still_joins_exactly() {
        let f = FunctionId::new(0);
        let g = FunctionId::new(1);
        // Six shared columns: the u128 key packs 3 exact + a fold of the rest,
        // and the compiled checks must reject near-miss rows.
        let atoms: &[(FunctionId, &[u32])] =
            &[(f, &[0, 1, 2, 3, 4, 5, 6]), (g, &[1, 2, 3, 4, 5, 6, 7])];
        let mut rows = HashMap::new();
        rows.insert(f, vec![(vec![10, 1, 2, 3, 4, 5, 6], 1)]);
        rows.insert(
            g,
            vec![
                (vec![1, 2, 3, 4, 5, 6, 20], 1),
                // Differs only in the FOLDED tail — must not match.
                (vec![1, 2, 3, 4, 5, 7, 21], 1),
            ],
        );
        assert_eq!(
            run_once(atoms, &rows),
            vec![(vec![10, 1, 2, 3, 4, 5, 6, 20], 1)]
        );
    }

    #[test]
    fn plan_reuses_columns_across_wide_variable_chain() {
        let func = FunctionId::new(0);
        let final_var = W as u32 + 1;
        let body = (0..=W as u32)
            .map(|var| body_atom(func, [var, var + 1]))
            .collect();
        let plan = plan_join(&test_rule("wide chain", body, func, [final_var])).unwrap();

        assert_eq!(plan.var_order(), vec![final_var]);
        assert!(plan
            .projection
            .step_col
            .iter()
            .all(|layout| layout.len() <= W));
    }

    #[test]
    fn plan_rejects_live_variable_frontier_wider_than_row() {
        let func = FunctionId::new(0);
        let rule = test_rule(
            "wide frontier",
            vec![body_atom(func, 0..W as u32), body_atom(func, [0, W as u32])],
            func,
            0..=W as u32,
        );

        let error = plan_join(&rule)
            .err()
            .expect("wide live frontier must fail");
        assert!(error.contains("live body-variable frontier exceeds W"));
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
