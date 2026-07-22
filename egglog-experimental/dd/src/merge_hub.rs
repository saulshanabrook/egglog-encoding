//! The merge hub: ONE stateful operator hosting every written table's
//! authoritative fold state inside a compiled schedule region, mirroring the
//! host `MergeTransaction`'s semantics at each timestamp
//! (docs/rebuild-in-dataflow.md).
//!
//! Input is a latched (append-only) stream of tagged write ops; output is the
//! exact `±(table, row)` delta stream of every table's current contents. At
//! each frontier-complete timestamp the hub applies, in the host's order:
//!
//! 1. `OP_SIE` — the term encoder's `set-if-empty` hash-cons (applied during
//!    head evaluation on the host, hence first): insert if the key is absent,
//!    otherwise nothing.
//! 2. `OP_DELETE` — batched removals (the host applies removes before sets).
//! 3. `OP_SET` — merge-aware sets, processed in WAVES to a fixed point:
//!    sorted by (merge-dependency level, table, row); a same-key collision
//!    runs the table's `MergeFn` program, and merge-block `set` actions
//!    (e.g. the union-find loser edge) join the next wave. Waves happen
//!    within ONE timestamp, so `(run n)` round budgets are untouched —
//!    exactly the host's waves-within-iteration model.
//!
//! Primitives inside merge programs are evaluated against a CLONED
//! `Database`, which is sound only when results never intern new base
//! values. The hub enforces this dynamically: a primitive result must be an
//! argument echo or the unit rep; anything else reports the offending
//! primitive through [`HubChannels::unsafe_prim`], the run is aborted before
//! any host mutation, and the caller falls back to the interpreter (caching
//! the primitive as uncompilable).

use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::rc::Rc;
use std::sync::Arc;

use differential_dataflow::lattice::Lattice;
use differential_dataflow::{AsCollection, VecCollection};
use egglog_backend_trait::{ExternalFunctionId, MergeAction, MergeFn, Value};
use egglog_core_relations::Database;
use egglog_numeric_id::NumericId;
use hashbrown::HashMap;
use timely::dataflow::channels::pact::Pipeline;
use timely::dataflow::operators::generic::operator::Operator;
use timely::dataflow::operators::CapabilitySet;
use timely::progress::Timestamp;

use crate::dd_native::{RowN, W};

type Row = RowN<W>;

/// Hub op kinds, in application order within a timestamp.
pub(crate) const OP_SIE: u8 = 0;
pub(crate) const OP_DELETE: u8 = 1;
pub(crate) const OP_SET: u8 = 2;

/// A tagged hub write: `(op, table rep, row)`. `OP_DELETE` rows carry the key
/// in the low slots; the others carry full rows.
pub(crate) type HubOp = (u8, u32, Row);

/// Per-table metadata the hub folds with.
#[derive(Clone)]
pub(crate) struct HubTable {
    pub(crate) n_keys: usize,
    pub(crate) arity: usize,
    pub(crate) merge: Arc<MergeFn>,
    pub(crate) n_identity_vals: Option<usize>,
    /// Wave ordering: readable merge targets before their readers.
    pub(crate) level: usize,
    /// For error messages.
    pub(crate) name: String,
}

/// Host-visible outcome channels, checked after the worker run.
#[derive(Clone, Default)]
pub(crate) struct HubChannels {
    /// A merge error (e.g. an `AssertEq` violation), with the host's message.
    pub(crate) error: Rc<RefCell<Option<String>>>,
    /// A primitive whose result was neither an argument echo nor unit.
    pub(crate) unsafe_prim: Rc<RefCell<Option<ExternalFunctionId>>>,
}

impl HubChannels {
    pub(crate) fn poisoned(&self) -> bool {
        self.error.borrow().is_some() || self.unsafe_prim.borrow().is_some()
    }
}

/// Build the hub over a latched op stream. `seeds` are each table's rows at
/// region entry (`key -> values`); output deltas are relative to those seeds.
pub(crate) fn merge_hub<'s, T>(
    ops: &VecCollection<'s, T, HubOp>,
    tables: HashMap<u32, HubTable>,
    seeds: HashMap<u32, HashMap<Vec<u32>, Vec<u32>>>,
    db: Database,
    unit_rep: u32,
    channels: HubChannels,
) -> VecCollection<'s, T, (u32, Row)>
where
    T: Timestamp + Lattice + Ord,
{
    let stream = ops
        .inner
        .clone()
        .unary_frontier(Pipeline, "MergeHub", move |_default_cap, _info| {
            // Pending-data-only capabilities (see `monotone`): a capability
            // parked at the frontier would livelock feedback loops.
            let mut caps: CapabilitySet<T> = CapabilitySet::new();
            let mut queue: BinaryHeap<Reverse<(T, HubOp, isize)>> = BinaryHeap::new();
            let mut state = seeds;
            move |(input, frontier), output| {
                input.for_each(|cap, data| {
                    caps.insert(cap.retain(0));
                    for (op, t, r) in data.drain(..) {
                        queue.push(Reverse((t, op, r)));
                    }
                });
                while queue
                    .peek()
                    .is_some_and(|Reverse((t, _, _))| !frontier.frontier().less_equal(t))
                {
                    let time = queue.peek().expect("peeked above").0 .0.clone();
                    let mut net: HashMap<HubOp, isize> = HashMap::new();
                    while queue.peek().is_some_and(|Reverse((t, _, _))| *t == time) {
                        let Reverse((_, op, r)) = queue.pop().expect("peeked above");
                        *net.entry(op).or_insert(0) += r;
                    }
                    if channels.poisoned() {
                        continue;
                    }
                    // Latched inputs only ever appear; keep net-positive ops,
                    // in deterministic order.
                    let mut batch: Vec<HubOp> = net
                        .into_iter()
                        .filter(|&(_, w)| w > 0)
                        .map(|(op, _)| op)
                        .collect();
                    batch.sort();

                    let mut emits: Vec<((u32, Row), isize)> = Vec::new();
                    apply_timestamp(
                        &mut state,
                        &tables,
                        &db,
                        unit_rep,
                        &channels,
                        batch,
                        &mut emits,
                    );

                    let cap = caps.delayed(&time);
                    let mut session = output.session(&cap);
                    for (data, weight) in emits {
                        session.give((data, time.clone(), weight));
                    }
                }
                match queue.peek() {
                    Some(Reverse((t, _, _))) => {
                        let t = t.clone();
                        caps.downgrade([t]);
                    }
                    None => caps.downgrade(Vec::<T>::new()),
                }
            }
        });
    stream.as_collection()
}

/// Apply one timestamp's ops in host order: set-if-empty, deletes, then merge
/// waves to a fixed point.
fn apply_timestamp(
    state: &mut HashMap<u32, HashMap<Vec<u32>, Vec<u32>>>,
    tables: &HashMap<u32, HubTable>,
    db: &Database,
    unit_rep: u32,
    channels: &HubChannels,
    batch: Vec<HubOp>,
    emits: &mut Vec<((u32, Row), isize)>,
) {
    // The sort key (op, func, row) already groups SIE < DELETE < SET.
    let mut wave: Vec<(u32, Row)> = Vec::new();
    for (op, func, row) in batch {
        let table = &tables[&func];
        match op {
            OP_SIE => {
                let key = row_slice(&row, 0, table.n_keys);
                let rows = state.entry(func).or_default();
                if !rows.contains_key(&key) {
                    rows.insert(key, row_slice(&row, table.n_keys, table.arity));
                    emits.push(((func, row), 1));
                }
            }
            OP_DELETE => {
                let key = row_slice(&row, 0, table.n_keys);
                if let Some(old) = state.entry(func).or_default().remove(&key) {
                    emits.push(((func, pack(&key, &old)), -1));
                }
            }
            OP_SET => wave.push((func, row)),
            _ => unreachable!("unknown hub op"),
        }
    }

    // Merge waves: host MergeTransaction::run_inner's loop.
    while !wave.is_empty() && !channels.poisoned() {
        let mut current = std::mem::take(&mut wave);
        current.sort_by_key(|(func, row)| (tables[func].level, *func, *row));
        for (func, row) in current {
            apply_set(state, tables, db, unit_rep, channels, func, row, emits, &mut wave);
            if channels.poisoned() {
                return;
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn apply_set(
    state: &mut HashMap<u32, HashMap<Vec<u32>, Vec<u32>>>,
    tables: &HashMap<u32, HubTable>,
    db: &Database,
    unit_rep: u32,
    channels: &HubChannels,
    func: u32,
    row: Row,
    emits: &mut Vec<((u32, Row), isize)>,
    next_wave: &mut Vec<(u32, Row)>,
) {
    let table = &tables[&func];
    let key = row_slice(&row, 0, table.n_keys);
    let incoming = row_slice(&row, table.n_keys, table.arity);
    let rows = state.entry(func).or_default();
    let Some(old) = rows.get(&key).cloned() else {
        rows.insert(key, incoming);
        emits.push(((func, row), 1));
        return;
    };

    let values_unchanged = old == incoming;
    let identity_unchanged = table
        .n_identity_vals
        .is_some_and(|count| old[..count] == incoming[..count]);
    if values_unchanged || identity_unchanged {
        return;
    }

    let ctx = EvalCtx {
        db,
        unit_rep,
        channels,
        table_name: &table.name,
    };
    let (actions, result) = match table.merge.as_ref() {
        MergeFn::Block { actions, result } => (actions.as_slice(), result.as_ref()),
        result => (&[][..], result),
    };
    let mut env: Vec<u32> = Vec::new();
    for action in actions {
        match action {
            MergeAction::Set(target, arguments) => {
                let Some(vals) = ctx.eval_args(arguments, &old, &incoming, 0, &env) else {
                    return;
                };
                let target = target.rep_u32();
                next_wave.push((target, pack_full(&vals)));
            }
            MergeAction::Let { value, .. } => {
                let Some(v) = ctx.eval(value, &old, &incoming, 0, &env) else {
                    return;
                };
                env.push(v);
            }
            MergeAction::Union(..) => {
                ctx.fail("native merge unions are rejected at table registration");
                return;
            }
        }
    }
    let merged: Option<Vec<u32>> = match result {
        MergeFn::Columns(results) => results
            .iter()
            .enumerate()
            .map(|(col, expr)| ctx.eval(expr, &old, &incoming, col, &env))
            .collect(),
        expr => ctx.eval(expr, &old, &incoming, 0, &env).map(|v| vec![v]),
    };
    let Some(merged) = merged else {
        return;
    };

    if merged != old {
        emits.push(((func, pack(&key, &old)), -1));
        emits.push(((func, pack(&key, &merged)), 1));
        state
            .entry(func)
            .or_default()
            .insert(key, merged);
    }
}

struct EvalCtx<'a> {
    db: &'a Database,
    unit_rep: u32,
    channels: &'a HubChannels,
    table_name: &'a str,
}

impl EvalCtx<'_> {
    fn fail(&self, message: impl Into<String>) {
        let mut slot = self.channels.error.borrow_mut();
        if slot.is_none() {
            *slot = Some(message.into());
        }
    }

    fn eval_args(
        &self,
        arguments: &[MergeFn],
        old: &[u32],
        new: &[u32],
        self_col: usize,
        env: &[u32],
    ) -> Option<Vec<u32>> {
        arguments
            .iter()
            .map(|a| self.eval(a, old, new, self_col, env))
            .collect()
    }

    /// The host `MergeTransaction::eval`, minus table lookups (gated out at
    /// compile time). `None` means an error or unsafe primitive was recorded.
    fn eval(
        &self,
        expression: &MergeFn,
        old: &[u32],
        new: &[u32],
        self_col: usize,
        env: &[u32],
    ) -> Option<u32> {
        match expression {
            MergeFn::AssertEq => {
                if old[self_col] != new[self_col] {
                    self.fail(format!(
                        "illegal merge attempted for function `{}`",
                        self.table_name
                    ));
                    return None;
                }
                Some(old[self_col])
            }
            MergeFn::UnionId => Some(old[self_col].min(new[self_col])),
            MergeFn::Old => Some(old[self_col]),
            MergeFn::New => Some(new[self_col]),
            MergeFn::OldCol(index) => Some(old[*index]),
            MergeFn::NewCol(index) => Some(new[*index]),
            MergeFn::LetVar(slot) => match env.get(*slot) {
                Some(v) => Some(*v),
                None => {
                    self.fail(format!(
                        "merge for `{}` references an unbound let slot",
                        self.table_name
                    ));
                    None
                }
            },
            MergeFn::Const(value) => Some(value.rep()),
            MergeFn::Primitive(id, arguments) => {
                let args = self.eval_args(arguments, old, new, self_col, env)?;
                let values: Vec<Value> = args.iter().copied().map(Value::new).collect();
                let result = self
                    .db
                    .with_execution_state(|st| st.call_external_func(*id, &values));
                let Some(result) = result else {
                    self.fail(format!(
                        "merge primitive failed for function `{}`",
                        self.table_name
                    ));
                    return None;
                };
                let rep = result.rep();
                // Sound only for argument echoes / unit: anything else may
                // have interned a NEW base value into our clone, diverging
                // from the host's interners.
                if !args.contains(&rep) && rep != self.unit_rep {
                    let mut slot = self.channels.unsafe_prim.borrow_mut();
                    if slot.is_none() {
                        *slot = Some(*id);
                    }
                    return None;
                }
                Some(rep)
            }
            MergeFn::Function(..) | MergeFn::Lookup(..) => {
                self.fail(format!(
                    "merge table lookups for `{}` are gated out of compiled schedules",
                    self.table_name
                ));
                None
            }
            MergeFn::Columns(_) | MergeFn::Block { .. } => {
                self.fail(format!(
                    "nested merge programs for `{}` are rejected at registration",
                    self.table_name
                ));
                None
            }
        }
    }
}

fn row_slice(row: &Row, from: usize, to: usize) -> Vec<u32> {
    (from..to).map(|i| row[i]).collect()
}

fn pack(key: &[u32], vals: &[u32]) -> Row {
    let mut row = Row::default();
    for (i, v) in key.iter().chain(vals.iter()).enumerate() {
        row[i] = *v;
    }
    row
}

fn pack_full(vals: &[u32]) -> Row {
    let mut row = Row::default();
    for (i, v) in vals.iter().enumerate() {
        row[i] = *v;
    }
    row
}

/// `FunctionId` reps are how hub ops name tables (u32, `ExchangeData`).
pub(crate) trait FuncRep {
    fn rep_u32(&self) -> u32;
}

impl FuncRep for egglog_backend_trait::FunctionId {
    fn rep_u32(&self) -> u32 {
        use egglog_numeric_id::NumericId;
        self.rep()
    }
}
