//! Instructions that are executed on the results of a query.
//!
//! This allows us to execute the "right-hand-side" of a rule. The
//! implementation here is optimized to execute on a batch of rows at a time.
use std::{
    ops::Deref,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use crate::{
    common::HashMap,
    free_join::{invoke_batch, invoke_batch_assign},
    numeric_id::{DenseIdMap, NumericId},
};
use egglog_concurrency::NotificationList;
use smallvec::SmallVec;

use crate::{
    BaseValues, CausalReceipts, CausalWave, CauseDraftId, ContainerValues, EqualityEdgeCount,
    EqualityEndpoint, ExternalFunctionId, FactId, ReplayConstructorSpec, ReplaySortId,
    ReplayTermId, WrappedTable,
    common::Value,
    free_join::{CounterId, Counters, ExternalFunctions, TableId, TableInfo, Variable},
    pool::{Clear, Pooled, with_pool_set},
    receipts::{
        ActionReceiptKind, CauseCapability, CheckEndpointSpec, CheckTermSource,
        DeferredEqualityCause, PendingMatchBatch, PendingPremiseResolver, ReplayBindingSource,
        TypedEqualityProposal,
    },
    table_spec::{ColumnId, MutationBuffer},
};

use self::mask::{Mask, MaskIter, ValueSource};

#[macro_use]
pub(crate) mod mask;

#[cfg(test)]
mod tests;

/// A representation of a value within a query or rule.
///
/// A QueryEntry is either a variable bound in a join, or an untyped constant.
#[derive(Copy, Clone, Debug)]
pub enum QueryEntry {
    Var(Variable),
    Const(Value),
}

impl From<Variable> for QueryEntry {
    fn from(var: Variable) -> Self {
        QueryEntry::Var(var)
    }
}

impl From<Value> for QueryEntry {
    fn from(val: Value) -> Self {
        QueryEntry::Const(val)
    }
}

/// A value that can be written to a table in an action.
#[derive(Debug, Clone, Copy)]
pub enum WriteVal {
    /// A variable or a constant.
    QueryEntry(QueryEntry),
    /// A fresh value from the given counter.
    IncCounter(CounterId),
    /// The value of the current row index.
    CurrentVal(usize),
}

impl<T> From<T> for WriteVal
where
    T: Into<QueryEntry>,
{
    fn from(val: T) -> Self {
        WriteVal::QueryEntry(val.into())
    }
}

impl From<CounterId> for WriteVal {
    fn from(ctr: CounterId) -> Self {
        WriteVal::IncCounter(ctr)
    }
}

/// A value that can be written to the database during a merge action.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MergeVal {
    /// A fresh value from the given counter.
    Counter(CounterId),
    /// A standard constant value.
    Constant(Value),
}

impl From<CounterId> for MergeVal {
    fn from(ctr: CounterId) -> Self {
        MergeVal::Counter(ctr)
    }
}

impl From<Value> for MergeVal {
    fn from(val: Value) -> Self {
        MergeVal::Constant(val)
    }
}

/// Bindings store a sequence of values for a given set of variables.
///
/// The intent of bindings is to store a sequence of mappings from [`Variable`] to [`Value`], in a
/// struct-of-arrays style that is better laid out for processing bindings in batches.
pub(crate) struct Bindings {
    matches: usize,
    /// The maximum number of calls to `push` that we can receive before we clear the
    /// [`Bindings`].
    // This is used to preallocate chunks of the flat `data` vector.
    max_batch_size: usize,
    data: Pooled<Vec<Value>>,
    /// Points into `data`. `data[vars[var].. vars[var]+matches]` contains the values for `data`.
    var_offsets: DenseIdMap<Variable, usize>,
    /// Absent for ordinary rules, keeping every causal allocation off the
    /// receipt-disabled path.
    receipt: Option<Box<ReceiptBindings>>,
}

struct ReceiptBindings {
    kind: ActionReceiptKind,
    wave: CausalWave,
    binding_sources: Box<[ReplayBindingSource]>,
    premises: ReceiptPremises,
    causes: Vec<Option<CauseDraftId>>,
    pending_rule_batch: Option<Arc<PendingMatchBatch>>,
    first_native_ordinal: Option<u64>,
    produced_terms: DenseIdMap<Variable, Vec<ReplayTermId>>,
}

enum ReceiptPremises {
    Flat {
        arity: usize,
        facts: Vec<FactId>,
    },
    Lazy {
        arity: usize,
        resolver: Arc<dyn PendingPremiseResolver>,
        lanes: Vec<u32>,
    },
}

impl ReceiptPremises {
    fn arity(&self) -> usize {
        match self {
            Self::Flat { arity, .. } | Self::Lazy { arity, .. } => *arity,
        }
    }

    fn resolve(&self, lane: usize) -> SmallVec<[FactId; 4]> {
        match self {
            Self::Flat { arity, facts } => {
                let start = lane * *arity;
                SmallVec::from_slice(&facts[start..start + *arity])
            }
            Self::Lazy {
                arity,
                resolver,
                lanes,
            } => {
                let result = resolver.resolve(lanes[lane]);
                assert_eq!(result.len(), *arity, "receipt witness has wrong arity");
                result
            }
        }
    }
}

impl std::ops::Index<Variable> for Bindings {
    type Output = [Value];
    fn index(&self, var: Variable) -> &[Value] {
        self.get(var).unwrap()
    }
}

impl std::fmt::Debug for Bindings {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut table = f.debug_map();
        for (var, start) in self.var_offsets.iter() {
            table.entry(&var, &&self.data[*start..*start + self.matches]);
        }
        table.finish()
    }
}

impl Bindings {
    pub(crate) fn new(max_batch_size: usize) -> Self {
        Bindings {
            matches: 0,
            max_batch_size,
            data: Default::default(),
            var_offsets: DenseIdMap::new(),
            receipt: None,
        }
    }
    fn assert_invariant(&self) {
        #[cfg(debug_assertions)]
        {
            assert!(self.matches <= self.max_batch_size);
            for (var, start) in self.var_offsets.iter() {
                assert!(
                    start + self.matches <= self.data.len(),
                    "Variable {:?} starts at {}, but data only has {} elements",
                    var,
                    start,
                    self.data.len()
                );
            }
        }
    }

    pub(crate) fn clear(&mut self) {
        self.matches = 0;
        self.var_offsets.clear();
        self.data.clear();
        self.receipt = None;
        self.assert_invariant();
    }

    fn get(&self, var: Variable) -> Option<&[Value]> {
        let start = self.var_offsets.get(var)?;
        Some(&self.data[*start..*start + self.matches])
    }

    fn add_mapping(&mut self, var: Variable, vals: &[Value]) {
        let start = self.data.len();
        self.data.extend_from_slice(vals);
        // We have a flat representation of the data, meaning that writing more than
        // `max_batch_size` values to `var` could overwrite values for a different variable, which
        // would produce some mysterious results that are hard to debug.
        debug_assert!(vals.len() <= self.max_batch_size);
        if vals.len() < self.max_batch_size {
            let target_len = self.data.len() + self.max_batch_size - vals.len();
            self.data.resize(target_len, Value::stale());
        }
        self.var_offsets.insert(var, start);
    }

    pub(crate) fn insert(&mut self, var: Variable, vals: &[Value]) {
        if self.var_offsets.n_ids() == 0 {
            self.matches = vals.len();
        } else {
            assert_eq!(self.matches, vals.len());
        }
        self.add_mapping(var, vals);
        self.assert_invariant();
    }

    /// Push a new set of bindings for the given variables.
    ///
    /// # Safety:
    /// This method assumes that all calls to `push`:
    /// * Have a mapping for every member of `used_vars`.
    /// * Are passed the same `used_vars`.
    ///
    /// It is unsafe to avoid bounds-checking. This method is called extremely frequently and the
    /// overhead of boundschecking is noticeable.
    pub(crate) unsafe fn push(
        &mut self,
        map: &DenseIdMap<Variable, Value>,
        used_vars: &[Variable],
    ) {
        if self.matches != 0 {
            assert!(self.matches < self.max_batch_size);
            #[cfg(debug_assertions)]
            {
                for var in used_vars {
                    assert!(
                        self.var_offsets.get(*var).is_some(),
                        "Variable {:?} not found in bindings {:?}",
                        var,
                        self.var_offsets
                    );
                }
            }
            for var in used_vars {
                let var = var.index();
                // Safe version: this degrades some benchmarks by ~6%
                // let start = self.var_offsets.raw()[var].unwrap();
                // self.data[start + self.matches] = map.raw()[var].unwrap();
                unsafe {
                    let start = self.var_offsets.raw().get_unchecked(var).unwrap_unchecked();
                    *self.data.get_unchecked_mut(start + self.matches) =
                        map.raw().get_unchecked(var).unwrap_unchecked();
                }
            }
        } else {
            for (var, val) in map.iter() {
                self.add_mapping(var, &[*val]);
            }
        }

        self.matches += 1;
        self.assert_invariant();
    }

    pub(crate) fn push_receipt(
        &mut self,
        kind: &ActionReceiptKind,
        wave: CausalWave,
        premises: &[FactId],
        binding_sources: &[ReplayBindingSource],
    ) {
        if let Some(existing) = &mut self.receipt {
            assert_eq!(&existing.kind, kind);
            assert_eq!(existing.wave, wave);
            assert_eq!(existing.binding_sources.as_ref(), binding_sources);
            let ReceiptPremises::Flat { arity, facts } = &mut existing.premises else {
                panic!("cannot mix eager and lazy receipt witnesses in one action batch")
            };
            assert_eq!(*arity, premises.len());
            facts.extend_from_slice(premises);
            existing.causes.push(None);
        } else {
            self.receipt = Some(Box::new(ReceiptBindings {
                kind: kind.clone(),
                wave,
                binding_sources: binding_sources.into(),
                premises: ReceiptPremises::Flat {
                    arity: premises.len(),
                    facts: premises.into(),
                },
                causes: vec![None],
                pending_rule_batch: None,
                first_native_ordinal: None,
                produced_terms: DenseIdMap::new(),
            }));
        }
    }

    pub(crate) fn push_lazy_receipt(
        &mut self,
        kind: &ActionReceiptKind,
        wave: CausalWave,
        premise_arity: usize,
        binding_sources: &[ReplayBindingSource],
        resolver: Arc<dyn PendingPremiseResolver>,
        witness_lane: u32,
    ) {
        if let Some(existing) = &mut self.receipt {
            assert_eq!(&existing.kind, kind);
            assert_eq!(existing.wave, wave);
            assert_eq!(existing.binding_sources.as_ref(), binding_sources);
            let ReceiptPremises::Lazy {
                arity,
                resolver: existing_resolver,
                lanes,
            } = &mut existing.premises
            else {
                panic!("cannot mix eager and lazy receipt witnesses in one action batch")
            };
            assert_eq!(*arity, premise_arity);
            assert!(
                Arc::ptr_eq(existing_resolver, &resolver),
                "one action batch must share one witness resolver"
            );
            lanes.push(witness_lane);
            existing.causes.push(None);
        } else {
            self.receipt = Some(Box::new(ReceiptBindings {
                kind: kind.clone(),
                wave,
                binding_sources: binding_sources.into(),
                premises: ReceiptPremises::Lazy {
                    arity: premise_arity,
                    resolver,
                    lanes: vec![witness_lane],
                },
                causes: vec![None],
                pending_rule_batch: None,
                first_native_ordinal: None,
                produced_terms: DenseIdMap::new(),
            }));
        }
    }

    fn ensure_pending_rule_batch(&mut self, receipts: &CausalReceipts) {
        let state = self
            .receipt
            .as_ref()
            .expect("receipt-enabled action requires exact match witnesses");
        if state.pending_rule_batch.is_some() {
            return;
        }
        let ActionReceiptKind::Rule(rule) = &state.kind else {
            panic!("only rule matches may defer equality cause promotion")
        };
        let rule = *rule;
        let wave = state.wave;
        let premise_arity = state.premises.arity();
        let binding_sources = state.binding_sources.clone();
        let first_native_ordinal = state
            .first_native_ordinal
            .expect("native match ordinals must be reserved when head execution starts");
        let mut current_terms = SmallVec::<[ReplayTermId; 16]>::new();
        for lane in 0..self.matches {
            for source in binding_sources.iter().copied() {
                if let ReplayBindingSource::Current { variable, sort } = source {
                    let _ = sort;
                    let term = state
                        .produced_terms
                        .get(variable)
                        .and_then(|terms| terms.get(lane))
                        .copied()
                        .filter(|term| !term.is_missing())
                        .unwrap_or(ReplayTermId::MISSING);
                    current_terms.push(term);
                }
            }
        }
        let batch = match &state.premises {
            ReceiptPremises::Flat { facts, .. } => receipts.pending_rule_batch_at(
                rule,
                wave,
                first_native_ordinal,
                premise_arity,
                &binding_sources,
                facts,
                &current_terms,
                self.matches,
            ),
            ReceiptPremises::Lazy {
                resolver, lanes, ..
            } => receipts.pending_rule_batch_lazy(
                rule,
                wave,
                first_native_ordinal,
                premise_arity,
                &binding_sources,
                Arc::clone(resolver),
                lanes,
                &current_terms,
            ),
        };
        self.receipt.as_mut().unwrap().pending_rule_batch = Some(batch);
    }

    fn begin_receipt_execution(&mut self, receipts: &CausalReceipts) {
        let Some(state) = self.receipt.as_mut() else {
            return;
        };
        if !matches!(state.kind, ActionReceiptKind::Rule(_)) {
            return;
        }
        assert!(
            state.first_native_ordinal.is_none(),
            "one receipt binding batch executed more than once"
        );
        state.first_native_ordinal = Some(receipts.reserve_native_match_ordinals(self.matches));
    }

    fn record_produced_term(&mut self, variable: Variable, lane: usize, term: ReplayTermId) {
        if self.receipt.is_none() {
            return;
        }
        assert!(
            !term.is_missing(),
            "producer captured a missing replay term"
        );
        let state = self.receipt.as_mut().unwrap();
        let terms = state.produced_terms.get_or_default(variable);
        if terms.is_empty() {
            terms.resize(self.matches, ReplayTermId::MISSING);
        }
        assert_eq!(terms.len(), self.matches);
        let slot = &mut terms[lane];
        assert!(
            slot.is_missing() || *slot == term,
            "one current variable lane acquired conflicting producer terms"
        );
        *slot = term;
    }

    fn current_binding_sort(&self, variable: Variable) -> Option<ReplaySortId> {
        self.receipt
            .as_ref()?
            .binding_sources
            .iter()
            .find_map(|source| match *source {
                ReplayBindingSource::Current {
                    variable: current,
                    sort,
                } if current == variable => Some(sort),
                _ => None,
            })
    }

    fn replay_term_for_entry(
        &self,
        entry: QueryEntry,
        sort: ReplaySortId,
        lane: usize,
        receipts: &CausalReceipts,
    ) -> ReplayTermId {
        if let QueryEntry::Var(variable) = entry
            && let Some(term) = self
                .receipt
                .as_ref()
                .and_then(|state| state.produced_terms.get(variable))
                .and_then(|terms| terms.get(lane))
                .copied()
                .filter(|term| !term.is_missing())
        {
            return term;
        }
        let value = match entry {
            QueryEntry::Const(value) => value,
            QueryEntry::Var(variable) => self[variable][lane],
        };
        receipts.lookup_term(sort, value).unwrap_or_else(|| {
            panic!("value {value:?} has no producer-installed ReplayTermId for sort {sort:?}")
        })
    }

    fn deferred_equality_cause(
        &mut self,
        lane: usize,
        receipts: &CausalReceipts,
    ) -> DeferredEqualityCause {
        if let Some(cause) = self.receipt_cause(lane) {
            return DeferredEqualityCause::ready(cause);
        }
        if matches!(
            self.receipt.as_ref().map(|state| &state.kind),
            Some(ActionReceiptKind::Source(_))
        ) {
            self.ensure_receipt_causes(&[lane], receipts);
            return DeferredEqualityCause::ready(
                self.receipt_cause(lane)
                    .expect("source effect is missing its exact receipt cause"),
            );
        }
        self.ensure_pending_rule_batch(receipts);
        let batch = self
            .receipt
            .as_ref()
            .unwrap()
            .pending_rule_batch
            .as_ref()
            .unwrap();
        DeferredEqualityCause::pending(receipts.pending_rule_cause(batch, lane))
    }

    fn ensure_receipt_causes(&mut self, lanes: &[usize], receipts: &CausalReceipts) {
        let state = self
            .receipt
            .as_ref()
            .expect("receipt-enabled action requires exact match witnesses");
        let mut missing = SmallVec::<[usize; 16]>::new();
        missing.extend(
            lanes
                .iter()
                .copied()
                .filter(|lane| state.causes[*lane].is_none()),
        );
        if missing.is_empty() {
            return;
        }
        if let Some(batch) = state.pending_rule_batch.clone() {
            let registered = missing
                .iter()
                .copied()
                .map(|lane| (lane, receipts.pending_rule_cause(&batch, lane).promote()))
                .collect::<SmallVec<[(usize, CauseDraftId); 16]>>();
            let state = self.receipt.as_mut().unwrap();
            for (lane, cause) in registered {
                state.causes[lane] = Some(cause);
            }
            return;
        }
        if let ActionReceiptKind::Source(source) = &state.kind {
            let registered = receipts.register_source_actions(source, &missing);
            let state = self.receipt.as_mut().unwrap();
            for (lane, cause) in registered {
                state.causes[lane] = Some(cause);
            }
            return;
        }
        let ActionReceiptKind::Rule(_) = &state.kind else {
            panic!("check receipt action cannot stage native effects");
        };
        panic!("rule causes must be promoted through their pending match batch")
    }

    fn receipt_cause(&self, lane: usize) -> Option<CauseDraftId> {
        self.receipt.as_ref()?.causes[lane]
    }

    fn check_receipt(&self, lane: usize) -> (CausalWave, SmallVec<[FactId; 4]>) {
        let state = self
            .receipt
            .as_ref()
            .expect("receipt-aware check requires exact native witnesses");
        assert_eq!(
            state.kind,
            ActionReceiptKind::Check,
            "check recorder reached non-check receipt metadata"
        );
        (state.wave, state.premises.resolve(lane))
    }

    /// A method that removes the bindings for the given variable and allows for its values to be
    /// used independently from the [`Bindings`] struct. This is helpful when an operation needs to
    /// mutably borrow the values for one value while reading the values for another.
    ///
    /// To add the values back, use [`Bindings::replace`].
    pub(crate) fn take(&mut self, var: Variable) -> Option<ExtractedBinding> {
        let mut vals: Pooled<Vec<Value>> = with_pool_set(|ps| ps.get());
        vals.extend_from_slice(self.get(var)?);
        let start = self.var_offsets.take(var)?;
        Some(ExtractedBinding {
            var,
            offset: start,
            vals,
        })
    }

    /// Replace a binding extracted with [`Bindings::take`].
    ///
    /// # Panics
    /// This method will panic if the length of the values in `bdg` does not match the current
    /// number of matches in `Bindings`. It may panic if `bdg` was extracted from a different
    /// [`Bindings`] than the one it is being replaced in.
    pub(crate) fn replace(&mut self, bdg: ExtractedBinding) {
        // Replace the binding with the new values.
        let ExtractedBinding {
            var,
            offset,
            mut vals,
        } = bdg;
        assert_eq!(vals.len(), self.matches);
        self.data
            .splice(offset..offset + self.matches, vals.drain(..));
        self.var_offsets.insert(var, offset);
    }
}

/// A binding that has been extracted from a [`Bindings`] struct via the [`Bindings::take`] method.
///
/// This allows for a variable's contents to be read while the [`Bindings`] struct has been
/// borrowed mutably. The contents will not be readable until [`Bindings::replace`] is called.
pub(crate) struct ExtractedBinding {
    var: Variable,
    offset: usize,
    pub(crate) vals: Pooled<Vec<Value>>,
}

#[derive(Default)]
pub(crate) struct PredictedVals {
    #[allow(clippy::type_complexity)]
    data: HashMap<(TableId, SmallVec<[Value; 3]>), Pooled<Vec<Value>>>,
}

impl Clear for PredictedVals {
    fn reuse(&self) -> bool {
        self.data.capacity() > 0
    }
    fn clear(&mut self) {
        self.data.clear()
    }
    fn bytes(&self) -> usize {
        self.data.capacity()
            * (std::mem::size_of::<(TableId, SmallVec<[Value; 3]>)>()
                + std::mem::size_of::<Pooled<Vec<Value>>>())
    }
}

impl PredictedVals {
    pub(crate) fn get_val(
        &mut self,
        table: TableId,
        key: &[Value],
        default: impl FnOnce() -> Pooled<Vec<Value>>,
    ) -> impl Deref<Target = Pooled<Vec<Value>>> + '_ {
        self.data
            .entry((table, SmallVec::from_slice(key)))
            .or_insert_with(default)
    }
}

#[derive(Clone)]
pub(crate) enum ActiveCause {
    Ready(CauseCapability),
    Deferred(DeferredEqualityCause),
    DeferredMerge {
        incoming: DeferredEqualityCause,
        prior_fact: FactId,
        shared: Option<DeferredEqualityCause>,
    },
}

impl ActiveCause {
    fn deferred(&mut self, receipts: &CausalReceipts) -> DeferredEqualityCause {
        match self {
            Self::Ready(cause) => DeferredEqualityCause::capability(*cause),
            Self::Deferred(cause) => cause.clone(),
            Self::DeferredMerge {
                incoming,
                prior_fact,
                shared,
            } => shared
                .get_or_insert_with(|| receipts.pending_merge_cause(incoming.clone(), *prior_fact))
                .clone(),
        }
    }

    fn ready_capability(&self) -> Option<CauseCapability> {
        match self {
            Self::Ready(cause) => Some(*cause),
            Self::Deferred(_) | Self::DeferredMerge { .. } => None,
        }
    }
}

#[derive(Copy, Clone)]
pub(crate) struct DbView<'a> {
    pub(crate) table_info: &'a DenseIdMap<TableId, TableInfo>,
    pub(crate) counters: &'a Counters,
    pub(crate) external_funcs: &'a ExternalFunctions,
    pub(crate) bases: &'a BaseValues,
    pub(crate) containers: &'a ContainerValues,
    pub(crate) notification_list: &'a NotificationList<TableId>,
    pub(crate) causal_receipts: Option<&'a CausalReceipts>,
    pub(crate) causal_wave: CausalWave,
}

/// A handle on a database that may be in the process of running a rule.
///
/// An ExecutionState grants immutable access to the (much of) the database, and also provides a
/// limited API to mutate database contents.
///
/// A few important notes:
///
/// ## Some tables may be missing
/// Callers external to this crate cannot construct an `ExecutionState` directly. Depending on the
/// context, some tables may not be available. In particular, when running [`crate::Table::merge`]
/// operations, only a table's read-side dependencies are available for reading (sim. for writing).
/// This allows tables that do not need access to one another to be merged in parallel.
///
/// When executing a rule, ExecutionState has access to all tables.
///
/// ## Limited Mutability
/// Callers can only stage insertsions and deletions to tables. These changes are not applied until
/// the next call to `merge` on the underlying table.
///
/// ## Predicted Values
/// ExecutionStates provide a means of synchronizing the results of a pending write across
/// different executions of a rule. This is particularly important in the case where the result of
/// an operation (such as "lookup or insert new id" operatiosn) is a fresh id. A common
/// ExecutionState ensures that future lookups will see the same id (even across calls to
/// [`ExecutionState::clone`]).
pub struct ExecutionState<'a> {
    pub(crate) predicted: PredictedVals,
    pub(crate) db: DbView<'a>,
    buffers: MutationBuffers<'a>,
    /// Whether any mutations have been staged via this ExecutionState.
    pub(crate) changed: bool,
    /// Atomic flag for early stopping of rule execution.
    /// This flag is shared across all handles (clones) of this ExecutionState.
    stop_match: Arc<AtomicBool>,
    /// Cause inherited by every native write performed in the current action
    /// lane or merge callback. It is state-local so parallel execution cannot
    /// cross-attribute proposals.
    active_cause: Option<ActiveCause>,
    /// Logical sort selected for a prepared container-registry union.
    active_container_union_sort: Option<ReplaySortId>,
}

/// A basic wrapper around an map from table id to a mutation buffer for that table that also
/// tracks if a table has been modified.
struct MutationBuffers<'a> {
    notify_list: &'a NotificationList<TableId>,
    buffers: DenseIdMap<TableId, Box<dyn MutationBuffer>>,
    transaction: Option<crate::table_spec::MutationTransaction>,
    transaction_changed: HashMap<TableId, ()>,
}

impl Clone for MutationBuffers<'_> {
    fn clone(&self) -> Self {
        let mut res = MutationBuffers::new(self.notify_list, Default::default());
        res.transaction = self.transaction.clone();
        res.transaction_changed = self.transaction_changed.clone();
        for (id, buf) in self.buffers.iter() {
            res.buffers.insert(id, buf.fresh_handle());
        }
        res
    }
}

impl<'a> MutationBuffers<'a> {
    fn new(
        notify_list: &'a NotificationList<TableId>,
        buffers: DenseIdMap<TableId, Box<dyn MutationBuffer>>,
    ) -> MutationBuffers<'a> {
        MutationBuffers {
            notify_list,
            buffers,
            transaction: None,
            transaction_changed: HashMap::default(),
        }
    }

    fn defer_until(&mut self, transaction: crate::table_spec::MutationTransaction) {
        assert!(
            self.buffers.iter().next().is_none(),
            "a mutation commit guard must be installed before opening buffers"
        );
        assert!(
            self.transaction.replace(transaction).is_none(),
            "an execution state received more than one mutation commit guard"
        );
    }

    fn lazy_init(&mut self, table_id: TableId, f: impl FnOnce() -> Box<dyn MutationBuffer>) {
        self.buffers.get_or_insert(table_id, || {
            let mut buffer = f();
            if let Some(transaction) = &self.transaction {
                buffer.defer_until(transaction.clone());
            }
            buffer
        });
    }

    fn note_changed(&mut self, table_id: TableId) {
        if let Some(transaction) = &self.transaction {
            if self.transaction_changed.insert(table_id, ()).is_none() {
                transaction.defer_changed_table(table_id);
            }
        } else {
            self.notify_list.notify(table_id);
        }
    }

    fn stage_insert(&mut self, table_id: TableId, row: &[Value]) {
        self.buffers[table_id].stage_insert(row);
        self.note_changed(table_id);
    }

    fn stage_insert_deferred(
        &mut self,
        table_id: TableId,
        row: &[Value],
        cause: DeferredEqualityCause,
    ) {
        self.buffers[table_id].stage_insert_deferred(row, cause);
        self.note_changed(table_id);
    }

    fn stage_insert_deferred_with_terms(
        &mut self,
        table_id: TableId,
        row: &[Value],
        cause: DeferredEqualityCause,
        terms: &[ReplayTermId],
    ) {
        self.buffers[table_id].stage_insert_deferred_with_terms(row, cause, terms);
        self.note_changed(table_id);
    }

    fn stage_typed_union_deferred(
        &mut self,
        table_id: TableId,
        row: &[Value],
        cause: DeferredEqualityCause,
        proposal: TypedEqualityProposal,
    ) {
        self.buffers[table_id].stage_typed_union_deferred(row, cause, proposal);
        self.note_changed(table_id);
    }

    fn stage_remove(&mut self, table_id: TableId, key: &[Value]) {
        self.buffers[table_id].stage_remove(key);
        self.note_changed(table_id);
    }
}

impl Clone for ExecutionState<'_> {
    fn clone(&self) -> Self {
        ExecutionState {
            predicted: Default::default(),
            db: self.db,
            buffers: self.buffers.clone(),
            changed: false,
            stop_match: Arc::clone(&self.stop_match),
            active_cause: self.active_cause.clone(),
            active_container_union_sort: self.active_container_union_sort,
        }
    }
}

impl<'a> ExecutionState<'a> {
    pub(crate) fn new(
        db: DbView<'a>,
        buffers: DenseIdMap<TableId, Box<dyn MutationBuffer>>,
    ) -> Self {
        ExecutionState {
            predicted: Default::default(),
            db,
            buffers: MutationBuffers::new(db.notification_list, buffers),
            changed: false,
            stop_match: Arc::new(AtomicBool::new(false)),
            active_cause: None,
            active_container_union_sort: None,
        }
    }

    /// Delay every native mutation staged through this state until one shared
    /// transaction reaches an explicit commit decision.
    pub(crate) fn defer_mutations_until(
        &mut self,
        transaction: crate::table_spec::MutationTransaction,
    ) {
        if let Some(receipts) = self.db.causal_receipts {
            transaction.validate_causal_scope(receipts, self.db.causal_wave);
        }
        self.buffers.defer_until(transaction);
    }

    /// Stage an insertion of the given row into `table`.
    ///
    /// If you are using `egglog`, consider using `egglog_bridge::TableAction`.
    pub fn stage_insert(&mut self, table: TableId, row: &[Value]) {
        self.buffers
            .lazy_init(table, || self.db.table_info[table].table.new_buffer());
        if let Some(receipts) = self.db.causal_receipts {
            let cause = self
                .active_cause
                .as_mut()
                .expect("receipt-enabled native insertion reached an uninstrumented action")
                .deferred(receipts);
            match receipts
                .constructor_row_terms(table, row)
                .unwrap_or_else(|error| panic!("cannot stage exact constructor row terms: {error}"))
            {
                Some(terms) => self
                    .buffers
                    .stage_insert_deferred_with_terms(table, row, cause, &terms),
                None => self.buffers.stage_insert_deferred(table, row, cause),
            }
        } else {
            self.buffers.stage_insert(table, row);
        }
        self.changed = true;
    }

    /// Stage one equality proposal with an explicit logical sort. Endpoint
    /// terms are resolved before the native union-find buffer is touched.
    pub fn stage_union_with_replay(
        &mut self,
        table: TableId,
        left: Value,
        right: Value,
        timestamp: Value,
        sort: ReplaySortId,
    ) {
        let receipts = self
            .db
            .causal_receipts
            .expect("typed union staging requires causal receipts");
        let cause = self
            .active_cause
            .as_mut()
            .expect("receipt-enabled union reached an uninstrumented action")
            .deferred(receipts);
        self.stage_union_with_deferred_cause(table, left, right, timestamp, sort, cause);
    }

    fn stage_union_with_deferred_cause(
        &mut self,
        table: TableId,
        left: Value,
        right: Value,
        timestamp: Value,
        sort: ReplaySortId,
        cause: DeferredEqualityCause,
    ) {
        let receipts = self
            .db
            .causal_receipts
            .expect("typed union staging requires causal receipts");
        receipts
            .validate_deferred_equality_cause(&cause)
            .unwrap_or_else(|error| panic!("invalid equality cause: {error}"));
        receipts
            .validate_equality_wave_timestamp(self.db.causal_wave, timestamp)
            .unwrap_or_else(|error| panic!("invalid equality timestamp: {error}"));
        let proposal = receipts
            .typed_equality_proposal(self.db.causal_wave, sort, left, right)
            .unwrap_or_else(|error| panic!("invalid typed union proposal: {error}"));
        let row = [left, right, timestamp];
        self.buffers
            .lazy_init(table, || self.db.table_info[table].table.new_buffer());
        self.buffers
            .stage_typed_union_deferred(table, &row, cause, proposal);
        self.changed = true;
    }

    /// Whether this execution belongs to a database recording causal receipts.
    pub fn causal_receipts_enabled(&self) -> bool {
        self.db.causal_receipts.is_some()
    }

    /// Resolve the instance-local logical sort registered for one table cell.
    pub fn causal_replay_sort(&self, table: TableId, column: ColumnId) -> Option<ReplaySortId> {
        self.db
            .causal_receipts
            .and_then(|receipts| receipts.table_column_sort(table, column.index()))
    }

    pub(crate) fn set_active_cause(&mut self, cause: Option<CauseDraftId>) {
        self.active_cause = cause.map(|cause| {
            ActiveCause::Ready(
                self.db
                    .causal_receipts
                    .expect("active receipt cause requires causal receipts")
                    .cause_capability(cause),
            )
        });
    }

    pub(crate) fn set_active_cause_capability(&mut self, cause: Option<CauseCapability>) {
        self.active_cause = cause.map(ActiveCause::Ready);
    }

    fn set_active_deferred_cause(&mut self, cause: Option<DeferredEqualityCause>) {
        self.active_cause = cause.map(ActiveCause::Deferred);
    }

    pub(crate) fn active_cause_capability(&self) -> Option<CauseCapability> {
        self.active_cause
            .as_ref()
            .and_then(ActiveCause::ready_capability)
    }

    pub(crate) fn begin_deferred_merge_cause(
        &mut self,
        incoming: DeferredEqualityCause,
        prior_fact: FactId,
    ) -> Option<ActiveCause> {
        self.active_cause.replace(ActiveCause::DeferredMerge {
            incoming,
            prior_fact,
            shared: None,
        })
    }

    pub(crate) fn end_deferred_merge_cause(
        &mut self,
        previous: Option<ActiveCause>,
        require_cause: bool,
    ) -> Option<DeferredEqualityCause> {
        let mut active = self
            .active_cause
            .take()
            .expect("deferred merge lost its active cause");
        let result = require_cause.then(|| {
            let receipts = self
                .db
                .causal_receipts
                .expect("deferred merge cause requires causal receipts");
            active.deferred(receipts)
        });
        self.active_cause = previous;
        result
    }

    pub(crate) fn set_active_container_canonicalization(
        &mut self,
        cause: Option<(CauseCapability, ReplaySortId)>,
    ) {
        match cause {
            Some((cause, sort)) => {
                self.active_cause = Some(ActiveCause::Ready(cause));
                self.active_container_union_sort = Some(sort);
            }
            None => {
                self.active_cause = None;
                self.active_container_union_sort = None;
            }
        }
    }

    /// Stage the prepared container-registry union through the ordinary typed
    /// equality path. Only the registry merge callback may call this method.
    pub fn stage_container_union(
        &mut self,
        table: TableId,
        left: Value,
        right: Value,
        timestamp: Value,
    ) {
        let sort = self
            .active_container_union_sort
            .expect("container union has no prepared logical sort");
        self.stage_union_with_replay(table, left, right, timestamp, sort);
    }

    pub(crate) fn causal_receipts(&self) -> Option<&CausalReceipts> {
        self.db.causal_receipts
    }

    pub(crate) fn causal_wave(&self) -> CausalWave {
        self.db.causal_wave
    }

    /// Stage a removal of the given row from `table` if it is present.
    ///
    /// If you are using `egglog`, consider using `egglog_bridge::TableAction`.
    pub fn stage_remove(&mut self, table: TableId, key: &[Value]) {
        assert!(
            self.db.causal_receipts.is_none(),
            "causal receipts do not support removal; failing closed"
        );
        self.buffers
            .lazy_init(table, || self.db.table_info[table].table.new_buffer());
        self.buffers.stage_remove(table, key);
        self.changed = true;
    }

    /// Call an external function.
    pub fn call_external_func(
        &mut self,
        func: ExternalFunctionId,
        args: &[Value],
    ) -> Option<Value> {
        self.db.external_funcs[func].invoke(self, args)
    }

    pub fn inc_counter(&self, ctr: CounterId) -> usize {
        self.db.counters.inc(ctr)
    }

    pub fn read_counter(&self, ctr: CounterId) -> usize {
        self.db.counters.read(ctr)
    }

    /// Iterate over the identifiers of all tables visible to this execution state.
    pub fn table_ids(&self) -> impl Iterator<Item = TableId> + '_ {
        self.db.table_info.iter().map(|(id, _)| id)
    }

    /// Get an immutable reference to the table with id `table`.
    /// Dangerous: Reading from a table during action execution may break the semi-naive evaluation
    pub fn get_table(&self, table: TableId) -> &'a WrappedTable {
        &self.db.table_info[table].table
    }

    /// Get the human-readable name for a table, if one exists.
    pub fn table_name(&self, table: TableId) -> Option<&'a str> {
        self.db.table_info[table].name()
    }

    pub fn base_values(&self) -> &'a BaseValues {
        self.db.bases
    }

    pub fn container_values(&self) -> &'a ContainerValues {
        self.db.containers
    }

    /// Get the _current_ value for a given key in `table`, or otherwise insert
    /// the unique _next_ value.
    ///
    /// Insertions into tables are not performed immediately, but rules and
    /// merge functions sometimes need to get the result of an insertion. For
    /// such cases, executions keep a cache of "predicted" values for a given
    /// mapping that manage the insertions, etc.
    ///
    /// If you are using `egglog`, consider using `egglog_bridge::TableAction`.
    pub fn predict_val(
        &mut self,
        table: TableId,
        key: &[Value],
        vals: impl ExactSizeIterator<Item = MergeVal>,
    ) -> Pooled<Vec<Value>> {
        if let Some(row) = self.db.table_info[table].table.get_row(key) {
            return row.vals;
        }
        let cause = self.db.causal_receipts.map(|receipts| {
            self.active_cause
                .as_mut()
                .expect("receipt-enabled predicted insertion is missing its match cause")
                .deferred(receipts)
        });
        Pooled::cloned(
            self.predicted
                .get_val(table, key, || {
                    Self::construct_new_row(
                        &self.db,
                        &mut self.buffers,
                        &mut self.changed,
                        table,
                        key,
                        vals,
                        cause,
                    )
                })
                .deref(),
        )
    }

    fn construct_new_row(
        db: &DbView,
        buffers: &mut MutationBuffers,
        changed: &mut bool,
        table: TableId,
        key: &[Value],
        vals: impl ExactSizeIterator<Item = MergeVal>,
        cause: Option<DeferredEqualityCause>,
    ) -> Pooled<Vec<Value>> {
        with_pool_set(|ps| {
            let mut new = ps.get::<Vec<Value>>();
            new.reserve(key.len() + vals.len());
            new.extend_from_slice(key);
            for val in vals {
                new.push(match val {
                    MergeVal::Counter(ctr) => Value::from_usize(db.counters.inc(ctr)),
                    MergeVal::Constant(c) => c,
                })
            }
            buffers.lazy_init(table, || db.table_info[table].table.new_buffer());
            if let Some(receipts) = db.causal_receipts {
                let cause =
                    cause.expect("receipt-enabled predicted insertion is missing its match cause");
                match receipts
                    .constructor_row_terms(table, &new)
                    .unwrap_or_else(|error| {
                        panic!("cannot stage exact constructor row terms: {error}")
                    }) {
                    Some(terms) => {
                        buffers.stage_insert_deferred_with_terms(table, &new, cause, &terms)
                    }
                    None => buffers.stage_insert_deferred(table, &new, cause),
                }
            } else {
                buffers.stage_insert(table, &new);
            }
            *changed = true;
            new
        })
    }

    /// A variant of [`ExecutionState::predict_val`] that avoids materializing the full row, and
    /// instead only returns the value in the given column.
    pub fn predict_col(
        &mut self,
        table: TableId,
        key: &[Value],
        vals: impl ExactSizeIterator<Item = MergeVal>,
        col: ColumnId,
    ) -> Value {
        if let Some(val) = self.db.table_info[table].table.get_row_column(key, col) {
            return val;
        }
        let cause = self.db.causal_receipts.map(|receipts| {
            self.active_cause
                .as_mut()
                .expect("receipt-enabled predicted insertion is missing its match cause")
                .deferred(receipts)
        });
        self.predicted.get_val(table, key, || {
            Self::construct_new_row(
                &self.db,
                &mut self.buffers,
                &mut self.changed,
                table,
                key,
                vals,
                cause,
            )
        })[col.index()]
    }

    /// Trigger early stopping by setting the stop_match flag.
    /// This causes rule execution to halt at the next opportunity.
    ///
    /// Uses Release ordering to ensure all prior writes are visible to threads that observe this flag.
    pub fn trigger_early_stop(&self) {
        self.stop_match.store(true, Ordering::Release);
    }

    /// Check if early stopping has been requested.
    ///
    /// Uses Acquire ordering to ensure we see all writes that happened before the flag was set.
    pub fn should_stop(&self) -> bool {
        self.stop_match.load(Ordering::Acquire)
    }
}

impl ExecutionState<'_> {
    /// Returns the number of matches that make it to the end of the instructions
    pub(crate) fn run_instrs(&mut self, instrs: &[Instr], bindings: &mut Bindings) -> usize {
        if bindings.var_offsets.next_id().rep() == 0 {
            // If we have no variables, we want to run the rules once.
            bindings.matches = 1;
        }
        if let Some(receipts) = self.db.causal_receipts {
            bindings.begin_receipt_execution(receipts);
        }

        // Vectorized execution for larger batch sizes
        let mut mask = with_pool_set(|ps| Mask::new(0..bindings.matches, ps));
        for instr in instrs {
            if mask.is_empty() {
                return 0;
            }
            self.run_instr(&mut mask, instr, bindings);
        }
        mask.count_ones()
    }
    fn run_instr(&mut self, mask: &mut Mask, inst: &Instr, bindings: &mut Bindings) {
        fn assert_impl(
            bindings: &mut Bindings,
            mask: &mut Mask,
            l: &QueryEntry,
            r: &QueryEntry,
            op: impl Fn(Value, Value) -> bool,
        ) {
            match (l, r) {
                (QueryEntry::Var(v1), QueryEntry::Var(v2)) => {
                    mask.iter(&bindings[*v1])
                        .zip(&bindings[*v2])
                        .retain(|(v1, v2)| op(*v1, *v2));
                }
                (QueryEntry::Var(v), QueryEntry::Const(c))
                | (QueryEntry::Const(c), QueryEntry::Var(v)) => {
                    mask.iter(&bindings[*v]).retain(|v| op(*v, *c));
                }
                (QueryEntry::Const(c1), QueryEntry::Const(c2)) => {
                    if !op(*c1, *c2) {
                        mask.clear();
                    }
                }
            }
        }

        match inst {
            Instr::LookupOrInsertDefault {
                table: table_id,
                args,
                default,
                dst_col,
                dst_var,
            } => {
                let pool = with_pool_set(|ps| ps.get_pool::<Vec<Value>>().clone());
                self.buffers.lazy_init(*table_id, || {
                    self.db.table_info[*table_id].table.new_buffer()
                });
                let table = &self.db.table_info[*table_id].table;
                // Do two passes over the current vector. First, do a round of lookups. Then, for
                // any offsets where the lookup failed, insert the default value.
                let mut mask_copy = mask.clone();
                table.lookup_row_vectorized(&mut mask_copy, bindings, args, *dst_col, *dst_var);
                mask_copy.symmetric_difference(mask);
                if mask_copy.is_empty() {
                    return;
                }
                let deferred_causes = if let Some(receipts) = self.db.causal_receipts {
                    let mut causes = vec![None; bindings.matches];
                    let mut cause_mask = mask_copy.clone();
                    cause_mask.empty_iter().for_each_indexed(|offset, ()| {
                        causes[offset] = Some(bindings.deferred_equality_cause(offset, receipts));
                    });
                    Some(causes)
                } else {
                    None
                };
                let mut out = bindings.take(*dst_var).unwrap();
                for_each_binding_with_mask!(mask_copy, args.as_slice(), bindings, |iter| {
                    iter.assign_vec(&mut out.vals, |offset, key| {
                        // First, check if the entry is already in the table:
                        // if let Some(row) = table.get_row_column(&key, *dst_col) {
                        //     return row;
                        // }
                        // If not, insert the default value.
                        //
                        // We avoid doing this more than once by using the
                        // `predicted` map.
                        let prediction_key = (
                            *table_id,
                            SmallVec::<[Value; 3]>::from_slice(key.as_slice()),
                        );
                        let buffers = &mut self.buffers;
                        // Bind some mutable references because the closure passed
                        // to or_insert_with is `move`.
                        let ctrs = &self.db.counters;
                        let bindings = &bindings;
                        let pool = pool.clone();
                        let row = self
                            .predicted
                            .data
                            .entry(prediction_key)
                            .or_insert_with(|| {
                                let mut row = pool.get();
                                row.extend_from_slice(key.as_slice());
                                // Extend the key with the default values.
                                row.reserve(default.len());
                                for val in default {
                                    let val = match val {
                                        WriteVal::QueryEntry(QueryEntry::Const(c)) => *c,
                                        WriteVal::QueryEntry(QueryEntry::Var(v)) => {
                                            bindings[*v][offset]
                                        }
                                        WriteVal::IncCounter(ctr) => {
                                            Value::from_usize(ctrs.inc(*ctr))
                                        }
                                        WriteVal::CurrentVal(ix) => row[*ix],
                                    };
                                    row.push(val)
                                }
                                if let Some(causes) = &deferred_causes {
                                    buffers.stage_insert_deferred(
                                        *table_id,
                                        &row,
                                        causes[offset].clone().expect(
                                            "constructor lane is missing its exact receipt cause",
                                        ),
                                    );
                                } else {
                                    buffers.stage_insert(*table_id, &row);
                                }
                                row
                            });
                        row[dst_col.index()]
                    });
                });
                bindings.replace(out);
            }
            Instr::LookupOrInsertDefaultReplay {
                table: table_id,
                args,
                default,
                dst_col,
                dst_var,
                replay,
            } => {
                let receipts = self
                    .db
                    .causal_receipts
                    .expect("replay constructor instruction requires causal receipts");
                let pool = with_pool_set(|ps| ps.get_pool::<Vec<Value>>().clone());
                self.buffers.lazy_init(*table_id, || {
                    self.db.table_info[*table_id].table.new_buffer()
                });
                let table = &self.db.table_info[*table_id].table;

                // Phase 1: read all hits and construct each distinct missing
                // predicted row once, but do not stage any effect yet.
                let mut missing = mask.clone();
                table.lookup_row_vectorized(&mut missing, bindings, args, *dst_col, *dst_var);
                missing.symmetric_difference(mask);
                let mut owners = Vec::<(SmallVec<[Value; 3]>, usize)>::new();
                if !missing.is_empty() {
                    let mut out = bindings.take(*dst_var).unwrap();
                    let ctrs = &self.db.counters;
                    let predicted = &mut self.predicted.data;
                    for_each_binding_with_mask!(missing, args.as_slice(), bindings, |iter| {
                        iter.assign_vec(&mut out.vals, |offset, key| {
                            let key = SmallVec::<[Value; 3]>::from_slice(key.as_slice());
                            let prediction_key = (*table_id, key.clone());
                            use hashbrown::hash_map::Entry;
                            let row = match predicted.entry(prediction_key) {
                                Entry::Occupied(entry) => entry.into_mut(),
                                Entry::Vacant(entry) => {
                                    let mut row = pool.get();
                                    row.extend_from_slice(&key);
                                    row.reserve(default.len());
                                    for val in default {
                                        let val = match val {
                                            WriteVal::QueryEntry(QueryEntry::Const(c)) => *c,
                                            WriteVal::QueryEntry(QueryEntry::Var(v)) => {
                                                bindings[*v][offset]
                                            }
                                            WriteVal::IncCounter(ctr) => {
                                                Value::from_usize(ctrs.inc(*ctr))
                                            }
                                            WriteVal::CurrentVal(ix) => row[*ix],
                                        };
                                        row.push(val);
                                    }
                                    owners.push((key, offset));
                                    entry.insert(row)
                                }
                            };
                            row[dst_col.index()]
                        });
                    });
                    bindings.replace(out);
                }

                // Snapshot the exact producer term for every active lane,
                // including lookup hits. A native value may already have a
                // different structural alias in the global current map.
                let active_lanes = {
                    let mut lanes = Vec::new();
                    let mut active = mask.clone();
                    active
                        .empty_iter()
                        .for_each_indexed(|lane, ()| lanes.push(lane));
                    lanes
                };
                for lane in active_lanes {
                    let mut children = SmallVec::<[ReplayTermId; 4]>::new();
                    for (sort, arg) in replay.child_sorts.iter().copied().zip(args) {
                        children.push(bindings.replay_term_for_entry(*arg, sort, lane, receipts));
                    }
                    let output = bindings[*dst_var][lane];
                    let call = receipts
                        .intern_spec_call(replay, &children, output)
                        .expect("constructor producer must install a typed output");
                    bindings.record_produced_term(*dst_var, lane, call);
                }

                // Phase 2: only distinct missing rows are effects. Preserve
                // the exact Call node assembled for each owner beside its
                // staged row; a global current-value lookup can select a
                // different structural alias by commit time.
                if !owners.is_empty() {
                    let predicted = &self.predicted.data;
                    let buffers = &mut self.buffers;
                    for (key, lane) in owners {
                        let row = predicted
                            .get(&(*table_id, key))
                            .expect("new constructor prediction disappeared");
                        let mut terms = vec![ReplayTermId::MISSING; row.len()];
                        let mut children = SmallVec::<[ReplayTermId; 4]>::new();
                        for (sort, arg) in replay.child_sorts.iter().copied().zip(args) {
                            children
                                .push(bindings.replay_term_for_entry(*arg, sort, lane, receipts));
                        }
                        let call = bindings
                            .receipt
                            .as_ref()
                            .and_then(|state| state.produced_terms.get(*dst_var))
                            .and_then(|terms| terms.get(lane))
                            .copied()
                            .filter(|term| !term.is_missing())
                            .expect("constructor output is missing its producer term");
                        terms[..children.len()].copy_from_slice(&children);
                        terms[children.len()] = call;
                        buffers.stage_insert_deferred_with_terms(
                            *table_id,
                            row,
                            bindings.deferred_equality_cause(lane, receipts),
                            &terms,
                        );
                    }
                }
            }
            Instr::LookupWithDefault {
                table,
                args,
                dst_col,
                dst_var,
                default,
            } => {
                let table = &self.db.table_info[*table].table;
                table.lookup_with_default_vectorized(
                    mask, bindings, args, *dst_col, *default, *dst_var,
                );
            }
            Instr::Lookup {
                table,
                args,
                dst_col,
                dst_var,
            } => {
                let table = &self.db.table_info[*table].table;
                table.lookup_row_vectorized(mask, bindings, args, *dst_col, *dst_var);
            }

            Instr::LookupWithFallback {
                table: table_id,
                table_key,
                func,
                func_args,
                dst_col,
                dst_var,
            } => {
                let table = &self.db.table_info[*table_id].table;
                let mut lookup_result = mask.clone();
                table.lookup_row_vectorized(
                    &mut lookup_result,
                    bindings,
                    table_key,
                    *dst_col,
                    *dst_var,
                );
                let mut to_call_func = lookup_result.clone();
                to_call_func.symmetric_difference(mask);
                if to_call_func.is_empty() {
                    return;
                }

                // Call the given external function on all entries where the lookup failed.
                invoke_batch_assign(
                    self.db.external_funcs[*func].as_ref(),
                    self,
                    &mut to_call_func,
                    bindings,
                    func_args,
                    *dst_var,
                );
                // The new mask should be the lanes where the lookup succeeded or where `func`
                // succeeded.
                lookup_result.union(&to_call_func);
                *mask = lookup_result;
            }
            Instr::Insert { table, vals } => {
                if let Some(receipts) = self.db.causal_receipts {
                    let mut causes = vec![None; bindings.matches];
                    let mut cause_mask = mask.clone();
                    cause_mask.empty_iter().for_each_indexed(|offset, ()| {
                        causes[offset] = Some(bindings.deferred_equality_cause(offset, receipts));
                    });
                    for_each_binding_with_mask!(mask, vals.as_slice(), bindings, |iter| {
                        iter.for_each_indexed(|offset, vals| {
                            self.set_active_deferred_cause(causes[offset].clone());
                            self.stage_insert(*table, vals.as_slice());
                        })
                    });
                    self.set_active_deferred_cause(None);
                } else {
                    // Keep the ordinary loop byte-for-byte equivalent to the
                    // pre-receipt action path.
                    for_each_binding_with_mask!(mask, vals.as_slice(), bindings, |iter| {
                        iter.for_each(|vals| {
                            self.stage_insert(*table, vals.as_slice());
                        })
                    });
                }
            }
            Instr::UnionWithReplay {
                table,
                left,
                right,
                timestamp,
                sort,
            } => {
                let receipts = self
                    .db
                    .causal_receipts
                    .expect("typed union instruction requires causal receipts");
                mask.empty_iter().for_each_indexed(|offset, ()| {
                    let get = |entry| match entry {
                        QueryEntry::Const(value) => value,
                        QueryEntry::Var(variable) => bindings[variable][offset],
                    };
                    let left = get(*left);
                    let right = get(*right);
                    let timestamp = get(*timestamp);
                    let cause = bindings.deferred_equality_cause(offset, receipts);
                    self.stage_union_with_deferred_cause(
                        *table, left, right, timestamp, *sort, cause,
                    );
                });
            }
            Instr::InsertIfEq { table, l, r, vals } => {
                if let Some(receipts) = self.db.causal_receipts {
                    fn get(bindings: &Bindings, entry: QueryEntry, offset: usize) -> Value {
                        match entry {
                            QueryEntry::Const(value) => value,
                            QueryEntry::Var(variable) => bindings[variable][offset],
                        }
                    }
                    let mut lanes = Vec::new();
                    let mut cause_mask = mask.clone();
                    cause_mask.empty_iter().for_each_indexed(|offset, ()| {
                        if get(bindings, *l, offset) == get(bindings, *r, offset) {
                            lanes.push(offset);
                        }
                    });
                    if !lanes.is_empty() {
                        let mut causes = vec![None; bindings.matches];
                        for offset in lanes {
                            causes[offset] =
                                Some(bindings.deferred_equality_cause(offset, receipts));
                        }
                        for_each_binding_with_mask!(mask, vals.as_slice(), bindings, |iter| {
                            iter.for_each_indexed(|offset, vals| {
                                if get(bindings, *l, offset) == get(bindings, *r, offset) {
                                    self.set_active_deferred_cause(causes[offset].clone());
                                    self.stage_insert(*table, vals.as_slice());
                                }
                            })
                        });
                    }
                    self.set_active_deferred_cause(None);
                } else {
                    match (l, r) {
                        (QueryEntry::Var(v1), QueryEntry::Var(v2)) => {
                            for_each_binding_with_mask!(mask, vals.as_slice(), bindings, |iter| {
                                iter.zip(&bindings[*v1]).zip(&bindings[*v2]).for_each(
                                    |((vals, v1), v2)| {
                                        if v1 == v2 {
                                            self.stage_insert(*table, &vals);
                                        }
                                    },
                                )
                            })
                        }
                        (QueryEntry::Var(v), QueryEntry::Const(c))
                        | (QueryEntry::Const(c), QueryEntry::Var(v)) => {
                            for_each_binding_with_mask!(mask, vals.as_slice(), bindings, |iter| {
                                iter.zip(&bindings[*v]).for_each(|(vals, cond)| {
                                    if cond == c {
                                        self.stage_insert(*table, &vals);
                                    }
                                })
                            })
                        }
                        (QueryEntry::Const(c1), QueryEntry::Const(c2)) => {
                            if c1 == c2 {
                                for_each_binding_with_mask!(
                                    mask,
                                    vals.as_slice(),
                                    bindings,
                                    |iter| {
                                        iter.for_each(|vals| {
                                            self.stage_insert(*table, &vals);
                                        })
                                    }
                                )
                            }
                        }
                    }
                }
            }
            Instr::Remove { table, args } => {
                assert!(
                    self.db.causal_receipts.is_none(),
                    "causal receipts do not support removal; failing closed"
                );
                for_each_binding_with_mask!(mask, args.as_slice(), bindings, |iter| {
                    iter.for_each(|args| {
                        self.stage_remove(*table, args.as_slice());
                    })
                });
            }
            Instr::External { func, args, dst } => {
                invoke_batch(
                    self.db.external_funcs[*func].as_ref(),
                    self,
                    mask,
                    bindings,
                    args,
                    *dst,
                );
            }
            Instr::ExternalWithFallback {
                f1,
                args1,
                f2,
                args2,
                dst,
            } => {
                let mut f1_result = mask.clone();
                invoke_batch(
                    self.db.external_funcs[*f1].as_ref(),
                    self,
                    &mut f1_result,
                    bindings,
                    args1,
                    *dst,
                );
                let mut to_call_f2 = f1_result.clone();
                to_call_f2.symmetric_difference(mask);
                if to_call_f2.is_empty() {
                    return;
                }
                // Call the given external function on all entries where the first call failed.
                invoke_batch_assign(
                    self.db.external_funcs[*f2].as_ref(),
                    self,
                    &mut to_call_f2,
                    bindings,
                    args2,
                    *dst,
                );
                // The new mask should be the lanes where either `f1` or `f2` succeeded.
                f1_result.union(&to_call_f2);
                *mask = f1_result;
            }
            Instr::ExternalWithFallbackReplay {
                f1,
                args1,
                f2,
                args2,
                dst,
                replay,
            } => {
                let receipts = self
                    .db
                    .causal_receipts
                    .cloned()
                    .expect("primitive replay promotion requires causal receipts");
                let mut f1_result = mask.clone();
                invoke_batch(
                    self.db.external_funcs[*f1].as_ref(),
                    self,
                    &mut f1_result,
                    bindings,
                    args1,
                    *dst,
                );
                promote_replay_call(&receipts, &mut f1_result, bindings, args1, *dst, replay);
                let mut to_call_f2 = f1_result.clone();
                to_call_f2.symmetric_difference(mask);
                if to_call_f2.is_empty() {
                    return;
                }
                invoke_batch_assign(
                    self.db.external_funcs[*f2].as_ref(),
                    self,
                    &mut to_call_f2,
                    bindings,
                    args2,
                    *dst,
                );
                f1_result.union(&to_call_f2);
                *mask = f1_result;
            }
            Instr::PromoteReplayCall { args, dst, replay } => {
                let receipts = self
                    .db
                    .causal_receipts
                    .expect("primitive replay promotion requires causal receipts");
                promote_replay_call(receipts, mask, bindings, args, *dst, replay);
            }
            Instr::AssertAnyNe { ops, divider } => {
                for_each_binding_with_mask!(mask, ops.as_slice(), bindings, |iter| {
                    iter.retain(|vals| {
                        vals[0..*divider]
                            .iter()
                            .zip(&vals[*divider..])
                            .any(|(l, r)| l != r)
                    })
                })
            }
            Instr::RecordCheck {
                check,
                equalities,
                as_of_edges,
            } => {
                let receipts = self
                    .db
                    .causal_receipts
                    .expect("receipt-aware check requires causal receipts");
                let premise_requests = equalities
                    .iter()
                    .flat_map(|(left, right)| [left, right])
                    .filter_map(|endpoint| match endpoint.term {
                        source @ (CheckTermSource::Premise { .. }
                        | CheckTermSource::Constructor { .. }) => Some((source, endpoint.sort)),
                        CheckTermSource::Current => None,
                    })
                    .collect::<SmallVec<[(CheckTermSource, ReplaySortId); 8]>>();
                let mut winner = None::<(
                    CausalWave,
                    SmallVec<[FactId; 4]>,
                    SmallVec<[(EqualityEndpoint, EqualityEndpoint); 4]>,
                )>;
                mask.empty_iter().for_each_indexed(|offset, ()| {
                    let (wave, premises) = bindings.check_receipt(offset);
                    let premise_terms = receipts
                        .check_premise_terms(&premises, &premise_requests)
                        .unwrap_or_else(|error| panic!("invalid exact check root: {error}"));
                    let mut premise_terms = premise_terms.into_iter();
                    let get = |entry| match entry {
                        QueryEntry::Const(value) => value,
                        QueryEntry::Var(variable) => bindings[variable][offset],
                    };
                    let mut resolve = |endpoint: CheckEndpointSpec| {
                        let raw = get(endpoint.value);
                        match endpoint.term {
                            CheckTermSource::Premise { .. }
                            | CheckTermSource::Constructor { .. } => EqualityEndpoint {
                                sort: endpoint.sort,
                                term: premise_terms
                                    .next()
                                    .expect("one term for every premise endpoint"),
                                raw,
                            },
                            CheckTermSource::Current => receipts
                                .equality_endpoint(endpoint.sort, raw)
                                .unwrap_or_else(|error| {
                                    panic!("invalid exact check root: {error}")
                                }),
                        }
                    };
                    let resolved = equalities
                        .iter()
                        .map(|&(left, right)| (resolve(left), resolve(right)))
                        .collect::<SmallVec<[(EqualityEndpoint, EqualityEndpoint); 4]>>();
                    debug_assert!(premise_terms.next().is_none());
                    let replace = winner.as_ref().is_none_or(|current| {
                        (wave, premises.as_slice(), resolved.as_slice())
                            < (current.0, current.1.as_slice(), current.2.as_slice())
                    });
                    if replace {
                        winner = Some((wave, premises, resolved));
                    }
                });
                let (wave, premises, resolved) =
                    winner.expect("nonempty check mask has one exact candidate");
                receipts
                    .record_check_root(*check, wave, &premises, &resolved, *as_of_edges)
                    .unwrap_or_else(|error| panic!("invalid exact check root: {error}"));
            }
            Instr::AssertEq(l, r) => assert_impl(bindings, mask, l, r, |l, r| l == r),
            Instr::AssertNe(l, r) => assert_impl(bindings, mask, l, r, |l, r| l != r),
            Instr::ReadCounter { counter, dst } => {
                let mut vals = with_pool_set(|ps| ps.get::<Vec<Value>>());
                let ctr_val = Value::from_usize(self.read_counter(*counter));
                vals.resize(bindings.matches, ctr_val);
                bindings.insert(*dst, &vals);
                if let (Some(receipts), Some(sort)) =
                    (self.db.causal_receipts, bindings.current_binding_sort(*dst))
                {
                    let term = receipts.lookup_term(sort, ctr_val).unwrap_or_else(|| {
                        panic!("counter value has no producer-installed ReplayTermId")
                    });
                    for lane in 0..bindings.matches {
                        bindings.record_produced_term(*dst, lane, term);
                    }
                }
            }
        }
    }
}

fn promote_replay_call(
    receipts: &CausalReceipts,
    mask: &mut Mask,
    bindings: &mut Bindings,
    args: &[QueryEntry],
    dst: Variable,
    replay: &ReplayConstructorSpec,
) {
    assert_eq!(
        replay.child_sorts.len(),
        args.len(),
        "primitive replay metadata needs one sort per argument"
    );
    receipts
        .register_spec_container_type(replay)
        .expect("pure primitive replay sort has conflicting container metadata");
    let outputs = bindings[dst].to_vec();
    mask.iter(&outputs).for_each_indexed(|offset, output| {
        let mut children = SmallVec::<[ReplayTermId; 4]>::new();
        for (sort, arg) in replay.child_sorts.iter().copied().zip(args) {
            children.push(bindings.replay_term_for_entry(*arg, sort, offset, receipts));
        }
        let term = receipts
            .intern_spec_call(replay, &children, *output)
            .expect("pure primitive call must install a typed output");
        bindings.record_produced_term(dst, offset, term);
    });
}

#[derive(Debug, Clone)]
pub(crate) enum Instr {
    /// Look up the value of the given table, inserting a new entry with a
    /// default value if it is not there.
    LookupOrInsertDefault {
        table: TableId,
        args: Vec<QueryEntry>,
        default: Vec<WriteVal>,
        dst_col: ColumnId,
        dst_var: Variable,
    },

    /// Receipt-only constructor producer. Ordinary rules use the distinct
    /// variant above and never touch replay-term metadata or storage.
    LookupOrInsertDefaultReplay {
        table: TableId,
        args: Vec<QueryEntry>,
        default: Vec<WriteVal>,
        dst_col: ColumnId,
        dst_var: Variable,
        replay: Box<ReplayConstructorSpec>,
    },

    /// Look up the value of the given table; if the value is not there, use the
    /// given default.
    LookupWithDefault {
        table: TableId,
        args: Vec<QueryEntry>,
        dst_col: ColumnId,
        dst_var: Variable,
        default: QueryEntry,
    },

    /// Look up a value of the given table, halting execution if it is not
    /// there.
    Lookup {
        table: TableId,
        args: Vec<QueryEntry>,
        dst_col: ColumnId,
        dst_var: Variable,
    },

    /// Look up the given key in the table: if the value is not present in the given table, then
    /// call the given external function with the given arguments. If the external function returns
    /// a value, that value is returned in the given `dst_var`. If the lookup fails and the
    /// external function does not return a value, then execution is halted.
    LookupWithFallback {
        table: TableId,
        table_key: Vec<QueryEntry>,
        func: ExternalFunctionId,
        func_args: Vec<QueryEntry>,
        dst_col: ColumnId,
        dst_var: Variable,
    },

    /// Insert the given return value value with the provided arguments into the
    /// table.
    Insert {
        table: TableId,
        vals: Vec<QueryEntry>,
    },

    /// Receipt-only typed staging for the native equality table.
    UnionWithReplay {
        table: TableId,
        left: QueryEntry,
        right: QueryEntry,
        timestamp: QueryEntry,
        sort: ReplaySortId,
    },

    /// Terminal receipt-only action for one successful positive check.
    RecordCheck {
        check: u32,
        equalities: Box<[(CheckEndpointSpec, CheckEndpointSpec)]>,
        as_of_edges: EqualityEdgeCount,
    },

    /// Insert `vals` into `table` if `l` and `r` are equal.
    InsertIfEq {
        table: TableId,
        l: QueryEntry,
        r: QueryEntry,
        vals: Vec<QueryEntry>,
    },

    /// Remove the entry corresponding to `args` in `func`.
    Remove {
        table: TableId,
        args: Vec<QueryEntry>,
    },

    /// Bind the result of the external function to a variable.
    External {
        func: ExternalFunctionId,
        args: Vec<QueryEntry>,
        dst: Variable,
    },

    /// Bind the result of the external function to a variable. If the first external function
    /// fails, then use the second external function. If both fail, execution is haulted, (as in a
    /// single failure of `External`).
    ExternalWithFallback {
        f1: ExternalFunctionId,
        args1: Vec<QueryEntry>,
        f2: ExternalFunctionId,
        args2: Vec<QueryEntry>,
        dst: Variable,
    },

    /// Receipt-only fallback call. Only successful lanes from the primary
    /// primitive are promoted, so a returning fallback cannot be mislabeled as
    /// an invocation of `f1`.
    ExternalWithFallbackReplay {
        f1: ExternalFunctionId,
        args1: Vec<QueryEntry>,
        f2: ExternalFunctionId,
        args2: Vec<QueryEntry>,
        dst: Variable,
        replay: Box<ReplayConstructorSpec>,
    },

    /// Receipt-only promotion of an already-computed pure primitive result to
    /// one hash-consed structural replay term. This never executes the
    /// primitive or stages an effect.
    PromoteReplayCall {
        args: Vec<QueryEntry>,
        dst: Variable,
        replay: Box<ReplayConstructorSpec>,
    },

    /// Continue execution iff the two variables are equal.
    AssertEq(QueryEntry, QueryEntry),

    /// Continue execution iff the two variables are not equal.
    AssertNe(QueryEntry, QueryEntry),

    /// For the two slices: ops[0..divider] and ops[divider..], continue
    /// execution iff there is one pair of values at the same offset that are
    /// not equal.
    AssertAnyNe {
        ops: Vec<QueryEntry>,
        divider: usize,
    },

    /// Read the value of a counter and write it to the given variable.
    ReadCounter {
        /// The counter to broadcast.
        counter: CounterId,
        /// The variable to write the value to.
        dst: Variable,
    },
}
