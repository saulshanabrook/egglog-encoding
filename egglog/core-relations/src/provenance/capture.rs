//! Hot trace capture and barrier-local publication.
//!
//! Capture does not construct explanations or perform backward slicing.

use super::*;

#[path = "view.rs"]
mod view;

pub use view::*;

struct ActiveTraceViewGuard<'a> {
    active: &'a AtomicBool,
}

impl<'a> ActiveTraceViewGuard<'a> {
    fn enter(active: &'a AtomicBool) -> Result<Self, TraceViewError> {
        active
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .map(|_| Self { active })
            .map_err(|_| {
                TraceViewError::Invalid("causal capture inspection is not reentrant".into())
            })
    }
}

impl Drop for ActiveTraceViewGuard<'_> {
    fn drop(&mut self) {
        self.active.store(false, Ordering::Release);
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct AppliedEqualityProposal {
    pub(crate) left: PendingEqualityEndpoint,
    pub(crate) right: PendingEqualityEndpoint,
}

#[derive(Clone, Copy, Debug)]
struct FlatRange {
    start: u32,
    len: u32,
}

impl FlatRange {
    fn new(start: usize, len: usize) -> Self {
        Self {
            start: start.try_into().expect("trace arena exceeds u32"),
            len: len.try_into().expect("capture range exceeds u32"),
        }
    }

    fn as_range(self) -> std::ops::Range<usize> {
        let start = self.start as usize;
        start..start + self.len as usize
    }

    fn shifted(self, offset: usize) -> Self {
        Self::new(self.as_range().start + offset, self.len as usize)
    }
}

/// An action-batch-owned resolver for compact join witnesses. Implementations
/// retain the immutable materialization DAGs needed by their lanes; the
/// trace arena resolves the complete batch exactly once when native head
/// execution begins.
pub(crate) trait PendingPremiseResolver: Send + Sync {
    fn resolve(&self, lane: u32) -> SmallVec<[FactId; 4]>;

    fn resolve_batch(&self, lanes: &[u32], premise_arity: usize) -> Box<[FactId]> {
        let mut premises = Vec::with_capacity(
            lanes
                .len()
                .checked_mul(premise_arity)
                .expect("observed premise slab exceeds usize"),
        );
        for &lane in lanes {
            let resolved = self.resolve(lane);
            assert_eq!(resolved.len(), premise_arity);
            premises.extend_from_slice(&resolved);
        }
        premises.into_boxed_slice()
    }
}

/// A compact, cloneable handle for one contiguous batch of already-published
/// firings. Native head execution can cite each lane without another promotion
/// allocation or a pending-batch lifetime.
#[derive(Clone)]
pub(crate) struct ObservedFiringBatch {
    trace: Trace,
    first: FiringId,
    lanes: u32,
    wave: Wave,
}

#[derive(Clone)]
pub(crate) struct PendingFiringCause {
    trace: Trace,
    firing: FiringId,
    wave: Wave,
}

#[derive(Clone)]
pub(crate) struct PendingNativeLease(Arc<PendingNativeLeaseInner>);

struct PendingNativeLeaseInner {
    trace: Trace,
    wave: Wave,
}

impl Drop for PendingNativeLeaseInner {
    fn drop(&mut self) {
        self.trace
            .0
            .open_native_leases
            .fetch_sub(1, Ordering::Release);
    }
}

impl PendingNativeLease {
    pub(crate) fn matches(&self, trace: &Trace, wave: Wave) -> bool {
        Arc::ptr_eq(&self.0.trace.0, &trace.0) && self.0.wave == wave
    }
}

impl PendingFiringCause {
    pub(crate) fn promote(&self) -> PackedCauseRef {
        PackedCauseRef::rule(self.firing)
    }

    fn prepare(&self, trace: &Trace, current_wave: Wave) -> Result<(), String> {
        if !Arc::ptr_eq(&self.trace.0, &trace.0) {
            return Err(format!(
                "observed firing {:?} belongs to another causal trace arena",
                self.firing
            ));
        }
        if self.wave != current_wave {
            return Err(format!(
                "observed firing {:?} from wave {:?} was used in wave {:?}",
                self.firing, self.wave, current_wave
            ));
        }
        if self
            .trace
            .0
            .poisoned_rule_executions
            .load(Ordering::Acquire)
            != 0
        {
            return Err("firing belongs to a panicking execution".into());
        }
        Ok(())
    }

    fn record_merge_read(&self, prior_fact: FactId) {
        self.trace.record_firing_merge_read(self.firing, prior_fact);
    }
}

/// Opaque, prevalidated description of one semantic table rekey.
///
/// The table layer carries this value across its native remove/insert decision.
/// Capture publishes the retained rekey only after that decision supplies the
/// final [`RekeyOutcome`]; a pure move therefore need not allocate a cause.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct PreparedRekey {
    table: TableId,
    wave: Wave,
    prior_fact: FactId,
    /// Inclusive global history high-water captured before the rekey mutates
    /// native state. Unlike the rekey event position, zero is valid here.
    position: HistoryPosition,
    equalities: SmallVec<[TypedCellEquality; 4]>,
}

impl PreparedRekey {
    pub(crate) fn prior_fact(&self) -> FactId {
        self.prior_fact
    }

    pub(crate) fn metadata(
        &self,
    ) -> (TableId, Wave, FactId, HistoryPosition, &[TypedCellEquality]) {
        (
            self.table,
            self.wave,
            self.prior_fact,
            self.position,
            &self.equalities,
        )
    }

    pub(crate) fn from_staged(
        table: TableId,
        wave: Wave,
        prior_fact: FactId,
        position: HistoryPosition,
        equalities: &[TypedCellEquality],
    ) -> Self {
        Self {
            table,
            wave,
            prior_fact,
            position,
            equalities: SmallVec::from_slice(equalities),
        }
    }
}

/// Cause representation accepted by the equality staging path. Existing
/// rebuild/container callers keep their ready draft; ordinary rule unions use
/// the pending form until preflight proves them effective.
#[derive(Clone)]
enum DeferredEqualityCauseKind {
    Ready {
        cause: PackedCauseRef,
        equality: Option<EqualityCauseSummary>,
    },
    Pending(PendingFiringCause),
    Merge(Arc<PendingMergeCause>),
}

struct PendingMergeCause {
    trace: Trace,
    incoming: DeferredEqualityCause,
    prior_fact: FactId,
    history_cutoff: HistoryPosition,
    equality: EqualityCauseSummary,
    cause: OnceLock<PackedCauseRef>,
}

/// Opaque cause carrier for one staged native mutation.
///
/// The carrier may hold an already durable cause or a rule/merge cause whose
/// detail is promoted only if prepared equality work changes native state.
/// Redundant work therefore need not materialize an additional shared cause.
#[doc(hidden)]
#[derive(Clone)]
pub struct DeferredEqualityCause(DeferredEqualityCauseKind);

impl DeferredEqualityCause {
    pub(crate) fn ready(cause: impl Into<PackedCauseRef>) -> Self {
        let cause = cause.into();
        assert!(
            !cause.is_unattributed(),
            "typed equality proposal is missing its exact cause"
        );
        Self(DeferredEqualityCauseKind::Ready {
            cause,
            equality: None,
        })
    }

    pub(crate) fn capability(cause: CauseCapability) -> Self {
        Self(DeferredEqualityCauseKind::Ready {
            cause: PackedCauseRef::node(cause.id),
            equality: Some(cause.equality),
        })
    }

    pub(crate) fn promote(&self) -> PackedCauseRef {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => *cause,
            DeferredEqualityCauseKind::Pending(cause) => cause.promote(),
            DeferredEqualityCauseKind::Merge(cause) => *cause
                .cause
                .get_or_init(|| cause.trace.promote_pending_merge_cause(cause)),
        }
    }

    pub(crate) fn ready_id(&self) -> Option<PackedCauseRef> {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => Some(*cause),
            DeferredEqualityCauseKind::Pending(_) | DeferredEqualityCauseKind::Merge(_) => None,
        }
    }

    fn originating_rule(&self) -> Option<FiringId> {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => cause.firing(),
            DeferredEqualityCauseKind::Pending(cause) => Some(cause.firing),
            DeferredEqualityCauseKind::Merge(cause) => cause.incoming.originating_rule(),
        }
    }

    pub(crate) fn pending(cause: PendingFiringCause) -> Self {
        Self(DeferredEqualityCauseKind::Pending(cause))
    }

    /// Attach a table merge callback's immutable predecessor to the incoming
    /// replay owner without promoting it. Nested merge causes preserve the
    /// original incoming firing or source command as their attribution owner.
    pub(crate) fn record_merge_read(&self, trace: &Trace, prior_fact: FactId) {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => {
                trace.record_ready_merge_read(*cause, prior_fact)
            }
            DeferredEqualityCauseKind::Pending(cause) => cause.record_merge_read(prior_fact),
            DeferredEqualityCauseKind::Merge(cause) => {
                cause.incoming.record_merge_read(trace, prior_fact)
            }
        }
    }

    fn equality_summary(&self, trace: &Trace) -> EqualityCauseSummary {
        match &self.0 {
            DeferredEqualityCauseKind::Ready {
                cause: _,
                equality: Some(equality),
            } => *equality,
            DeferredEqualityCauseKind::Ready {
                cause,
                equality: None,
            } => {
                if cause.firing().is_some() {
                    return EqualityCauseSummary::Rule;
                }
                let arena = trace.0.arena.lock().unwrap();
                arena
                    .cause_summary(cause.cause_node().expect("ready cause has no node id"))
                    .unwrap_or_else(|error| panic!("cannot classify deferred cause: {error}"))
            }
            DeferredEqualityCauseKind::Pending(_) => EqualityCauseSummary::Rule,
            DeferredEqualityCauseKind::Merge(cause) => cause.equality,
        }
    }

    pub(crate) fn prepare(&self, trace: &Trace, current_wave: Wave) -> Result<(), String> {
        self.equality_summary(trace)
            .validate()
            .map_err(str::to_owned)?;
        self.prepare_dependencies(trace, current_wave)
    }

    fn prepare_dependencies(&self, trace: &Trace, current_wave: Wave) -> Result<(), String> {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => match cause.firing() {
                Some(firing) => trace.prepare_firing(firing, current_wave),
                None => Ok(()),
            },
            DeferredEqualityCauseKind::Pending(cause) => cause.prepare(trace, current_wave),
            // A direct rebuild is invalid as a root equality cause but valid
            // beneath a merge that supplies its prior fact. Prepare its lazy
            // payload without re-validating the child as a standalone root.
            DeferredEqualityCauseKind::Merge(cause) => {
                cause.incoming.prepare_dependencies(trace, current_wave)
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreparedRemoval {
    Tracked {
        removed_fact: FactId,
        cause: FiringId,
    },
    PresenceRelation,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EqualityCauseError {
    Source,
    Mixed,
}

impl EqualityCauseError {
    fn message(self) -> &'static str {
        match self {
            EqualityCauseError::Source => {
                "unsupported equality cause: source trace cannot justify a union"
            }
            EqualityCauseError::Mixed => {
                "unsupported equality cause: merge DAG mixes rule and rebuild proposals"
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EqualityCauseSummary {
    Source,
    Rule,
    Container {
        position: HistoryPosition,
    },
    Rebuild {
        position: HistoryPosition,
        complete: bool,
    },
    Invalid(EqualityCauseError),
}

impl EqualityCauseSummary {
    fn through_merge(self) -> Self {
        match self {
            Self::Rule => Self::Rule,
            Self::Container { .. } => Self::Invalid(EqualityCauseError::Mixed),
            Self::Rebuild { position, .. } => Self::Rebuild {
                position,
                complete: true,
            },
            Self::Source => Self::Invalid(EqualityCauseError::Source),
            Self::Invalid(error) => Self::Invalid(error),
        }
    }

    pub(crate) fn validate(self) -> Result<(), &'static str> {
        match self {
            Self::Rule | Self::Container { .. } => Ok(()),
            Self::Rebuild { complete: true, .. } => Ok(()),
            Self::Rebuild { .. } => {
                Err("unsupported equality cause: a direct rebuild cannot justify a union")
            }
            Self::Source => Ok(()),
            Self::Invalid(error) => Err(error.message()),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CauseCapability {
    id: CauseDraftId,
    equality: EqualityCauseSummary,
}

#[derive(Clone, Debug)]
enum DurableCause {
    Source(SourceRef),
    Rebuild {
        prior_fact: FactId,
        position: HistoryPosition,
        equalities: FlatRange,
    },
    ContainerCanonicalize {
        position: HistoryPosition,
        equalities: FlatRange,
    },
    ContainerRefresh {
        prior_fact: FactId,
        position: HistoryPosition,
        equalities: FlatRange,
    },
    Merge {
        incoming: PackedCauseRef,
        prior_fact: FactId,
        history_cutoff: HistoryPosition,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RowOriginRef {
    Site(RowOriginSiteId),
    Fact(FactId),
}

#[derive(Clone, Copy, Debug)]
enum FactOrigin {
    Site(RowOriginSiteId),
    Fact(FactId),
    Merge {
        incoming: RowOriginRef,
        prior: FactId,
    },
}

struct FactRecord {
    table: TableId,
    position: HistoryPosition,
    cause: PackedCauseRef,
    values: FlatRange,
    origin: Option<FactOrigin>,
}

struct EqualityRecord {
    position: HistoryPosition,
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    cause: PackedCauseRef,
}

#[derive(Clone, Debug)]
struct DurableFiring {
    rule: u32,
    wave: Wave,
    history_cutoff: HistoryPosition,
    premises: FlatRange,
}

#[derive(Default)]
struct TraceArena {
    facts: Vec<Option<FactRecord>>,
    durable_firings: Vec<Option<DurableFiring>>,
    durable_premises: Vec<FactId>,
    /// Sparse because ordinary firings never invoke a merge callback.
    merge_reads: HashMap<FiringId, SmallVec<[FactId; 2]>>,
    /// Sparse because most source action bundles never invoke a merge callback.
    source_merge_reads: HashMap<SourceRef, SmallVec<[FactId; 2]>>,
    durable_fact_values: Vec<Value>,
    /// Flat typed-cell equality slab shared by rebuild and container causes.
    durable_cell_equalities: Vec<TypedCellEquality>,
    durable_causes: Vec<Option<(DurableCause, EqualityCauseSummary)>>,
    durable_equalities: Vec<Option<EqualityRecord>>,
    rekeys: Vec<RekeyRecord>,
    removals: Vec<Tombstone>,
    check_roots: HashMap<u32, Criterion>,
    published_facts: u64,
    published_firings: u64,
    published_causes: u64,
    published_equalities: u64,
}

impl TraceArena {
    fn install_fact(&mut self, id: FactId, fact: FactRecord) {
        let index: usize = (id.get() - 1).try_into().expect("FactId overflow");
        if self.facts.len() <= index {
            self.facts.resize_with(index + 1, || None);
        }
        assert!(
            self.facts[index].replace(fact).is_none(),
            "duplicate FactId publication"
        );
        self.published_facts += 1;
    }

    fn install_cause(
        &mut self,
        id: CauseDraftId,
        cause: DurableCause,
        summary: EqualityCauseSummary,
    ) {
        let index = (id.get() - 1) as usize;
        if self.durable_causes.len() <= index {
            self.durable_causes.resize_with(index + 1, || None);
        }
        assert!(
            self.durable_causes[index]
                .replace((cause, summary))
                .is_none(),
            "duplicate cause-node publication"
        );
        self.published_causes += 1;
    }

    fn durable_cause(&self, id: CauseDraftId) -> Option<&DurableCause> {
        self.durable_causes
            .get((id.get().checked_sub(1)?) as usize)?
            .as_ref()
            .map(|(cause, _)| cause)
    }

    fn install_equality(&mut self, id: AppliedEqualityId, equality: EqualityRecord) {
        let index = (id.get() - 1) as usize;
        if self.durable_equalities.len() <= index {
            self.durable_equalities.resize_with(index + 1, || None);
        }
        assert!(
            self.durable_equalities[index].replace(equality).is_none(),
            "duplicate equality publication"
        );
        self.published_equalities += 1;
    }

    fn has_fact(&self, id: FactId) -> bool {
        !id.is_missing()
            && self
                .facts
                .get((id.get() - 1) as usize)
                .is_some_and(Option::is_some)
    }

    fn fact_values(&self, id: FactId) -> Option<(TableId, &[Value])> {
        if id.is_missing() {
            return None;
        }
        let fact = self.facts.get((id.get() - 1) as usize)?.as_ref()?;
        Some((
            fact.table,
            &self.durable_fact_values[fact.values.as_range()],
        ))
    }

    fn cause_summary(&self, id: CauseDraftId) -> Result<EqualityCauseSummary, &'static str> {
        self.durable_causes
            .get((id.get().checked_sub(1).ok_or("missing cause node")?) as usize)
            .and_then(Option::as_ref)
            .map(|(_, summary)| *summary)
            .ok_or("cause node has not been published")
    }

    fn originating_rule(&self, mut cause: PackedCauseRef) -> Option<FiringId> {
        loop {
            if let Some(rule) = cause.firing() {
                return Some(rule);
            }
            let node = cause.cause_node()?;
            match self.durable_cause(node)? {
                DurableCause::Merge { incoming, .. } => cause = *incoming,
                DurableCause::Source(_)
                | DurableCause::Rebuild { .. }
                | DurableCause::ContainerCanonicalize { .. }
                | DurableCause::ContainerRefresh { .. } => return None,
            }
        }
    }

    fn equality_reason(&self, root: PackedCauseRef) -> EqualityReason {
        let summary = if root.firing().is_some() {
            EqualityCauseSummary::Rule
        } else {
            self.cause_summary(root.cause_node().expect("equality cause is unattributed"))
                .expect("applied equality cause has no classification")
        };
        summary.validate().unwrap_or_else(|error| panic!("{error}"));
        if let Some(rule) = root.firing() {
            return EqualityReason::RuleUnion(rule);
        }
        let node = root.cause_node().expect("equality cause is unattributed");
        match (
            self.durable_cause(node)
                .expect("equality cause node is not durable"),
            summary,
        ) {
            (DurableCause::Source(_), EqualityCauseSummary::Source) => {
                EqualityReason::SourceUnion {
                    cause: node.public(),
                }
            }
            (_, EqualityCauseSummary::Rule) => EqualityReason::MergeFn {
                cause: node.public(),
            },
            (_, EqualityCauseSummary::Container { position }) => EqualityReason::Congruence {
                cause: node.public(),
                position,
            },
            (_, EqualityCauseSummary::Rebuild { position, .. }) => EqualityReason::Congruence {
                cause: node.public(),
                position,
            },
            _ => unreachable!("validated equality cause has no public reason"),
        }
    }
}

struct TraceShared {
    next_fact: AtomicU64,
    next_firing: AtomicU64,
    next_term: AtomicU32,
    next_equality: AtomicU64,
    next_history: AtomicU64,
    next_cause_draft: AtomicU64,
    open_fragments: AtomicUsize,
    open_native_leases: AtomicUsize,
    abandoned_fragments: AtomicU64,
    poisoned_rule_executions: AtomicU64,
    view_active: AtomicBool,
    replay_terms: TermInterner,
    equality_value_sorts: Mutex<HashMap<Value, ReplaySortId>>,
    equality_wave_timestamp: Mutex<Option<(Wave, Value)>>,
    /// One canonical source-order binding recipe per source-level rule.
    rule_binding_recipes: RwLock<HashMap<u32, Arc<[ReplayBindingSource]>>>,
    /// Every exact premise-cell/constant equality enforced by the lowered
    /// native query, including compiler-generated variables.
    rule_equality_recipes:
        RwLock<HashMap<u32, Arc<[(FiringEqualitySource, FiringEqualitySource)]>>>,
    /// Cold compile-time recipes shared by every seminaive/decomposed variant.
    static_term_recipes: Mutex<StaticTermRecipeStore>,
    /// Successful lazy projections are immutable once their fact or firing is
    /// published, so runtime container anchors and cold views can reuse them.
    term_projection_memo: Mutex<TermProjectionMemo>,
    arena: Mutex<TraceArena>,
}

impl Default for TraceShared {
    fn default() -> Self {
        Self {
            next_fact: AtomicU64::new(0),
            next_firing: AtomicU64::new(0),
            next_term: AtomicU32::new(0),
            next_equality: AtomicU64::new(0),
            next_history: AtomicU64::new(0),
            next_cause_draft: AtomicU64::new(0),
            open_fragments: AtomicUsize::new(0),
            open_native_leases: AtomicUsize::new(0),
            abandoned_fragments: AtomicU64::new(0),
            poisoned_rule_executions: AtomicU64::new(0),
            view_active: AtomicBool::new(false),
            replay_terms: TermInterner::default(),
            equality_value_sorts: Mutex::new(HashMap::default()),
            equality_wave_timestamp: Mutex::new(None),
            rule_binding_recipes: RwLock::new(HashMap::default()),
            rule_equality_recipes: RwLock::new(HashMap::default()),
            static_term_recipes: Mutex::new(StaticTermRecipeStore::default()),
            term_projection_memo: Mutex::new(TermProjectionMemo::default()),
            arena: Mutex::new(TraceArena::default()),
        }
    }
}

impl TraceShared {
    fn alloc_u64(counter: &AtomicU64, count: usize) -> u64 {
        assert!(count > 0);
        counter.fetch_add(count as u64, Ordering::Relaxed) + 1
    }
}

/// A commit-local capture batch. It performs no locking while native rows are
/// merged and publishes once at the surrounding engine barrier.
pub(crate) struct CaptureBatch {
    shared: Arc<TraceShared>,
    facts: Vec<(FactId, FactRecord)>,
    fact_values: Vec<Value>,
    equalities: Vec<(AppliedEqualityId, EqualityRecord)>,
    published: bool,
}

impl CaptureBatch {
    fn new(shared: Arc<TraceShared>) -> Self {
        shared.open_fragments.fetch_add(1, Ordering::Relaxed);
        Self {
            shared,
            facts: Vec::new(),
            fact_values: Vec::new(),
            equalities: Vec::new(),
            published: false,
        }
    }

    /// Record one effective logical fact using only its raw creation row and
    /// compact static mutation-site origin. This is the production serial
    /// path: it performs no replay-term lookup, interning, or per-row heap
    /// allocation.
    pub(crate) fn record_fact_with_origin(
        &mut self,
        table: TableId,
        cause: impl Into<PackedCauseRef>,
        row: &[Value],
        origin: RowOriginSiteId,
    ) -> FactId {
        let cause = cause.into();
        assert!(
            !cause.is_unattributed(),
            "effective commit is missing exact causal attribution"
        );
        assert_ne!(origin.get(), 0, "effective fact has no static row origin");
        self.push_fact(table, cause, row, Some(FactOrigin::Site(origin)))
    }

    /// Record a fresh immutable fact version whose structural syntax is the
    /// exact historical syntax of `prior_fact`. Container refresh republishes
    /// a row after canonicalizing a stable-id registry value; it must not lose
    /// that prior term merely because the physical table row is new.
    pub(crate) fn record_fact_from_prior(
        &mut self,
        table: TableId,
        cause: impl Into<PackedCauseRef>,
        row: &[Value],
        prior_fact: FactId,
    ) -> FactId {
        let cause = cause.into();
        assert!(
            !prior_fact.is_missing(),
            "fact-attributed commit has no immutable prior FactId"
        );
        self.push_fact(table, cause, row, Some(FactOrigin::Fact(prior_fact)))
    }

    pub(crate) fn record_fact_from_origin(
        &mut self,
        table: TableId,
        cause: impl Into<PackedCauseRef>,
        row: &[Value],
        origin: Option<RowOriginRef>,
    ) -> FactId {
        match origin {
            Some(RowOriginRef::Site(origin)) => {
                self.record_fact_with_origin(table, cause, row, origin)
            }
            Some(RowOriginRef::Fact(prior_fact)) => {
                self.record_fact_from_prior(table, cause, row, prior_fact)
            }
            None => self.push_fact(table, cause.into(), row, None),
        }
    }

    pub(crate) fn record_merged_fact(
        &mut self,
        table: TableId,
        cause: impl Into<PackedCauseRef>,
        row: &[Value],
        incoming: RowOriginRef,
        prior: FactId,
    ) -> FactId {
        let cause = cause.into();
        assert!(
            !cause.is_unattributed(),
            "effective commit is missing exact causal attribution"
        );
        assert!(
            !prior.is_missing(),
            "merged row has no immutable prior FactId"
        );
        self.push_fact(
            table,
            cause,
            row,
            Some(FactOrigin::Merge { incoming, prior }),
        )
    }

    fn push_fact(
        &mut self,
        table: TableId,
        cause: PackedCauseRef,
        row: &[Value],
        origin: Option<FactOrigin>,
    ) -> FactId {
        assert!(
            !cause.is_unattributed(),
            "effective commit is missing exact causal attribution"
        );
        let id = FactId::new(TraceShared::alloc_u64(&self.shared.next_fact, 1));
        let position = HistoryPosition::new(TraceShared::alloc_u64(&self.shared.next_history, 1));
        if let Some((last, _)) = self.facts.last() {
            debug_assert!(
                *last < id,
                "CaptureBatch FactIds must remain strictly increasing"
            );
        }
        let values = FlatRange::new(self.fact_values.len(), row.len());
        self.fact_values.extend_from_slice(row);
        self.facts.push((
            id,
            FactRecord {
                table,
                position,
                cause,
                values,
                origin,
            },
        ));
        id
    }

    pub(crate) fn record_applied_union(
        &mut self,
        proposal: AppliedEqualityProposal,
        native_parent: crate::Value,
        native_child: crate::Value,
        cause: PackedCauseRef,
    ) -> AppliedEqualityId {
        assert!(
            !cause.is_unattributed(),
            "applied union is missing exact causal attribution"
        );
        let id = AppliedEqualityId::new(TraceShared::alloc_u64(&self.shared.next_equality, 1));
        let position = HistoryPosition::new(TraceShared::alloc_u64(&self.shared.next_history, 1));
        self.equalities.push((
            id,
            EqualityRecord {
                position,
                proposal,
                native_parent,
                native_child,
                cause,
            },
        ));
        id
    }

    pub(crate) fn publish(mut self) {
        {
            let mut arena = self.shared.arena.lock().unwrap();
            let fact_value_base = arena.durable_fact_values.len();
            arena.durable_fact_values.append(&mut self.fact_values);
            for (id, mut fact) in self.facts.drain(..) {
                fact.values = fact.values.shifted(fact_value_base);
                arena.install_fact(id, fact);
            }
            for (id, equality) in self.equalities.drain(..) {
                arena.install_equality(id, equality);
            }
        }
        self.published = true;
        self.shared.open_fragments.fetch_sub(1, Ordering::Release);
    }
}

impl Drop for CaptureBatch {
    fn drop(&mut self) {
        if self.published {
            return;
        }
        if !self.facts.is_empty() || !self.fact_values.is_empty() || !self.equalities.is_empty() {
            self.shared
                .abandoned_fragments
                .fetch_add(1, Ordering::Relaxed);
        }
        self.shared.open_fragments.fetch_sub(1, Ordering::Release);
    }
}

/// Cloneable handle to the database's shared causal trace arena.
///
/// Native execution records observed firing contexts and effective mutations
/// through commit-local batches, then publishes them at engine barriers.
/// Static replay metadata and structural terms are retained independently of
/// durable record projection; explanation is deferred to [`Trace::with_view`]
/// once capture is quiescent. [`Trace::default`] creates an independent empty
/// arena; cloning shares the arena, replay catalog, term interner, and view
/// exclusion state.
#[derive(Clone, Default)]
pub struct Trace(Arc<TraceShared>);

impl Trace {
    pub(crate) fn poison_rule_execution(&self) {
        self.0
            .poisoned_rule_executions
            .fetch_add(1, Ordering::Release);
    }

    /// Inclusive high-water of the already-published logical history. Zero is
    /// the valid boundary before the first effective event; observing this
    /// counter never allocates a history event.
    pub(crate) fn history_boundary(&self) -> HistoryPosition {
        HistoryPosition::new(self.0.next_history.load(Ordering::Acquire))
    }

    pub(crate) fn register_row_origin(&self, spec: RowOriginSpec) -> RowOriginSiteId {
        let layout = self
            .0
            .replay_terms
            .table_layout(spec.table)
            .expect("row origin table has no replay layout");
        assert_eq!(
            layout.len(),
            spec.cells.len(),
            "row origin and table layout have different arities"
        );
        for (column, (sort, cell)) in layout.iter().zip(spec.cells.iter()).enumerate() {
            assert!(
                sort.is_some() || cell.is_none(),
                "engine-only row origin column {column} has structural syntax"
            );
        }
        let mut store = self.0.static_term_recipes.lock().unwrap();
        let id = RowOriginSiteId::new(
            u32::try_from(store.row_origins.len() + 1)
                .expect("causal row-origin catalog exceeds u32"),
        );
        store.row_origins.push(spec);
        id
    }

    pub(crate) fn register_term_origin(&self, spec: TermOriginSpec) -> TermOriginSiteId {
        let mut store = self.0.static_term_recipes.lock().unwrap();
        let id = TermOriginSiteId::new(
            u32::try_from(store.term_origins.len() + 1)
                .expect("causal term-origin catalog exceeds u32"),
        );
        store.term_origins.push(spec);
        id
    }

    pub(crate) fn typed_equality_proposal_from_sites(
        &self,
        wave: Wave,
        sort: ReplaySortId,
        left: Value,
        left_site: TermOriginSiteId,
        right: Value,
        right_site: TermOriginSiteId,
    ) -> Result<TypedEqualityProposal, &'static str> {
        if left_site.get() == 0 || right_site.get() == 0 {
            return Err("typed equality endpoint has no static term-origin site");
        }
        let store = self.0.static_term_recipes.lock().unwrap();
        for site in [left_site, right_site] {
            let Some(spec) = store.term_origins.get((site.get() - 1) as usize) else {
                return Err("typed equality endpoint has an unknown term-origin site");
            };
            if spec.sort != sort {
                return Err("typed equality endpoint term-origin site has the wrong sort");
            }
        }
        drop(store);
        self.typed_equality_proposal_from_refs(
            wave,
            PendingEqualityEndpoint {
                sort,
                raw: left,
                term: EqualityTermRef::Site(left_site),
            },
            PendingEqualityEndpoint {
                sort,
                raw: right,
                term: EqualityTermRef::Site(right_site),
            },
        )
    }

    pub(crate) fn register_rule_term_recipe(
        &self,
        rule: u32,
        recipe: TermRecipe,
    ) -> Arc<TermRecipe> {
        let mut store = self.0.static_term_recipes.lock().unwrap();
        if let Some(existing) = store.rules.get(&rule) {
            assert_eq!(
                existing.as_ref(),
                &recipe,
                "one causal owner registered inconsistent static term recipes"
            );
            return Arc::clone(existing);
        }
        let recipe = Arc::new(recipe);
        store.rules.insert(rule, Arc::clone(&recipe));
        recipe
    }

    /// Register and share the immutable source-order binding recipe for one
    /// source-level rule. Seminaive/decomposed variants must agree exactly.
    pub(crate) fn register_rule_binding_recipe(
        &self,
        rule: u32,
        sources: &[ReplayBindingSource],
    ) -> Arc<[ReplayBindingSource]> {
        let mut next_residual = 0u32;
        for source in sources {
            match source {
                ReplayBindingSource::Current { residual, .. } => {
                    assert_eq!(
                        *residual, next_residual,
                        "rule capture Current slots must be dense in source order"
                    );
                    next_residual += 1;
                }
                ReplayBindingSource::Constant { term } => {
                    assert!(!term.is_missing(), "rule capture constant term is missing");
                }
                ReplayBindingSource::Premise { .. } => {}
            }
        }

        let mut recipes = self.0.rule_binding_recipes.write().unwrap();
        if let Some(existing) = recipes.get(&rule) {
            assert_eq!(
                existing.as_ref(),
                sources,
                "one causal rule registered inconsistent binding recipes"
            );
            return Arc::clone(existing);
        }
        let recipe: Arc<[ReplayBindingSource]> = sources.into();
        recipes.insert(rule, Arc::clone(&recipe));
        recipe
    }

    pub(crate) fn register_rule_equality_recipe(
        &self,
        rule: u32,
        equalities: &[(FiringEqualitySource, FiringEqualitySource)],
    ) -> Arc<[(FiringEqualitySource, FiringEqualitySource)]> {
        for (left, right) in equalities {
            for source in [left, right] {
                if let FiringEqualitySource::Constant(endpoint) = source {
                    assert!(
                        !endpoint.term.is_missing(),
                        "rule equality constant term is missing"
                    );
                    assert_eq!(
                        self.replay_term(endpoint.term).map(|term| term.sort()),
                        Some(endpoint.sort),
                        "rule equality constant has the wrong replay sort"
                    );
                }
            }
        }

        let mut recipes = self.0.rule_equality_recipes.write().unwrap();
        if let Some(existing) = recipes.get(&rule) {
            assert_eq!(
                existing.as_ref(),
                equalities,
                "one causal rule registered inconsistent equality recipes"
            );
            return Arc::clone(existing);
        }
        let recipe: Arc<[(FiringEqualitySource, FiringEqualitySource)]> = equalities.into();
        recipes.insert(rule, Arc::clone(&recipe));
        recipe
    }

    pub(crate) fn pending_native_lease(&self, wave: Wave) -> PendingNativeLease {
        self.0.open_native_leases.fetch_add(1, Ordering::Relaxed);
        PendingNativeLease(Arc::new(PendingNativeLeaseInner {
            trace: self.clone(),
            wave,
        }))
    }
    /// Register the physical ordered-container type and positional child sorts
    /// represented by one logical replay sort.
    ///
    /// Repeating the same registration is idempotent. A conflicting physical
    /// type or child-sort layout is rejected.
    pub fn register_container_sort(
        &self,
        sort: ReplaySortId,
        container_type: TypeId,
        child_sorts: &[ReplaySortId],
    ) -> Result<(), &'static str> {
        self.0
            .replay_terms
            .register_container_sort(sort, container_type, child_sorts)
    }

    /// Register the logical replay sort of each physical table column.
    ///
    /// A `None` entry marks an engine-only column that has no structural replay
    /// syntax. Repeating the same layout is idempotent; a different layout for
    /// an already registered table is rejected.
    pub fn register_table_layout(
        &self,
        table: TableId,
        sorts: &[Option<ReplaySortId>],
    ) -> Result<(), &'static str> {
        self.0.replay_terms.register_table_layout(table, sorts)
    }

    /// Register the table's replay-observable keyed-row semantics.
    ///
    /// The kind determines, in particular, whether removals need durable
    /// [`Tombstone`] records. Repeating the same kind is idempotent; a
    /// conflicting kind is rejected.
    pub fn register_table_kind(
        &self,
        table: TableId,
        kind: ReplayTableKind,
    ) -> Result<(), &'static str> {
        self.0.replay_terms.register_table_kind(table, kind)
    }

    /// Register how many leading columns form the table's logical key.
    ///
    /// The replay layout must already exist, and `key_columns` must fit both
    /// that layout and the compact `u16` catalog representation. Repeating the
    /// same arity is idempotent.
    pub fn register_table_key_columns(
        &self,
        table: TableId,
        key_columns: usize,
    ) -> Result<(), &'static str> {
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("register table layout before key arity")?;
        if key_columns > layout.len() {
            return Err("table key arity exceeds the replay layout");
        }
        self.0
            .replay_terms
            .register_table_key_columns(table, key_columns)
    }

    /// Associate a table with the structural constructor produced by its rows.
    ///
    /// The metadata lets a cold view recover constructor occurrences without
    /// eagerly storing output terms per fact. Repeating an identical
    /// registration is idempotent; conflicting metadata is rejected. A
    /// declared physical container type is also registered for the result sort
    /// here, so it must agree with any prior container-sort registration. This
    /// method does not validate the constructor against the table's layout,
    /// key, or kind; their agreement is a caller invariant.
    pub fn register_table_constructor(
        &self,
        table: TableId,
        constructor: ReplayCallSpec,
    ) -> Result<(), &'static str> {
        self.0
            .replay_terms
            .register_table_constructor(table, constructor)
    }

    /// Check structural constructor metadata without changing the trace.
    ///
    /// This lets callers preflight a multi-field table registration before
    /// committing any of its independently stored metadata.
    pub fn validate_table_constructor(
        &self,
        table: TableId,
        constructor: &ReplayCallSpec,
    ) -> Result<(), &'static str> {
        self.0
            .replay_terms
            .validate_table_constructor(table, constructor)
    }

    /// Register the read-only table call that names an effective scalar merge result.
    ///
    /// Its arguments must be exactly the table's logical key columns, and its
    /// result must be the table's sole logical value column. Identical repeated
    /// registration is accepted. A table without this metadata remains valid,
    /// but a reached causal merge collision fails closed before its callback.
    pub fn register_table_merge_result(
        &self,
        table: TableId,
        result: ReplayCallSpec,
    ) -> Result<(), &'static str> {
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("register table layout before merge result")?;
        let key_columns = self
            .0
            .replay_terms
            .table_key_columns
            .get(&table)
            .map(|columns| *columns as usize)
            .ok_or("register table key arity before merge result")?;
        if result.child_sorts.len() != key_columns {
            return Err("merge-result call arguments do not match the table key arity");
        }
        if layout[..key_columns]
            .iter()
            .copied()
            .ne(result.child_sorts.iter().copied().map(Some))
        {
            return Err("merge-result call argument sorts do not match the table keys");
        }
        if layout.get(key_columns).copied().flatten() != Some(result.result_sort) {
            return Err("merge-result call sort does not match the table output");
        }
        if layout[key_columns + 1..].iter().any(Option::is_some) {
            return Err("causal merge-result calls require exactly one logical output");
        }
        self.0
            .replay_terms
            .register_table_merge_result(table, result)
    }

    pub(crate) fn table_column_sort(&self, table: TableId, column: usize) -> Option<ReplaySortId> {
        self.0
            .replay_terms
            .table_layouts
            .get(&table)?
            .get(column)
            .copied()
            .flatten()
    }

    pub(crate) fn table_replay_layout(
        &self,
        table: TableId,
    ) -> Option<Arc<[Option<ReplaySortId>]>> {
        self.0.replay_terms.table_layout(table)
    }

    pub(crate) fn table_kind(&self, table: TableId) -> Option<ReplayTableKind> {
        self.0
            .replay_terms
            .table_kinds
            .get(&table)
            .map(|kind| *kind)
    }

    pub(crate) fn table_constructor(&self, table: TableId) -> Option<ReplayCallSpec> {
        self.0
            .replay_terms
            .table_constructors
            .get(&table)
            .map(|constructor| constructor.clone())
    }

    pub(crate) fn validate_merge_result(
        &self,
        table: TableId,
        incoming_available: bool,
    ) -> Result<(), &'static str> {
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("merge table has no replay layout")?;
        let key_columns = self
            .0
            .replay_terms
            .table_key_columns
            .get(&table)
            .map(|columns| *columns as usize)
            .ok_or("merge table has no replay key arity")?;
        let table_kind = self
            .0
            .replay_terms
            .table_kinds
            .get(&table)
            .map(|kind| *kind)
            .ok_or("merge table has no replay semantics")?;
        let result_required = table_kind != ReplayTableKind::PresenceRelation
            && layout[key_columns..].iter().any(Option::is_some);
        if result_required && !self.0.replay_terms.table_merge_results.contains_key(&table) {
            return Err("merge reached an unsupported structural result expression");
        }
        if !incoming_available {
            return Err("merge incoming row has no exact structural origin");
        }
        Ok(())
    }

    /// Whether rebuild must prove that no table collision reaches this merge
    /// before publishing its removal/rekey batch. Fully supported bridge
    /// tables do not need the extra key set. Missing scalar result metadata is
    /// reached semantics, so its collision must fail while the rebuild
    /// transaction is still abortable.
    pub(crate) fn requires_collision_preflight(&self, table: TableId) -> bool {
        self.validate_merge_result(table, true).is_err()
    }

    /// Whether an effective physical row replacement changes any
    /// replay-visible logical column. Timestamp and subsumption columns have
    /// no replay sort, so a mark-only subsume keeps the prior immutable
    /// FactId and does not promote its firing.
    pub(crate) fn logical_row_changed(
        &self,
        table: TableId,
        prior: &[Value],
        next: &[Value],
    ) -> Result<bool, &'static str> {
        if prior.len() != next.len() {
            return Err("logical row comparison has different arities");
        }
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("logical row comparison table has no replay layout")?;
        if layout.len() != prior.len() {
            return Err("logical row comparison and replay layout have different arities");
        }
        Ok(layout
            .iter()
            .enumerate()
            .any(|(column, sort)| sort.is_some() && prior[column] != next[column]))
    }

    /// Capture one history landmark at a native maintenance barrier.
    /// Every allocated equality before the landmark must already have been
    /// published without holes.
    pub(crate) fn maintenance_landmark(&self) -> Result<HistoryPosition, &'static str> {
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild with open capture fragments");
        }
        if self.0.abandoned_fragments.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild after an abandoned capture fragment");
        }
        let count = self.0.next_equality.load(Ordering::Acquire);
        let arena = self.0.arena.lock().unwrap();
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err("capture fragment opened while capturing a rebuild history landmark");
        }
        if count != arena.published_equalities {
            return Err("rebuild history landmark does not contain one complete equality prefix");
        }
        Ok(self.history_boundary())
    }

    pub(crate) fn validate_deferred_equality_cause(
        &self,
        cause: &DeferredEqualityCause,
    ) -> Result<(), &'static str> {
        cause.equality_summary(self).validate()
    }

    /// Validate one effective keyed-row removal before native state changes.
    /// Missing rows never reach this method. Source/top-level removals have no
    /// originating rule and therefore fail closed before staging can commit.
    pub(crate) fn prepare_removal(
        &self,
        table: TableId,
        wave: Wave,
        removed_fact: FactId,
        cause: &DeferredEqualityCause,
    ) -> Result<PreparedRemoval, String> {
        if removed_fact.is_missing() {
            return Err("effective removal has no immutable victim FactId".into());
        }
        cause.prepare(self, wave)?;
        let cause = cause.originating_rule().ok_or_else(|| {
            "causal trace support named-rule removals only; source/top-level removal is unsupported"
                .to_owned()
        })?;
        let arena = self.0.arena.lock().unwrap();
        let victim = arena
            .facts
            .get((removed_fact.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or_else(|| "effective removal references an unknown victim FactId".to_owned())?;
        if victim.table != table {
            return Err("effective removal victim belongs to another table".into());
        }
        drop(arena);
        match self
            .table_kind(table)
            .ok_or_else(|| "effective removal table has no ReplayTableKind metadata".to_owned())?
        {
            ReplayTableKind::PresenceRelation => Ok(PreparedRemoval::PresenceRelation),
            ReplayTableKind::Constructor | ReplayTableKind::ValueFunction => {
                Ok(PreparedRemoval::Tracked {
                    removed_fact,
                    cause,
                })
            }
        }
    }

    /// Publish a prevalidated serial removal batch after native deletion and
    /// before the table's pending writes are merged.
    pub(crate) fn record_removals(&self, removals: impl IntoIterator<Item = PreparedRemoval>) {
        let mut tracked = Vec::new();
        for removal in removals {
            match removal {
                PreparedRemoval::Tracked {
                    removed_fact,
                    cause,
                } => tracked.push(Tombstone {
                    position: HistoryPosition::new(TraceShared::alloc_u64(&self.0.next_history, 1)),
                    removed_fact,
                    cause,
                }),
                PreparedRemoval::PresenceRelation => {}
            }
        }
        if tracked.is_empty() {
            return;
        }
        let mut arena = self.0.arena.lock().unwrap();
        arena.removals.extend(tracked);
    }

    pub(crate) fn pending_merge_cause(
        &self,
        incoming: DeferredEqualityCause,
        prior_fact: FactId,
        history_cutoff: HistoryPosition,
    ) -> DeferredEqualityCause {
        assert!(
            !prior_fact.is_missing(),
            "deferred merge capture is missing its prior FactId"
        );
        let equality = incoming.equality_summary(self).through_merge();
        DeferredEqualityCause(DeferredEqualityCauseKind::Merge(Arc::new(
            PendingMergeCause {
                trace: self.clone(),
                incoming,
                prior_fact,
                history_cutoff,
                equality,
                cause: OnceLock::new(),
            },
        )))
    }

    fn promote_pending_merge_cause(&self, cause: &PendingMergeCause) -> PackedCauseRef {
        assert!(Arc::ptr_eq(&self.0, &cause.trace.0));
        let incoming = cause.incoming.promote();
        let id = CauseDraftId::new(TraceShared::alloc_u64(&self.0.next_cause_draft, 1));
        let mut arena = self.0.arena.lock().unwrap();
        arena.install_cause(
            id,
            DurableCause::Merge {
                incoming,
                prior_fact: cause.prior_fact,
                history_cutoff: cause.history_cutoff,
            },
            cause.equality,
        );
        PackedCauseRef::node(id)
    }

    pub(crate) fn cause_capability(&self, cause: CauseDraftId) -> CauseCapability {
        let arena = self.0.arena.lock().unwrap();
        let equality = arena
            .cause_summary(cause)
            .unwrap_or_else(|error| panic!("cannot resolve active cause: {error}"));
        CauseCapability {
            id: cause,
            equality,
        }
    }

    pub(crate) fn validate_equality_wave_timestamp(
        &self,
        wave: Wave,
        timestamp: Value,
    ) -> Result<(), &'static str> {
        let mut current = self.0.equality_wave_timestamp.lock().unwrap();
        match *current {
            None => *current = Some((wave, timestamp)),
            Some((known_wave, known_timestamp)) if known_wave == wave => {
                if timestamp < known_timestamp {
                    return Err("equality timestamps decreased within one causal wave");
                }
                *current = Some((wave, timestamp));
            }
            Some((known_wave, known_timestamp)) if known_wave < wave => {
                if timestamp < known_timestamp {
                    return Err("equality timestamps decreased across causal waves");
                }
                *current = Some((wave, timestamp));
            }
            Some(_) => return Err("equality proposal returned to an earlier causal wave"),
        }
        Ok(())
    }

    /// Validate one exact semantic table rekey before its removal/insertion is
    /// staged. The returned handle owns its small landmark and allocates no
    /// cause or durable event until the native table decides its disposition.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prepare_rekey(
        &self,
        table: TableId,
        wave: Wave,
        prior_fact: FactId,
        old_row: &[Value],
        new_row: &[Value],
        rebuild_columns: &[crate::ColumnId],
        position: HistoryPosition,
    ) -> Result<PreparedRekey, &'static str> {
        if prior_fact.is_missing() {
            return Err("rebuild row has no immutable prior FactId");
        }
        let Some(layout) = self.0.replay_terms.table_layout(table) else {
            return Err("rebuild table has no replay-term layout");
        };
        if layout.len() != old_row.len() || old_row.len() != new_row.len() {
            return Err("rebuild rows and replay-term table layout have different arities");
        }

        if rebuild_columns
            .iter()
            .any(|column| column.index() >= layout.len())
        {
            return Err("rebuild column exceeds the registered table layout");
        }

        // Store only typed raw endpoints on the rebuild path. Structural terms
        // are reconstructed lazily for retained landmarks.
        let mut pairs = SmallVec::<[TypedCellEquality; 4]>::new();
        for (index, declared_sort) in layout.iter().copied().enumerate() {
            let column = crate::ColumnId::from_usize(index);
            if !rebuild_columns.contains(&column) || old_row[index] == new_row[index] {
                continue;
            }
            let Some(sort) = declared_sort else {
                return Err("changed rebuild column has no replay sort");
            };
            pairs.push(TypedCellEquality {
                column,
                left: EqualityEndpoint {
                    sort,
                    term: ReplayTermId::MISSING,
                    raw: old_row[index],
                },
                right: EqualityEndpoint {
                    sort,
                    term: ReplayTermId::MISSING,
                    raw: new_row[index],
                },
            });
        }
        if pairs.is_empty() {
            return Err("rebuild capture has no changed semantic column");
        }

        let arena = self.0.arena.lock().unwrap();
        let Some(fact) = arena
            .facts
            .get((prior_fact.get() - 1) as usize)
            .and_then(Option::as_ref)
        else {
            return Err("rebuild row references an unknown prior FactId");
        };
        if fact.table != table {
            return Err("rebuild row prior FactId belongs to another table");
        }
        drop(arena);
        Ok(PreparedRekey {
            table,
            wave,
            prior_fact,
            position,
            equalities: pairs,
        })
    }

    /// Promote a rekey cause only after the native table proves that the
    /// rekey collides with a live row and therefore enters merge execution.
    /// Pure moves never allocate a cause or copy their endpoint pairs.
    pub(crate) fn prepared_rekey_cause(&self, rekey: &PreparedRekey) -> DeferredEqualityCause {
        let mut arena = self.0.arena.lock().unwrap();
        let equalities =
            FlatRange::new(arena.durable_cell_equalities.len(), rekey.equalities.len());
        arena
            .durable_cell_equalities
            .extend_from_slice(&rekey.equalities);
        let id = CauseDraftId::new(TraceShared::alloc_u64(&self.0.next_cause_draft, 1));
        arena.install_cause(
            id,
            DurableCause::Rebuild {
                prior_fact: rekey.prior_fact,
                position: rekey.position,
                equalities,
            },
            EqualityCauseSummary::Rebuild {
                position: rekey.position,
                complete: false,
            },
        );
        DeferredEqualityCause::ready(id)
    }

    pub(crate) fn commit_prepared_rekey(&self, rekey: PreparedRekey, outcome: RekeyOutcome) {
        // Rebuild can stage two physical rows carrying the same immutable
        // logical fact. Once the first row has moved the fact to the
        // canonical key, publishing the later row collides with that same
        // FactId. This is neither another logical rekey nor the end of the
        // fact's lifetime: its endpoints describe the discarded physical
        // copy and do not continue the already-published occurrence.
        if matches!(outcome, RekeyOutcome::Absorbed(successor) | RekeyOutcome::Replaced(successor) if successor == rekey.prior_fact)
        {
            return;
        }
        let position = HistoryPosition::new(TraceShared::alloc_u64(&self.0.next_history, 1));
        let mut arena = self.0.arena.lock().unwrap();
        arena.rekeys.push(RekeyRecord {
            fact: rekey.prior_fact,
            position,
            equalities: EqualityLandmark {
                position: rekey.position,
                pairs: rekey.equalities.as_slice().into(),
            },
            outcome,
        });
    }

    /// Resolve the positional equality dependencies of one ordered container
    /// value before the registry mutates it. No explanation path is walked
    /// here; the immutable forest is unfolded lazily by the slicer.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn container_dependency(
        &self,
        journal: &ContainerAnchorJournal,
        container_type: TypeId,
        outer_raw: Value,
        wave: Wave,
        before: &[Value],
        after: &[Value],
        position: HistoryPosition,
    ) -> Result<SmallVec<[ContainerVersionDependency; 2]>, &'static str> {
        if before.len() != after.len() {
            return Err("positional container rebuild changed arity");
        }
        let value_sorts = self.0.equality_value_sorts.lock().unwrap();
        let mut typed = SmallVec::<[Option<ReplaySortId>; 4]>::new();
        for (&left, &right) in before.iter().zip(after) {
            if left == right {
                typed.push(None);
                continue;
            }
            let Some(left_sort) = value_sorts.get(&left).copied() else {
                return Err("container child before rebuild has no equality sort");
            };
            let Some(right_sort) = value_sorts.get(&right).copied() else {
                return Err("container child after rebuild has no equality sort");
            };
            if left_sort != right_sort {
                return Err("container child rebuild crossed logical sorts");
            }
            typed.push(Some(left_sort));
        }
        drop(value_sorts);

        let mut pairs = SmallVec::<[TypedCellEquality; 4]>::new();
        for (slot, ((&left, &right), sort)) in before.iter().zip(after).zip(typed).enumerate() {
            let Some(sort) = sort else {
                continue;
            };
            pairs.push(TypedCellEquality {
                column: crate::ColumnId::from_usize(slot),
                // Exact structural endpoints already exist in the applied
                // equality history at this cutoff. Keep the rebuild hook to
                // raw typed values and resolve terms only for a selected view read.
                left: EqualityEndpoint {
                    sort,
                    term: ReplayTermId::MISSING,
                    raw: left,
                },
                right: EqualityEndpoint {
                    sort,
                    term: ReplayTermId::MISSING,
                    raw: right,
                },
            });
        }
        if pairs.is_empty() {
            return Ok(SmallVec::new());
        }
        let mut outer_candidates = SmallVec::<[EqualityEndpoint; 2]>::new();
        let mut logical_sort = None;
        for entry in self.0.replay_terms.container_type_by_sort.iter() {
            if *entry.value() != container_type {
                continue;
            }
            let sort = *entry.key();
            if self
                .0
                .replay_terms
                .container_child_sorts
                .get(&sort)
                .is_none()
            {
                continue;
            }
            let anchors = self
                .0
                .replay_terms
                .container_anchors_with_journal(journal, sort, outer_raw);
            if anchors.is_empty() {
                continue;
            }
            if logical_sort
                .replace(sort)
                .is_some_and(|known| known != sort)
            {
                return Err("changed container has multiple exact logical replay sorts");
            }
            outer_candidates.extend(anchors.into_iter().map(|term| EqualityEndpoint {
                sort,
                term,
                raw: outer_raw,
            }));
        }
        if outer_candidates.is_empty() {
            return Err("changed container has no exact typed structural producer");
        }
        let dependency = Arc::new(ContainerDependency {
            wave,
            equalities: EqualityLandmark {
                position,
                pairs: pairs.into_vec().into_boxed_slice(),
            },
        });
        Ok(outer_candidates
            .into_iter()
            .map(|outer| ContainerVersionDependency {
                outer,
                dependency: Arc::clone(&dependency),
            })
            .collect())
    }

    /// Resolve one raw reverse-index candidate to an exact logical parent.
    /// The physical registry type and exact child term both have to agree;
    /// raw `Value` equality alone is never container ancestry.
    pub(crate) fn container_parent_candidates(
        &self,
        journal: &ContainerAnchorJournal,
        container_type: TypeId,
        parent_raw: Value,
    ) -> SmallVec<[ContainerParentCandidate; 2]> {
        let mut candidates = SmallVec::<[ContainerParentCandidate; 2]>::new();
        for entry in self.0.replay_terms.container_type_by_sort.iter() {
            if *entry.value() != container_type {
                continue;
            }
            let sort = *entry.key();
            let Some(child_sorts) = self
                .0
                .replay_terms
                .container_child_sorts
                .get(&sort)
                .map(|sorts| Arc::clone(&sorts))
            else {
                continue;
            };
            for term in self
                .0
                .replay_terms
                .container_anchors_with_journal(journal, sort, parent_raw)
            {
                candidates.push(ContainerParentCandidate {
                    endpoint: EqualityEndpoint {
                        sort,
                        term,
                        raw: parent_raw,
                    },
                    child_sorts: Arc::clone(&child_sorts),
                });
            }
        }
        candidates
    }

    pub(crate) fn stage_container_anchor_transfer(
        &self,
        journal: &mut ContainerAnchorJournal,
        container_type: TypeId,
        from: Value,
        to: Value,
    ) -> Result<(), &'static str> {
        self.0
            .replay_terms
            .stage_container_anchor_transfer(journal, container_type, from, to)
    }

    pub(crate) fn validate_container_anchor_journal(
        &self,
        journal: &ContainerAnchorJournal,
    ) -> Result<(), &'static str> {
        self.0
            .replay_terms
            .validate_container_anchor_journal(journal)
    }

    pub(crate) fn publish_container_anchor_journal(&self, journal: ContainerAnchorJournal) {
        self.0
            .replay_terms
            .publish_container_anchor_journal(journal);
    }

    /// Register one exact container-registry collision cause and return the
    /// only logical outer sort shared by its native ids.
    pub(crate) fn container_canonicalization_cause(
        &self,
        journal: &ContainerAnchorJournal,
        container_type: TypeId,
        wave: Wave,
        left: Value,
        right: Value,
        position: HistoryPosition,
    ) -> Result<(CauseCapability, TypedEqualityProposal), &'static str> {
        let anchor_pairs =
            self.0
                .replay_terms
                .compatible_call_pairs(journal, container_type, left, right)?;
        let value_sorts = self.0.equality_value_sorts.lock().unwrap();
        let mut candidates = SmallVec::<
            [(
                ReplaySortId,
                ReplayTermId,
                ReplayTermId,
                SmallVec<[TypedCellEquality; 4]>,
            ); 2],
        >::new();
        for (sort, left_term, right_term) in anchor_pairs {
            let Some(ReplayTerm::Call {
                children: left_children,
                ..
            }) = self.0.replay_terms.node(left_term)
            else {
                unreachable!("compatible Call sort lost its left Call")
            };
            let Some(ReplayTerm::Call {
                children: right_children,
                ..
            }) = self.0.replay_terms.node(right_term)
            else {
                unreachable!("compatible Call sort lost its right Call")
            };
            let mut pairs = SmallVec::<[TypedCellEquality; 4]>::new();
            let mut exact = true;
            for (slot, (&left_child, &right_child)) in
                left_children.iter().zip(right_children.iter()).enumerate()
            {
                if left_child == right_child {
                    continue;
                }
                let left_node = self
                    .0
                    .replay_terms
                    .node(left_child)
                    .expect("left container child term is unknown");
                let right_node = self
                    .0
                    .replay_terms
                    .node(right_child)
                    .expect("right container child term is unknown");
                let child_sort = left_node.sort();
                if right_node.sort() != child_sort {
                    exact = false;
                    break;
                }
                let Some(left_raw) = self.0.replay_terms.original_value(child_sort, left_child)
                else {
                    exact = false;
                    break;
                };
                let Some(right_raw) = self.0.replay_terms.original_value(child_sort, right_child)
                else {
                    exact = false;
                    break;
                };
                if left_raw != right_raw
                    && (value_sorts.get(&left_raw) != Some(&child_sort)
                        || value_sorts.get(&right_raw) != Some(&child_sort))
                {
                    exact = false;
                    break;
                }
                pairs.push(TypedCellEquality {
                    column: crate::ColumnId::from_usize(slot),
                    left: EqualityEndpoint {
                        sort: child_sort,
                        term: left_child,
                        raw: left_raw,
                    },
                    right: EqualityEndpoint {
                        sort: child_sort,
                        term: right_child,
                        raw: right_raw,
                    },
                });
            }
            // Distinct native container ids can already denote one hash-consed
            // structural Call. That collision is exact even without changed
            // child pairs; the UF records it as a native alias, not an
            // equality-forest edge.
            if exact && (!pairs.is_empty() || left_term == right_term) {
                candidates.push((sort, left_term, right_term, pairs));
            }
        }
        drop(value_sorts);
        let Some((sort, left_term, right_term, pairs)) = candidates.first().cloned() else {
            return Err("container ids have no exact typed Call collision");
        };
        if candidates
            .iter()
            .any(|(candidate_sort, ..)| *candidate_sort != sort)
        {
            return Err("container ids have multiple exact logical replay sorts");
        }
        let proposal = self.typed_equality_proposal_from_refs(
            wave,
            PendingEqualityEndpoint {
                sort,
                raw: left,
                term: EqualityTermRef::Exact(left_term),
            },
            PendingEqualityEndpoint {
                sort,
                raw: right,
                term: EqualityTermRef::Exact(right_term),
            },
        )?;
        let mut arena = self.0.arena.lock().unwrap();
        let equalities = FlatRange::new(arena.durable_cell_equalities.len(), pairs.len());
        arena.durable_cell_equalities.extend_from_slice(&pairs);
        let id = CauseDraftId::new(TraceShared::alloc_u64(&self.0.next_cause_draft, 1));
        let summary = EqualityCauseSummary::Container { position };
        arena.install_cause(
            id,
            DurableCause::ContainerCanonicalize {
                position,
                equalities,
            },
            summary,
        );
        Ok((
            CauseCapability {
                id,
                equality: summary,
            },
            proposal,
        ))
    }

    /// Register the exact prior fact and child equality landmark for one
    /// same-id container parent-row refresh.
    pub(crate) fn container_refresh_draft(
        &self,
        prior_fact: FactId,
        candidates: &[(crate::ColumnId, &[ContainerVersionDependency])],
    ) -> Result<CauseDraftId, &'static str> {
        if prior_fact.is_missing() {
            return Err("container refresh row has no immutable prior FactId");
        }
        let mut selected: Option<ContainerDependency> = None;
        for &(column, dependencies) in candidates {
            let fact_term = self
                .project_fact_term(prior_fact, column.index())
                .map_err(|_| "container refresh cannot reconstruct its prior structural term")?;
            for version in dependencies {
                if version.outer.term != fact_term {
                    continue;
                }
                let dependency = &version.dependency;
                match &mut selected {
                    None => selected = Some(dependency.as_ref().clone()),
                    Some(current) => {
                        if current.wave != dependency.wave
                            || current.equalities.position != dependency.equalities.position
                        {
                            return Err(
                                "one row refresh combines incompatible container landmarks",
                            );
                        }
                        let mut pairs = current.equalities.pairs.to_vec();
                        for pair in &dependency.equalities.pairs {
                            if !pairs.contains(pair) {
                                pairs.push(*pair);
                            }
                        }
                        current.equalities.pairs = pairs.into_boxed_slice();
                    }
                }
            }
        }
        let Some(dependency) = selected else {
            return Err("container refresh prior FactId matches no exact structural version");
        };
        if dependency.equalities.pairs.is_empty() {
            return Err("container refresh has no child dependency");
        }
        let mut arena = self.0.arena.lock().unwrap();
        let equalities = FlatRange::new(
            arena.durable_cell_equalities.len(),
            dependency.equalities.pairs.len(),
        );
        arena
            .durable_cell_equalities
            .extend_from_slice(&dependency.equalities.pairs);
        let id = CauseDraftId::new(TraceShared::alloc_u64(&self.0.next_cause_draft, 1));
        arena.install_cause(
            id,
            DurableCause::ContainerRefresh {
                prior_fact,
                position: dependency.equalities.position,
                equalities,
            },
            EqualityCauseSummary::Invalid(EqualityCauseError::Mixed),
        );
        Ok(id)
    }

    /// Intern a typed structural literal and associate it with one raw value.
    ///
    /// Raw-value lookup is first-wins, but this method returns the exact
    /// requested literal node. This distinction preserves source spellings
    /// such as `0.0` versus `-0.0` even when the native value arena gives them
    /// one identity. Structurally identical nodes share one [`ReplayTermId`].
    pub fn intern_literal(
        &self,
        sort: ReplaySortId,
        literal: ReplayLiteral,
        value: Value,
    ) -> ReplayTermId {
        let term = self
            .0
            .replay_terms
            .intern(&self.0.next_term, ReplayTerm::Literal { sort, literal });
        self.0
            .replay_terms
            .install_value(sort, value, term)
            .expect("newly interned literal must have a matching sort");
        term
    }

    /// Intern a typed structural call and associate it with one raw value.
    ///
    /// Every child must already be interned. Call nodes are structurally
    /// deduplicated, and the exact call id is returned. The independent
    /// `(sort, value)` reverse mapping remains first-wins, so
    /// [`Trace::lookup_term`] may return an earlier term for the same raw value.
    /// Operator arity and child sorts are caller invariants.
    pub(crate) fn intern_call(
        &self,
        sort: ReplaySortId,
        op: ReplayOpId,
        children: &[ReplayTermId],
        value: Value,
    ) -> Result<ReplayTermId, &'static str> {
        if children
            .iter()
            .any(|child| self.0.replay_terms.node(*child).is_none())
        {
            return Err("call has an unknown ReplayTermId child");
        }
        let term = self.0.replay_terms.intern(
            &self.0.next_term,
            ReplayTerm::Call {
                sort,
                op,
                children: children.into(),
            },
        );
        self.0.replay_terms.install_value(sort, value, term)?;
        Ok(term)
    }

    /// Intern a call using its registered producer metadata.
    ///
    /// This uses the call specification's result sort, operation, and optional
    /// container type. Every child id must exist, but this method does not
    /// validate child arity or sorts against `spec.child_sorts`; the
    /// caller must supply those children in the registered order. Container
    /// producers also retain an exact structural-version anchor for the raw id.
    /// This method records the call immediately regardless of whether the
    /// producer is configured to anchor on primitive return.
    pub fn intern_spec_call(
        &self,
        spec: &ReplayCallSpec,
        children: &[ReplayTermId],
        value: Value,
    ) -> Result<ReplayTermId, &'static str> {
        self.0.replay_terms.register_container_type(spec)?;
        let term = self.intern_call(spec.result_sort, spec.op, children, value)?;
        if spec.container_type.is_some() {
            self.0
                .replay_terms
                .install_container_anchor(spec.result_sort, value, term)?;
        }
        Ok(term)
    }

    /// Return the first structural term installed for a typed raw value.
    ///
    /// Mutable containers can have additional exact versions in the internal
    /// anchor index; this generic lookup intentionally returns only the stable
    /// first-wins mapping.
    pub(crate) fn lookup_term(&self, sort: ReplaySortId, value: Value) -> Option<ReplayTermId> {
        self.0.replay_terms.lookup(sort, value)
    }

    /// Whether `term` was installed from this exact typed native value.
    ///
    /// This accepts structural spellings that share one native value even
    /// when the stable reverse lookup above points at an earlier spelling.
    pub fn term_matches_value(&self, sort: ReplaySortId, value: Value, term: ReplayTermId) -> bool {
        self.0.replay_terms.original_value(sort, term) == Some(value)
    }

    #[cfg(test)]
    pub(crate) fn equality_endpoint(
        &self,
        sort: ReplaySortId,
        raw: Value,
    ) -> Result<EqualityEndpoint, &'static str> {
        let term = self
            .lookup_term(sort, raw)
            .ok_or("typed endpoint has no ReplayTermId for its declared sort")?;
        Ok(EqualityEndpoint { sort, term, raw })
    }

    pub(crate) fn check_premise_endpoints(
        &self,
        premises: &[FactId],
        requests: &[(CheckTermSource, ReplaySortId)],
    ) -> Result<SmallVec<[EqualityEndpoint; 8]>, String> {
        enum Lookup {
            Direct {
                term: ReplayTermId,
                raw: Value,
                sort: ReplaySortId,
            },
            Constructor {
                premise: usize,
                fact: FactId,
                column: usize,
                term: ReplayTermId,
                raw: Value,
                sort: ReplaySortId,
                op: ReplayOpId,
            },
        }

        let lookups = {
            let recipes = self.0.rule_binding_recipes.read().unwrap();
            let term_recipes = self.0.static_term_recipes.lock().unwrap();
            let arena = self.0.arena.lock().unwrap();
            let mut projection_memo = self.0.term_projection_memo.lock().unwrap();
            let mut projector = TermProjector::new(
                &arena,
                &recipes,
                &term_recipes,
                &self.0.replay_terms,
                &self.0.next_term,
                &mut projection_memo,
            );
            let mut lookups = SmallVec::<[Lookup; 8]>::new();
            for &(request, sort) in requests {
                match request {
                    CheckTermSource::Premise { premise, column } => {
                        let fact = *premises.get(premise).ok_or_else(|| {
                            "check endpoint cites a missing premise slot".to_owned()
                        })?;
                        let term = projector.fact_term(fact, column).map_err(|_| {
                            "check endpoint has no reconstructible fact term".to_owned()
                        })?;
                        let raw = arena
                            .fact_values(fact)
                            .and_then(|(_, values)| values.get(column).copied())
                            .ok_or_else(|| {
                                "check endpoint has no reconstructible fact occurrence".to_owned()
                            })?;
                        lookups.push(Lookup::Direct { term, raw, sort });
                    }
                    CheckTermSource::Constructor {
                        premise,
                        atom: _,
                        input_columns,
                        op,
                        origin,
                    } => {
                        let fact = *premises.get(premise).ok_or_else(|| {
                            "check endpoint cites a missing premise slot".to_owned()
                        })?;
                        let origin = origin.ok_or_else(|| {
                            "check constructor endpoint has no exact source-term origin".to_owned()
                        })?;
                        let spec = term_recipes
                            .term_origins
                            .get((origin.get() - 1) as usize)
                            .ok_or_else(|| {
                                "check constructor endpoint has an unknown source-term origin"
                                    .to_owned()
                            })?;
                        if spec.sort != sort {
                            return Err(
                                "check constructor source-term origin has the wrong sort".into()
                            );
                        }
                        let term = projector
                            .runtime_anchor_template(&spec.term, &[], premises)
                            .map_err(|error| {
                                format!(
                                    "check constructor source term cannot be reconstructed: {error}"
                                )
                            })?;
                        let raw = arena
                            .fact_values(fact)
                            .and_then(|(_, values)| values.get(input_columns).copied())
                            .ok_or_else(|| {
                                "check constructor producer has no exact fact occurrence".to_owned()
                            })?;
                        lookups.push(Lookup::Constructor {
                            premise,
                            fact,
                            column: input_columns,
                            term,
                            raw,
                            sort,
                            op,
                        });
                    }
                    CheckTermSource::Constant { .. } => {
                        return Err(
                            "non-premise check endpoint was requested as a premise term".into()
                        );
                    }
                }
            }
            lookups
        };

        let mut endpoints = SmallVec::<[EqualityEndpoint; 8]>::new();
        for lookup in lookups {
            let (term, raw, sort) = match lookup {
                Lookup::Direct { term, raw, sort } => {
                    let node = self.0.replay_terms.node(term).ok_or_else(|| {
                        "check endpoint fact owns an unknown ReplayTermId".to_owned()
                    })?;
                    if node.sort() != sort {
                        return Err("check endpoint fact term has the wrong declared sort".into());
                    }
                    (term, raw, sort)
                }
                Lookup::Constructor {
                    premise,
                    fact,
                    column,
                    term,
                    raw,
                    sort,
                    op,
                } => {
                    let node = self.0.replay_terms.node(term).ok_or_else(|| {
                        "check constructor output owns an unknown ReplayTermId".to_owned()
                    })?;
                    if !matches!(node, ReplayTerm::Call { sort: actual_sort, op: actual_op, .. }
                        if actual_sort == sort && actual_op == op)
                    {
                        let (fact_table, fact_origin) = {
                            let arena = self.0.arena.lock().unwrap();
                            let slot = arena
                                .facts
                                .get((fact.get() - 1) as usize)
                                .and_then(Option::as_ref);
                            slot.map_or((None, None), |fact| (Some(fact.table), fact.origin))
                        };
                        let fact_table_constructor = fact_table.and_then(|table| {
                            self.0
                                .replay_terms
                                .table_constructors
                                .get(&table)
                                .map(|constructor| (constructor.result_sort, constructor.op))
                        });
                        let origin_template = match fact_origin {
                            Some(FactOrigin::Site(site)) => self
                                .0
                                .static_term_recipes
                                .lock()
                                .unwrap()
                                .row_origins
                                .get((site.get() - 1) as usize)
                                .and_then(|origin| origin.cells.get(column))
                                .cloned()
                                .flatten(),
                            _ => None,
                        };
                        return Err(format!(
                            "check constructor output does not match its declared producer: premise={premise}, premises={premises:?}, fact={fact:?}, fact_table={fact_table:?}, fact_table_constructor={fact_table_constructor:?}, fact_origin={fact_origin:?}, origin_template={origin_template:?}, column={column}, expected_sort={sort:?}, expected_op={op:?}, term={term:?}, actual={node:?}"
                        ));
                    }
                    (term, raw, sort)
                }
            };
            endpoints.push(EqualityEndpoint { sort, term, raw });
        }
        Ok(endpoints)
    }

    pub(crate) fn project_fact_term(
        &self,
        fact: FactId,
        column: usize,
    ) -> Result<ReplayTermId, String> {
        let recipes = self.0.rule_binding_recipes.read().unwrap();
        let term_recipes = self.0.static_term_recipes.lock().unwrap();
        let arena = self.0.arena.lock().unwrap();
        let mut projection_memo = self.0.term_projection_memo.lock().unwrap();
        let mut projector = TermProjector::new(
            &arena,
            &recipes,
            &term_recipes,
            &self.0.replay_terms,
            &self.0.next_term,
            &mut projection_memo,
        );
        projector.fact_term(fact, column)
    }

    pub(crate) fn with_container_anchor_installer<R>(
        &self,
        site: TermOriginSiteId,
        replay: &ReplayCallSpec,
        f: impl FnOnce(
            &mut dyn FnMut(
                &[ReplayBindingSource],
                &[FactId],
                &[Value],
                Value,
            ) -> Result<ReplayTermId, String>,
        ) -> R,
    ) -> Result<R, String> {
        if !replay.anchors_on_primitive_return() || replay.container_type.is_none() {
            return Err("runtime term anchoring is reserved for container producers".into());
        }
        self.0.replay_terms.register_container_type(replay)?;

        // Lock the immutable causal substrates once for the complete native
        // action batch. One projector and memo are then shared by every live
        // lane, so repeated leaves and common premises are expanded once.
        let recipes = self.0.rule_binding_recipes.read().unwrap();
        let term_recipes = self.0.static_term_recipes.lock().unwrap();
        let spec = term_recipes
            .term_origins
            .get((site.get() - 1) as usize)
            .cloned()
            .ok_or("container anchor has an unknown static term-origin site")?;
        if spec.sort != replay.result_sort {
            return Err("container anchor site has the wrong logical result sort".into());
        }
        let TermTemplate::Call { sort, op, .. } = spec.term.as_ref() else {
            return Err("container anchor site is not a structural call".into());
        };
        if *sort != replay.result_sort || *op != replay.op {
            return Err("container anchor site does not match its primitive producer".into());
        }
        let arena = self.0.arena.lock().unwrap();
        let mut projection_memo = self.0.term_projection_memo.lock().unwrap();
        let mut projector = TermProjector::new(
            &arena,
            &recipes,
            &term_recipes,
            &self.0.replay_terms,
            &self.0.next_term,
            &mut projection_memo,
        );
        let mut install = |binding_sources: &[ReplayBindingSource],
                           premises: &[FactId],
                           child_values: &[Value],
                           value: Value|
         -> Result<ReplayTermId, String> {
            if child_values.len() != replay.child_sorts.len() {
                return Err("container anchor has the wrong runtime child arity".into());
            }
            let term = projector.runtime_anchor_template(&spec.term, binding_sources, premises)?;
            let Some(ReplayTerm::Call { children, .. }) = self.0.replay_terms.node(term) else {
                unreachable!("container anchor template instantiated a non-call")
            };
            if children.len() != child_values.len() {
                return Err("container anchor template has the wrong child arity".into());
            }
            for ((sort, term), value) in replay
                .child_sorts
                .iter()
                .copied()
                .zip(children.iter().copied())
                .zip(child_values.iter().copied())
            {
                self.0.replay_terms.install_value(sort, value, term)?;
            }
            self.0
                .replay_terms
                .install_container_anchor(spec.sort, value, term)
                .map_err(str::to_owned)
        };
        Ok(f(&mut install))
    }

    #[cfg(test)]
    pub(crate) fn install_test_container_anchor(
        &self,
        sort: ReplaySortId,
        container_type: TypeId,
        child_sorts: &[ReplaySortId],
        value: Value,
        term: ReplayTermId,
    ) -> Result<ReplayTermId, &'static str> {
        self.0
            .replay_terms
            .register_container_sort(sort, container_type, child_sorts)?;
        self.0
            .replay_terms
            .install_container_anchor(sort, value, term)
    }

    /// Publish one fully-resolved check root atomically. Runtime values and
    /// their independently-selected structural terms are validated before the
    /// equality history or root storage is changed.
    pub(crate) fn record_check_root(
        &self,
        check: u32,
        wave: Wave,
        premises: &[FactId],
        equalities: &[CriterionEquality],
        landmark: HistoryPosition,
    ) -> Result<(), &'static str> {
        if premises.iter().any(|fact| fact.is_missing()) {
            return Err("check root has a missing exact premise FactId");
        }
        for equality in equalities {
            let ((left, right), (left_occurrence, right_occurrence)) =
                (equality.endpoints, equality.occurrences);
            if left.sort != right.sort {
                return Err("one check equality crosses logical sorts");
            }
            let distinct_fact_cells = matches!(
                (left_occurrence, right_occurrence),
                (
                    CriterionEndpointOccurrence::FactCell(left),
                    CriterionEndpointOccurrence::FactCell(right),
                ) if left != right
            );
            if left.term == right.term && left.raw == right.raw && !distinct_fact_cells {
                return Err(
                    "causal equality endpoints collapsed to one structural occurrence; exact source terms are unavailable",
                );
            }
            for endpoint in [left, right] {
                if endpoint.term.is_missing() {
                    return Err("check equality endpoint has no exact ReplayTermId");
                }
                let node = self
                    .0
                    .replay_terms
                    .node(endpoint.term)
                    .ok_or("check equality endpoint has an unknown ReplayTermId")?;
                if node.sort() != endpoint.sort {
                    return Err("check equality endpoint term has the wrong declared sort");
                }
            }
        }
        for occurrence in equalities
            .iter()
            .flat_map(|equality| [&equality.occurrences.0, &equality.occurrences.1])
        {
            let fact = match occurrence {
                CriterionEndpointOccurrence::FactCell(cell) => Some(cell.fact),
                CriterionEndpointOccurrence::Current => None,
            };
            if fact.is_some_and(FactId::is_missing) {
                return Err("check equality occurrence has a missing premise FactId");
            }
        }
        let mut arena = self.0.arena.lock().unwrap();
        let equality_count = self.0.next_equality.load(Ordering::Acquire);
        let equality_after_landmark = arena
            .durable_equalities
            .last()
            .and_then(Option::as_ref)
            .is_some_and(|equality| equality.position > landmark);
        if arena.published_equalities != equality_count || equality_after_landmark {
            return Err("check equality history changed after its exact landmark was captured");
        }
        if premises.iter().any(|fact| {
            arena
                .facts
                .get((fact.get() - 1) as usize)
                .and_then(Option::as_ref)
                .is_none()
        }) {
            return Err("check root references an unknown exact premise FactId");
        }
        if let Some(current) = arena.check_roots.get(&check) {
            if current.premises.len() != premises.len()
                || current.equalities.len() != equalities.len()
                || current
                    .equalities
                    .iter()
                    .zip(equalities)
                    .any(|(old, new)| old.occurrences != new.occurrences)
                || current
                    .equalities
                    .iter()
                    .map(|equality| equality.endpoints.0.sort)
                    .ne(equalities.iter().map(|equality| equality.endpoints.0.sort))
            {
                return Err("stable check id was reused with a different capture layout");
            }
            // Causal capture is serial-only: the first successful native
            // witness is the check root. A repeated callback for the same
            // check is diagnostic duplication, not a later replacement.
            return Ok(());
        }
        let position = HistoryPosition::new(TraceShared::alloc_u64(&self.0.next_history, 1));
        arena.check_roots.insert(
            check,
            Criterion {
                check,
                wave,
                position,
                premises: premises.into(),
                equalities: equalities.into(),
            },
        );
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn typed_equality_proposal(
        &self,
        wave: Wave,
        sort: ReplaySortId,
        left: Value,
        right: Value,
    ) -> Result<TypedEqualityProposal, &'static str> {
        let left_endpoint = self.equality_endpoint(sort, left)?;
        let right_endpoint = self.equality_endpoint(sort, right)?;
        self.typed_equality_proposal_from_refs(
            wave,
            PendingEqualityEndpoint {
                sort,
                raw: left,
                term: EqualityTermRef::Exact(left_endpoint.term),
            },
            PendingEqualityEndpoint {
                sort,
                raw: right,
                term: EqualityTermRef::Exact(right_endpoint.term),
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn typed_merge_equality_proposal(
        &self,
        wave: Wave,
        sort: ReplaySortId,
        left: Value,
        right: Value,
        table: TableId,
        column: usize,
        prior_fact: FactId,
        incoming: RowOriginRef,
    ) -> Result<TypedEqualityProposal, &'static str> {
        let column = u16::try_from(column).map_err(|_| "merge endpoint column exceeds u16")?;
        if self.table_column_sort(table, column as usize) != Some(sort) {
            return Err("merge equality endpoint sort does not match its source column");
        }
        self.typed_equality_proposal_from_refs(
            wave,
            PendingEqualityEndpoint {
                sort,
                raw: left,
                term: EqualityTermRef::Cell {
                    origin: RowOriginRef::Fact(prior_fact),
                    table,
                    column,
                },
            },
            PendingEqualityEndpoint {
                sort,
                raw: right,
                term: EqualityTermRef::Cell {
                    origin: incoming,
                    table,
                    column,
                },
            },
        )
    }

    fn typed_equality_proposal_from_refs(
        &self,
        wave: Wave,
        left: PendingEqualityEndpoint,
        right: PendingEqualityEndpoint,
    ) -> Result<TypedEqualityProposal, &'static str> {
        if left.sort != right.sort {
            return Err("typed equality endpoints belong to different logical sorts");
        }
        let mut value_sorts = self.0.equality_value_sorts.lock().unwrap();
        for value in [left.raw, right.raw] {
            if value_sorts
                .get(&value)
                .is_some_and(|known_sort| *known_sort != left.sort)
            {
                return Err("one native equality value was used through different logical sorts");
            }
        }
        value_sorts.entry(left.raw).or_insert(left.sort);
        value_sorts.entry(right.raw).or_insert(right.sort);
        Ok(TypedEqualityProposal { wave, left, right })
    }

    /// Clone one interned structural term, or return `None` for an unknown id,
    /// including [`ReplayTermId::MISSING`].
    pub(crate) fn replay_term(&self, id: ReplayTermId) -> Option<ReplayTerm> {
        self.0.replay_terms.node(id)
    }

    /// A compact test-only structural node. Real producers install equivalent
    /// handles; the capture kernel never renders the label.
    #[cfg(test)]
    pub fn intern_test_term(&self, label: &str) -> ReplayTermId {
        self.0.replay_terms.intern(
            &self.0.next_term,
            ReplayTerm::Literal {
                sort: ReplaySortId::new(0),
                literal: ReplayLiteral::String(label.into()),
            },
        )
    }

    pub(crate) fn new_batch(&self) -> CaptureBatch {
        CaptureBatch::new(self.0.clone())
    }

    fn validate_pending_premises(&self, premises: &[FactId]) -> Result<(), String> {
        let arena = self.0.arena.lock().unwrap();
        for fact in premises.iter().copied() {
            if !arena.has_fact(fact) {
                return Err(format!(
                    "observed firing references unavailable premise {fact:?}"
                ));
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn install_observed_firings(
        &self,
        rule: u32,
        wave: Wave,
        history_cutoff: HistoryPosition,
        first_firing: FiringId,
        premise_arity: usize,
        premises: &[FactId],
        lanes: usize,
    ) {
        let mut arena = self.0.arena.lock().unwrap();
        let premise_start = arena.durable_premises.len();
        arena.durable_premises.extend_from_slice(premises);
        for lane in 0..lanes {
            let id = first_firing.get() + lane as u64;
            let index = (id - 1) as usize;
            if arena.durable_firings.len() <= index {
                arena.durable_firings.resize_with(index + 1, || None);
            }
            assert!(
                arena.durable_firings[index].is_none(),
                "duplicate FiringId publication"
            );
            arena.durable_firings[index] = Some(DurableFiring {
                rule,
                wave,
                history_cutoff,
                premises: FlatRange::new(premise_start + lane * premise_arity, premise_arity),
            });
        }
        arena.published_firings += lanes as u64;
    }

    /// Install structural terms for an original input row and return its static
    /// row-origin site.
    ///
    /// The row, term slice, and registered table layout must have equal arity.
    /// Typed columns require an existing term of the declared sort; engine-only
    /// columns require [`ReplayTermId::MISSING`]. Successful installation also
    /// establishes the first-wins typed raw-value mappings used by later
    /// capture, while the returned origin keeps the exact supplied terms. This
    /// method does not publish a [`FactId`] or allocate a history event.
    pub fn install_source_row(
        &self,
        table: TableId,
        row: &[Value],
        terms: &[ReplayTermId],
    ) -> Result<RowOriginSiteId, &'static str> {
        self.0.replay_terms.install_source_row(table, row, terms)?;
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("table has no replay-term layout")?;
        let cells = layout
            .iter()
            .copied()
            .zip(terms.iter().copied())
            .map(|(sort, term)| sort.map(|_| Arc::new(TermTemplate::Static { term })))
            .collect();
        Ok(self.register_row_origin(RowOriginSpec { table, cells }))
    }

    /// Build a static source-row origin whose output is one constructor call.
    ///
    /// `children` must match the constructor's child sorts. The origin places
    /// those terms in the first columns and the constructor result immediately
    /// after them; the registered layout must declare that output slot with the
    /// result sort. Agreement between the leading layout sorts and child sorts
    /// is a caller invariant. The method records an origin recipe but neither
    /// interns the result call nor publishes a fact.
    pub fn source_constructor_origin(
        &self,
        table: TableId,
        children: &[ReplayTermId],
        constructor: &ReplayCallSpec,
    ) -> Result<RowOriginSiteId, &'static str> {
        if children.len() != constructor.child_sorts.len() {
            return Err("source constructor has the wrong structural child arity");
        }
        for (&sort, &term) in constructor.child_sorts.iter().zip(children) {
            let node = self
                .0
                .replay_terms
                .node(term)
                .ok_or("source constructor has an unknown child term")?;
            if node.sort() != sort {
                return Err("source constructor child term has the wrong logical sort");
            }
        }
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("source constructor table has no replay layout")?;
        let output = children.len();
        if layout.get(output).copied().flatten() != Some(constructor.result_sort) {
            return Err("source constructor output does not match its table layout");
        }
        let mut cells = vec![None; layout.len()];
        for (column, &term) in children.iter().enumerate() {
            cells[column] = Some(Arc::new(TermTemplate::Static { term }));
        }
        cells[output] = Some(Arc::new(TermTemplate::Call {
            sort: constructor.result_sort,
            op: constructor.op,
            children: children
                .iter()
                .copied()
                .map(|term| Arc::new(TermTemplate::Static { term }))
                .collect(),
        }));
        Ok(self.register_row_origin(RowOriginSpec {
            table,
            cells: cells.into(),
        }))
    }

    #[cfg(test)]
    pub(crate) fn source_draft(&self, source: SourceRef) -> CauseDraftId {
        let id = CauseDraftId::new(TraceShared::alloc_u64(&self.0.next_cause_draft, 1));
        let mut arena = self.0.arena.lock().unwrap();
        arena.install_cause(
            id,
            DurableCause::Source(source),
            EqualityCauseSummary::Source,
        );
        id
    }

    pub(crate) fn register_source_actions(
        &self,
        source: &SourceRef,
        lanes: &[usize],
    ) -> Vec<(usize, CauseDraftId)> {
        if lanes.is_empty() {
            return Vec::new();
        }
        let first = TraceShared::alloc_u64(&self.0.next_cause_draft, lanes.len());
        let mut arena = self.0.arena.lock().unwrap();
        lanes
            .iter()
            .copied()
            .enumerate()
            .map(|(offset, lane)| {
                let id = CauseDraftId::new(first + offset as u64);
                arena.install_cause(
                    id,
                    DurableCause::Source(source.clone()),
                    EqualityCauseSummary::Source,
                );
                (lane, id)
            })
            .collect()
    }

    /// Register heterogeneous source rows contiguously under one arena lock.
    pub(crate) fn register_source_rows(&self, sources: &[SourceRef]) -> Vec<CauseDraftId> {
        if sources.is_empty() {
            return Vec::new();
        }
        let first = TraceShared::alloc_u64(&self.0.next_cause_draft, sources.len());
        let mut arena = self.0.arena.lock().unwrap();
        sources
            .iter()
            .enumerate()
            .map(|(offset, source)| {
                let id = CauseDraftId::new(first + offset as u64);
                arena.install_cause(
                    id,
                    DurableCause::Source(source.clone()),
                    EqualityCauseSummary::Source,
                );
                id
            })
            .collect()
    }

    /// Test helper that publishes one native observation batch eagerly and
    /// returns its first stable firing id.
    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn pending_firing_batch(
        &self,
        rule: u32,
        wave: Wave,
        premise_arity: usize,
        binding_sources: &[ReplayBindingSource],
        flat_premises: &[FactId],
        lanes: usize,
    ) -> ObservedFiringBatch {
        assert!(lanes > 0, "observed firing batch cannot be empty");
        assert_eq!(
            flat_premises.len(),
            lanes * premise_arity,
            "pending firing premises must be dense and lane-aligned"
        );
        self.validate_pending_premises(flat_premises)
            .unwrap_or_else(|error| panic!("cannot observe test rule batch: {error}"));
        let first_native_ordinal = self.reserve_firing_ordinals(lanes);
        self.register_rule_binding_recipe(rule, binding_sources);
        self.observe_firing_batch_at(
            rule,
            wave,
            first_native_ordinal,
            premise_arity,
            flat_premises,
            lanes,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn observe_firing_batch_at(
        &self,
        rule: u32,
        wave: Wave,
        first_native_ordinal: u64,
        premise_arity: usize,
        flat_premises: &[FactId],
        lanes: usize,
    ) -> ObservedFiringBatch {
        assert!(first_native_ordinal > 0);
        assert_eq!(
            flat_premises.len(),
            lanes
                .checked_mul(premise_arity)
                .expect("pending firing premise slab exceeds usize"),
            "observed firing premises must be dense and lane-aligned"
        );
        let history_cutoff = self.history_boundary();
        let premises: Box<[FactId]> = flat_premises.into();
        self.validate_pending_premises(&premises)
            .unwrap_or_else(|error| panic!("cannot observe firing batch: {error}"));
        let first_firing = FiringId::new(first_native_ordinal);
        self.install_observed_firings(
            rule,
            wave,
            history_cutoff,
            first_firing,
            premise_arity,
            &premises,
            lanes,
        );
        ObservedFiringBatch {
            trace: self.clone(),
            first: first_firing,
            lanes: lanes
                .try_into()
                .expect("observed firing batch exceeds u32 lanes"),
            wave,
        }
    }

    /// Resolve compact join witnesses once when head execution begins, then
    /// publish the complete native observation batch eagerly.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn observe_firing_batch_lazy(
        &self,
        rule: u32,
        wave: Wave,
        first_native_ordinal: u64,
        premise_arity: usize,
        resolver: Arc<dyn PendingPremiseResolver>,
        witness_lanes: &[u32],
    ) -> ObservedFiringBatch {
        let lanes = witness_lanes.len();
        assert!(lanes > 0, "observed firing batch cannot be empty");
        assert!(first_native_ordinal > 0);
        let premises = resolver.resolve_batch(witness_lanes, premise_arity);
        self.validate_pending_premises(&premises)
            .unwrap_or_else(|error| panic!("cannot observe firing batch: {error}"));
        let history_cutoff = self.history_boundary();
        let first_firing = FiringId::new(first_native_ordinal);
        self.install_observed_firings(
            rule,
            wave,
            history_cutoff,
            first_firing,
            premise_arity,
            &premises,
            lanes,
        );
        ObservedFiringBatch {
            trace: self.clone(),
            first: first_firing,
            lanes: lanes
                .try_into()
                .expect("observed firing batch exceeds u32 lanes"),
            wave,
        }
    }

    pub(crate) fn reserve_firing_ordinals(&self, lanes: usize) -> u64 {
        TraceShared::alloc_u64(&self.0.next_firing, lanes)
    }

    pub(crate) fn pending_firing_cause(
        &self,
        observed: &ObservedFiringBatch,
        lane: usize,
    ) -> PendingFiringCause {
        assert!(
            Arc::ptr_eq(&self.0, &observed.trace.0),
            "observed firing batch belongs to another causal trace arena"
        );
        assert!(
            lane < observed.lanes as usize,
            "observed firing lane {lane} is outside a {}-lane batch",
            observed.lanes
        );
        let firing = FiringId::new(
            observed
                .first
                .get()
                .checked_add(lane as u64)
                .expect("observed firing id overflow"),
        );
        assert!(
            firing.get() <= self.0.next_firing.load(Ordering::Acquire),
            "observed firing batch references unreserved firing {firing:?}"
        );
        PendingFiringCause {
            trace: self.clone(),
            firing,
            wave: observed.wave,
        }
    }

    fn prepare_firing(&self, firing: FiringId, expected_wave: Wave) -> Result<(), String> {
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0 {
            return Err("firing belongs to a panicking execution".into());
        }
        let arena = self.0.arena.lock().unwrap();
        let Some(record) = firing
            .get()
            .checked_sub(1)
            .and_then(|index| arena.durable_firings.get(index as usize))
            .and_then(Option::as_ref)
        else {
            return Err(format!("unknown observed firing {firing:?}"));
        };
        if record.wave != expected_wave {
            return Err(format!(
                "observed firing {firing:?} from wave {:?} was used in wave {:?}",
                record.wave, expected_wave
            ));
        }
        Ok(())
    }

    fn record_firing_merge_read(&self, firing: FiringId, prior_fact: FactId) {
        assert!(
            !prior_fact.is_missing(),
            "capture-enabled table merge read a row without an immutable FactId"
        );
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0 {
            panic!("cannot record merge read: firing belongs to a panicking execution");
        }
        self.0
            .arena
            .lock()
            .unwrap()
            .merge_reads
            .entry(firing)
            .or_default()
            .push(prior_fact);
    }

    fn record_ready_merge_read(&self, cause: PackedCauseRef, prior_fact: FactId) {
        if let Some(firing) = cause.firing() {
            self.record_firing_merge_read(firing, prior_fact);
            return;
        }
        assert!(
            !prior_fact.is_missing(),
            "capture-enabled table merge read a row without an immutable FactId"
        );
        let Some(node) = cause.cause_node() else {
            return;
        };
        let mut arena = self.0.arena.lock().unwrap();
        let source = match arena.durable_cause(node) {
            Some(DurableCause::Source(source)) => source.clone(),
            _ => return,
        };
        arena
            .source_merge_reads
            .entry(source)
            .or_default()
            .push(prior_fact);
    }

    /// Test-only eager registration helper for low-level capture fixtures.
    /// Production rule execution always uses pending batches.
    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn register_firings(
        &self,
        rule: u32,
        wave: Wave,
        premise_arity: usize,
        binding_sources: &[ReplayBindingSource],
        flat_premises: &[FactId],
        lanes: &[usize],
    ) -> Vec<(usize, PackedCauseRef)> {
        if lanes.is_empty() {
            return Vec::new();
        }
        self.register_rule_binding_recipe(rule, binding_sources);
        let first_firing = FiringId::new(self.reserve_firing_ordinals(lanes.len()));
        let history_cutoff = self.history_boundary();
        let mut selected_premises = Vec::with_capacity(lanes.len() * premise_arity);
        for lane in lanes.iter().copied() {
            let premise_start = lane * premise_arity;
            selected_premises
                .extend_from_slice(&flat_premises[premise_start..premise_start + premise_arity]);
        }
        self.validate_pending_premises(&selected_premises)
            .unwrap_or_else(|error| panic!("cannot observe test rule batch: {error}"));
        self.install_observed_firings(
            rule,
            wave,
            history_cutoff,
            first_firing,
            premise_arity,
            &selected_premises,
            lanes.len(),
        );
        lanes
            .iter()
            .copied()
            .enumerate()
            .map(|(offset, lane)| {
                (
                    lane,
                    PackedCauseRef::rule(FiringId::new(first_firing.get() + offset as u64)),
                )
            })
            .collect()
    }

    /// Validate that the current synchronous wave is quiescent and completely
    /// published.
    ///
    /// This check is read-only and repeatable at quiescence: observed firings
    /// are already durable, so it neither promotes nor reclaims records.
    /// Caller-controlled lifecycle violations are returned without changing
    /// trace state.
    ///
    /// # Panics
    ///
    /// Panics if a supposedly quiescent arena has a dense publication hole or
    /// its mutex is poisoned. Those states indicate internal capture
    /// corruption rather than a supported caller-controlled lifecycle state.
    pub(crate) fn finalize_wave(&self) -> Result<(), TraceLifecycleError> {
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0 {
            return Err(TraceLifecycleError::PoisonedExecution);
        }
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err(TraceLifecycleError::OpenCaptureBatches);
        }
        if self.0.abandoned_fragments.load(Ordering::Acquire) != 0 {
            return Err(TraceLifecycleError::AbandonedCaptureBatch);
        }
        if self.0.open_native_leases.load(Ordering::Acquire) != 0 {
            return Err(TraceLifecycleError::ActiveNativeLeases);
        }
        let arena = self.0.arena.lock().unwrap();
        assert_eq!(
            arena.published_facts,
            self.0.next_fact.load(Ordering::Acquire),
            "direct fact publication left an ID hole"
        );
        assert_eq!(
            arena.published_firings,
            self.0.next_firing.load(Ordering::Acquire),
            "observed firing publication left an ID hole"
        );
        assert_eq!(
            arena.published_causes,
            self.0.next_cause_draft.load(Ordering::Acquire),
            "direct cause publication left an ID hole"
        );
        assert_eq!(
            arena.published_equalities,
            self.0.next_equality.load(Ordering::Acquire),
            "direct equality publication left an ID hole"
        );
        Ok(())
    }

    /// Borrow a checked view of quiescent, publication-complete captured
    /// history.
    ///
    /// The method rejects poisoned execution, open or abandoned capture
    /// batches, queued native mutations, and publication/history holes.
    /// Nested or concurrent views across any clone are rejected as invalid, and
    /// poisoned internal locks are reported separately. The higher-ranked
    /// closure cannot return guard-borrowed data, so capture storage cannot
    /// escape. This check does not freeze concurrent term/catalog registration;
    /// callers that require a stable catalog must quiesce those writers too.
    pub fn with_view<R>(
        &self,
        inspect: impl for<'view> FnOnce(&mut TraceView<'view>) -> Result<R, TraceViewError>,
    ) -> Result<R, TraceViewError> {
        let _active = ActiveTraceViewGuard::enter(&self.0.view_active)?;
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0 {
            return Err(TraceViewError::NotFinalized(
                "a rule execution failed before trace publication",
            ));
        }
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err(TraceViewError::NotFinalized("capture batches remain open"));
        }
        if self.0.open_native_leases.load(Ordering::Acquire) != 0 {
            return Err(TraceViewError::NotFinalized(
                "transactional native mutations remain queued",
            ));
        }
        if self.0.abandoned_fragments.load(Ordering::Acquire) != 0 {
            return Err(TraceViewError::NotFinalized(
                "a capture batch was abandoned",
            ));
        }
        let recipes = self
            .0
            .rule_binding_recipes
            .read()
            .map_err(|_| TraceViewError::Poisoned("rule binding recipes"))?;
        let equality_recipes = self
            .0
            .rule_equality_recipes
            .read()
            .map_err(|_| TraceViewError::Poisoned("rule equality recipes"))?;
        let term_recipes = self
            .0
            .static_term_recipes
            .lock()
            .map_err(|_| TraceViewError::Poisoned("static term recipes"))?;
        let arena = self
            .0
            .arena
            .lock()
            .map_err(|_| TraceViewError::Poisoned("trace arena"))?;
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0
            || self.0.open_fragments.load(Ordering::Acquire) != 0
            || self.0.open_native_leases.load(Ordering::Acquire) != 0
            || self.0.abandoned_fragments.load(Ordering::Acquire) != 0
        {
            return Err(TraceViewError::NotFinalized(
                "capture state changed while acquiring the trace view",
            ));
        }
        let expected = [
            (
                arena.published_facts,
                self.0.next_fact.load(Ordering::Acquire),
                "fact",
            ),
            (
                arena.published_firings,
                self.0.next_firing.load(Ordering::Acquire),
                "firing",
            ),
            (
                arena.published_causes,
                self.0.next_cause_draft.load(Ordering::Acquire),
                "cause",
            ),
            (
                arena.published_equalities,
                self.0.next_equality.load(Ordering::Acquire),
                "applied equality",
            ),
        ];
        if let Some((_, _, kind)) = expected
            .into_iter()
            .find(|(published, allocated, _)| published != allocated)
        {
            return Err(TraceViewError::NotFinalized(match kind {
                "fact" => "fact publication has an ID hole",
                "firing" => "firing publication has an ID hole",
                "cause" => "cause publication has an ID hole",
                _ => "applied-equality publication has an ID hole",
            }));
        }
        let history_boundary = HistoryPosition::new(self.0.next_history.load(Ordering::Acquire));
        let expected_history = arena
            .published_facts
            .checked_add(arena.published_equalities)
            .and_then(|events| events.checked_add(arena.rekeys.len() as u64))
            .and_then(|events| events.checked_add(arena.removals.len() as u64))
            .and_then(|events| events.checked_add(arena.check_roots.len() as u64))
            .ok_or_else(|| TraceViewError::Invalid("trace history count overflow".into()))?;
        if history_boundary.get() != expected_history {
            return Err(TraceViewError::NotFinalized(
                "global history publication has an ID hole",
            ));
        }
        let mut projection_memo = self
            .0
            .term_projection_memo
            .lock()
            .map_err(|_| TraceViewError::Poisoned("term projection memo"))?;
        let projector = TermProjector::new(
            &arena,
            &recipes,
            &term_recipes,
            &self.0.replay_terms,
            &self.0.next_term,
            &mut projection_memo,
        );
        let mut view = TraceView {
            arena: &arena,
            binding_recipes: &recipes,
            equality_recipes: &equality_recipes,
            term_recipes: &term_recipes,
            replay_terms: &self.0.replay_terms,
            projector,
            history_boundary,
            equality_index: None,
            rekey_index: None,
            merge_replacement_index: None,
            row_call_occurrence_index: None,
            occurrence_support_cache: HashMap::default(),
            exact_occurrence_support_cache: HashMap::default(),
        };
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| inspect(&mut view))) {
            Ok(result) => result,
            Err(payload) => {
                drop(view);
                drop(projection_memo);
                drop(arena);
                drop(term_recipes);
                drop(equality_recipes);
                drop(recipes);
                std::panic::resume_unwind(payload)
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn observed_firing_batch_for_test(
        &self,
        first: FiringId,
        lanes: u32,
        wave: Wave,
    ) -> ObservedFiringBatch {
        ObservedFiringBatch {
            trace: self.clone(),
            first,
            lanes,
            wave,
        }
    }
}

#[cfg(test)]
#[path = "capture_tests.rs"]
mod tests;
