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
    pub(crate) wave: Wave,
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

/// A compact, cloneable cause handle carried by one staged equality proposal.
/// the firing was already published when native head execution began, so the
/// handle needs no batch lifetime or promotion allocation.
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

#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct PreparedRekey {
    table: TableId,
    wave: Wave,
    prior_fact: FactId,
    as_of_edges: EdgeHorizon,
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
    ) -> (
        TableId,
        Wave,
        FactId,
        EdgeHorizon,
        HistoryPosition,
        &[TypedCellEquality],
    ) {
        (
            self.table,
            self.wave,
            self.prior_fact,
            self.as_of_edges,
            self.position,
            &self.equalities,
        )
    }

    pub(crate) fn from_staged(
        table: TableId,
        wave: Wave,
        prior_fact: FactId,
        as_of_edges: EdgeHorizon,
        position: HistoryPosition,
        equalities: &[TypedCellEquality],
    ) -> Self {
        Self {
            table,
            wave,
            prior_fact,
            as_of_edges,
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
    equality: EqualityCauseSummary,
    cause: OnceLock<PackedCauseRef>,
}

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
    /// rule lane without promoting it. Nested merge causes preserve the
    /// original incoming firing as their attribution owner.
    pub(crate) fn record_merge_read(&self, prior_fact: FactId) {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { .. } => {}
            DeferredEqualityCauseKind::Pending(cause) => cause.record_merge_read(prior_fact),
            DeferredEqualityCauseKind::Merge(cause) => cause.incoming.record_merge_read(prior_fact),
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
    MissingFact,
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
            EqualityCauseError::MissingFact => {
                "equality cause references a missing immutable FactId"
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EqualityCauseSummary {
    Source,
    Rule,
    Container {
        wave: Wave,
        as_of_edges: EdgeHorizon,
        position: HistoryPosition,
    },
    Rebuild {
        wave: Wave,
        as_of_edges: EdgeHorizon,
        position: HistoryPosition,
        complete: bool,
    },
    Invalid(EqualityCauseError),
}

impl EqualityCauseSummary {
    fn with_prior_fact(self, fact: FactId) -> Self {
        if fact.is_missing() {
            return Self::Invalid(EqualityCauseError::MissingFact);
        }
        match self {
            Self::Rule => Self::Rule,
            Self::Container { .. } => Self::Invalid(EqualityCauseError::Mixed),
            Self::Rebuild {
                wave,
                as_of_edges,
                position,
                ..
            } => Self::Rebuild {
                wave,
                as_of_edges,
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

impl CauseCapability {
    #[cfg(test)]
    pub(crate) fn id(self) -> CauseDraftId {
        self.id
    }
}

#[derive(Clone, Debug)]
enum DurableCause {
    Source(SourceRef),
    Rebuild {
        wave: Wave,
        prior_fact: FactId,
        as_of_edges: EdgeHorizon,
        position: HistoryPosition,
        equalities: FlatRange,
    },
    ContainerCanonicalize {
        wave: Wave,
        as_of_edges: EdgeHorizon,
        position: HistoryPosition,
        equalities: FlatRange,
    },
    ContainerRefresh {
        wave: Wave,
        prior_fact: FactId,
        as_of_edges: EdgeHorizon,
        position: HistoryPosition,
        equalities: FlatRange,
    },
    Merge {
        incoming: PackedCauseRef,
        prior_fact: FactId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RowOriginRef {
    Site(RowOriginSiteId),
    Fact(FactId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MergeCellOrigin {
    Incoming(u16),
    Prior(u16),
    /// The merge synthesized a value not structurally named by either input.
    Unsupported,
}

#[derive(Clone, Copy, Debug)]
enum FactOrigin {
    Site(RowOriginSiteId),
    Fact(FactId),
    Merge {
        incoming: Option<RowOriginRef>,
        prior: FactId,
        cells: FlatRange,
    },
}

#[derive(Clone, Debug)]
pub(crate) enum PreparedFactOrigin {
    None,
    Direct(RowOriginRef),
    Merge {
        incoming: Option<RowOriginRef>,
        prior: FactId,
        cells: SmallVec<[MergeCellOrigin; 4]>,
    },
}

#[derive(Clone, Debug)]
struct PendingFact {
    table: TableId,
    position: HistoryPosition,
    cause: PackedCauseRef,
    values: FlatRange,
    origin: Option<FactOrigin>,
}

#[derive(Clone, Debug)]
struct DurableFact {
    table: TableId,
    position: HistoryPosition,
    cause: PackedCauseRef,
    values: FlatRange,
    origin: Option<FactOrigin>,
}

#[derive(Clone, Debug)]
struct PendingEquality {
    position: HistoryPosition,
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    cause: PackedCauseRef,
}

struct DurableEquality {
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
    position: HistoryPosition,
    as_of_edges: EdgeHorizon,
    premises: FlatRange,
}

#[derive(Default)]
struct TraceArena {
    facts: Vec<Option<DurableFact>>,
    durable_firings: Vec<Option<DurableFiring>>,
    durable_premises: Vec<FactId>,
    /// Sparse because ordinary firings never invoke a merge callback.
    merge_reads: HashMap<FiringId, SmallVec<[FactId; 2]>>,
    durable_fact_values: Vec<Value>,
    durable_merge_cell_origins: Vec<MergeCellOrigin>,
    durable_rebuild_equalities: Vec<TypedCellEquality>,
    durable_causes: Vec<Option<(DurableCause, EqualityCauseSummary)>>,
    durable_equalities: Vec<Option<DurableEquality>>,
    rekeys: Vec<RekeyRecord>,
    removals: Vec<Tombstone>,
    check_roots: HashMap<u32, Criterion>,
    published_facts: u64,
    published_firings: u64,
    published_causes: u64,
    published_equalities: u64,
    counters: CaptureCounters,
}

impl TraceArena {
    fn install_fact(&mut self, id: FactId, fact: DurableFact) {
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

    fn install_equality(&mut self, id: AppliedEqualityId, equality: DurableEquality) {
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

    fn record_firing_term_storage(&mut self, logical: usize, stored: usize) {
        let logical = logical as u64;
        let stored = stored as u64;
        let handle_bytes = mem::size_of::<ReplayTermId>() as u64;
        self.counters.logical_firing_term_handles += logical;
        self.counters.stored_firing_term_handles += stored;
        self.counters.logical_firing_term_bytes += logical * handle_bytes;
        self.counters.stored_firing_term_bytes += stored * handle_bytes;
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
            (
                _,
                EqualityCauseSummary::Container {
                    wave,
                    as_of_edges,
                    position,
                },
            ) => EqualityReason::Congruence {
                cause: node.public(),
                wave,
                as_of_edges,
                position,
            },
            (
                _,
                EqualityCauseSummary::Rebuild {
                    wave,
                    as_of_edges,
                    position,
                    ..
                },
            ) => EqualityReason::Congruence {
                cause: node.public(),
                wave,
                as_of_edges,
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
        RwLock<HashMap<u32, Arc<[(ReplayEqualitySource, ReplayEqualitySource)]>>>,
    /// Cold compile-time recipes shared by every seminaive/decomposed variant.
    static_term_recipes: Mutex<StaticTermRecipeStore>,
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

/// A worker/shard-local capture fragment. It performs no locking while native
/// rows are merged and publishes once at the surrounding engine barrier.
pub(crate) struct CaptureBatch {
    shared: Arc<TraceShared>,
    facts: Vec<(FactId, PendingFact)>,
    fact_values: Vec<Value>,
    merge_cell_origins: Vec<MergeCellOrigin>,
    equalities: Vec<(AppliedEqualityId, PendingEquality)>,
    redundant_unions: u64,
    unattributed_commits: u64,
    published: bool,
}

impl CaptureBatch {
    fn new(shared: Arc<TraceShared>) -> Self {
        shared.open_fragments.fetch_add(1, Ordering::Relaxed);
        Self {
            shared,
            facts: Vec::new(),
            fact_values: Vec::new(),
            merge_cell_origins: Vec::new(),
            equalities: Vec::new(),
            redundant_unions: 0,
            unattributed_commits: 0,
            published: false,
        }
    }

    pub(crate) fn record_fact(
        &mut self,
        table: TableId,
        cause: impl Into<PackedCauseRef>,
        row: &[Value],
    ) -> FactId {
        self.push_fact(table, cause.into(), row, None)
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

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_merged_fact(
        &mut self,
        table: TableId,
        cause: impl Into<PackedCauseRef>,
        row: &[Value],
        prepared: PreparedFactOrigin,
    ) -> FactId {
        let cause = cause.into();
        assert!(
            !cause.is_unattributed(),
            "effective commit is missing exact causal attribution"
        );
        let origin = match prepared {
            PreparedFactOrigin::None => None,
            PreparedFactOrigin::Direct(RowOriginRef::Site(site)) => Some(FactOrigin::Site(site)),
            PreparedFactOrigin::Direct(RowOriginRef::Fact(fact)) => Some(FactOrigin::Fact(fact)),
            PreparedFactOrigin::Merge {
                incoming,
                prior,
                cells,
            } => {
                assert_eq!(cells.len(), row.len());
                let range = FlatRange::new(self.merge_cell_origins.len(), cells.len());
                self.merge_cell_origins.extend(cells);
                Some(FactOrigin::Merge {
                    incoming,
                    prior,
                    cells: range,
                })
            }
        };
        self.push_fact(table, cause, row, origin)
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
            PendingFact {
                table,
                position,
                cause,
                values,
                origin,
            },
        ));
        id
    }

    pub(crate) fn record_redundant_union(&mut self) {
        self.redundant_unions += 1;
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
            PendingEquality {
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
            let merge_origin_base = arena.durable_merge_cell_origins.len();
            arena
                .durable_merge_cell_origins
                .append(&mut self.merge_cell_origins);
            for (id, mut fact) in self.facts.drain(..) {
                fact.values = fact.values.shifted(fact_value_base);
                if let Some(FactOrigin::Merge { cells, .. }) = &mut fact.origin {
                    *cells = cells.shifted(merge_origin_base);
                }
                arena.install_fact(
                    id,
                    DurableFact {
                        table: fact.table,
                        position: fact.position,
                        cause: fact.cause,
                        values: fact.values,
                        origin: fact.origin,
                    },
                );
            }
            for (id, equality) in self.equalities.drain(..) {
                arena.install_equality(
                    id,
                    DurableEquality {
                        position: equality.position,
                        proposal: equality.proposal,
                        native_parent: equality.native_parent,
                        native_child: equality.native_child,
                        cause: equality.cause,
                    },
                );
            }
            arena.counters.redundant_unions += self.redundant_unions;
            arena.counters.unattributed_commits += self.unattributed_commits;
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
        if !self.facts.is_empty()
            || !self.fact_values.is_empty()
            || !self.merge_cell_origins.is_empty()
            || !self.equalities.is_empty()
            || self.redundant_unions != 0
            || self.unattributed_commits != 0
        {
            self.shared
                .abandoned_fragments
                .fetch_add(1, Ordering::Relaxed);
        }
        self.shared.open_fragments.fetch_sub(1, Ordering::Release);
    }
}

/// Shared read/finalization handle to the database's causal trace arena.
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
    fn history_boundary(&self) -> HistoryPosition {
        HistoryPosition::new(self.0.next_history.load(Ordering::Acquire))
    }

    fn equality_boundary(&self) -> EdgeHorizon {
        EdgeHorizon::new(self.0.next_equality.load(Ordering::Acquire))
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
        let supported = recipe
            .current_roots
            .iter()
            .filter(|root| root.is_some())
            .count() as u64;
        let missing = recipe.current_roots.len() as u64 - supported;
        let recipe = Arc::new(recipe);
        store.rules.insert(rule, Arc::clone(&recipe));
        drop(store);
        let mut arena = self.0.arena.lock().unwrap();
        arena.counters.supported_current_recipe_roots += supported;
        arena.counters.missing_current_recipe_roots += missing;
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
                ReplayBindingSource::Premise {
                    representative,
                    occurrences,
                } => {
                    assert!(
                        !occurrences.is_empty(),
                        "rule capture premise binding has no occurrences"
                    );
                    assert!(
                        occurrences.contains(representative),
                        "rule capture representative is not one of its premise occurrences"
                    );
                }
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
        equalities: &[(ReplayEqualitySource, ReplayEqualitySource)],
    ) -> Arc<[(ReplayEqualitySource, ReplayEqualitySource)]> {
        for (left, right) in equalities {
            for source in [left, right] {
                if let ReplayEqualitySource::Constant(endpoint) = source {
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
        let recipe: Arc<[(ReplayEqualitySource, ReplayEqualitySource)]> = equalities.into();
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

    pub fn register_table_layout(
        &self,
        table: TableId,
        sorts: &[Option<ReplaySortId>],
    ) -> Result<(), &'static str> {
        self.0.replay_terms.register_table_layout(table, sorts)
    }

    pub fn register_table_kind(
        &self,
        table: TableId,
        kind: ReplayTableKind,
    ) -> Result<(), &'static str> {
        self.0.replay_terms.register_table_kind(table, kind)
    }

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

    pub fn register_table_constructor(
        &self,
        table: TableId,
        constructor: ReplayConstructorSpec,
    ) -> Result<(), &'static str> {
        self.0
            .replay_terms
            .register_table_constructor(table, constructor)
    }

    pub fn register_table_merge_origins(
        &self,
        table: TableId,
        origins: &[MergeOriginSelector],
    ) -> Result<(), &'static str> {
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("register table layout before merge origins")?;
        if layout.len() != origins.len() {
            return Err("merge-origin metadata and table layout have different arities");
        }
        for (destination, origin) in origins.iter().copied().enumerate() {
            let check = |source: u16| {
                let source = source as usize;
                if source >= layout.len() {
                    return Err("merge-origin source column exceeds the table layout");
                }
                if layout[source] != layout[destination] {
                    return Err("merge-origin source and destination have different replay sorts");
                }
                Ok(())
            };
            match origin {
                MergeOriginSelector::Incoming { column }
                | MergeOriginSelector::Prior { column } => check(column)?,
                MergeOriginSelector::NativeMin {
                    incoming_column,
                    prior_column,
                }
                | MergeOriginSelector::PriorOrIncoming {
                    incoming_column,
                    prior_column,
                } => {
                    check(incoming_column)?;
                    check(prior_column)?;
                }
                MergeOriginSelector::Unsupported => {}
            }
        }
        self.0
            .replay_terms
            .register_table_merge_origins(table, origins)
    }

    pub fn register_table_merge_identity_guard(
        &self,
        table: TableId,
        start: usize,
        len: usize,
    ) -> Result<(), &'static str> {
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("register table layout before merge identity guard")?;
        if len == 0 || start.checked_add(len).is_none_or(|end| end > layout.len()) {
            return Err("merge identity guard is outside the table layout");
        }
        let guard = (
            start
                .try_into()
                .map_err(|_| "merge identity guard exceeds u16")?,
            len.try_into()
                .map_err(|_| "merge identity guard exceeds u16")?,
        );
        match self.0.replay_terms.table_merge_identity_guards.entry(table) {
            Entry::Occupied(entry) if *entry.get() == guard => Ok(()),
            Entry::Occupied(_) => Err("table already has a different merge identity guard"),
            Entry::Vacant(entry) => {
                entry.insert(guard);
                Ok(())
            }
        }
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

    pub(crate) fn table_constructor(&self, table: TableId) -> Option<ReplayConstructorSpec> {
        self.0
            .replay_terms
            .table_constructors
            .get(&table)
            .map(|constructor| constructor.clone())
    }

    pub(crate) fn validate_merge_origin(
        &self,
        table: TableId,
        incoming_available: bool,
    ) -> Result<(), &'static str> {
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("merge table has no replay layout")?;
        let origins = self
            .0
            .replay_terms
            .table_merge_origins
            .get(&table)
            .ok_or("merge table has no static origin metadata")?;
        for (sort, origin) in layout.iter().zip(origins.iter()) {
            if sort.is_some() && matches!(origin, MergeOriginSelector::Unsupported) {
                return Err("merge reached an unsupported structural result expression");
            }
            if sort.is_some()
                && !incoming_available
                && matches!(
                    origin,
                    MergeOriginSelector::Incoming { .. }
                        | MergeOriginSelector::NativeMin { .. }
                        | MergeOriginSelector::PriorOrIncoming { .. }
                )
            {
                return Err("merge incoming row has no exact structural origin");
            }
        }
        Ok(())
    }

    /// Whether rebuild must prove that no table collision reaches this merge
    /// before publishing its removal/rekey batch. Fully supported bridge
    /// tables do not need the extra key set: the callback and these selectors
    /// are compiled from the same merge AST, and commit-time validation is an
    /// internal consistency assertion. Missing metadata and typed
    /// `Unsupported` selectors are reached semantics, so their collision must
    /// fail while the rebuild transaction is still abortable.
    pub(crate) fn requires_collision_preflight(&self, table: TableId) -> bool {
        let Some(layout) = self.0.replay_terms.table_layout(table) else {
            return true;
        };
        let Some(origins) = self.0.replay_terms.table_merge_origins.get(&table) else {
            return true;
        };
        layout.iter().zip(origins.iter()).any(|(sort, origin)| {
            sort.is_some() && matches!(origin, MergeOriginSelector::Unsupported)
        })
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

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prepare_merged_fact_origin(
        &self,
        table: TableId,
        row: &[Value],
        prior_row: &[Value],
        incoming_row: &[Value],
        prior_fact: FactId,
        incoming: Option<RowOriginRef>,
    ) -> Result<PreparedFactOrigin, &'static str> {
        if prior_fact.is_missing() {
            return Err("merged row has no immutable prior FactId");
        }
        if row.len() != prior_row.len() || row.len() != incoming_row.len() {
            return Err("merge result and input rows have different arities");
        }
        let layout = self
            .0
            .replay_terms
            .table_layout(table)
            .ok_or("merged fact table has no replay layout")?;
        if layout.len() != row.len() {
            return Err("merge result and replay layout have different arities");
        }
        if !layout.iter().any(Option::is_some) {
            return Ok(PreparedFactOrigin::None);
        }
        let selectors = self
            .0
            .replay_terms
            .table_merge_origins
            .get(&table)
            .ok_or("merge table has no static origin metadata")?;
        let identity_guard = self
            .0
            .replay_terms
            .table_merge_identity_guards
            .get(&table)
            .map(|guard| *guard);
        let identity_unchanged = identity_guard.is_some_and(|(start, len)| {
            let start = start as usize;
            let end = start + len as usize;
            prior_row.get(start..end) == incoming_row.get(start..end)
        });
        let mut cells = SmallVec::<[MergeCellOrigin; 4]>::with_capacity(row.len());
        for (column, sort) in layout.iter().copied().enumerate() {
            let selected = if sort.is_none() {
                MergeCellOrigin::Unsupported
            } else if identity_unchanged
                && identity_guard.is_some_and(|(value_start, _)| column >= value_start as usize)
            {
                MergeCellOrigin::Prior(
                    column
                        .try_into()
                        .expect("function table has more than u16 columns"),
                )
            } else {
                match selectors.get(column).copied() {
                    Some(MergeOriginSelector::Incoming { column: source })
                        if incoming.is_some()
                            && incoming_row.get(source as usize) == row.get(column) =>
                    {
                        MergeCellOrigin::Incoming(source)
                    }
                    Some(MergeOriginSelector::Prior { column: source })
                        if prior_row.get(source as usize) == row.get(column) =>
                    {
                        MergeCellOrigin::Prior(source)
                    }
                    Some(MergeOriginSelector::NativeMin {
                        incoming_column,
                        prior_column,
                    }) if incoming.is_some() => {
                        let incoming_value = incoming_row.get(incoming_column as usize);
                        let prior_value = prior_row.get(prior_column as usize);
                        match (incoming_value, prior_value) {
                            (Some(incoming_value), Some(prior_value))
                                if row.get(column)
                                    == Some(std::cmp::min(incoming_value, prior_value)) =>
                            {
                                if prior_value <= incoming_value {
                                    MergeCellOrigin::Prior(prior_column)
                                } else {
                                    MergeCellOrigin::Incoming(incoming_column)
                                }
                            }
                            _ => MergeCellOrigin::Unsupported,
                        }
                    }
                    Some(MergeOriginSelector::PriorOrIncoming {
                        incoming_column,
                        prior_column,
                    }) if incoming.is_some() => {
                        let incoming_value = incoming_row.get(incoming_column as usize);
                        let prior_value = prior_row.get(prior_column as usize);
                        let result = row.get(column);
                        match (
                            result == prior_value,
                            result == incoming_value,
                            prior_value,
                            incoming_value,
                        ) {
                            (true, _, Some(_), Some(_)) => MergeCellOrigin::Prior(prior_column),
                            (false, true, Some(_), Some(_)) => {
                                MergeCellOrigin::Incoming(incoming_column)
                            }
                            _ => MergeCellOrigin::Unsupported,
                        }
                    }
                    _ => MergeCellOrigin::Unsupported,
                }
            };
            cells.push(selected);
        }
        if layout
            .iter()
            .zip(&cells)
            .any(|(sort, origin)| sort.is_some() && matches!(origin, MergeCellOrigin::Unsupported))
        {
            return Err("effective merge violated its exact structural-origin selector");
        }
        let all_incoming = layout.iter().zip(&cells).enumerate().all(
            |(column, (sort, selected))| {
                sort.is_none()
                    || matches!(selected, MergeCellOrigin::Incoming(source) if *source as usize == column)
            },
        );
        if all_incoming {
            return incoming
                .map(PreparedFactOrigin::Direct)
                .ok_or("merge incoming row has no exact structural origin");
        }
        let all_prior = layout.iter().zip(&cells).enumerate().all(
            |(column, (sort, selected))| {
                sort.is_none()
                    || matches!(selected, MergeCellOrigin::Prior(source) if *source as usize == column)
            },
        );
        if all_prior {
            return Ok(PreparedFactOrigin::Direct(RowOriginRef::Fact(prior_fact)));
        }
        Ok(PreparedFactOrigin::Merge {
            incoming,
            prior: prior_fact,
            cells,
        })
    }

    /// Capture one complete applied-edge prefix at the native rebuild
    /// barrier. A bare counter read is insufficient: every allocated edge up
    /// to the cutoff must already have been published without holes.
    pub(crate) fn equality_edge_count(&self) -> Result<EdgeHorizon, &'static str> {
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild with open capture fragments");
        }
        if self.0.abandoned_fragments.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild after an abandoned capture fragment");
        }
        let count = self.0.next_equality.load(Ordering::Acquire);
        let arena = self.0.arena.lock().unwrap();
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err("capture fragment opened while capturing rebuild equality cutoff");
        }
        if count != arena.published_equalities {
            return Err("rebuild equality cutoff is not one complete dense prefix");
        }
        Ok(EdgeHorizon::new(count))
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
    pub(crate) fn record_removals(
        &self,
        wave: Wave,
        removals: impl IntoIterator<Item = PreparedRemoval>,
    ) {
        let as_of_edges = self.equality_boundary();
        let mut tracked = Vec::new();
        let mut relation_count = 0_u64;
        for removal in removals {
            match removal {
                PreparedRemoval::Tracked {
                    removed_fact,
                    cause,
                } => tracked.push(Tombstone {
                    wave,
                    position: HistoryPosition::new(TraceShared::alloc_u64(&self.0.next_history, 1)),
                    as_of_edges,
                    removed_fact,
                    cause,
                }),
                PreparedRemoval::PresenceRelation => relation_count += 1,
            }
        }
        if tracked.is_empty() && relation_count == 0 {
            return;
        }
        let mut arena = self.0.arena.lock().unwrap();
        arena.counters.effective_removals += tracked.len() as u64;
        arena.counters.relation_removals += relation_count;
        arena.removals.extend(tracked);
    }

    pub(crate) fn pending_merge_cause(
        &self,
        incoming: DeferredEqualityCause,
        prior_fact: FactId,
    ) -> DeferredEqualityCause {
        assert!(
            !prior_fact.is_missing(),
            "deferred merge capture is missing its prior FactId"
        );
        let equality = incoming.equality_summary(self).with_prior_fact(prior_fact);
        DeferredEqualityCause(DeferredEqualityCauseKind::Merge(Arc::new(
            PendingMergeCause {
                trace: self.clone(),
                incoming,
                prior_fact,
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
        as_of_edges: EdgeHorizon,
    ) -> Result<PreparedRekey, &'static str> {
        let position = self.history_boundary();
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
            as_of_edges,
            position,
            equalities: pairs,
        })
    }

    /// Promote a rekey cause only after the native table proves that the
    /// rekey collides with a live row and therefore enters merge execution.
    /// Pure moves never allocate a cause or copy their endpoint pairs.
    pub(crate) fn prepared_rekey_cause(&self, rekey: &PreparedRekey) -> DeferredEqualityCause {
        let mut arena = self.0.arena.lock().unwrap();
        let equalities = FlatRange::new(
            arena.durable_rebuild_equalities.len(),
            rekey.equalities.len(),
        );
        arena
            .durable_rebuild_equalities
            .extend_from_slice(&rekey.equalities);
        let id = CauseDraftId::new(TraceShared::alloc_u64(&self.0.next_cause_draft, 1));
        arena.install_cause(
            id,
            DurableCause::Rebuild {
                wave: rekey.wave,
                prior_fact: rekey.prior_fact,
                as_of_edges: rekey.as_of_edges,
                position: rekey.position,
                equalities,
            },
            EqualityCauseSummary::Rebuild {
                wave: rekey.wave,
                as_of_edges: rekey.as_of_edges,
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
            table: rekey.table,
            wave: rekey.wave,
            position,
            equalities: EqualityLandmark {
                as_of_edges: rekey.as_of_edges,
                position: rekey.position,
                pairs: rekey.equalities.as_slice().into(),
            },
            outcome,
        });
        arena.counters.rebuild_causes += 1;
        arena.counters.rebuild_equalities += rekey.equalities.len() as u64;
        arena.counters.rebuild_bytes += (mem::size_of::<RekeyRecord>()
            + rekey.equalities.len() * mem::size_of::<TypedCellEquality>())
            as u64;
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
        as_of_edges: EdgeHorizon,
    ) -> Result<SmallVec<[ContainerVersionDependency; 2]>, &'static str> {
        let position = self.history_boundary();
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
                as_of_edges,
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
        as_of_edges: EdgeHorizon,
    ) -> Result<(CauseCapability, TypedEqualityProposal), &'static str> {
        let position = self.history_boundary();
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
                if value_sorts.get(&left_raw) != Some(&child_sort)
                    || value_sorts.get(&right_raw) != Some(&child_sort)
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
        let equalities = FlatRange::new(arena.durable_rebuild_equalities.len(), pairs.len());
        arena.durable_rebuild_equalities.extend_from_slice(&pairs);
        let id = CauseDraftId::new(TraceShared::alloc_u64(&self.0.next_cause_draft, 1));
        let summary = EqualityCauseSummary::Container {
            wave,
            as_of_edges,
            position,
        };
        arena.install_cause(
            id,
            DurableCause::ContainerCanonicalize {
                wave,
                as_of_edges,
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
                        if (current.wave, current.equalities.as_of_edges)
                            != (dependency.wave, dependency.equalities.as_of_edges)
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
            arena.durable_rebuild_equalities.len(),
            dependency.equalities.pairs.len(),
        );
        arena
            .durable_rebuild_equalities
            .extend_from_slice(&dependency.equalities.pairs);
        let id = CauseDraftId::new(TraceShared::alloc_u64(&self.0.next_cause_draft, 1));
        arena.install_cause(
            id,
            DurableCause::ContainerRefresh {
                wave: dependency.wave,
                prior_fact,
                as_of_edges: dependency.equalities.as_of_edges,
                position: dependency.equalities.position,
                equalities,
            },
            EqualityCauseSummary::Invalid(EqualityCauseError::Mixed),
        );
        Ok(id)
    }

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
            .expect("newly interned literal must have a matching sort")
    }

    pub fn intern_call(
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

    /// Intern one call using its complete producer metadata. Container
    /// producers also establish the physical registry type for the result
    /// sort, which later makes dirty-container ancestry type-safe.
    pub fn intern_spec_call(
        &self,
        constructor: &ReplayConstructorSpec,
        children: &[ReplayTermId],
        value: Value,
    ) -> Result<ReplayTermId, &'static str> {
        self.0.replay_terms.register_container_type(constructor)?;
        let term = self.intern_call(constructor.result_sort, constructor.op, children, value)?;
        if constructor.container_type.is_some() {
            self.0
                .replay_terms
                .install_container_anchor(constructor.result_sort, value, term)?;
        }
        Ok(term)
    }

    pub fn lookup_term(&self, sort: ReplaySortId, value: Value) -> Option<ReplayTermId> {
        self.0.replay_terms.lookup(sort, value)
    }

    /// Resolve one already-recorded structural call without installing a
    /// current-value mapping or allocating a new DAG node. Positive check roots
    /// use this to preserve their source endpoint syntax after congruence has
    /// canonicalized both runtime values.
    pub fn lookup_call(
        &self,
        sort: ReplaySortId,
        op: ReplayOpId,
        children: &[ReplayTermId],
    ) -> Option<ReplayTermId> {
        self.0.replay_terms.lookup_node(&ReplayTerm::Call {
            sort,
            op,
            children: children.into(),
        })
    }

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
            let mut projector = TermProjector::new(
                &arena,
                &recipes,
                &term_recipes,
                &self.0.replay_terms,
                &self.0.next_term,
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
                    CheckTermSource::Constant { .. } | CheckTermSource::Current => {
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
        let mut projector = TermProjector::new(
            &arena,
            &recipes,
            &term_recipes,
            &self.0.replay_terms,
            &self.0.next_term,
        );
        projector.fact_term(fact, column)
    }

    pub(crate) fn with_container_anchor_installer<R>(
        &self,
        site: TermOriginSiteId,
        replay: &ReplayConstructorSpec,
        f: impl FnOnce(
            &mut dyn FnMut(
                &[ReplayBindingSource],
                &[FactId],
                &[Value],
                Value,
            ) -> Result<ReplayTermId, String>,
        ) -> R,
    ) -> Result<R, String> {
        if !replay.promote_immediately || replay.container_type.is_none() {
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
        let mut projector = TermProjector::new(
            &arena,
            &recipes,
            &term_recipes,
            &self.0.replay_terms,
            &self.0.next_term,
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
    /// applied-equality cutoff or root storage is changed.
    pub(crate) fn record_check_root(
        &self,
        check: u32,
        wave: Wave,
        premises: &[FactId],
        equalities: &[(EqualityEndpoint, EqualityEndpoint)],
        equality_occurrences: &[(CriterionEndpointOccurrence, CriterionEndpointOccurrence)],
        as_of_edges: EdgeHorizon,
    ) -> Result<(), &'static str> {
        if premises.iter().any(|fact| fact.is_missing()) {
            return Err("check root has a missing exact premise FactId");
        }
        if equality_occurrences.len() != equalities.len() {
            return Err("check equality endpoints and occurrence metadata have different arities");
        }
        for ((left, right), (left_occurrence, right_occurrence)) in
            equalities.iter().zip(equality_occurrences)
        {
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
        for occurrence in equality_occurrences
            .iter()
            .flat_map(|(left, right)| [left, right])
        {
            let fact = match occurrence {
                CriterionEndpointOccurrence::FactCell(cell) => Some(cell.fact),
                CriterionEndpointOccurrence::Current => None,
            };
            if fact.is_some_and(FactId::is_missing) {
                return Err("check equality occurrence has a missing premise FactId");
            }
        }
        if self.0.next_equality.load(Ordering::Acquire) != as_of_edges.get() {
            return Err("check equality history changed after its exact cutoff was captured");
        }
        let mut arena = self.0.arena.lock().unwrap();
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
                || current.equality_occurrences.as_ref() != equality_occurrences
                || current
                    .equalities
                    .iter()
                    .map(|(left, _)| left.sort)
                    .ne(equalities.iter().map(|(left, _)| left.sort))
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
                equality_occurrences: equality_occurrences.into(),
                as_of_edges,
            },
        );
        Ok(())
    }

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

    pub fn replay_term(&self, id: ReplayTermId) -> Option<ReplayTerm> {
        self.0.replay_terms.node(id)
    }

    pub fn replay_term_counters(&self) -> TermInternerCounters {
        self.0.replay_terms.counters()
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
        position: HistoryPosition,
        as_of_edges: EdgeHorizon,
        first_firing: FiringId,
        premise_arity: usize,
        premises: &[FactId],
        lanes: usize,
        binding_arity: usize,
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
                position,
                as_of_edges,
                premises: FlatRange::new(premise_start + lane * premise_arity, premise_arity),
            });
        }
        arena.published_firings += lanes as u64;
        arena.counters.premise_handles += premises.len() as u64;
        arena.record_firing_term_storage(lanes * binding_arity, 0);
        arena.counters.observed_firings += lanes as u64;
    }

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

    pub fn source_constructor_origin(
        &self,
        table: TableId,
        children: &[ReplayTermId],
        constructor: &ReplayConstructorSpec,
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
        let binding_sources = self.register_rule_binding_recipe(rule, binding_sources);
        self.observe_firing_batch_at(
            rule,
            wave,
            first_native_ordinal,
            premise_arity,
            binding_sources,
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
        binding_sources: Arc<[ReplayBindingSource]>,
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
        let position = self.history_boundary();
        let as_of_edges = self.equality_boundary();
        let premises: Box<[FactId]> = flat_premises.into();
        self.validate_pending_premises(&premises)
            .unwrap_or_else(|error| panic!("cannot observe firing batch: {error}"));
        let first_firing = FiringId::new(first_native_ordinal);
        self.install_observed_firings(
            rule,
            wave,
            position,
            as_of_edges,
            first_firing,
            premise_arity,
            &premises,
            lanes,
            binding_sources.len(),
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
        binding_sources: Arc<[ReplayBindingSource]>,
        resolver: Arc<dyn PendingPremiseResolver>,
        witness_lanes: &[u32],
    ) -> ObservedFiringBatch {
        let lanes = witness_lanes.len();
        assert!(lanes > 0, "observed firing batch cannot be empty");
        assert!(first_native_ordinal > 0);
        let premises = resolver.resolve_batch(witness_lanes, premise_arity);
        self.validate_pending_premises(&premises)
            .unwrap_or_else(|error| panic!("cannot observe firing batch: {error}"));
        let position = self.history_boundary();
        let as_of_edges = self.equality_boundary();
        let first_firing = FiringId::new(first_native_ordinal);
        self.install_observed_firings(
            rule,
            wave,
            position,
            as_of_edges,
            first_firing,
            premise_arity,
            &premises,
            lanes,
            binding_sources.len(),
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
        let binding_sources = self.register_rule_binding_recipe(rule, binding_sources);
        let first_firing = FiringId::new(self.reserve_firing_ordinals(lanes.len()));
        let position = self.history_boundary();
        let as_of_edges = self.equality_boundary();
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
            position,
            as_of_edges,
            first_firing,
            premise_arity,
            &selected_premises,
            lanes.len(),
            binding_sources.len(),
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

    pub(crate) fn finalize_wave(&self) {
        assert_eq!(
            self.0.poisoned_rule_executions.load(Ordering::Acquire),
            0,
            "cannot finalize causal trace after a panicking rule execution"
        );
        assert_eq!(
            self.0.open_fragments.load(Ordering::Acquire),
            0,
            "cannot finalize causal wave with open worker fragments"
        );
        assert_eq!(
            self.0.abandoned_fragments.load(Ordering::Acquire),
            0,
            "causal worker fragment was dropped without publication"
        );
        assert_eq!(
            self.0.open_native_leases.load(Ordering::Acquire),
            0,
            "cannot finalize causal wave with queued transactional native mutations"
        );
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
    }

    /// Borrow a checked view of finalized raw trace. The closure cannot
    /// return references tied to the arena guards, so no capture storage or
    /// static recipe can escape its read boundary.
    pub fn with_view<R>(
        &self,
        inspect: impl for<'view> FnOnce(&mut TraceView<'view>) -> Result<R, TraceViewError>,
    ) -> Result<R, TraceViewError> {
        let _active = ActiveTraceViewGuard::enter(&self.0.view_active)?;
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0 {
            return Err(TraceViewError::NotFinalized("a rule execution panicked"));
        }
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err(TraceViewError::NotFinalized(
                "worker capture fragments remain open",
            ));
        }
        if self.0.open_native_leases.load(Ordering::Acquire) != 0 {
            return Err(TraceViewError::NotFinalized(
                "transactional native mutations remain queued",
            ));
        }
        if self.0.abandoned_fragments.load(Ordering::Acquire) != 0 {
            return Err(TraceViewError::NotFinalized(
                "a worker capture fragment was abandoned",
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
        let projector = TermProjector::new(
            &arena,
            &recipes,
            &term_recipes,
            &self.0.replay_terms,
            &self.0.next_term,
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
            constructor_occurrence_index: None,
            occurrence_support_cache: HashMap::default(),
            exact_occurrence_support_cache: HashMap::default(),
            counters: TraceViewCounters::default(),
        };
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| inspect(&mut view))) {
            Ok(result) => result,
            Err(payload) => {
                drop(view);
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
mod tests {
    use super::*;

    #[test]
    fn capture_view_rejects_reentrancy_without_poisoning_capture() {
        let trace = Trace::default();
        let error = trace
            .with_view(|_| trace.with_view(|_| Ok(())))
            .unwrap_err();
        assert!(matches!(
            error,
            TraceViewError::Invalid(ref message) if message.contains("not reentrant")
        ));
        trace
            .with_view(|_| {
                std::thread::scope(|scope| {
                    let nested = scope.spawn(|| trace.with_view(|_| Ok(()))).join().unwrap();
                    assert!(matches!(
                        nested,
                        Err(TraceViewError::Invalid(ref message))
                            if message.contains("not reentrant")
                    ));
                });
                Ok(())
            })
            .unwrap();
        assert!(trace.with_view(|_| Ok(())).is_ok());
    }

    #[test]
    fn panicking_capture_view_callback_does_not_poison_capture_locks() {
        let trace = Trace::default();
        let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ =
                trace.with_view(|_| -> Result<(), TraceViewError> { panic!("inspection panic") });
        }));
        assert!(failure.is_err());
        assert!(trace.with_view(|_| Ok(())).is_ok());
    }

    #[test]
    fn physical_rekey_collision_with_same_fact_records_no_logical_transition() {
        let trace = Trace::default();
        let fact = FactId::new(17);
        let sort = ReplaySortId::new(3);
        let pair = TypedCellEquality {
            column: crate::ColumnId::new(0),
            left: EqualityEndpoint {
                sort,
                term: ReplayTermId::MISSING,
                raw: Value::new(20),
            },
            right: EqualityEndpoint {
                sort,
                term: ReplayTermId::MISSING,
                raw: Value::new(10),
            },
        };
        let prepared = || {
            PreparedRekey::from_staged(
                TableId::new(4),
                Wave::new(2),
                fact,
                EdgeHorizon::new(1),
                HistoryPosition::new(9),
                &[pair],
            )
        };

        trace.commit_prepared_rekey(prepared(), RekeyOutcome::Absorbed(fact));
        trace.commit_prepared_rekey(prepared(), RekeyOutcome::Replaced(fact));

        assert!(trace.0.arena.lock().unwrap().rekeys.is_empty());
        assert_eq!(trace.history_boundary(), HistoryPosition::new(0));

        trace.commit_prepared_rekey(prepared(), RekeyOutcome::Absorbed(FactId::new(18)));
        assert_eq!(trace.0.arena.lock().unwrap().rekeys.len(), 1);
        assert_eq!(trace.history_boundary(), HistoryPosition::new(1));
    }

    #[test]
    fn structural_occurrence_rejects_uncertified_non_table_calls() {
        let trace = Trace::default();
        let sort = ReplaySortId::new(1);
        let certified_op = ReplayOpId::new(10);
        let unknown_op = ReplayOpId::new(11);
        let certified_raw = Value::new_const(10);
        let unknown_raw = Value::new_const(11);
        let certified_term = trace
            .intern_call(sort, certified_op, &[], certified_raw)
            .unwrap();
        let unknown_term = trace
            .intern_call(sort, unknown_op, &[], unknown_raw)
            .unwrap();
        trace.register_rule_term_recipe(
            7,
            TermRecipe {
                current_roots: [Some(Arc::new(TermTemplate::Call {
                    sort,
                    op: certified_op,
                    children: Arc::from([]),
                }))]
                .into(),
            },
        );

        trace
            .with_view(|view| {
                let support = view.explain_term_occurrence_at(
                    certified_term,
                    sort,
                    certified_raw,
                    EdgeHorizon::new(0),
                    HistoryPosition::new(0),
                    FactId::MISSING,
                )?;
                assert!(
                    support.is_some(),
                    "a certified pure call reexecutes in replay"
                );
                Ok(())
            })
            .unwrap();

        let error = trace
            .with_view(|view| {
                view.explain_term_occurrence_at(
                    unknown_term,
                    sort,
                    unknown_raw,
                    EdgeHorizon::new(0),
                    HistoryPosition::new(0),
                    FactId::MISSING,
                )
            })
            .unwrap_err();
        assert!(
            matches!(error, TraceViewError::Invalid(ref message) if message.contains("no registered constructor or certified replay recipe")),
            "unknown non-table calls must fail closed: {error:?}"
        );
    }

    #[test]
    fn derived_fact_owns_the_terms_for_its_committed_row() {
        let trace = Trace::default();
        let table = TableId::new_const(0);
        let value_sort = ReplaySortId::new(1);
        let timestamp_sort = ReplaySortId::new(2);
        trace
            .register_table_layout(table, &[Some(value_sort), Some(timestamp_sort)])
            .unwrap();
        let row = [Value::new_const(7), Value::new_const(0)];
        let terms = [
            trace.intern_literal(value_sort, ReplayLiteral::I64(7), row[0]),
            trace.intern_literal(timestamp_sort, ReplayLiteral::I64(0), row[1]),
        ];
        let origin = trace.install_source_row(table, &row, &terms).unwrap();
        let source_cause = trace.source_draft(SourceRef::Synthetic(0));
        let mut source_batch = trace.new_batch();
        let source = source_batch.record_fact_with_origin(table, source_cause, &row, origin);
        source_batch.publish();
        trace.finalize_wave();
        trace
            .with_view(|view| {
                assert_eq!(view.fact_terms(source)?.as_ref(), &terms);
                Ok(())
            })
            .unwrap();

        let binding_sources = [
            ReplayBindingSource::Premise {
                representative: PremiseOccurrence {
                    premise: 0,
                    column: 0,
                },
                occurrences: [PremiseOccurrence {
                    premise: 0,
                    column: 0,
                }]
                .into(),
            },
            ReplayBindingSource::Premise {
                representative: PremiseOccurrence {
                    premise: 0,
                    column: 1,
                },
                occurrences: [PremiseOccurrence {
                    premise: 0,
                    column: 1,
                }]
                .into(),
            },
        ];
        let [(lane, rule_cause)] = trace
            .register_firings(7, Wave::new(1), 1, &binding_sources, &[source], &[0])
            .try_into()
            .unwrap();
        assert_eq!(lane, 0);
        let mut derived_batch = trace.new_batch();
        let derived = derived_batch.record_fact_with_origin(table, rule_cause, &row, origin);
        derived_batch.publish();
        trace.finalize_wave();

        trace
            .with_view(|view| {
                assert_eq!(
                    view.fact_terms(derived)?.as_ref(),
                    &terms,
                    "fact terms belong to the immutable committed row, not its Source cause"
                );
                Ok(())
            })
            .unwrap();

        let [(lane, next_cause)] = trace
            .register_firings(8, Wave::new(2), 1, &binding_sources, &[derived], &[0])
            .try_into()
            .unwrap();
        assert_eq!(lane, 0);
        let mut next_batch = trace.new_batch();
        next_batch.record_fact_with_origin(table, next_cause, &row, origin);
        next_batch.publish();
        trace.finalize_wave();
        trace
            .with_view(|view| {
                let next_firing = (1..=view.totals().firings)
                    .map(FiringId::new)
                    .find(|id| view.firing(*id).is_ok_and(|firing| firing.rule == 8))
                    .unwrap();
                assert_eq!(
                    view.firing_terms(next_firing)?.as_ref(),
                    &terms,
                    "a later rule must resolve terms through a derived FactId"
                );
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn promoted_firings_reconstruct_current_terms_from_static_recipes() {
        let trace = Trace::default();
        let table = TableId::new_const(0);
        let sort = ReplaySortId::new(1);
        trace.register_table_layout(table, &[Some(sort)]).unwrap();

        let source_row = [Value::new_const(7)];
        let source_term = trace.intern_literal(sort, ReplayLiteral::I64(7), source_row[0]);
        let source_origin = trace
            .install_source_row(table, &source_row, &[source_term])
            .unwrap();
        let source_cause = trace.source_draft(SourceRef::Synthetic(0));
        let mut source_batch = trace.new_batch();
        let source_fact =
            source_batch.record_fact_with_origin(table, source_cause, &source_row, source_origin);
        source_batch.publish();
        trace.finalize_wave();

        let constant_value = Value::new_const(8);
        let constant_term = trace.intern_literal(sort, ReplayLiteral::I64(8), constant_value);
        let current_value = Value::new_const(9);
        let current_term = trace.intern_literal(sort, ReplayLiteral::I64(9), current_value);
        let derived_row = [Value::new_const(10)];
        let derived_term = trace.intern_literal(sort, ReplayLiteral::I64(10), derived_row[0]);
        let derived_origin = trace
            .install_source_row(table, &derived_row, &[derived_term])
            .unwrap();

        let binding_sources = [
            ReplayBindingSource::Premise {
                representative: PremiseOccurrence {
                    premise: 0,
                    column: 0,
                },
                occurrences: [PremiseOccurrence {
                    premise: 0,
                    column: 0,
                }]
                .into(),
            },
            ReplayBindingSource::Constant {
                term: constant_term,
            },
            ReplayBindingSource::Current {
                variable: Variable::new(0),
                sort,
                residual: 0,
            },
        ];
        trace.register_rule_term_recipe(
            11,
            TermRecipe {
                current_roots: [Some(Arc::new(TermTemplate::Static { term: current_term }))].into(),
            },
        );
        let [(_, rule_cause)] = trace
            .register_firings(11, Wave::new(1), 1, &binding_sources, &[source_fact], &[0])
            .try_into()
            .unwrap();
        let mut derived_batch = trace.new_batch();
        derived_batch.record_fact_with_origin(table, rule_cause, &derived_row, derived_origin);
        derived_batch.publish();
        trace.finalize_wave();

        trace
            .with_view(|view| {
                assert_eq!(
                    view.firing_terms(FiringId::new(1))?.as_ref(),
                    &[source_term, constant_term, current_term],
                    "lazy expansion must preserve the complete binding layout"
                );
                let counters = view.counters();
                assert_eq!(counters.logical_firing_term_handles, 3);
                assert_eq!(counters.stored_firing_term_handles, 0);
                assert_eq!(
                    counters.logical_firing_term_bytes,
                    3 * mem::size_of::<ReplayTermId>() as u64
                );
                assert_eq!(counters.stored_firing_term_bytes, 0);
                assert_eq!(counters.logical_firing_term_handles, 3);
                Ok(())
            })
            .unwrap();
        assert_eq!(
            trace.replay_term(derived_term),
            Some(ReplayTerm::Literal {
                sort,
                literal: ReplayLiteral::I64(10),
            })
        );
    }

    #[test]
    fn container_anchor_projects_only_referenced_bindings_and_memoizes_repeated_leaves() {
        let trace = Trace::default();
        let table = TableId::new_const(0);
        let source_sort = ReplaySortId::new(10);
        let current_sort = ReplaySortId::new(11);
        let container_sort = ReplaySortId::new(12);
        let pure_op = ReplayOpId::new(10);
        let container_op = ReplayOpId::new(11);
        trace
            .register_table_layout(table, &[Some(source_sort)])
            .unwrap();

        let used_value = Value::new_const(10);
        let unused_value = Value::new_const(11);
        let used_term = trace.intern_literal(source_sort, ReplayLiteral::I64(10), used_value);
        let unused_term = trace.intern_literal(source_sort, ReplayLiteral::I64(11), unused_value);
        let used_origin = trace
            .install_source_row(table, &[used_value], &[used_term])
            .unwrap();
        let unused_origin = trace
            .install_source_row(table, &[unused_value], &[unused_term])
            .unwrap();
        let cause = trace.source_draft(SourceRef::Synthetic(10));
        let mut facts = trace.new_batch();
        let used_fact = facts.record_fact_with_origin(table, cause, &[used_value], used_origin);
        let mut unused_fact =
            facts.record_fact_with_origin(table, cause, &[unused_value], unused_origin);
        for _ in 0..32 {
            unused_fact = facts.record_fact_from_prior(table, cause, &[unused_value], unused_fact);
        }
        facts.publish();

        let binding_sources = [
            ReplayBindingSource::Premise {
                representative: PremiseOccurrence {
                    premise: 0,
                    column: 0,
                },
                occurrences: [PremiseOccurrence {
                    premise: 0,
                    column: 0,
                }]
                .into(),
            },
            ReplayBindingSource::Premise {
                representative: PremiseOccurrence {
                    premise: 1,
                    column: 0,
                },
                occurrences: [PremiseOccurrence {
                    premise: 1,
                    column: 0,
                }]
                .into(),
            },
            // Production lowering expands this pure Current producer into the
            // nested template below. Keeping the binding here proves that the
            // runtime installer never scans unreferenced residual bindings.
            ReplayBindingSource::Current {
                variable: Variable::new(0),
                sort: current_sort,
                residual: 0,
            },
        ];
        let repeated_current = Arc::new(TermTemplate::Call {
            sort: current_sort,
            op: pure_op,
            children: [Arc::new(TermTemplate::Binding { binding: 0 })].into(),
        });
        let site = trace.register_term_origin(TermOriginSpec {
            sort: container_sort,
            term: Arc::new(TermTemplate::Call {
                sort: container_sort,
                op: container_op,
                children: [Arc::clone(&repeated_current), repeated_current].into(),
            }),
        });
        let replay =
            ReplayConstructorSpec::new(container_sort, container_op, [current_sort, current_sort])
                .with_immediate_promotion()
                .with_container_type(TypeId::of::<Vec<Value>>());
        let current_value = Value::new_const(12);
        let container_value = Value::new_const(13);

        reset_term_projector_fact_expansions();
        let installed = trace
            .with_container_anchor_installer(site, &replay, |install| {
                install(
                    &binding_sources,
                    &[used_fact, unused_fact],
                    &[current_value, current_value],
                    container_value,
                )
            })
            .unwrap()
            .unwrap();

        assert_eq!(
            term_projector_fact_expansions(),
            1,
            "the used premise should expand once; the repeated leaf must hit the memo and the deep unused premise must remain cold"
        );
        let ReplayTerm::Call { children, .. } = trace.replay_term(installed).unwrap() else {
            panic!("container anchor did not produce a structural call")
        };
        assert_eq!(children.len(), 2);
        assert_eq!(
            children[0], children[1],
            "the repeated Current producer diverged"
        );
        assert_eq!(
            trace.lookup_term(current_sort, current_value),
            Some(children[0]),
            "the exact nested Current producer was not installed for its runtime value"
        );
    }

    #[test]
    fn replay_value_lookup_is_scoped_by_stable_sort() {
        let trace = Trace::default();
        let value = Value::new_const(7);
        let left_sort = ReplaySortId::new(40);
        let right_sort = ReplaySortId::new(41);
        let left = trace.intern_literal(left_sort, ReplayLiteral::String("left".into()), value);
        let right = trace.intern_literal(right_sort, ReplayLiteral::String("right".into()), value);

        assert_ne!(left, right);
        assert_eq!(trace.lookup_term(left_sort, value), Some(left));
        assert_eq!(trace.lookup_term(right_sort, value), Some(right));
    }
}
