//! Compact causal receipts recorded at native execution sites.
//!
//! Provisional matches and cause nodes are wave-local. Native workers append
//! to local [`ReceiptBatch`] fragments and publish once at an existing table
//! or union-find barrier. Finalization promotes only cause nodes reachable from
//! effective facts and applied unions, then drops the complete provisional
//! segment.

use std::{
    mem,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering},
    },
};

use crate::{AtomId, TableId, Variable, numeric_id::DenseIdMap};

macro_rules! handle {
    ($name:ident, $inner:ty) => {
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name($inner);

        impl $name {
            pub const fn new(value: $inner) -> Self {
                Self(value)
            }

            pub const fn get(self) -> $inner {
                self.0
            }
        }
    };
}

handle!(FactId, u64);
handle!(RuleMatchId, u64);
handle!(ReplayTermId, u32);
handle!(CausalWave, u64);
handle!(CauseDraftId, u64);
handle!(MatchDraftId, u64);
handle!(DurableCauseId, u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PremiseSlot(u16);

impl PremiseSlot {
    pub(crate) fn from_usize(value: usize) -> Self {
        Self(
            value
                .try_into()
                .expect("a receipt has more than u16 premises"),
        )
    }

    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

impl FactId {
    pub(crate) const MISSING: Self = Self(0);

    pub(crate) fn is_missing(self) -> bool {
        self == Self::MISSING
    }
}

impl CauseDraftId {
    pub(crate) const UNATTRIBUTED: Self = Self(0);

    pub(crate) fn is_unattributed(self) -> bool {
        self == Self::UNATTRIBUTED
    }
}

/// Stable reference back to one original input fact.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SourceRef {
    /// Test and embedding callers may provide their own stable input ordinal.
    Synthetic(u64),
}

/// Static receipt metadata retained with a compiled rule.
#[derive(Clone, Debug)]
pub struct RuleReceiptSpec {
    pub(crate) rule: u32,
    pub(crate) premises: Box<[AtomId]>,
    pub(crate) ordinary_vars: Box<[Variable]>,
}

impl RuleReceiptSpec {
    pub fn new(
        rule: u32,
        premises: impl IntoIterator<Item = AtomId>,
        ordinary_vars: impl IntoIterator<Item = Variable>,
    ) -> Self {
        Self {
            rule,
            premises: premises.into_iter().collect(),
            ordinary_vars: ordinary_vars.into_iter().collect(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ActionReceiptSpec {
    pub(crate) rule: u32,
    pub(crate) premise_count: usize,
    pub(crate) premise_slots: Arc<DenseIdMap<AtomId, PremiseSlot>>,
    /// For each ordinary variable, the premise slot and table column whose
    /// committed row carries its producer-installed structural term handle.
    pub(crate) binding_cells: Box<[(usize, usize)]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchRecord {
    pub id: RuleMatchId,
    pub rule: u32,
    pub wave: CausalWave,
    pub premises: Box<[FactId]>,
    pub terms: Box<[ReplayTermId]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FactCause {
    Source(SourceRef),
    Rule(RuleMatchId),
    Merge {
        /// Matches whose proposals contributed to the committed value, in
        /// native merge-fold order.
        rule_matches: Box<[RuleMatchId]>,
        /// Previously committed versions read by the merge fold. Same-wave
        /// proposals do not yet have a FactId.
        prior_facts: Box<[FactId]>,
    },
}

impl FactCause {
    pub fn rule_match(&self) -> Option<RuleMatchId> {
        match self {
            FactCause::Source(_) => None,
            FactCause::Rule(id) => Some(*id),
            FactCause::Merge { rule_matches, .. } => rule_matches.last().copied(),
        }
    }

    pub fn rule_matches(&self) -> &[RuleMatchId] {
        match self {
            FactCause::Source(_) => &[],
            FactCause::Rule(id) => std::slice::from_ref(id),
            FactCause::Merge { rule_matches, .. } => rule_matches,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactRecord {
    pub id: FactId,
    pub table: TableId,
    pub cause: FactCause,
    pub terms: Box<[ReplayTermId]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EqualityReason {
    RuleUnion(RuleMatchId),
    MergeFn {
        rule_matches: Box<[RuleMatchId]>,
        prior_facts: Box<[FactId]>,
    },
}

impl EqualityReason {
    pub fn rule_match(&self) -> Option<RuleMatchId> {
        match self {
            EqualityReason::RuleUnion(id) => Some(*id),
            EqualityReason::MergeFn { rule_matches, .. } => rule_matches.last().copied(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualityRecord {
    pub left: crate::Value,
    pub right: crate::Value,
    pub reason: EqualityReason,
    pub applied: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReceiptCounters {
    pub provisional_matches: u64,
    pub promoted_matches: u64,
    pub premise_handles: u64,
    pub term_handles: u64,
    pub peak_provisional_bytes: u64,
    pub live_provisional_bytes: u64,
    pub promotion_misses: u64,
    pub unattributed_commits: u64,
    pub redundant_unions: u64,
}

#[derive(Clone, Debug, Default)]
pub struct ReceiptSnapshot {
    pub facts: Vec<FactRecord>,
    pub matches: Vec<MatchRecord>,
    pub equalities: Vec<EqualityRecord>,
    pub counters: ReceiptCounters,
}

#[derive(Clone, Copy, Debug)]
struct FlatRange {
    start: u32,
    len: u32,
}

impl FlatRange {
    fn new(start: usize, len: usize) -> Self {
        Self {
            start: start.try_into().expect("receipt arena exceeds u32"),
            len: len.try_into().expect("receipt range exceeds u32"),
        }
    }

    fn as_range(self) -> std::ops::Range<usize> {
        let start = self.start as usize;
        start..start + self.len as usize
    }
}

#[derive(Clone, Debug)]
struct MatchDraft {
    rule: u32,
    wave: CausalWave,
    premises: FlatRange,
    terms: FlatRange,
}

#[derive(Clone, Debug)]
enum CauseDraft {
    Source {
        source: SourceRef,
        terms: FlatRange,
    },
    Rule(MatchDraftId),
    Merge {
        incoming: CauseDraftId,
        prior: PriorVersion,
    },
}

#[derive(Clone, Copy, Debug)]
enum PriorVersion {
    Fact(FactId),
    Draft(CauseDraftId),
}

#[derive(Clone, Debug)]
enum DurableCause {
    Source {
        source: SourceRef,
        terms: FlatRange,
    },
    Rule(RuleMatchId),
    Merge {
        incoming: DurableCauseId,
        prior: DurablePrior,
    },
}

#[derive(Clone, Copy, Debug)]
enum DurablePrior {
    Fact(FactId),
    Cause(DurableCauseId),
}

#[derive(Clone, Debug)]
struct PendingFact {
    table: TableId,
    cause: CauseDraftId,
}

#[derive(Clone, Debug)]
struct DurableFact {
    table: TableId,
    cause: DurableCauseId,
}

#[derive(Clone, Debug)]
enum FactSlot {
    Pending(PendingFact),
    Durable(DurableFact),
}

#[derive(Clone, Debug)]
struct PendingEquality {
    left: crate::Value,
    right: crate::Value,
    cause: CauseDraftId,
}

#[derive(Clone, Debug)]
struct DurableEquality {
    left: crate::Value,
    right: crate::Value,
    cause: DurableCauseId,
}

struct IdSegment<T> {
    base: Option<u64>,
    slots: Vec<Option<T>>,
}

impl<T> Default for IdSegment<T> {
    fn default() -> Self {
        Self {
            base: None,
            slots: Vec::new(),
        }
    }
}

impl<T> IdSegment<T> {
    fn install(&mut self, id: u64, value: T) {
        let mut base = *self.base.get_or_insert(id);
        if id < base {
            let prefix: usize = (base - id)
                .try_into()
                .expect("receipt segment rebase overflow");
            let old = mem::take(&mut self.slots);
            self.slots = Vec::with_capacity(prefix + old.len());
            self.slots.resize_with(prefix, || None);
            self.slots.extend(old);
            self.base = Some(id);
            base = id;
        }
        let index: usize = (id - base).try_into().expect("receipt segment overflow");
        if self.slots.len() <= index {
            self.slots.resize_with(index + 1, || None);
        }
        assert!(
            self.slots[index].replace(value).is_none(),
            "duplicate receipt ID"
        );
    }

    fn index(&self, id: u64) -> Option<usize> {
        let base = self.base?;
        (id >= base).then(|| (id - base).try_into().ok()).flatten()
    }

    fn get(&self, id: u64) -> Option<&T> {
        self.slots.get(self.index(id)?)?.as_ref()
    }

    fn assert_complete(&self, kind: &str) {
        assert!(
            self.slots.iter().all(Option::is_some),
            "missing {kind} publication before causal-wave finalization"
        );
    }

    fn present(&self) -> usize {
        self.slots.iter().filter(|slot| slot.is_some()).count()
    }
}

#[derive(Default)]
struct ProvisionalArena {
    matches: IdSegment<MatchDraft>,
    causes: IdSegment<CauseDraft>,
    premises: Vec<FactId>,
    terms: Vec<ReplayTermId>,
    pending_equalities: Vec<PendingEquality>,
}

impl ProvisionalArena {
    fn bytes(&self, pending_facts: usize) -> usize {
        self.matches.present() * mem::size_of::<MatchDraft>()
            + self.causes.present() * mem::size_of::<CauseDraft>()
            + self.premises.len() * mem::size_of::<FactId>()
            + self.terms.len() * mem::size_of::<ReplayTermId>()
            + self.pending_equalities.len() * mem::size_of::<PendingEquality>()
            + pending_facts * mem::size_of::<PendingFact>()
    }

    fn is_empty(&self) -> bool {
        self.matches.present() == 0
            && self.causes.present() == 0
            && self.premises.is_empty()
            && self.terms.is_empty()
            && self.pending_equalities.is_empty()
    }
}

#[derive(Clone, Debug)]
struct DurableMatch {
    rule: u32,
    wave: CausalWave,
    premises: FlatRange,
    terms: FlatRange,
}

#[derive(Default)]
struct ReceiptArena {
    provisional: ProvisionalArena,
    facts: Vec<Option<FactSlot>>,
    durable_matches: Vec<DurableMatch>,
    durable_premises: Vec<FactId>,
    durable_terms: Vec<ReplayTermId>,
    durable_source_terms: Vec<ReplayTermId>,
    durable_causes: Vec<DurableCause>,
    durable_equalities: Vec<DurableEquality>,
    counters: ReceiptCounters,
}

impl ReceiptArena {
    fn install_fact(&mut self, id: FactId, fact: PendingFact) {
        let index: usize = (id.get() - 1).try_into().expect("FactId overflow");
        if self.facts.len() <= index {
            self.facts.resize_with(index + 1, || None);
        }
        assert!(
            self.facts[index].replace(FactSlot::Pending(fact)).is_none(),
            "duplicate FactId publication"
        );
    }

    fn update_live_bytes(&mut self) {
        let pending_facts = self
            .facts
            .iter()
            .filter(|slot| matches!(slot, Some(FactSlot::Pending(_))))
            .count();
        let live = self.provisional.bytes(pending_facts) as u64;
        self.counters.live_provisional_bytes = live;
        self.counters.peak_provisional_bytes = self.counters.peak_provisional_bytes.max(live);
        self.counters.provisional_matches = self.provisional.matches.present() as u64;
    }

    fn fact_term(&self, id: FactId, column: usize) -> Option<ReplayTermId> {
        if id.is_missing() {
            return None;
        }
        let slot = self.facts.get((id.get() - 1) as usize)?.as_ref()?;
        let cause = match slot {
            FactSlot::Pending(fact) => {
                let CauseDraft::Source { terms, .. } =
                    self.provisional.causes.get(fact.cause.get())?
                else {
                    return None;
                };
                return self
                    .provisional
                    .terms
                    .get(terms.as_range().start + column)
                    .copied();
            }
            FactSlot::Durable(fact) => &self.durable_causes[(fact.cause.get() - 1) as usize],
        };
        let DurableCause::Source { terms, .. } = cause else {
            return None;
        };
        self.durable_source_terms
            .get(terms.as_range().start + column)
            .copied()
    }

    fn unfold_cause(&self, root: DurableCauseId) -> Option<FactCause> {
        let root_node = self.durable_causes.get((root.get() - 1) as usize)?;
        match root_node {
            DurableCause::Source { source, .. } => return Some(FactCause::Source(source.clone())),
            DurableCause::Rule(rule) => return Some(FactCause::Rule(*rule)),
            DurableCause::Merge { .. } => {}
        }

        enum Item {
            Cause(DurableCauseId),
            Fact(FactId),
        }
        let mut stack = vec![Item::Cause(root)];
        let mut rule_matches = Vec::new();
        let mut prior_facts = Vec::new();
        while let Some(item) = stack.pop() {
            match item {
                Item::Fact(fact) => prior_facts.push(fact),
                Item::Cause(cause) => {
                    match &self.durable_causes[(cause.get() - 1) as usize] {
                        DurableCause::Source { .. } => return None,
                        DurableCause::Rule(rule) => rule_matches.push(*rule),
                        DurableCause::Merge { incoming, prior } => {
                            // Stack is LIFO: visit the prior proposal/version first.
                            stack.push(Item::Cause(*incoming));
                            stack.push(match prior {
                                DurablePrior::Fact(fact) => Item::Fact(*fact),
                                DurablePrior::Cause(cause) => Item::Cause(*cause),
                            });
                        }
                    }
                }
            }
        }
        Some(FactCause::Merge {
            rule_matches: rule_matches.into_boxed_slice(),
            prior_facts: prior_facts.into_boxed_slice(),
        })
    }
}

struct ReceiptShared {
    next_fact: AtomicU64,
    next_match_draft: AtomicU64,
    next_rule_match: AtomicU64,
    next_term: AtomicU32,
    next_cause_draft: AtomicU64,
    open_fragments: AtomicUsize,
    abandoned_fragments: AtomicU64,
    arena: Mutex<ReceiptArena>,
}

impl Default for ReceiptShared {
    fn default() -> Self {
        Self {
            next_fact: AtomicU64::new(0),
            next_match_draft: AtomicU64::new(0),
            next_rule_match: AtomicU64::new(0),
            next_term: AtomicU32::new(0),
            next_cause_draft: AtomicU64::new(0),
            open_fragments: AtomicUsize::new(0),
            abandoned_fragments: AtomicU64::new(0),
            arena: Mutex::new(ReceiptArena::default()),
        }
    }
}

impl ReceiptShared {
    fn alloc_u64(counter: &AtomicU64, count: usize) -> u64 {
        assert!(count > 0);
        counter.fetch_add(count as u64, Ordering::Relaxed) + 1
    }
}

/// A worker/shard-local receipt fragment. It performs no locking while native
/// rows are merged and publishes once at the surrounding engine barrier.
pub(crate) struct ReceiptBatch {
    shared: Arc<ReceiptShared>,
    drafts: Vec<(CauseDraftId, CauseDraft)>,
    facts: Vec<(FactId, PendingFact)>,
    equalities: Vec<PendingEquality>,
    redundant_unions: u64,
    unattributed_commits: u64,
    published: bool,
}

impl ReceiptBatch {
    fn new(shared: Arc<ReceiptShared>) -> Self {
        shared.open_fragments.fetch_add(1, Ordering::Relaxed);
        Self {
            shared,
            drafts: Vec::new(),
            facts: Vec::new(),
            equalities: Vec::new(),
            redundant_unions: 0,
            unattributed_commits: 0,
            published: false,
        }
    }

    pub(crate) fn merge_draft(
        &mut self,
        incoming: CauseDraftId,
        prior_fact: FactId,
    ) -> CauseDraftId {
        assert!(
            !incoming.is_unattributed(),
            "merge receipt is missing its incoming cause"
        );
        assert!(
            !prior_fact.is_missing(),
            "merge receipt is missing its prior FactId"
        );
        self.add_draft(CauseDraft::Merge {
            incoming,
            prior: PriorVersion::Fact(prior_fact),
        })
    }

    pub(crate) fn merge_drafts(
        &mut self,
        incoming: CauseDraftId,
        prior: CauseDraftId,
    ) -> CauseDraftId {
        assert!(
            !incoming.is_unattributed() && !prior.is_unattributed(),
            "same-wave merge receipt is missing an exact proposal cause"
        );
        self.add_draft(CauseDraft::Merge {
            incoming,
            prior: PriorVersion::Draft(prior),
        })
    }

    fn add_draft(&mut self, draft: CauseDraft) -> CauseDraftId {
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.shared.next_cause_draft, 1));
        self.drafts.push((id, draft));
        id
    }

    pub(crate) fn record_fact(&mut self, table: TableId, cause: CauseDraftId) -> FactId {
        assert!(
            !cause.is_unattributed(),
            "effective commit is missing exact causal attribution"
        );
        let id = FactId::new(ReceiptShared::alloc_u64(&self.shared.next_fact, 1));
        self.facts.push((id, PendingFact { table, cause }));
        id
    }

    pub(crate) fn record_union(
        &mut self,
        left: crate::Value,
        right: crate::Value,
        cause: CauseDraftId,
        applied: bool,
    ) {
        if !applied {
            self.redundant_unions += 1;
        } else {
            assert!(
                !cause.is_unattributed(),
                "applied union is missing exact causal attribution"
            );
            self.equalities.push(PendingEquality { left, right, cause });
        }
    }

    pub(crate) fn publish(mut self) {
        {
            let mut arena = self.shared.arena.lock().unwrap();
            for (id, draft) in self.drafts.drain(..) {
                arena.provisional.causes.install(id.get(), draft);
            }
            for (id, fact) in self.facts.drain(..) {
                arena.install_fact(id, fact);
            }
            arena
                .provisional
                .pending_equalities
                .append(&mut self.equalities);
            arena.counters.redundant_unions += self.redundant_unions;
            arena.counters.unattributed_commits += self.unattributed_commits;
            arena.update_live_bytes();
        }
        self.published = true;
        self.shared.open_fragments.fetch_sub(1, Ordering::Release);
    }
}

impl Drop for ReceiptBatch {
    fn drop(&mut self) {
        if self.published {
            return;
        }
        if !self.drafts.is_empty() || !self.facts.is_empty() || !self.equalities.is_empty() {
            self.shared
                .abandoned_fragments
                .fetch_add(1, Ordering::Relaxed);
        }
        self.shared.open_fragments.fetch_sub(1, Ordering::Release);
    }
}

/// Shared read/finalization handle to the database's causal receipt arena.
#[derive(Clone, Default)]
pub struct CausalReceipts(Arc<ReceiptShared>);

impl CausalReceipts {
    /// A compact test-only structural node. Real producers install equivalent
    /// handles; the receipt kernel never renders the label.
    pub fn intern_test_term(&self, _label: &str) -> ReplayTermId {
        ReplayTermId::new(self.0.next_term.fetch_add(1, Ordering::Relaxed) + 1)
    }

    pub(crate) fn new_batch(&self) -> ReceiptBatch {
        ReceiptBatch::new(self.0.clone())
    }

    pub(crate) fn source_draft(&self, source: SourceRef, terms: &[ReplayTermId]) -> CauseDraftId {
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
        let mut arena = self.0.arena.lock().unwrap();
        let term_range = FlatRange::new(arena.provisional.terms.len(), terms.len());
        arena.provisional.terms.extend_from_slice(terms);
        arena.provisional.causes.install(
            id.get(),
            CauseDraft::Source {
                source,
                terms: term_range,
            },
        );
        arena.counters.term_handles += terms.len() as u64;
        arena.update_live_bytes();
        id
    }

    /// Register all previously-unregistered action lanes with one arena lock.
    /// FactId lookups are dense and all term cells are resolved in this same
    /// bulk access.
    pub(crate) fn register_rule_matches(
        &self,
        rule: u32,
        wave: CausalWave,
        premise_arity: usize,
        binding_cells: &[(usize, usize)],
        flat_premises: &[FactId],
        lanes: &[usize],
    ) -> Vec<(usize, CauseDraftId)> {
        if lanes.is_empty() {
            return Vec::new();
        }
        let first_match = ReceiptShared::alloc_u64(&self.0.next_match_draft, lanes.len());
        let first_cause = ReceiptShared::alloc_u64(&self.0.next_cause_draft, lanes.len());
        let mut arena = self.0.arena.lock().unwrap();
        let mut result = Vec::with_capacity(lanes.len());
        for (offset, lane) in lanes.iter().copied().enumerate() {
            let premise_start = lane * premise_arity;
            let premises = &flat_premises[premise_start..premise_start + premise_arity];
            let premise_range = FlatRange::new(arena.provisional.premises.len(), premises.len());
            arena.provisional.premises.extend_from_slice(premises);

            let term_start = arena.provisional.terms.len();
            for &(premise, column) in binding_cells {
                let fact = premises[premise];
                let term = arena.fact_term(fact, column).unwrap_or_else(|| {
                    panic!("missing producer-installed ReplayTermId for {fact:?} column {column}")
                });
                arena.provisional.terms.push(term);
            }
            let term_range = FlatRange::new(term_start, arena.provisional.terms.len() - term_start);
            let match_id = MatchDraftId::new(first_match + offset as u64);
            arena.provisional.matches.install(
                match_id.get(),
                MatchDraft {
                    rule,
                    wave,
                    premises: premise_range,
                    terms: term_range,
                },
            );
            let cause_id = CauseDraftId::new(first_cause + offset as u64);
            arena
                .provisional
                .causes
                .install(cause_id.get(), CauseDraft::Rule(match_id));
            result.push((lane, cause_id));
        }
        arena.counters.premise_handles += (lanes.len() * premise_arity) as u64;
        arena.counters.term_handles += (lanes.len() * binding_cells.len()) as u64;
        arena.update_live_bytes();
        result
    }

    /// Promote all roots published by completed native barriers and reclaim the
    /// full wave-local provisional segment.
    pub(crate) fn finalize_wave(&self) {
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
        let mut arena = self.0.arena.lock().unwrap();
        let has_pending_facts = arena
            .facts
            .iter()
            .any(|slot| matches!(slot, Some(FactSlot::Pending(_))));
        if arena.provisional.is_empty() && !has_pending_facts {
            return;
        }
        arena.provisional.matches.assert_complete("match draft");
        arena.provisional.causes.assert_complete("cause draft");
        assert!(
            arena.facts.iter().all(Option::is_some),
            "missing dense FactId publication before causal-wave finalization"
        );

        let cause_len = arena.provisional.causes.slots.len();
        let mut reachable_causes = vec![false; cause_len];
        let mut reachable_matches = vec![false; arena.provisional.matches.slots.len()];
        let mut stack = Vec::new();
        for slot in &arena.facts {
            if let Some(FactSlot::Pending(fact)) = slot {
                stack.push(fact.cause);
            }
        }
        stack.extend(
            arena
                .provisional
                .pending_equalities
                .iter()
                .map(|edge| edge.cause),
        );
        while let Some(cause_id) = stack.pop() {
            let Some(index) = arena.provisional.causes.index(cause_id.get()) else {
                arena.counters.promotion_misses += 1;
                panic!("effective receipt root references an unpublished cause draft");
            };
            if mem::replace(&mut reachable_causes[index], true) {
                continue;
            }
            match arena.provisional.causes.slots[index]
                .as_ref()
                .expect("complete cause segment")
            {
                CauseDraft::Source { .. } => {}
                CauseDraft::Rule(match_id) => {
                    let Some(match_index) = arena.provisional.matches.index(match_id.get()) else {
                        arena.counters.promotion_misses += 1;
                        panic!("effective rule cause references an unpublished match draft");
                    };
                    reachable_matches[match_index] = true;
                }
                CauseDraft::Merge { incoming, prior } => {
                    stack.push(*incoming);
                    if let PriorVersion::Draft(prior) = prior {
                        stack.push(*prior);
                    }
                }
            }
        }

        let mut match_map = vec![None; reachable_matches.len()];
        for (index, promote) in reachable_matches.iter().copied().enumerate() {
            if !promote {
                continue;
            }
            let draft = arena.provisional.matches.slots[index]
                .as_ref()
                .expect("reachable match draft")
                .clone();
            let id = RuleMatchId::new(self.0.next_rule_match.fetch_add(1, Ordering::Relaxed) + 1);
            let premises_start = arena.durable_premises.len();
            let premises = arena.provisional.premises[draft.premises.as_range()].to_vec();
            arena.durable_premises.extend_from_slice(&premises);
            let terms_start = arena.durable_terms.len();
            let terms = arena.provisional.terms[draft.terms.as_range()].to_vec();
            arena.durable_terms.extend_from_slice(&terms);
            arena.durable_matches.push(DurableMatch {
                rule: draft.rule,
                wave: draft.wave,
                premises: FlatRange::new(premises_start, draft.premises.len as usize),
                terms: FlatRange::new(terms_start, draft.terms.len as usize),
            });
            debug_assert_eq!(id.get() as usize, arena.durable_matches.len());
            match_map[index] = Some(id);
            arena.counters.promoted_matches += 1;
        }

        // Cause IDs are allocated after their children, so a single forward
        // pass copies the reachable DAG without recursive unfolding.
        let mut cause_map = vec![None; cause_len];
        for index in 0..cause_len {
            if !reachable_causes[index] {
                continue;
            }
            let draft = arena.provisional.causes.slots[index]
                .as_ref()
                .expect("reachable cause draft")
                .clone();
            let durable = match draft {
                CauseDraft::Source { source, terms } => {
                    let start = arena.durable_source_terms.len();
                    let source_terms = arena.provisional.terms[terms.as_range()].to_vec();
                    arena.durable_source_terms.extend_from_slice(&source_terms);
                    DurableCause::Source {
                        source,
                        terms: FlatRange::new(start, terms.len as usize),
                    }
                }
                CauseDraft::Rule(match_id) => {
                    let index = arena
                        .provisional
                        .matches
                        .index(match_id.get())
                        .expect("rule cause match belongs to current segment");
                    DurableCause::Rule(
                        match_map[index].expect("reachable rule cause promotes its match"),
                    )
                }
                CauseDraft::Merge { incoming, prior } => {
                    let incoming_index = arena
                        .provisional
                        .causes
                        .index(incoming.get())
                        .expect("merge child belongs to current segment");
                    let incoming =
                        cause_map[incoming_index].expect("cause children precede parents");
                    let prior = match prior {
                        PriorVersion::Fact(fact) if !fact.is_missing() => DurablePrior::Fact(fact),
                        PriorVersion::Fact(_) => {
                            arena.counters.promotion_misses += 1;
                            panic!("merge cause references a missing prior FactId");
                        }
                        PriorVersion::Draft(prior) => {
                            let prior_index = arena
                                .provisional
                                .causes
                                .index(prior.get())
                                .expect("merge predecessor belongs to current segment");
                            DurablePrior::Cause(
                                cause_map[prior_index]
                                    .expect("cause predecessors precede merge nodes"),
                            )
                        }
                    };
                    DurableCause::Merge { incoming, prior }
                }
            };
            arena.durable_causes.push(durable);
            let id = DurableCauseId::new(
                arena
                    .durable_causes
                    .len()
                    .try_into()
                    .expect("durable cause arena exceeds u32"),
            );
            cause_map[index] = Some(id);
        }

        let pending_facts = arena
            .facts
            .iter()
            .enumerate()
            .filter_map(|(index, slot)| match slot {
                Some(FactSlot::Pending(fact)) => Some((index, fact.clone())),
                Some(FactSlot::Durable(_)) | None => None,
            })
            .collect::<Vec<_>>();
        for (slot_index, fact) in pending_facts {
            let index = arena
                .provisional
                .causes
                .index(fact.cause.get())
                .expect("fact cause belongs to current segment");
            let durable = cause_map[index].expect("effective fact cause is reachable");
            arena.facts[slot_index] = Some(FactSlot::Durable(DurableFact {
                table: fact.table,
                cause: durable,
            }));
        }
        let pending_equalities = mem::take(&mut arena.provisional.pending_equalities);
        for edge in pending_equalities {
            let index = arena
                .provisional
                .causes
                .index(edge.cause.get())
                .expect("equality cause belongs to current segment");
            arena.durable_equalities.push(DurableEquality {
                left: edge.left,
                right: edge.right,
                cause: cause_map[index].expect("applied equality cause is reachable"),
            });
        }

        arena.provisional = ProvisionalArena::default();
        arena.counters.provisional_matches = 0;
        arena.counters.live_provisional_bytes = 0;
    }

    pub fn snapshot(&self) -> ReceiptSnapshot {
        assert_eq!(
            self.0.open_fragments.load(Ordering::Acquire),
            0,
            "cannot snapshot causal receipts with open worker fragments"
        );
        assert_eq!(
            self.0.abandoned_fragments.load(Ordering::Acquire),
            0,
            "cannot snapshot causal receipts after an unpublished worker fragment"
        );
        let arena = self.0.arena.lock().unwrap();
        assert!(
            arena.provisional.is_empty()
                && !arena
                    .facts
                    .iter()
                    .any(|slot| matches!(slot, Some(FactSlot::Pending(_)))),
            "finalize the causal wave before taking a durable snapshot"
        );
        let matches = arena
            .durable_matches
            .iter()
            .enumerate()
            .map(|(index, record)| MatchRecord {
                id: RuleMatchId::new(index as u64 + 1),
                rule: record.rule,
                wave: record.wave,
                premises: arena.durable_premises[record.premises.as_range()].into(),
                terms: arena.durable_terms[record.terms.as_range()].into(),
            })
            .collect();
        let facts = arena
            .facts
            .iter()
            .enumerate()
            .map(|(index, slot)| {
                let Some(FactSlot::Durable(fact)) = slot else {
                    panic!("snapshot observed non-durable FactId slot")
                };
                let cause = arena
                    .unfold_cause(fact.cause)
                    .expect("durable fact cause must unfold");
                let terms: Box<[ReplayTermId]> =
                    match &arena.durable_causes[(fact.cause.get() - 1) as usize] {
                        DurableCause::Source { terms, .. } => {
                            arena.durable_source_terms[terms.as_range()].into()
                        }
                        DurableCause::Rule(_) | DurableCause::Merge { .. } => Box::new([]),
                    };
                FactRecord {
                    id: FactId::new(index as u64 + 1),
                    table: fact.table,
                    cause,
                    terms,
                }
            })
            .collect();
        let equalities = arena
            .durable_equalities
            .iter()
            .map(|edge| {
                let cause = arena
                    .unfold_cause(edge.cause)
                    .expect("durable equality cause must unfold");
                let reason = match cause {
                    FactCause::Rule(rule) => EqualityReason::RuleUnion(rule),
                    FactCause::Merge {
                        rule_matches,
                        prior_facts,
                    } => EqualityReason::MergeFn {
                        rule_matches,
                        prior_facts,
                    },
                    FactCause::Source(_) => {
                        panic!("source cause cannot justify a union")
                    }
                };
                EqualityRecord {
                    left: edge.left,
                    right: edge.right,
                    reason,
                    applied: true,
                }
            })
            .collect();
        ReceiptSnapshot {
            facts,
            matches,
            equalities,
            counters: arena.counters,
        }
    }

    /// Dense O(1) lookup used by focused identity canaries.
    pub fn fact_record(&self, id: FactId) -> Option<FactRecord> {
        if id.is_missing() {
            return None;
        }
        assert_eq!(
            self.0.open_fragments.load(Ordering::Acquire),
            0,
            "cannot read causal facts with open worker fragments"
        );
        let arena = self.0.arena.lock().unwrap();
        assert!(
            arena.provisional.is_empty(),
            "finalize the causal wave before reading durable facts"
        );
        let FactSlot::Durable(fact) = arena.facts.get((id.get() - 1) as usize)?.as_ref()? else {
            panic!("dense FactId lookup reached an unfinalized slot")
        };
        let cause = arena
            .unfold_cause(fact.cause)
            .expect("durable fact cause must unfold");
        let terms: Box<[ReplayTermId]> =
            match &arena.durable_causes[(fact.cause.get() - 1) as usize] {
                DurableCause::Source { terms, .. } => {
                    arena.durable_source_terms[terms.as_range()].into()
                }
                DurableCause::Rule(_) | DurableCause::Merge { .. } => Box::new([]),
            };
        Some(FactRecord {
            id,
            table: fact.table,
            cause,
            terms,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn receipt_batches_publish_out_of_order_without_holes() {
        let receipts = CausalReceipts::default();
        let mut lower = receipts.new_batch();
        let lower_id = lower.add_draft(CauseDraft::Rule(MatchDraftId::new(1)));
        let mut higher = receipts.new_batch();
        let higher_id = higher.add_draft(CauseDraft::Rule(MatchDraftId::new(2)));
        assert!(higher_id > lower_id);

        // Parallel shards can reach their publication barriers in either
        // order. The dense wave-local segment must rebase when the lower
        // atomic range arrives second.
        higher.publish();
        lower.publish();
        receipts.finalize_wave();

        let snapshot = receipts.snapshot();
        assert!(snapshot.facts.is_empty());
        assert!(snapshot.matches.is_empty());
        assert_eq!(snapshot.counters.provisional_matches, 0);
        assert_eq!(snapshot.counters.live_provisional_bytes, 0);
    }
}
