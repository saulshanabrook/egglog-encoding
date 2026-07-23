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

use dashmap::mapref::entry::Entry;

use crate::{AtomId, TableId, Value, Variable, common::DashMap, numeric_id::DenseIdMap};

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
handle!(ReplaySortId, u32);
handle!(ReplayOpId, u32);
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

impl ReplayTermId {
    pub const MISSING: Self = Self(0);

    pub fn is_missing(self) -> bool {
        self == Self::MISSING
    }
}

impl CauseDraftId {
    pub(crate) const UNATTRIBUTED: Self = Self(0);

    pub(crate) fn is_unattributed(self) -> bool {
        self == Self::UNATTRIBUTED
    }
}

/// Backend-neutral payload for one structural literal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReplayLiteral {
    Unit,
    Bool(bool),
    I64(i64),
    F64(u64),
    String(Arc<str>),
    /// Embeddings may reserve stable literal ordinals without exposing a
    /// runtime [`Value`] from the recorded database.
    Internal(u64),
}

/// One compact typed node in the replay-term DAG.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReplayTerm {
    Literal {
        sort: ReplaySortId,
        literal: ReplayLiteral,
    },
    Call {
        sort: ReplaySortId,
        op: ReplayOpId,
        children: Arc<[ReplayTermId]>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplayConstructorSpec {
    pub result_sort: ReplaySortId,
    pub op: ReplayOpId,
    pub child_sorts: Box<[ReplaySortId]>,
}

impl ReplayConstructorSpec {
    pub fn new(
        result_sort: ReplaySortId,
        op: ReplayOpId,
        child_sorts: impl IntoIterator<Item = ReplaySortId>,
    ) -> Self {
        Self {
            result_sort,
            op,
            child_sorts: child_sorts.into_iter().collect(),
        }
    }
}

impl ReplayTerm {
    pub fn sort(&self) -> ReplaySortId {
        match self {
            Self::Literal { sort, .. } | Self::Call { sort, .. } => *sort,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReplayTermCounters {
    pub interned_nodes: u64,
    pub installed_values: u64,
    pub table_layouts: u64,
}

#[derive(Default)]
struct ReplayTermStore {
    by_node: DashMap<ReplayTerm, ReplayTermId>,
    nodes: DashMap<ReplayTermId, ReplayTerm>,
    by_value: DashMap<(ReplaySortId, Value), ReplayTermId>,
    table_layouts: DashMap<TableId, Arc<[Option<ReplaySortId>]>>,
}

impl ReplayTermStore {
    fn intern(&self, next_term: &AtomicU32, node: ReplayTerm) -> ReplayTermId {
        match self.by_node.entry(node.clone()) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let id = ReplayTermId::new(next_term.fetch_add(1, Ordering::Relaxed) + 1);
                assert!(
                    self.nodes.insert(id, node).is_none(),
                    "duplicate ReplayTermId"
                );
                entry.insert(id);
                id
            }
        }
    }

    fn node(&self, id: ReplayTermId) -> Option<ReplayTerm> {
        self.nodes.get(&id).map(|node| node.clone())
    }

    fn install_value(
        &self,
        sort: ReplaySortId,
        value: Value,
        term: ReplayTermId,
    ) -> Result<ReplayTermId, &'static str> {
        let Some(node) = self.nodes.get(&term) else {
            return Err("ReplayTermId is not installed");
        };
        if node.sort() != sort {
            return Err("ReplayTermId sort does not match its value sort");
        }
        drop(node);
        match self.by_value.entry((sort, value)) {
            Entry::Occupied(entry) => Ok(*entry.get()),
            Entry::Vacant(entry) => {
                entry.insert(term);
                Ok(term)
            }
        }
    }

    fn lookup(&self, sort: ReplaySortId, value: Value) -> Option<ReplayTermId> {
        self.by_value.get(&(sort, value)).map(|term| *term)
    }

    fn register_table_layout(
        &self,
        table: TableId,
        sorts: &[Option<ReplaySortId>],
    ) -> Result<(), &'static str> {
        match self.table_layouts.entry(table) {
            Entry::Occupied(entry) if entry.get().as_ref() == sorts => Ok(()),
            Entry::Occupied(_) => Err("table already has a different replay-term layout"),
            Entry::Vacant(entry) => {
                entry.insert(sorts.into());
                Ok(())
            }
        }
    }

    fn install_source_row(
        &self,
        table: TableId,
        row: &[Value],
        terms: &[ReplayTermId],
    ) -> Result<(), &'static str> {
        let Some(layout) = self.table_layouts.get(&table) else {
            return Err("table has no replay-term layout");
        };
        if layout.len() != row.len() || row.len() != terms.len() {
            return Err("source row, term handles, and table layout have different arities");
        }
        for (sort, term) in layout.iter().copied().zip(terms) {
            let Some(sort) = sort else {
                if !term.is_missing() {
                    return Err("ignored source column must use ReplayTermId::MISSING");
                }
                continue;
            };
            let Some(node) = self.nodes.get(term) else {
                return Err("ReplayTermId is not installed");
            };
            if node.sort() != sort {
                return Err("ReplayTermId sort does not match its source column");
            }
        }
        for ((sort, value), term) in layout.iter().copied().zip(row).zip(terms) {
            if let Some(sort) = sort {
                self.install_value(sort, *value, *term)?;
            }
        }
        Ok(())
    }

    fn append_row_terms(
        &self,
        table: TableId,
        row: &[Value],
        out: &mut Vec<ReplayTermId>,
    ) -> Result<FlatRange, &'static str> {
        let Some(layout) = self.table_layouts.get(&table) else {
            return Err("table has no replay-term layout");
        };
        if layout.len() != row.len() {
            return Err("committed row and replay-term table layout have different arities");
        }
        let start = out.len();
        for (sort, value) in layout.iter().copied().zip(row) {
            if let Some(sort) = sort {
                let Some(term) = self.lookup(sort, *value) else {
                    out.truncate(start);
                    return Err("committed row cell has no producer-installed ReplayTermId");
                };
                out.push(term);
            } else {
                out.push(ReplayTermId::MISSING);
            }
        }
        Ok(FlatRange::new(start, row.len()))
    }

    fn counters(&self) -> ReplayTermCounters {
        ReplayTermCounters {
            interned_nodes: self.nodes.len() as u64,
            installed_values: self.by_value.len() as u64,
            table_layouts: self.table_layouts.len() as u64,
        }
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
    pub(crate) current_vars: Box<[(Variable, ReplaySortId)]>,
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
            current_vars: Box::new([]),
        }
    }

    pub fn with_current_vars(
        mut self,
        vars: impl IntoIterator<Item = (Variable, ReplaySortId)>,
    ) -> Self {
        self.current_vars = vars.into_iter().collect();
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReplayBindingSource {
    Premise {
        premise: usize,
        column: usize,
    },
    Current {
        variable: Variable,
        sort: ReplaySortId,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct ActionReceiptSpec {
    pub(crate) rule: u32,
    pub(crate) premise_count: usize,
    pub(crate) premise_slots: Arc<DenseIdMap<AtomId, PremiseSlot>>,
    /// One exact term source for every ordinary variable, in source order.
    pub(crate) binding_sources: Box<[ReplayBindingSource]>,
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

    fn shifted(self, offset: usize) -> Self {
        Self::new(self.as_range().start + offset, self.len as usize)
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
    Source(SourceRef),
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
    Source(SourceRef),
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
    terms: FlatRange,
}

#[derive(Clone, Debug)]
struct DurableFact {
    table: TableId,
    cause: DurableCauseId,
    terms: FlatRange,
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
    fact_terms: Vec<ReplayTermId>,
    pending_equalities: Vec<PendingEquality>,
}

impl ProvisionalArena {
    fn bytes(&self, pending_facts: usize) -> usize {
        self.matches.present() * mem::size_of::<MatchDraft>()
            + self.causes.present() * mem::size_of::<CauseDraft>()
            + self.premises.len() * mem::size_of::<FactId>()
            + self.terms.len() * mem::size_of::<ReplayTermId>()
            + self.fact_terms.len() * mem::size_of::<ReplayTermId>()
            + self.pending_equalities.len() * mem::size_of::<PendingEquality>()
            + pending_facts * mem::size_of::<PendingFact>()
    }

    fn is_empty(&self) -> bool {
        self.matches.present() == 0
            && self.causes.present() == 0
            && self.premises.is_empty()
            && self.terms.is_empty()
            && self.fact_terms.is_empty()
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
    durable_fact_terms: Vec<ReplayTermId>,
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
        match slot {
            FactSlot::Pending(fact) => self
                .provisional
                .fact_terms
                .get(fact.terms.as_range().start + column)
                .copied()
                .filter(|term| !term.is_missing()),
            FactSlot::Durable(fact) => self
                .durable_fact_terms
                .get(fact.terms.as_range().start + column)
                .copied()
                .filter(|term| !term.is_missing()),
        }
    }

    fn unfold_cause(&self, root: DurableCauseId) -> Option<FactCause> {
        let root_node = self.durable_causes.get((root.get() - 1) as usize)?;
        match root_node {
            DurableCause::Source(source) => return Some(FactCause::Source(source.clone())),
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
                        DurableCause::Source(_) => return None,
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
    replay_terms: ReplayTermStore,
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
            replay_terms: ReplayTermStore::default(),
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
    fact_terms: Vec<ReplayTermId>,
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
            fact_terms: Vec::new(),
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

    pub(crate) fn record_fact(
        &mut self,
        table: TableId,
        cause: CauseDraftId,
        row: &[Value],
    ) -> FactId {
        assert!(
            !cause.is_unattributed(),
            "effective commit is missing exact causal attribution"
        );
        let term_range = self
            .shared
            .replay_terms
            .append_row_terms(table, row, &mut self.fact_terms)
            .unwrap_or_else(|error| panic!("cannot record exact committed fact: {error}"));
        let id = FactId::new(ReceiptShared::alloc_u64(&self.shared.next_fact, 1));
        self.facts.push((
            id,
            PendingFact {
                table,
                cause,
                terms: term_range,
            },
        ));
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
            let fact_term_base = arena.provisional.fact_terms.len();
            arena.provisional.fact_terms.append(&mut self.fact_terms);
            for (id, mut fact) in self.facts.drain(..) {
                fact.terms = fact.terms.shifted(fact_term_base);
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
        if !self.drafts.is_empty()
            || !self.facts.is_empty()
            || !self.fact_terms.is_empty()
            || !self.equalities.is_empty()
        {
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
    pub fn register_table_layout(
        &self,
        table: TableId,
        sorts: &[Option<ReplaySortId>],
    ) -> Result<(), &'static str> {
        self.0.replay_terms.register_table_layout(table, sorts)
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
        self.0.replay_terms.install_value(sort, value, term)
    }

    /// Install a typed current-value mapping produced by a primitive. This is
    /// the bounded seam used before general primitive metadata is available.
    pub fn install_value_term(
        &self,
        sort: ReplaySortId,
        value: Value,
        term: ReplayTermId,
    ) -> Result<ReplayTermId, &'static str> {
        self.0.replay_terms.install_value(sort, value, term)
    }

    pub fn lookup_term(&self, sort: ReplaySortId, value: Value) -> Option<ReplayTermId> {
        self.0.replay_terms.lookup(sort, value)
    }

    pub fn replay_term(&self, id: ReplayTermId) -> Option<ReplayTerm> {
        self.0.replay_terms.node(id)
    }

    pub fn replay_term_counters(&self) -> ReplayTermCounters {
        self.0.replay_terms.counters()
    }

    /// A compact test-only structural node. Real producers install equivalent
    /// handles; the receipt kernel never renders the label.
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

    pub(crate) fn new_batch(&self) -> ReceiptBatch {
        ReceiptBatch::new(self.0.clone())
    }

    pub(crate) fn install_source_row(
        &self,
        table: TableId,
        row: &[Value],
        terms: &[ReplayTermId],
    ) -> Result<(), &'static str> {
        self.0.replay_terms.install_source_row(table, row, terms)
    }

    pub(crate) fn source_draft(&self, source: SourceRef) -> CauseDraftId {
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
        let mut arena = self.0.arena.lock().unwrap();
        arena
            .provisional
            .causes
            .install(id.get(), CauseDraft::Source(source));
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
        binding_sources: &[ReplayBindingSource],
        flat_premises: &[FactId],
        flat_current_terms: &[ReplayTermId],
        lanes: &[usize],
    ) -> Vec<(usize, CauseDraftId)> {
        if lanes.is_empty() {
            return Vec::new();
        }
        let current_arity = binding_sources
            .iter()
            .filter(|source| matches!(source, ReplayBindingSource::Current { .. }))
            .count();
        assert_eq!(
            flat_current_terms.len(),
            lanes.len() * current_arity,
            "current replay terms must be dense and lane-aligned"
        );
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
            let mut current = offset * current_arity;
            for source in binding_sources {
                let term = match *source {
                    ReplayBindingSource::Premise { premise, column } => {
                        let fact = premises[premise];
                        arena.fact_term(fact, column).unwrap_or_else(|| {
                            panic!(
                                "missing producer-installed ReplayTermId for {fact:?} column {column}"
                            )
                        })
                    }
                    ReplayBindingSource::Current { .. } => {
                        let term = flat_current_terms[current];
                        current += 1;
                        term
                    }
                };
                arena.provisional.terms.push(term);
            }
            let term_range = FlatRange::new(term_start, binding_sources.len());
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
        arena.counters.term_handles += (lanes.len() * binding_sources.len()) as u64;
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
                CauseDraft::Source(_) => {}
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
                CauseDraft::Source(source) => DurableCause::Source(source),
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
        let fact_terms = mem::take(&mut arena.provisional.fact_terms);
        arena.durable_fact_terms.reserve(fact_terms.len());
        for (slot_index, fact) in pending_facts {
            let index = arena
                .provisional
                .causes
                .index(fact.cause.get())
                .expect("fact cause belongs to current segment");
            let durable = cause_map[index].expect("effective fact cause is reachable");
            let term_start = arena.durable_fact_terms.len();
            arena
                .durable_fact_terms
                .extend_from_slice(&fact_terms[fact.terms.as_range()]);
            arena.facts[slot_index] = Some(FactSlot::Durable(DurableFact {
                table: fact.table,
                cause: durable,
                terms: FlatRange::new(term_start, fact.terms.len as usize),
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
                    arena.durable_fact_terms[fact.terms.as_range()].into();
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
        let terms: Box<[ReplayTermId]> = arena.durable_fact_terms[fact.terms.as_range()].into();
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

    #[test]
    fn derived_fact_owns_the_terms_for_its_committed_row() {
        let receipts = CausalReceipts::default();
        let table = TableId::new_const(0);
        let value_sort = ReplaySortId::new(1);
        let timestamp_sort = ReplaySortId::new(2);
        receipts
            .register_table_layout(table, &[Some(value_sort), Some(timestamp_sort)])
            .unwrap();
        let row = [Value::new_const(7), Value::new_const(0)];
        let terms = [
            receipts.intern_literal(value_sort, ReplayLiteral::I64(7), row[0]),
            receipts.intern_literal(timestamp_sort, ReplayLiteral::I64(0), row[1]),
        ];
        receipts.install_source_row(table, &row, &terms).unwrap();
        let source_cause = receipts.source_draft(SourceRef::Synthetic(0));
        let mut source_batch = receipts.new_batch();
        let source = source_batch.record_fact(table, source_cause, &row);
        source_batch.publish();
        receipts.finalize_wave();
        assert_eq!(receipts.fact_record(source).unwrap().terms.as_ref(), &terms);

        let binding_sources = [
            ReplayBindingSource::Premise {
                premise: 0,
                column: 0,
            },
            ReplayBindingSource::Premise {
                premise: 0,
                column: 1,
            },
        ];
        let [(lane, rule_cause)] = receipts
            .register_rule_matches(
                7,
                CausalWave::new(1),
                1,
                &binding_sources,
                &[source],
                &[],
                &[0],
            )
            .try_into()
            .unwrap();
        assert_eq!(lane, 0);
        let mut derived_batch = receipts.new_batch();
        let derived = derived_batch.record_fact(table, rule_cause, &row);
        derived_batch.publish();
        receipts.finalize_wave();

        assert_eq!(
            receipts.fact_record(derived).unwrap().terms.as_ref(),
            &terms,
            "fact terms belong to the immutable committed row, not its Source cause"
        );

        let [(lane, next_cause)] = receipts
            .register_rule_matches(
                8,
                CausalWave::new(2),
                1,
                &binding_sources,
                &[derived],
                &[],
                &[0],
            )
            .try_into()
            .unwrap();
        assert_eq!(lane, 0);
        let mut next_batch = receipts.new_batch();
        next_batch.record_fact(table, next_cause, &row);
        next_batch.publish();
        receipts.finalize_wave();
        let next_match = receipts
            .snapshot()
            .matches
            .into_iter()
            .find(|matched| matched.rule == 8)
            .unwrap();
        assert_eq!(
            next_match.terms.as_ref(),
            &terms,
            "a later rule must resolve terms through a derived FactId"
        );
    }

    #[test]
    fn out_of_order_fact_publication_rebases_term_ranges_without_holes() {
        let receipts = CausalReceipts::default();
        let table = TableId::new_const(1);
        let sort = ReplaySortId::new(30);
        receipts
            .register_table_layout(table, &[Some(sort)])
            .unwrap();
        let low_row = [Value::new_const(10)];
        let high_row = [Value::new_const(20)];
        let low_term = receipts.intern_literal(sort, ReplayLiteral::I64(10), low_row[0]);
        let high_term = receipts.intern_literal(sort, ReplayLiteral::I64(20), high_row[0]);
        receipts
            .install_source_row(table, &low_row, &[low_term])
            .unwrap();
        receipts
            .install_source_row(table, &high_row, &[high_term])
            .unwrap();

        let low_cause = receipts.source_draft(SourceRef::Synthetic(10));
        let high_cause = receipts.source_draft(SourceRef::Synthetic(20));
        let mut low = receipts.new_batch();
        let low_fact = low.record_fact(table, low_cause, &low_row);
        let mut high = receipts.new_batch();
        let high_fact = high.record_fact(table, high_cause, &high_row);
        assert!(high_fact > low_fact);

        high.publish();
        low.publish();
        receipts.finalize_wave();

        assert_eq!(
            receipts.fact_record(low_fact).unwrap().terms.as_ref(),
            &[low_term]
        );
        assert_eq!(
            receipts.fact_record(high_fact).unwrap().terms.as_ref(),
            &[high_term]
        );
        assert_eq!(
            receipts
                .snapshot()
                .facts
                .iter()
                .flat_map(|fact| fact.terms.iter().copied())
                .collect::<Vec<_>>(),
            [low_term, high_term],
            "FactId order must be independent of batch publication order"
        );
    }

    #[test]
    fn replay_value_lookup_is_scoped_by_stable_sort() {
        let receipts = CausalReceipts::default();
        let value = Value::new_const(7);
        let left_sort = ReplaySortId::new(40);
        let right_sort = ReplaySortId::new(41);
        let left = receipts.intern_literal(left_sort, ReplayLiteral::String("left".into()), value);
        let right =
            receipts.intern_literal(right_sort, ReplayLiteral::String("right".into()), value);

        assert_ne!(left, right);
        assert_eq!(receipts.lookup_term(left_sort, value), Some(left));
        assert_eq!(receipts.lookup_term(right_sort, value), Some(right));
    }
}
