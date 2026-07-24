//! Compact causal receipts recorded at native execution sites.
//!
//! Match identities are assigned in native batch order. Native workers append
//! compact cause nodes and effective events to local [`ReceiptBatch`]
//! fragments and publish once at an existing table or union-find barrier.

use std::{
    any::TypeId,
    mem,
    sync::{
        Arc, Mutex, OnceLock, RwLock,
        atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering},
    },
};

use dashmap::mapref::entry::Entry;
use smallvec::SmallVec;

use crate::{
    AtomId, QueryEntry, TableId, Value, Variable,
    common::{DashMap, HashMap, HashSet},
    numeric_id::{DenseIdMap, NumericId},
};

#[cfg(test)]
thread_local! {
    static TERM_PROJECTOR_FACT_EXPANSIONS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    static FINALIZE_FACT_SLOT_VISITS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_term_projector_fact_expansions() {
    TERM_PROJECTOR_FACT_EXPANSIONS.set(0);
}

#[cfg(test)]
pub(crate) fn term_projector_fact_expansions() -> usize {
    TERM_PROJECTOR_FACT_EXPANSIONS.get()
}

#[cfg(test)]
fn reset_finalize_fact_slot_visits() {
    FINALIZE_FACT_SLOT_VISITS.set(0);
}

#[cfg(test)]
fn finalize_fact_slot_visits() -> usize {
    FINALIZE_FACT_SLOT_VISITS.get()
}

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
handle!(EqNodeId, u64);
handle!(EqLeafId, u64);
handle!(EqualityEdgeCount, u64);
handle!(CausalWave, u64);
handle!(HistoryPosition, u64);
handle!(RowOriginSiteId, u32);
handle!(TermOriginSiteId, u32);
handle!(CauseDraftId, u64);
handle!(ReceiptCauseId, u32);

/// Stable index into the snapshot-owned, shared causal DAG.
/// A dependency can point directly at an observed rule match or at a shared
/// non-rule cause node. Keeping the tagged distinction public avoids
/// manufacturing one cause-arena node for every native match.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReceiptCauseRef {
    Rule(RuleMatchId),
    Cause(ReceiptCauseId),
}

/// Applied equality edges and their immutable binary join nodes are 1:1.
pub type EqualityEdgeId = EqNodeId;

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

    fn public(self) -> ReceiptCauseId {
        ReceiptCauseId::new(
            self.get()
                .try_into()
                .expect("public receipt cause arena exceeds u32"),
        )
    }
}

/// One word carried by native effects. The high bit distinguishes a direct
/// rule observation from a generic cause-node id; zero remains unattributed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct CauseRef(u64);

impl CauseRef {
    const MATCH_TAG: u64 = 1 << 63;
    pub(crate) const UNATTRIBUTED: Self = Self(0);

    fn rule(matched: RuleMatchId) -> Self {
        assert!(matched.get() != 0 && matched.get() < Self::MATCH_TAG);
        Self(Self::MATCH_TAG | matched.get())
    }

    fn node(node: CauseDraftId) -> Self {
        assert!(!node.is_unattributed() && node.get() < Self::MATCH_TAG);
        Self(node.get())
    }

    fn rule_match(self) -> Option<RuleMatchId> {
        (self.0 & Self::MATCH_TAG != 0).then(|| RuleMatchId::new(self.0 & !Self::MATCH_TAG))
    }

    fn cause_node(self) -> Option<CauseDraftId> {
        (self != Self::UNATTRIBUTED && self.0 & Self::MATCH_TAG == 0)
            .then(|| CauseDraftId::new(self.0))
    }

    fn is_unattributed(self) -> bool {
        self == Self::UNATTRIBUTED
    }

    pub(crate) fn public(self) -> ReceiptCauseRef {
        match self.rule_match() {
            Some(rule) => ReceiptCauseRef::Rule(rule),
            None => ReceiptCauseRef::Cause(
                self.cause_node()
                    .expect("unattributed cause cannot be published")
                    .public(),
            ),
        }
    }
}

impl From<CauseDraftId> for CauseRef {
    fn from(value: CauseDraftId) -> Self {
        Self::node(value)
    }
}

impl From<RuleMatchId> for CauseRef {
    fn from(value: RuleMatchId) -> Self {
        Self::rule(value)
    }
}

impl From<ReceiptCauseRef> for CauseRef {
    fn from(value: ReceiptCauseRef) -> Self {
        match value {
            ReceiptCauseRef::Rule(rule) => Self::rule(rule),
            ReceiptCauseRef::Cause(cause) => Self::node(CauseDraftId::new(cause.get() as u64)),
        }
    }
}

impl From<CauseDraftId> for ReceiptCauseRef {
    fn from(value: CauseDraftId) -> Self {
        Self::Cause(value.public())
    }
}

impl From<ReceiptCauseId> for ReceiptCauseRef {
    fn from(value: ReceiptCauseId) -> Self {
        Self::Cause(value)
    }
}

impl From<RuleMatchId> for ReceiptCauseRef {
    fn from(value: RuleMatchId) -> Self {
        Self::Rule(value)
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReplayConstructorSpec {
    pub result_sort: ReplaySortId,
    pub op: ReplayOpId,
    pub child_sorts: Box<[ReplaySortId]>,
    /// Promote successful calls before later query guards run. Container
    /// primitives need this because native interning is globally visible even
    /// when the surrounding rule match subsequently fails.
    pub promote_immediately: bool,
    /// Physical registry type for a container result. This is intentionally
    /// absent for ordinary e-class constructors and base-value primitives.
    container_type: Option<TypeId>,
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
            promote_immediately: false,
            container_type: None,
        }
    }

    pub fn with_immediate_promotion(mut self) -> Self {
        self.promote_immediately = true;
        self
    }

    pub fn with_container_type(mut self, container_type: TypeId) -> Self {
        self.container_type = Some(container_type);
        self
    }
}

/// Static structural origin of one column in an effective merge result.
/// The bridge derives this once from the source merge expression; native
/// capture stores only the resolved column references for changed facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MergeOriginSelector {
    Incoming {
        column: u16,
    },
    Prior {
        column: u16,
    },
    /// `UnionId` returns the lower native id, choosing the prior value when
    /// both inputs are already identical.
    NativeMin {
        incoming_column: u16,
        prior_column: u16,
    },
    /// The callback result must be exactly one of its two input cells. The
    /// native result decides which structural origin won; equal inputs choose
    /// the prior origin deterministically. This supports semantic min/max on
    /// base values without comparing their opaque runtime Value ids.
    PriorOrIncoming {
        incoming_column: u16,
        prior_column: u16,
    },
    Unsupported,
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
    pub container_anchor_keys: u64,
    pub container_anchor_terms: u64,
}

#[derive(Default)]
struct ReplayTermStore {
    by_node: RwLock<HashMap<ReplayTerm, ReplayTermId>>,
    nodes: RwLock<HashMap<ReplayTermId, ReplayTerm>>,
    by_value: RwLock<HashMap<(ReplaySortId, Value), ReplayTermId>>,
    /// Sparse exact structural versions for mutable ordered-container ids.
    /// Ordinary `by_value` remains first-wins for cheap generic lookup; only
    /// supported container paths enumerate this side index.
    container_anchors: RwLock<HashMap<(ReplaySortId, Value), SmallVec<[ReplayTermId; 2]>>>,
    original_value_by_term: RwLock<HashMap<(ReplaySortId, ReplayTermId), Value>>,
    table_layouts: DashMap<TableId, Arc<[Option<ReplaySortId>]>>,
    table_constructors: DashMap<TableId, ReplayConstructorSpec>,
    table_merge_origins: DashMap<TableId, Arc<[MergeOriginSelector]>>,
    table_merge_identity_guards: DashMap<TableId, (u16, u16)>,
    container_type_by_sort: DashMap<ReplaySortId, TypeId>,
    container_child_sorts: DashMap<ReplaySortId, Arc<[ReplaySortId]>>,
}

impl ReplayTermStore {
    fn intern(&self, next_term: &AtomicU32, node: ReplayTerm) -> ReplayTermId {
        let mut by_node = self.by_node.write().unwrap();
        if let Some(id) = by_node.get(&node).copied() {
            return id;
        }
        let id = ReplayTermId::new(next_term.fetch_add(1, Ordering::Relaxed) + 1);
        // This is the only operation that holds two structural-identity locks.
        // The order is always by_node -> nodes; no nodes reader calls another
        // store method while its guard is live. Publishing the reverse entry
        // last prevents another interner from observing a half-installed id.
        let mut nodes = self.nodes.write().unwrap();
        assert!(
            nodes.insert(id, node.clone()).is_none(),
            "duplicate ReplayTermId"
        );
        assert!(
            by_node.insert(node, id).is_none(),
            "duplicate ReplayTerm node"
        );
        id
    }

    fn node(&self, id: ReplayTermId) -> Option<ReplayTerm> {
        self.nodes.read().unwrap().get(&id).cloned()
    }

    fn lookup_node(&self, node: &ReplayTerm) -> Option<ReplayTermId> {
        self.by_node.read().unwrap().get(node).copied()
    }

    fn install_value(
        &self,
        sort: ReplaySortId,
        value: Value,
        term: ReplayTermId,
    ) -> Result<ReplayTermId, &'static str> {
        let Some(node_sort) = self.nodes.read().unwrap().get(&term).map(ReplayTerm::sort) else {
            return Err("ReplayTermId is not installed");
        };
        if node_sort != sort {
            return Err("ReplayTermId sort does not match its value sort");
        }
        let installed = {
            let mut by_value = self.by_value.write().unwrap();
            *by_value.entry((sort, value)).or_insert(term)
        };
        self.original_value_by_term
            .write()
            .unwrap()
            .entry((sort, term))
            .or_insert(value);
        Ok(installed)
    }

    fn lookup(&self, sort: ReplaySortId, value: Value) -> Option<ReplayTermId> {
        self.by_value.read().unwrap().get(&(sort, value)).copied()
    }

    fn install_container_anchor(
        &self,
        sort: ReplaySortId,
        value: Value,
        term: ReplayTermId,
    ) -> Result<ReplayTermId, &'static str> {
        if !matches!(self.node(term), Some(ReplayTerm::Call { sort: node_sort, .. }) if node_sort == sort)
        {
            return Err("container anchor is not a Call of its declared sort");
        }
        let installed = self.install_value(sort, value, term)?;
        let mut anchors = self.container_anchors.write().unwrap();
        let versions = anchors.entry((sort, value)).or_default();
        if !versions.contains(&term) {
            versions.push(term);
            versions.sort_unstable_by_key(|term| term.get());
        }
        Ok(installed)
    }

    fn container_anchors(&self, sort: ReplaySortId, value: Value) -> SmallVec<[ReplayTermId; 2]> {
        self.container_anchors
            .read()
            .unwrap()
            .get(&(sort, value))
            .cloned()
            .unwrap_or_default()
    }

    fn container_anchors_with_journal(
        &self,
        journal: &ContainerAnchorJournal,
        sort: ReplaySortId,
        value: Value,
    ) -> SmallVec<[ReplayTermId; 2]> {
        let mut anchors = self.container_anchors(sort, value);
        if let Some(staged) = journal.additions(sort, value) {
            for term in staged {
                if !anchors.contains(term) {
                    anchors.push(*term);
                }
            }
        }
        anchors.sort_unstable_by_key(|term| term.get());
        anchors
    }

    fn stage_container_anchor_transfer(
        &self,
        journal: &mut ContainerAnchorJournal,
        container_type: TypeId,
        from: Value,
        to: Value,
    ) -> Result<(), &'static str> {
        if from == to {
            return Ok(());
        }
        let mut found = false;
        for entry in self.container_type_by_sort.iter() {
            if *entry.value() != container_type {
                continue;
            }
            let sort = *entry.key();
            let source = self.container_anchors_with_journal(journal, sort, from);
            if source.is_empty() {
                continue;
            }
            found = true;
            let target = journal.additions.entry((sort, to)).or_default();
            for term in source {
                if !target.contains(&term) {
                    target.push(term);
                }
            }
            target.sort_unstable_by_key(|term| term.get());
        }
        found
            .then_some(())
            .ok_or("container id transfer has no exact structural anchor")
    }

    fn validate_container_anchor_journal(
        &self,
        journal: &ContainerAnchorJournal,
    ) -> Result<(), &'static str> {
        for ((sort, _), terms) in &journal.additions {
            if terms.is_empty() {
                return Err("container anchor journal contains an empty target");
            }
            if self.container_type_by_sort.get(sort).is_none() {
                return Err("container anchor journal references an unregistered sort");
            }
            for term in terms {
                if !matches!(
                    self.node(*term),
                    Some(ReplayTerm::Call { sort: node_sort, .. }) if node_sort == *sort
                ) {
                    return Err("container anchor journal contains a non-Call or wrong-sort term");
                }
            }
        }
        Ok(())
    }

    fn publish_container_anchor_journal(&self, journal: ContainerAnchorJournal) {
        self.validate_container_anchor_journal(&journal)
            .expect("prevalidated container anchor journal became invalid");
        let mut by_value = self.by_value.write().unwrap();
        let mut anchors = self.container_anchors.write().unwrap();
        for (key, mut staged) in journal.additions {
            staged.sort_unstable_by_key(|term| term.get());
            by_value.entry(key).or_insert(staged[0]);
            let current = anchors.entry(key).or_default();
            for term in staged {
                if !current.contains(&term) {
                    current.push(term);
                }
            }
            current.sort_unstable_by_key(|term| term.get());
        }
    }

    fn compatible_call_pairs(
        &self,
        journal: &ContainerAnchorJournal,
        container_type: TypeId,
        left: Value,
        right: Value,
    ) -> Result<SmallVec<[(ReplaySortId, ReplayTermId, ReplayTermId); 4]>, &'static str> {
        let mut pairs = SmallVec::<[(ReplaySortId, ReplayTermId, ReplayTermId); 4]>::new();
        for entry in self.container_type_by_sort.iter() {
            if *entry.value() != container_type {
                continue;
            }
            let sort = *entry.key();
            let left_anchors = self.container_anchors_with_journal(journal, sort, left);
            let right_anchors = self.container_anchors_with_journal(journal, sort, right);
            for left_term in left_anchors {
                for right_term in right_anchors.iter().copied() {
                    if matches!(
                        (self.node(left_term), self.node(right_term)),
                        (
                            Some(ReplayTerm::Call {
                                op: left_op,
                                children: left_children,
                                ..
                            }),
                            Some(ReplayTerm::Call {
                                op: right_op,
                                children: right_children,
                                ..
                            })
                        ) if left_op == right_op && left_children.len() == right_children.len()
                    ) {
                        pairs.push((sort, left_term, right_term));
                    }
                }
            }
        }
        pairs.sort_unstable_by_key(|(sort, left, right)| (sort.get(), left.get(), right.get()));
        if pairs.is_empty() {
            return Err("container ids have no compatible structural Call anchors");
        }
        Ok(pairs)
    }

    fn original_value(&self, sort: ReplaySortId, term: ReplayTermId) -> Option<Value> {
        self.original_value_by_term
            .read()
            .unwrap()
            .get(&(sort, term))
            .copied()
    }

    fn table_layout(&self, table: TableId) -> Option<Arc<[Option<ReplaySortId>]>> {
        self.table_layouts
            .get(&table)
            .map(|layout| Arc::clone(&layout))
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

    fn register_table_constructor(
        &self,
        table: TableId,
        constructor: ReplayConstructorSpec,
    ) -> Result<(), &'static str> {
        match self.table_constructors.entry(table) {
            Entry::Occupied(entry) if entry.get() == &constructor => Ok(()),
            Entry::Occupied(_) => Err("table already has different replay constructor metadata"),
            Entry::Vacant(entry) => {
                entry.insert(constructor);
                Ok(())
            }
        }
    }

    fn register_table_merge_origins(
        &self,
        table: TableId,
        origins: &[MergeOriginSelector],
    ) -> Result<(), &'static str> {
        match self.table_merge_origins.entry(table) {
            Entry::Occupied(entry) if entry.get().as_ref() == origins => Ok(()),
            Entry::Occupied(_) => Err("table already has different merge-origin metadata"),
            Entry::Vacant(entry) => {
                entry.insert(origins.into());
                Ok(())
            }
        }
    }

    fn register_container_type(
        &self,
        constructor: &ReplayConstructorSpec,
    ) -> Result<(), &'static str> {
        let Some(container_type) = constructor.container_type else {
            return Ok(());
        };
        match self.container_type_by_sort.entry(constructor.result_sort) {
            Entry::Occupied(entry) if *entry.get() == container_type => Ok(()),
            Entry::Occupied(_) => Err("replay sort has conflicting physical container types"),
            Entry::Vacant(entry) => {
                entry.insert(container_type);
                Ok(())
            }
        }
    }

    fn register_container_sort(
        &self,
        sort: ReplaySortId,
        container_type: TypeId,
        child_sorts: &[ReplaySortId],
    ) -> Result<(), &'static str> {
        match self.container_type_by_sort.entry(sort) {
            Entry::Occupied(entry) if *entry.get() == container_type => {}
            Entry::Occupied(_) => {
                return Err("replay sort has conflicting physical container types");
            }
            Entry::Vacant(entry) => {
                entry.insert(container_type);
            }
        }
        match self.container_child_sorts.entry(sort) {
            Entry::Occupied(entry) if entry.get().as_ref() == child_sorts => Ok(()),
            Entry::Occupied(_) => Err("replay container sort has conflicting child sorts"),
            Entry::Vacant(entry) => {
                entry.insert(child_sorts.into());
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
        let Some(layout) = self.table_layout(table) else {
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
            let Some(node) = self.node(*term) else {
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

    fn counters(&self) -> ReplayTermCounters {
        let container_anchors = self.container_anchors.read().unwrap();
        ReplayTermCounters {
            interned_nodes: self.nodes.read().unwrap().len() as u64,
            installed_values: self.by_value.read().unwrap().len() as u64,
            table_layouts: self.table_layouts.len() as u64,
            container_anchor_keys: container_anchors.len() as u64,
            container_anchor_terms: container_anchors
                .values()
                .map(|terms| terms.len() as u64)
                .sum(),
        }
    }
}

/// Stable reference back to one original input fact.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SourceRef {
    /// Test and embedding callers may provide their own stable input ordinal.
    Synthetic(u64),
    /// One physical row of an original `(input ...)` command.
    InputRow {
        /// Frontend-global source-command ordinal.
        command: u64,
        /// One-based physical line number in the source file.
        line: u64,
    },
}

/// Static source identity attached to every effective lane of one source
/// action. Source actions do not manufacture rule matches.
#[derive(Clone, Debug)]
pub struct SourceReceiptSpec {
    pub(crate) source: SourceRef,
}

impl SourceReceiptSpec {
    pub fn new(source: SourceRef) -> Self {
        Self { source }
    }
}

/// Static witness and typed-equality layout for one positive check.
#[derive(Clone, Copy, Debug)]
pub enum CheckEndpointSource {
    Premise {
        premise: usize,
        column: usize,
        value: QueryEntry,
        constructor: Option<(ReplaySortId, ReplayOpId)>,
    },
    Current {
        value: QueryEntry,
        sort: ReplaySortId,
    },
}

impl CheckEndpointSource {
    pub fn premise(premise: usize, column: usize, value: QueryEntry) -> Self {
        Self::Premise {
            premise,
            column,
            value,
            constructor: None,
        }
    }

    pub fn premise_constructor(
        premise: usize,
        column: usize,
        value: QueryEntry,
        sort: ReplaySortId,
        op: ReplayOpId,
    ) -> Self {
        Self::Premise {
            premise,
            column,
            value,
            constructor: Some((sort, op)),
        }
    }

    pub fn current(value: QueryEntry, sort: ReplaySortId) -> Self {
        Self::Current { value, sort }
    }

    pub(crate) fn value(&self) -> &QueryEntry {
        match self {
            Self::Premise { value, .. } | Self::Current { value, .. } => value,
        }
    }
}

/// Static witness and typed-equality layout for one positive check.
#[derive(Clone, Debug)]
pub struct CheckReceiptSpec {
    pub(crate) check: u32,
    pub(crate) premises: Box<[AtomId]>,
    pub(crate) equalities: Box<[(CheckEndpointSource, CheckEndpointSource)]>,
}

impl CheckReceiptSpec {
    pub fn new(check: u32, premises: impl IntoIterator<Item = AtomId>) -> Self {
        Self {
            check,
            premises: premises.into_iter().collect(),
            equalities: Box::new([]),
        }
    }

    pub fn with_equalities(
        mut self,
        equalities: impl IntoIterator<Item = (CheckEndpointSource, CheckEndpointSource)>,
    ) -> Self {
        self.equalities = equalities.into_iter().collect();
        self
    }
}

/// Static receipt metadata retained with a compiled rule.
#[derive(Clone, Debug)]
pub struct RuleReceiptSpec {
    pub(crate) rule: u32,
    pub(crate) premises: Box<[AtomId]>,
    pub(crate) bindings: Box<[RuleBindingSpec]>,
}

/// One source-ordered binding retained by an effective rule match.
#[derive(Clone, Copy, Debug)]
pub enum RuleBindingSpec {
    Variable {
        variable: Variable,
        current_sort: Option<ReplaySortId>,
    },
    Constant {
        term: ReplayTermId,
        sort: ReplaySortId,
    },
}

impl RuleBindingSpec {
    pub fn variable(variable: Variable, current_sort: Option<ReplaySortId>) -> Self {
        Self::Variable {
            variable,
            current_sort,
        }
    }

    pub fn constant(term: ReplayTermId, sort: ReplaySortId) -> Self {
        Self::Constant { term, sort }
    }
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
            bindings: ordinary_vars
                .into_iter()
                .map(|variable| RuleBindingSpec::variable(variable, None))
                .collect(),
        }
    }

    pub fn with_bindings(
        rule: u32,
        premises: impl IntoIterator<Item = AtomId>,
        bindings: impl IntoIterator<Item = RuleBindingSpec>,
    ) -> Self {
        Self {
            rule,
            premises: premises.into_iter().collect(),
            bindings: bindings.into_iter().collect(),
        }
    }

    pub fn with_current_vars(
        mut self,
        vars: impl IntoIterator<Item = (Variable, ReplaySortId)>,
    ) -> Self {
        let current_vars = vars.into_iter().collect::<HashMap<_, _>>();
        for binding in &mut self.bindings {
            if let RuleBindingSpec::Variable {
                variable,
                current_sort,
            } = binding
                && let Some(sort) = current_vars.get(variable)
            {
                *current_sort = Some(*sort);
            }
        }
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PremiseOccurrence {
    pub(crate) premise: usize,
    pub(crate) column: usize,
}

/// One node in the static source-to-action term recipe. Nodes share producer
/// subgraphs while a rule is compiled and instantiate only for promoted
/// observations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TermTemplate {
    Binding {
        binding: u16,
    },
    PremiseCell {
        premise: u16,
        column: u16,
    },
    Static {
        term: ReplayTermId,
    },
    Call {
        sort: ReplaySortId,
        op: ReplayOpId,
        children: Arc<[Arc<TermTemplate>]>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TermRecipe {
    /// Exact structural producers for `ReplayBindingSource::Current` entries,
    /// in residual-slot order. Premise and constant roots already live in the
    /// binding recipe and are not duplicated here.
    pub(crate) current_roots: Arc<[Option<Arc<TermTemplate>>]>,
}

#[derive(Default)]
struct StaticTermRecipeStore {
    rules: HashMap<u32, Arc<TermRecipe>>,
    row_origins: Vec<RowOriginSpec>,
    term_origins: Vec<TermOriginSpec>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RowOriginSpec {
    pub(crate) table: TableId,
    /// One exact structural recipe per physical table column. Engine-only
    /// columns are `None`; replay-typed columns must be reconstructible.
    pub(crate) cells: Arc<[Option<Arc<TermTemplate>>]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TermOriginSpec {
    pub(crate) sort: ReplaySortId,
    pub(crate) term: Arc<TermTemplate>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReplayBindingSource {
    Premise {
        /// Every source-ordered body cell containing this variable. The first
        /// premise containing the variable remains the public binding source;
        /// all occurrences are historical equality obligations for slicing.
        representative: PremiseOccurrence,
        occurrences: Arc<[PremiseOccurrence]>,
    },
    Current {
        variable: Variable,
        sort: ReplaySortId,
        /// Dense position in the match's physically stored residual terms.
        residual: u32,
    },
    Constant {
        term: ReplayTermId,
    },
}

impl ReplayBindingSource {
    #[cfg(test)]
    pub(crate) fn premise_occurrences(&self) -> Option<&[PremiseOccurrence]> {
        match self {
            Self::Premise { occurrences, .. } => Some(occurrences),
            Self::Current { .. } | Self::Constant { .. } => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ActionReceiptKind {
    Rule(u32),
    Source(SourceRef),
    Check,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum CheckTermSource {
    Premise {
        premise: usize,
        column: usize,
    },
    Constructor {
        premise: usize,
        input_columns: usize,
        op: ReplayOpId,
    },
    Current,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CheckEndpointSpec {
    pub(crate) value: QueryEntry,
    pub(crate) sort: ReplaySortId,
    pub(crate) term: CheckTermSource,
}

#[derive(Clone, Debug)]
pub(crate) struct ActionReceiptSpec {
    pub(crate) kind: ActionReceiptKind,
    pub(crate) premise_count: usize,
    pub(crate) premise_slots: Arc<DenseIdMap<AtomId, PremiseSlot>>,
    /// One exact term source for every ordinary variable, in source order.
    pub(crate) binding_sources: Arc<[ReplayBindingSource]>,
}

impl ActionReceiptSpec {
    pub(crate) fn captures_witness(&self) -> bool {
        self.premise_count != 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchRecord {
    pub id: RuleMatchId,
    pub rule: u32,
    pub wave: CausalWave,
    /// Inclusive cross-stream high-water captured once when native matching
    /// began. Repeated-variable and equality-body obligations must never use
    /// facts, rekeys, or zero-edge aliases published later in the wave.
    pub position: HistoryPosition,
    /// Applied equality prefix visible at the same match-start boundary.
    pub as_of_edges: EqualityEdgeCount,
    pub premises: Box<[FactId]>,
    pub terms: Box<[ReplayTermId]>,
    /// Immutable prior facts read by table merge callbacks for this firing,
    /// in native callback order. A read is retained only when another effect
    /// promotes the firing.
    pub merge_reads: Box<[FactId]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RebuildDependency {
    pub wave: CausalWave,
    pub prior_fact: FactId,
    pub equalities: EqualityLandmark,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RekeyOutcome {
    Moved,
    Absorbed(FactId),
    Replaced(FactId),
}

/// One effective logical-row relocation. Pure rekeys preserve `fact`; a
/// collision records which live fact absorbed or replaced it. The equality
/// landmark is immutable and historically bounded at the rebuild decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RekeyRecord {
    pub fact: FactId,
    pub table: TableId,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub equalities: EqualityLandmark,
    pub outcome: RekeyOutcome,
}

/// Exact positional child changes produced by one serial container rebuild.
///
/// The container's structural replay term remains immutable. Re-executing the
/// child equalities makes that same term denote the rebuilt native container.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContainerDependency {
    pub wave: CausalWave,
    pub equalities: EqualityLandmark,
}

/// Receipt-only logical identity for one container version. Public snapshots
/// expose the dependency itself; native refresh bookkeeping additionally
/// needs the exact structural producer that owned the raw container id.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContainerVersionDependency {
    pub(crate) outer: EqualityEndpoint,
    pub(crate) dependency: Arc<ContainerDependency>,
}

#[derive(Clone)]
pub(crate) struct ContainerParentCandidate {
    pub(crate) endpoint: EqualityEndpoint,
    pub(crate) child_sorts: Arc<[ReplaySortId]>,
}

/// Forward-only overlay of existing immutable container terms during one
/// cloned-registry rebuild transaction. Source mappings remain historical;
/// only additional `(sort, raw) -> term` anchors are staged. Abort drops this
/// value without touching shared receipt state.
#[derive(Clone, Debug, Default)]
pub(crate) struct ContainerAnchorJournal {
    additions: HashMap<(ReplaySortId, Value), SmallVec<[ReplayTermId; 2]>>,
}

impl ContainerAnchorJournal {
    fn additions(&self, sort: ReplaySortId, value: Value) -> Option<&[ReplayTermId]> {
        self.additions.get(&(sort, value)).map(SmallVec::as_slice)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.additions.is_empty()
    }

    pub(crate) fn extend(&mut self, other: Self) {
        for (key, terms) in other.additions {
            let current = self.additions.entry(key).or_default();
            for term in terms {
                if !current.contains(&term) {
                    current.push(term);
                }
            }
            current.sort_unstable_by_key(|term| term.get());
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FactCause {
    Source(SourceRef),
    Rule(RuleMatchId),
    Rebuild {
        wave: CausalWave,
        prior_fact: FactId,
        equalities: EqualityLandmark,
    },
    ContainerRefresh {
        wave: CausalWave,
        prior_fact: FactId,
        equalities: EqualityLandmark,
    },
    Merge {
        /// Shared exact native fold DAG. This preserves cross-kind ordering
        /// without copying a growing dependency prefix into every fact.
        cause: ReceiptCauseId,
    },
}

impl FactCause {
    pub fn rule_match(&self) -> Option<RuleMatchId> {
        match self {
            FactCause::Source(_)
            | FactCause::Rebuild { .. }
            | FactCause::ContainerRefresh { .. } => None,
            FactCause::Rule(id) => Some(*id),
            FactCause::Merge { .. } => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactRecord {
    pub id: FactId,
    pub table: TableId,
    /// Serial logical order shared with applied equalities, rekeys, and
    /// selected checks. Cold projection uses it to attach exact fact terms
    /// to the native equality component that existed when the fact appeared.
    pub position: HistoryPosition,
    pub cause: FactCause,
    pub values: Box<[Value]>,
    pub terms: Box<[ReplayTermId]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EqualityReason {
    RuleUnion(RuleMatchId),
    MergeFn {
        /// Shared exact cause root. Dependencies are unfolded lazily through
        /// [`ReceiptSnapshot::cause_dependencies`].
        cause: ReceiptCauseId,
    },
    Congruence {
        /// Shared exact cause root; no growing prefix is copied per edge.
        cause: ReceiptCauseId,
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
    },
}

impl EqualityReason {
    pub fn rule_match(&self) -> Option<RuleMatchId> {
        match self {
            EqualityReason::RuleUnion(id) => Some(*id),
            EqualityReason::MergeFn { .. } => None,
            EqualityReason::Congruence { .. } => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiptCausePrior {
    Fact(FactId),
    Cause(ReceiptCauseRef),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiptCauseRecord {
    Source(SourceRef),
    Rebuild {
        wave: CausalWave,
        prior_fact: FactId,
        equalities: EqualityLandmark,
    },
    ContainerCanonicalize {
        wave: CausalWave,
        equalities: EqualityLandmark,
    },
    ContainerRefresh {
        wave: CausalWave,
        prior_fact: FactId,
        equalities: EqualityLandmark,
    },
    Merge {
        incoming: ReceiptCauseRef,
        prior: ReceiptCausePrior,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiptCauseDependency<'a> {
    Source(&'a SourceRef),
    Rule(RuleMatchId),
    Fact(FactId),
    Rebuild {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: &'a [TypedCellEquality],
    },
    ContainerCanonicalize {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: &'a [TypedCellEquality],
    },
    ContainerRefresh {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: &'a [TypedCellEquality],
    },
}

enum CauseDependencyItem {
    Cause(ReceiptCauseRef),
    Fact(FactId),
}

pub struct ReceiptCauseDependencies<'a> {
    causes: &'a [ReceiptCauseRecord],
    stack: Vec<CauseDependencyItem>,
}

impl<'a> Iterator for ReceiptCauseDependencies<'a> {
    type Item = ReceiptCauseDependency<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.stack.pop()? {
                CauseDependencyItem::Fact(fact) => {
                    return Some(ReceiptCauseDependency::Fact(fact));
                }
                CauseDependencyItem::Cause(ReceiptCauseRef::Rule(rule)) => {
                    return Some(ReceiptCauseDependency::Rule(rule));
                }
                CauseDependencyItem::Cause(ReceiptCauseRef::Cause(cause)) => {
                    match &self.causes[(cause.get() - 1) as usize] {
                        ReceiptCauseRecord::Source(source) => {
                            return Some(ReceiptCauseDependency::Source(source));
                        }
                        ReceiptCauseRecord::Rebuild {
                            wave,
                            prior_fact,
                            equalities,
                        } => {
                            return Some(ReceiptCauseDependency::Rebuild {
                                wave: *wave,
                                prior_fact: *prior_fact,
                                as_of_edges: equalities.as_of_edges,
                                position: equalities.position,
                                equalities: &equalities.pairs,
                            });
                        }
                        ReceiptCauseRecord::ContainerCanonicalize { wave, equalities } => {
                            return Some(ReceiptCauseDependency::ContainerCanonicalize {
                                wave: *wave,
                                as_of_edges: equalities.as_of_edges,
                                position: equalities.position,
                                equalities: &equalities.pairs,
                            });
                        }
                        ReceiptCauseRecord::ContainerRefresh {
                            wave,
                            prior_fact,
                            equalities,
                        } => {
                            return Some(ReceiptCauseDependency::ContainerRefresh {
                                wave: *wave,
                                prior_fact: *prior_fact,
                                as_of_edges: equalities.as_of_edges,
                                position: equalities.position,
                                equalities: &equalities.pairs,
                            });
                        }
                        ReceiptCauseRecord::Merge { incoming, prior } => {
                            self.stack.push(CauseDependencyItem::Cause(*incoming));
                            self.stack.push(match prior {
                                ReceiptCausePrior::Fact(fact) => CauseDependencyItem::Fact(*fact),
                                ReceiptCausePrior::Cause(cause) => {
                                    CauseDependencyItem::Cause(*cause)
                                }
                            });
                        }
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EqualityEndpoint {
    pub sort: ReplaySortId,
    pub term: ReplayTermId,
    pub raw: crate::Value,
}

/// Exact native support retained for the first successful match of one check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckRoot {
    pub check: u32,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub premises: Box<[FactId]>,
    pub equalities: Box<[(EqualityEndpoint, EqualityEndpoint)]>,
    pub as_of_edges: EqualityEdgeCount,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypedCellEquality {
    pub column: crate::ColumnId,
    pub left: EqualityEndpoint,
    pub right: EqualityEndpoint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualityLandmark {
    /// Dense applied-edge prefix visible at this exact global history point.
    pub as_of_edges: EqualityEdgeCount,
    /// Cross-stream cutoff for zero-edge fact/rekey/alias attachments.
    pub position: HistoryPosition,
    pub pairs: Box<[TypedCellEquality]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum EqComponentRef {
    Leaf(EqLeafId),
    Node(EqNodeId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EqLeafRecord {
    pub id: EqLeafId,
    pub position: HistoryPosition,
    pub endpoint: EqualityEndpoint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqNodeRecord {
    pub id: EqNodeId,
    pub left: EqComponentRef,
    pub right: EqComponentRef,
    /// Occurrence-scoped leaf through which the edge enters each child.
    pub left_anchor: EqLeafId,
    pub right_anchor: EqLeafId,
    pub edge: EqualityEdgeId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualityRecord {
    pub id: EqualityEdgeId,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub left: EqualityEndpoint,
    pub right: EqualityEndpoint,
    pub native_parent: crate::Value,
    pub native_child: crate::Value,
    pub reason: EqualityReason,
}

/// One effective native union between distinct runtime ids whose endpoint
/// terms already belong to the same logical equality component. It is
/// attributable but adds no new logical equality, so it deliberately does
/// not allocate an equality-forest edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeAliasRecord {
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub left: EqualityEndpoint,
    pub right: EqualityEndpoint,
    pub native_parent: crate::Value,
    pub native_child: crate::Value,
    pub reason: EqualityReason,
}

/// A zero-edge structural alias learned when an exact fact term is published
/// into a native equality component that already has another structural
/// representative. The fact is the proof-producing attachment; no synthetic
/// equality edge is invented.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TermAttachmentDependency {
    Fact(FactId),
    Cause(ReceiptCauseRef),
    Rekey {
        position: HistoryPosition,
        fact: FactId,
    },
    /// `EqualityTermRef::Exact` proved this current-value alias existed
    /// before the applied event was staged. Its original occurrence carries
    /// the replay dependency; catch-up itself adds none.
    Trusted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TermAttachment {
    position: HistoryPosition,
    sort: ReplaySortId,
    raw: Value,
    term: ReplayTermId,
    leaf: EqLeafId,
    dependency: TermAttachmentDependency,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReceiptCounters {
    pub provisional_matches: u64,
    /// Every normal-return native rule lane, including inert observations.
    pub observed_matches: u64,
    pub promoted_matches: u64,
    pub premise_handles: u64,
    /// Logical match-term handles exposed by [`MatchRecord::terms`].
    pub logical_match_term_handles: u64,
    /// Match-term handles physically retained by the receipt arena.
    pub stored_match_term_handles: u64,
    /// Logical bytes exposed by [`MatchRecord::terms`].
    pub logical_match_term_bytes: u64,
    /// Match-term bytes physically retained by the receipt arena.
    pub stored_match_term_bytes: u64,
    /// Backward-compatible alias for [`Self::logical_match_term_handles`].
    pub term_handles: u64,
    /// Fact-owned constructor terms copied while preparing merge causes.
    /// This must scale with effective merged facts, not attempted collisions.
    pub merge_prior_term_copies: u64,
    pub peak_provisional_bytes: u64,
    pub live_provisional_bytes: u64,
    pub promotion_misses: u64,
    pub unattributed_commits: u64,
    pub redundant_unions: u64,
    /// Effective native unions that added no logical equality edge.
    pub native_alias_unions: u64,
    /// Semantic rows for which an exact rebuild cause was captured.
    pub rebuild_causes: u64,
    /// Changed typed cells stored across those rebuild causes.
    pub rebuild_equalities: u64,
    /// Logical bytes of rebuild cause and changed-cell payload captured.
    pub rebuild_bytes: u64,
    /// Container canonicalization and same-ID parent-refresh causes retained.
    pub container_causes: u64,
    /// Positional child equality pairs stored across container causes.
    pub container_equalities: u64,
    /// Logical bytes of container cause and child-pair payload captured.
    pub container_bytes: u64,
    /// `Current` binding slots with a complete replay-safe structural recipe.
    pub supported_current_recipe_roots: u64,
    /// `Current` binding slots whose structural producer remains unsupported.
    /// Reached slots fail closed during slicing; this counter makes cohort
    /// coverage visible before replay is wired.
    pub missing_current_recipe_roots: u64,
}

#[derive(Clone, Debug, Default)]
pub struct ReceiptSnapshot {
    pub facts: Vec<FactRecord>,
    pub matches: Vec<MatchRecord>,
    pub equality_leaves: Vec<EqLeafRecord>,
    pub equality_nodes: Vec<EqNodeRecord>,
    pub equalities: Vec<EqualityRecord>,
    pub native_aliases: Vec<NativeAliasRecord>,
    pub rekeys: Vec<RekeyRecord>,
    pub causes: Vec<ReceiptCauseRecord>,
    pub check_roots: Vec<CheckRoot>,
    pub counters: ReceiptCounters,
    equality_history_prefix: Box<[usize]>,
    equality_history_positions: Box<[HistoryPosition]>,
    term_attachments: Box<[TermAttachment]>,
}

impl ReceiptSnapshot {
    pub fn cause_dependencies(
        &self,
        root: impl Into<ReceiptCauseRef>,
    ) -> ReceiptCauseDependencies<'_> {
        let root = root.into();
        if let ReceiptCauseRef::Cause(root) = root {
            assert!(
                root.get() > 0 && root.get() as usize <= self.causes.len(),
                "receipt cause root is outside this snapshot"
            );
        }
        ReceiptCauseDependencies {
            causes: &self.causes,
            stack: vec![CauseDependencyItem::Cause(root)],
        }
    }

    /// Lazily unfold one exact applied-edge explanation as it existed at the
    /// supplied historical landmark. This walks only immutable receipt data;
    /// native path compression and later equality edges are irrelevant.
    ///
    /// The applied forest supplies one deterministic explanation. Shorter
    /// alternatives through redundant proposals are deliberately not stored
    /// on the recording hot path.
    #[cfg(test)]
    pub fn explain_equality_at_end(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        as_of: EqualityEdgeCount,
    ) -> Result<Box<[EqualityEdgeId]>, &'static str> {
        self.equality_explanation_index_at_end(as_of)?
            .explain_equality(left, right)
    }

    /// Explain at an exact cross-stream logical point. Unlike an edge-only
    /// cutoff, this includes zero-edge fact attachments published after the
    /// most recent union and excludes attachments published after the caller.
    pub fn explain_equality_at(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<Box<[EqualityEdgeId]>, &'static str> {
        self.equality_explanation_index_at(as_of, position)?
            .explain_equality(left, right)
    }

    pub fn explain_equality_support_at(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<EqualitySupport, &'static str> {
        self.equality_explanation_index_at(as_of, position)?
            .explain_equality_support(left, right)
    }

    /// Build one immutable forest index for a historical cutoff. A slicer
    /// should reuse this value for every changed-cell pair at that cutoff;
    /// membership checks during explanation are constant-time interval tests.
    #[cfg(test)]
    pub fn equality_explanation_index_at_end(
        &self,
        as_of: EqualityEdgeCount,
    ) -> Result<EqualityExplanationIndex<'_>, &'static str> {
        EqualityExplanationIndex::new(self, as_of, HistoryPosition::new(u64::MAX))
    }

    pub fn equality_explanation_index_at(
        &self,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<EqualityExplanationIndex<'_>, &'static str> {
        EqualityExplanationIndex::new(self, as_of, position)
    }
}

pub struct EqualityExplanationIndex<'a> {
    snapshot: &'a ReceiptSnapshot,
    cutoff: usize,
    leaf_positions: HashMap<EqLeafId, (EqComponentRef, usize)>,
    endpoint_leaves: HashMap<(ReplaySortId, ReplayTermId, Value), EqLeafId>,
    term_attachment_dependencies:
        HashMap<(ReplaySortId, ReplayTermId, Value), TermAttachmentDependency>,
    leaf_dependencies: HashMap<EqLeafId, TermAttachmentDependency>,
    node_intervals: Vec<Option<(usize, usize)>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualitySupport {
    pub edges: Box<[EqualityEdgeId]>,
    /// Exact fact publications needed for zero-edge structural attachment.
    /// These are dependencies, not synthetic equality edges.
    pub facts: Box<[FactId]>,
    /// Exact promoted causes that introduced a structural endpoint into an
    /// already-existing native component without adding an equality edge.
    pub causes: Box<[ReceiptCauseRef]>,
    /// Pure-rekey navigation records needed to make an occurrence available
    /// under its later raw value. Positions uniquely identify snapshot rekeys.
    pub rekeys: Box<[HistoryPosition]>,
}

impl<'a> EqualityExplanationIndex<'a> {
    fn new(
        snapshot: &'a ReceiptSnapshot,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<Self, &'static str> {
        let history_cutoff: usize = as_of
            .get()
            .try_into()
            .map_err(|_| "equality landmark exceeds addressable receipt storage")?;
        if history_cutoff > snapshot.equality_history_prefix.len() {
            return Err("equality landmark exceeds the recorded applied-edge prefix");
        }
        if position != HistoryPosition::new(u64::MAX) {
            let visible = snapshot
                .equality_history_positions
                .partition_point(|event| *event <= position);
            if visible != history_cutoff {
                return Err("equality edge cutoff disagrees with the global history position");
            }
        }
        let cutoff = history_cutoff
            .checked_sub(1)
            .map_or(0, |index| snapshot.equality_history_prefix[index]);
        if cutoff > snapshot.equality_nodes.len() || cutoff > snapshot.equalities.len() {
            return Err("equality history maps beyond the cold logical forest");
        }

        let mut leaf_parents = vec![None; snapshot.equality_leaves.len()];
        let mut node_parents = vec![None; cutoff];
        for index in 0..cutoff {
            let expected = EqNodeId::new(index as u64 + 1);
            let node = &snapshot.equality_nodes[index];
            let equality = &snapshot.equalities[index];
            if node.id != expected || node.edge != expected || equality.id != expected {
                return Err("equality receipt IDs are not one dense applied-edge prefix");
            }
            if equality.left.sort != equality.right.sort {
                return Err("one applied equality edge crosses logical sorts");
            }
            for child in [node.left, node.right] {
                match child {
                    EqComponentRef::Leaf(leaf) => {
                        let leaf_index: usize = leaf
                            .get()
                            .checked_sub(1)
                            .ok_or("equality forest references leaf zero")?
                            .try_into()
                            .map_err(|_| "equality leaf ID exceeds addressable storage")?;
                        if leaf_index >= snapshot.equality_leaves.len() {
                            return Err("equality forest references an absent leaf");
                        }
                        if leaf_parents[leaf_index].replace(node.id).is_some() {
                            return Err("equality forest leaf has multiple parents");
                        }
                    }
                    EqComponentRef::Node(child) => {
                        let child_index: usize = child
                            .get()
                            .checked_sub(1)
                            .ok_or("equality forest references node zero")?
                            .try_into()
                            .map_err(|_| "equality node ID exceeds addressable storage")?;
                        if child_index >= index {
                            return Err("equality forest child does not precede its parent");
                        }
                        if node_parents[child_index].replace(node.id).is_some() {
                            return Err("equality forest node has multiple parents");
                        }
                    }
                }
            }
        }

        enum Visit {
            Enter(EqComponentRef, EqNodeId),
            Exit(EqNodeId, usize),
        }
        let mut leaf_positions = HashMap::default();
        let mut node_intervals = vec![None; cutoff];
        let mut next_position = 0usize;
        for (root_index, parent) in node_parents.iter().enumerate().take(cutoff) {
            if parent.is_some() {
                continue;
            }
            let root = EqNodeId::new(root_index as u64 + 1);
            let mut stack = vec![Visit::Enter(EqComponentRef::Node(root), root)];
            while let Some(visit) = stack.pop() {
                match visit {
                    Visit::Enter(EqComponentRef::Leaf(leaf), root) => {
                        if leaf_positions
                            .insert(leaf, (EqComponentRef::Node(root), next_position))
                            .is_some()
                        {
                            return Err("equality forest leaf occurs more than once");
                        }
                        next_position += 1;
                    }
                    Visit::Enter(EqComponentRef::Node(node), root) => {
                        let index: usize = node
                            .get()
                            .checked_sub(1)
                            .ok_or("equality forest references node zero")?
                            .try_into()
                            .map_err(|_| "equality node ID exceeds addressable storage")?;
                        let record = snapshot
                            .equality_nodes
                            .get(index)
                            .ok_or("equality forest references an absent node")?;
                        let start = next_position;
                        stack.push(Visit::Exit(node, start));
                        stack.push(Visit::Enter(record.right, root));
                        stack.push(Visit::Enter(record.left, root));
                    }
                    Visit::Exit(node, start) => {
                        let index = (node.get() - 1) as usize;
                        if start == next_position {
                            return Err("equality forest node contains no term leaves");
                        }
                        if node_intervals[index]
                            .replace((start, next_position))
                            .is_some()
                        {
                            return Err("equality forest node was visited more than once");
                        }
                    }
                }
            }
        }
        if node_intervals.iter().any(Option::is_none) {
            return Err("equality forest contains an unreachable node");
        }

        // Leaves whose first parent lies after the requested edge cutoff are
        // standalone historical components at this point.
        for leaf in snapshot
            .equality_leaves
            .iter()
            .filter(|leaf| leaf.position <= position)
        {
            leaf_positions.entry(leaf.id).or_insert_with(|| {
                let position = next_position;
                next_position += 1;
                (EqComponentRef::Leaf(leaf.id), position)
            });
        }

        let mut endpoint_leaves = HashMap::default();
        for leaf in snapshot
            .equality_leaves
            .iter()
            .filter(|leaf| leaf.position <= position)
        {
            endpoint_leaves.insert(
                (leaf.endpoint.sort, leaf.endpoint.term, leaf.endpoint.raw),
                leaf.id,
            );
        }
        let mut term_attachment_dependencies = HashMap::default();
        let mut leaf_dependencies = HashMap::default();
        for attachment in snapshot
            .term_attachments
            .iter()
            .filter(|attachment| attachment.position <= position)
        {
            let key = (attachment.sort, attachment.term, attachment.raw);
            term_attachment_dependencies.insert(key, attachment.dependency);
            endpoint_leaves.insert(key, attachment.leaf);
            leaf_dependencies
                .entry(attachment.leaf)
                .or_insert(attachment.dependency);
        }

        let index = Self {
            snapshot,
            cutoff,
            leaf_positions,
            endpoint_leaves,
            term_attachment_dependencies,
            leaf_dependencies,
            node_intervals,
        };
        for node in snapshot.equality_nodes.iter().take(cutoff) {
            if !index.contains(node.left, node.left_anchor)
                || !index.contains(node.right, node.right_anchor)
            {
                return Err("applied edge anchors do not belong to their recorded components");
            }
        }
        Ok(index)
    }

    pub fn explain_equality(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
    ) -> Result<Box<[EqualityEdgeId]>, &'static str> {
        Ok(self.explain_equality_support(left, right)?.edges)
    }

    pub fn explain_equality_support(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
    ) -> Result<EqualitySupport, &'static str> {
        if left.sort != right.sort {
            return Err("cannot explain equality across logical sorts");
        }
        if left.term.is_missing() || right.term.is_missing() {
            return Err("cannot explain equality with a missing ReplayTermId");
        }
        let mut facts = Vec::new();
        let mut causes = Vec::new();
        let mut rekeys = Vec::new();
        let left_leaf = self.endpoint_leaf(left, &mut facts, &mut causes, &mut rekeys)?;
        let right_leaf = self.endpoint_leaf(right, &mut facts, &mut causes, &mut rekeys)?;
        facts.sort_unstable();
        facts.dedup();
        causes.sort_unstable();
        causes.dedup();
        rekeys.sort_unstable();
        rekeys.dedup();
        if left_leaf == right_leaf {
            return Ok(EqualitySupport {
                edges: Box::new([]),
                facts: facts.into_boxed_slice(),
                causes: causes.into_boxed_slice(),
                rekeys: rekeys.into_boxed_slice(),
            });
        }

        let Some(left_root) = self.root(left_leaf) else {
            return Err("left equality endpoint is absent from the historical forest");
        };
        let Some(right_root) = self.root(right_leaf) else {
            return Err("right equality endpoint is absent from the historical forest");
        };
        if left_root != right_root {
            return Err("equality endpoints were disconnected at the historical landmark");
        }
        Ok(EqualitySupport {
            edges: self.explain(left_root, left_leaf, right_leaf, left.sort)?,
            facts: facts.into_boxed_slice(),
            causes: causes.into_boxed_slice(),
            rekeys: rekeys.into_boxed_slice(),
        })
    }

    fn endpoint_leaf(
        &self,
        endpoint: EqualityEndpoint,
        facts: &mut Vec<FactId>,
        causes: &mut Vec<ReceiptCauseRef>,
        rekeys: &mut Vec<HistoryPosition>,
    ) -> Result<EqLeafId, &'static str> {
        let key = (endpoint.sort, endpoint.term, endpoint.raw);
        match self.term_attachment_dependencies.get(&key).copied() {
            Some(TermAttachmentDependency::Fact(fact)) => facts.push(fact),
            Some(TermAttachmentDependency::Cause(cause)) => causes.push(cause),
            Some(TermAttachmentDependency::Rekey { position, fact }) => {
                rekeys.push(position);
                facts.push(fact);
            }
            Some(TermAttachmentDependency::Trusted) => {}
            None => {}
        }
        let leaf = self
            .endpoint_leaves
            .get(&key)
            .copied()
            .ok_or("equality endpoint occurrence is absent at the historical position")?;
        match self.leaf_dependencies.get(&leaf).copied() {
            Some(TermAttachmentDependency::Fact(fact)) => facts.push(fact),
            Some(TermAttachmentDependency::Cause(cause)) => causes.push(cause),
            Some(TermAttachmentDependency::Rekey { position, fact }) => {
                rekeys.push(position);
                facts.push(fact);
            }
            Some(TermAttachmentDependency::Trusted) => {}
            None => {}
        }
        Ok(leaf)
    }

    fn root(&self, leaf: EqLeafId) -> Option<EqComponentRef> {
        self.leaf_positions.get(&leaf).map(|(root, _)| *root)
    }

    fn contains(&self, component: EqComponentRef, leaf: EqLeafId) -> bool {
        match component {
            EqComponentRef::Leaf(expected) => expected == leaf,
            EqComponentRef::Node(node) => {
                let Some((_, position)) = self.leaf_positions.get(&leaf) else {
                    return false;
                };
                let Some(index) = node.get().checked_sub(1).map(|id| id as usize) else {
                    return false;
                };
                let Some(Some((start, end))) = self.node_intervals.get(index) else {
                    return false;
                };
                *start <= *position && *position < *end
            }
        }
    }

    fn explain(
        &self,
        root: EqComponentRef,
        left: EqLeafId,
        right: EqLeafId,
        sort: ReplaySortId,
    ) -> Result<Box<[EqualityEdgeId]>, &'static str> {
        enum Task {
            Pair {
                component: EqComponentRef,
                left: EqLeafId,
                right: EqLeafId,
            },
            Edge(EqualityEdgeId),
        }

        let mut tasks = vec![Task::Pair {
            component: root,
            left,
            right,
        }];
        let mut result = Vec::new();
        while let Some(task) = tasks.pop() {
            let Task::Pair {
                component,
                left,
                right,
            } = task
            else {
                let Task::Edge(edge) = task else {
                    unreachable!()
                };
                result.push(edge);
                continue;
            };
            if left == right {
                continue;
            }
            let EqComponentRef::Node(node_id) = component else {
                return Err("distinct occurrences reached one leaf in the equality forest");
            };
            let node_index: usize = node_id
                .get()
                .checked_sub(1)
                .ok_or("equality explanation reached node zero")?
                .try_into()
                .map_err(|_| "equality node ID exceeds addressable storage")?;
            if node_index >= self.cutoff {
                return Err("equality explanation crossed its historical landmark");
            }
            let node = &self.snapshot.equality_nodes[node_index];
            let equality = &self.snapshot.equalities[node_index];
            if equality.left.sort != sort || equality.right.sort != sort {
                return Err("equality explanation crossed logical sorts");
            }
            if !self.contains(node.left, node.left_anchor)
                || !self.contains(node.right, node.right_anchor)
            {
                return Err("applied edge anchors do not belong to their recorded components");
            }
            let left_in_left = self.contains(node.left, left);
            let left_in_right = self.contains(node.right, left);
            let right_in_left = self.contains(node.left, right);
            let right_in_right = self.contains(node.right, right);
            if left_in_left && right_in_left {
                tasks.push(Task::Pair {
                    component: node.left,
                    left,
                    right,
                });
            } else if left_in_right && right_in_right {
                tasks.push(Task::Pair {
                    component: node.right,
                    left,
                    right,
                });
            } else if left_in_left && right_in_right {
                tasks.push(Task::Pair {
                    component: node.right,
                    left: node.right_anchor,
                    right,
                });
                tasks.push(Task::Edge(equality.id));
                tasks.push(Task::Pair {
                    component: node.left,
                    left,
                    right: node.left_anchor,
                });
            } else if left_in_right && right_in_left {
                tasks.push(Task::Pair {
                    component: node.left,
                    left: node.left_anchor,
                    right,
                });
                tasks.push(Task::Edge(equality.id));
                tasks.push(Task::Pair {
                    component: node.right,
                    left,
                    right: node.right_anchor,
                });
            } else {
                return Err("equality terms do not belong to the requested component");
            }
        }
        Ok(result.into_boxed_slice())
    }
}

/// Opaque proof that both raw union endpoints were resolved through the
/// canonical typed replay-term map before native staging.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EqualityTermRef {
    Exact(ReplayTermId),
    Site(TermOriginSiteId),
    Cell {
        origin: RowOriginRef,
        table: TableId,
        column: u16,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PendingEqualityEndpoint {
    pub(crate) sort: ReplaySortId,
    pub(crate) raw: crate::Value,
    pub(crate) term: EqualityTermRef,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[doc(hidden)]
pub struct TypedEqualityProposal {
    wave: CausalWave,
    left: PendingEqualityEndpoint,
    right: PendingEqualityEndpoint,
}

impl TypedEqualityProposal {
    pub(crate) fn wave(self) -> CausalWave {
        self.wave
    }

    pub(crate) fn left(self) -> PendingEqualityEndpoint {
        self.left
    }

    pub(crate) fn right(self) -> PendingEqualityEndpoint {
        self.right
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct AppliedEqualityProposal {
    pub(crate) wave: CausalWave,
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

/// An action-batch-owned resolver for compact join witnesses. Implementations
/// retain the immutable materialization DAGs needed by their lanes; the
/// receipt arena resolves the complete batch exactly once when native head
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
/// The match was already published when native head execution began, so the
/// handle needs no batch lifetime or promotion allocation.
#[derive(Clone)]
pub(crate) struct ObservedMatchBatch {
    receipts: CausalReceipts,
    first: RuleMatchId,
    lanes: u32,
    wave: CausalWave,
}

#[derive(Clone)]
pub(crate) struct PendingRuleCause {
    receipts: CausalReceipts,
    matched: RuleMatchId,
    wave: CausalWave,
}

#[derive(Clone)]
pub(crate) struct PendingNativeLease(Arc<PendingNativeLeaseInner>);

struct PendingNativeLeaseInner {
    receipts: CausalReceipts,
    wave: CausalWave,
}

impl Drop for PendingNativeLeaseInner {
    fn drop(&mut self) {
        self.receipts
            .0
            .open_native_leases
            .fetch_sub(1, Ordering::Release);
    }
}

impl PendingNativeLease {
    pub(crate) fn matches(&self, receipts: &CausalReceipts, wave: CausalWave) -> bool {
        Arc::ptr_eq(&self.0.receipts.0, &receipts.0) && self.0.wave == wave
    }
}

impl PendingRuleCause {
    pub(crate) fn promote(&self) -> CauseRef {
        CauseRef::rule(self.matched)
    }

    fn prepare(&self, receipts: &CausalReceipts, current_wave: CausalWave) -> Result<(), String> {
        if !Arc::ptr_eq(&self.receipts.0, &receipts.0) {
            return Err(format!(
                "observed match {:?} belongs to another causal receipt arena",
                self.matched
            ));
        }
        if self.wave != current_wave {
            return Err(format!(
                "observed match {:?} from wave {:?} was used in wave {:?}",
                self.matched, self.wave, current_wave
            ));
        }
        if self
            .receipts
            .0
            .poisoned_rule_executions
            .load(Ordering::Acquire)
            != 0
        {
            return Err("rule observation belongs to a panicking execution".into());
        }
        Ok(())
    }

    fn record_merge_read(&self, prior_fact: FactId) {
        self.receipts
            .record_observed_match_merge_read(self.matched, prior_fact);
    }
}

#[doc(hidden)]
#[derive(Clone, Debug)]
pub struct PreparedRekey {
    table: TableId,
    wave: CausalWave,
    prior_fact: FactId,
    as_of_edges: EqualityEdgeCount,
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
        CausalWave,
        FactId,
        EqualityEdgeCount,
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
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
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
        cause: CauseRef,
        equality: Option<EqualityCauseSummary>,
    },
    Pending(PendingRuleCause),
    Merge(Arc<PendingMergeCause>),
}

struct PendingMergeCause {
    receipts: CausalReceipts,
    incoming: DeferredEqualityCause,
    prior_fact: FactId,
    equality: EqualityCauseSummary,
    cause: OnceLock<CauseRef>,
}

#[doc(hidden)]
#[derive(Clone)]
pub struct DeferredEqualityCause(DeferredEqualityCauseKind);

impl DeferredEqualityCause {
    pub(crate) fn ready(cause: impl Into<CauseRef>) -> Self {
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
            cause: CauseRef::node(cause.id),
            equality: Some(cause.equality),
        })
    }

    pub(crate) fn promote(&self) -> CauseRef {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => *cause,
            DeferredEqualityCauseKind::Pending(cause) => cause.promote(),
            DeferredEqualityCauseKind::Merge(cause) => *cause
                .cause
                .get_or_init(|| cause.receipts.promote_pending_merge_cause(cause)),
        }
    }

    pub(crate) fn ready_id(&self) -> Option<CauseRef> {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => Some(*cause),
            DeferredEqualityCauseKind::Pending(_) | DeferredEqualityCauseKind::Merge(_) => None,
        }
    }

    pub(crate) fn pending(cause: PendingRuleCause) -> Self {
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

    fn equality_summary(&self, receipts: &CausalReceipts) -> EqualityCauseSummary {
        match &self.0 {
            DeferredEqualityCauseKind::Ready {
                cause: _,
                equality: Some(equality),
            } => *equality,
            DeferredEqualityCauseKind::Ready {
                cause,
                equality: None,
            } => {
                if cause.rule_match().is_some() {
                    return EqualityCauseSummary::Rule;
                }
                let arena = receipts.0.arena.lock().unwrap();
                arena
                    .cause_summary(cause.cause_node().expect("ready cause has no node id"))
                    .unwrap_or_else(|error| panic!("cannot classify deferred cause: {error}"))
            }
            DeferredEqualityCauseKind::Pending(_) => EqualityCauseSummary::Rule,
            DeferredEqualityCauseKind::Merge(cause) => cause.equality,
        }
    }

    pub(crate) fn prepare(
        &self,
        receipts: &CausalReceipts,
        current_wave: CausalWave,
    ) -> Result<(), String> {
        self.equality_summary(receipts)
            .validate()
            .map_err(str::to_owned)?;
        self.prepare_dependencies(receipts, current_wave)
    }

    fn prepare_dependencies(
        &self,
        receipts: &CausalReceipts,
        current_wave: CausalWave,
    ) -> Result<(), String> {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => match cause.rule_match() {
                Some(matched) => receipts.prepare_observed_rule_match(matched, current_wave),
                None => Ok(()),
            },
            DeferredEqualityCauseKind::Pending(cause) => cause.prepare(receipts, current_wave),
            // A direct rebuild is invalid as a root equality cause but valid
            // beneath a merge that supplies its prior fact. Prepare its lazy
            // payload without re-validating the child as a standalone root.
            DeferredEqualityCauseKind::Merge(cause) => {
                cause.incoming.prepare_dependencies(receipts, current_wave)
            }
        }
    }
}

#[derive(Clone, Debug)]
enum CauseDraft {
    #[cfg(test)]
    Source(SourceRef),
    Merge {
        incoming: CauseRef,
        prior: PriorVersion,
    },
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EqualityCauseError {
    Source,
    Mixed,
    MissingFact,
    LandmarkMismatch,
}

impl EqualityCauseError {
    fn message(self) -> &'static str {
        match self {
            EqualityCauseError::Source => {
                "unsupported equality cause: source receipts cannot justify a union"
            }
            EqualityCauseError::Mixed => {
                "unsupported equality cause: merge DAG mixes rule and rebuild proposals"
            }
            EqualityCauseError::MissingFact => {
                "equality cause references a missing immutable FactId"
            }
            EqualityCauseError::LandmarkMismatch => {
                "congruence dependencies used different waves or equality landmarks"
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EqualityCauseSummary {
    Source,
    Rule,
    Container {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
    },
    Rebuild {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
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

    fn merge(self, prior: Self) -> Self {
        match (self, prior) {
            (Self::Rule, Self::Rule) => Self::Rule,
            (
                Self::Rebuild {
                    wave: incoming_wave,
                    as_of_edges: incoming_edges,
                    position: incoming_position,
                    ..
                },
                Self::Rebuild {
                    wave: prior_wave,
                    as_of_edges: prior_edges,
                    position: prior_position,
                    ..
                },
            ) if incoming_wave == prior_wave
                && incoming_edges == prior_edges
                && incoming_position == prior_position =>
            {
                Self::Rebuild {
                    wave: incoming_wave,
                    as_of_edges: incoming_edges,
                    position: incoming_position,
                    complete: true,
                }
            }
            (Self::Invalid(error), _) | (_, Self::Invalid(error)) => Self::Invalid(error),
            (Self::Source, _) | (_, Self::Source) => Self::Invalid(EqualityCauseError::Source),
            (Self::Container { .. }, _) | (_, Self::Container { .. }) => {
                Self::Invalid(EqualityCauseError::Mixed)
            }
            (Self::Rebuild { .. }, Self::Rebuild { .. }) => {
                Self::Invalid(EqualityCauseError::LandmarkMismatch)
            }
            _ => Self::Invalid(EqualityCauseError::Mixed),
        }
    }

    pub(crate) fn validate(self) -> Result<(), &'static str> {
        match self {
            Self::Rule | Self::Container { .. } => Ok(()),
            Self::Rebuild { complete: true, .. } => Ok(()),
            Self::Rebuild { .. } => {
                Err("unsupported equality cause: a direct rebuild cannot justify a union")
            }
            Self::Source => {
                Err("unsupported equality cause: source receipts cannot justify a union")
            }
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

    pub(crate) fn cause_ref(self) -> CauseRef {
        CauseRef::node(self.id)
    }
}

#[derive(Clone, Copy, Debug)]
enum PriorVersion {
    Fact(FactId),
    Cause(CauseRef),
}

#[derive(Clone, Debug)]
enum DurableCause {
    Source(SourceRef),
    Rebuild {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: FlatRange,
    },
    ContainerCanonicalize {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: FlatRange,
    },
    ContainerRefresh {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        position: HistoryPosition,
        equalities: FlatRange,
    },
    Merge {
        incoming: CauseRef,
        prior: DurablePrior,
    },
}

#[derive(Clone, Copy, Debug)]
enum DurablePrior {
    Fact(FactId),
    Cause(CauseRef),
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
    cause: CauseRef,
    values: FlatRange,
    origin: Option<FactOrigin>,
}

#[derive(Clone, Debug)]
struct DurableFact {
    table: TableId,
    position: HistoryPosition,
    cause: CauseRef,
    values: FlatRange,
    origin: Option<FactOrigin>,
}

#[derive(Clone, Debug)]
struct PendingEquality {
    history: EqualityEdgeCount,
    position: HistoryPosition,
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    cause: CauseRef,
}

#[derive(Clone, Debug)]
struct DurableEquality {
    history: EqualityEdgeCount,
    position: HistoryPosition,
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    cause: CauseRef,
    reason: EqualityReason,
}

#[derive(Clone, Debug)]
struct DurableMatch {
    rule: u32,
    wave: CausalWave,
    position: HistoryPosition,
    as_of_edges: EqualityEdgeCount,
    premises: FlatRange,
}

#[derive(Default)]
struct ReceiptArena {
    facts: Vec<Option<DurableFact>>,
    durable_matches: Vec<Option<DurableMatch>>,
    durable_premises: Vec<FactId>,
    /// Sparse because ordinary matches never invoke a merge callback.
    merge_reads: HashMap<RuleMatchId, SmallVec<[FactId; 2]>>,
    durable_fact_values: Vec<Value>,
    durable_merge_cell_origins: Vec<MergeCellOrigin>,
    durable_rebuild_equalities: Vec<TypedCellEquality>,
    durable_causes: Vec<Option<DurableCause>>,
    cause_summaries: HashMap<CauseDraftId, EqualityCauseSummary>,
    durable_equalities: Vec<Option<DurableEquality>>,
    rekeys: Vec<RekeyRecord>,
    check_roots: HashMap<u32, CheckRoot>,
    published_facts: u64,
    published_matches: u64,
    published_causes: u64,
    published_equalities: u64,
    counters: ReceiptCounters,
}

impl ReceiptArena {
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
            self.durable_causes[index].replace(cause).is_none(),
            "duplicate cause-node publication"
        );
        assert!(self.cause_summaries.insert(id, summary).is_none());
        self.published_causes += 1;
    }

    fn durable_cause(&self, id: CauseDraftId) -> Option<&DurableCause> {
        self.durable_causes
            .get((id.get().checked_sub(1)?) as usize)?
            .as_ref()
    }

    fn install_equality(&mut self, id: EqNodeId, equality: DurableEquality) {
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

    fn record_match_term_storage(&mut self, logical: usize, stored: usize) {
        let logical = logical as u64;
        let stored = stored as u64;
        let handle_bytes = mem::size_of::<ReplayTermId>() as u64;
        self.counters.logical_match_term_handles += logical;
        self.counters.stored_match_term_handles += stored;
        self.counters.logical_match_term_bytes += logical * handle_bytes;
        self.counters.stored_match_term_bytes += stored * handle_bytes;
        self.counters.term_handles += logical;
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
        self.cause_summaries
            .get(&id)
            .copied()
            .ok_or("cause node has not been published")
    }

    fn originating_rule(&self, mut cause: CauseRef) -> Option<RuleMatchId> {
        loop {
            if let Some(rule) = cause.rule_match() {
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

    fn equality_reason(&self, root: CauseRef, summary: EqualityCauseSummary) -> EqualityReason {
        summary.validate().unwrap_or_else(|error| panic!("{error}"));
        if let Some(rule) = root.rule_match() {
            return EqualityReason::RuleUnion(rule);
        }
        let node = root.cause_node().expect("equality cause is unattributed");
        match (
            self.durable_cause(node)
                .expect("equality cause node is not durable"),
            summary,
        ) {
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

    /// Derive the compatibility snapshot's effective match view without
    /// putting a cited bit or lock on the native hot path. The raw arena keeps
    /// every observation; only facts, applied equalities, and selected checks
    /// seed this cold dependency walk.
    fn cited_matches(&self) -> Result<HashSet<RuleMatchId>, String> {
        #[derive(Clone, Copy)]
        enum Item {
            Fact(FactId),
            Cause(CauseRef),
            Matched(RuleMatchId),
        }

        let mut stack = Vec::new();
        for fact in self.facts.iter().filter_map(Option::as_ref) {
            stack.push(Item::Cause(fact.cause));
        }
        stack.extend(
            self.durable_equalities
                .iter()
                .filter_map(Option::as_ref)
                .map(|edge| Item::Cause(edge.cause)),
        );
        for root in self.check_roots.values() {
            stack.extend(root.premises.iter().copied().map(Item::Fact));
        }

        let mut facts = HashSet::default();
        let mut causes = HashSet::default();
        let mut matches = HashSet::default();
        while let Some(item) = stack.pop() {
            match item {
                Item::Fact(fact) => {
                    if fact.is_missing() {
                        return Err("cited dependency contains the missing FactId sentinel".into());
                    }
                    if !facts.insert(fact) {
                        continue;
                    }
                    let Some(slot) = self
                        .facts
                        .get((fact.get() - 1) as usize)
                        .and_then(Option::as_ref)
                    else {
                        return Err(format!("cited dependency references missing fact {fact:?}"));
                    };
                    stack.push(Item::Cause(slot.cause));
                }
                Item::Cause(cause) => {
                    if let Some(matched) = cause.rule_match() {
                        stack.push(Item::Matched(matched));
                        continue;
                    }
                    let Some(node) = cause.cause_node() else {
                        return Err("cited dependency contains an unattributed cause".into());
                    };
                    if !causes.insert(node) {
                        continue;
                    }
                    let Some(cause) = self.durable_cause(node) else {
                        return Err(format!(
                            "cited dependency references missing cause node {node:?}"
                        ));
                    };
                    match cause {
                        DurableCause::Source(_) | DurableCause::ContainerCanonicalize { .. } => {}
                        DurableCause::Rebuild { prior_fact, .. }
                        | DurableCause::ContainerRefresh { prior_fact, .. } => {
                            stack.push(Item::Fact(*prior_fact));
                        }
                        DurableCause::Merge { incoming, prior } => {
                            stack.push(Item::Cause(*incoming));
                            stack.push(match prior {
                                DurablePrior::Fact(fact) => Item::Fact(*fact),
                                DurablePrior::Cause(cause) => Item::Cause(*cause),
                            });
                        }
                    }
                }
                Item::Matched(matched) => {
                    if !matches.insert(matched) {
                        continue;
                    }
                    let Some(record) = self
                        .durable_matches
                        .get((matched.get() - 1) as usize)
                        .and_then(Option::as_ref)
                    else {
                        return Err(format!(
                            "cited dependency references missing observed match {matched:?}"
                        ));
                    };
                    stack.extend(
                        self.durable_premises[record.premises.as_range()]
                            .iter()
                            .copied()
                            .map(Item::Fact),
                    );
                    if let Some(reads) = self.merge_reads.get(&matched) {
                        stack.extend(reads.iter().copied().map(Item::Fact));
                    }
                }
            }
        }
        Ok(matches)
    }
}

/// Cold compatibility projector. Native capture stores raw creation rows and
/// compact static origin sites; only an explicit snapshot/debug read expands
/// those references into the historical replay-term DAG.
#[derive(Clone)]
enum TemplateOwner {
    Durable(RuleMatchId),
}

struct TermProjector<'a> {
    arena: &'a ReceiptArena,
    binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
    term_recipes: &'a StaticTermRecipeStore,
    replay_terms: &'a ReplayTermStore,
    next_term: &'a AtomicU32,
    fact_memo: HashMap<(FactId, usize), ReplayTermId>,
    match_memo: HashMap<(RuleMatchId, usize), ReplayTermId>,
    visiting_facts: HashSet<(FactId, usize)>,
    visiting_matches: HashSet<(RuleMatchId, usize)>,
}

struct ProjectedEqualityEndpoint {
    endpoint: EqualityEndpoint,
    /// Immutable creation-row value when this endpoint was reconstructed
    /// through a stable FactId. A pure rekey may make it differ from
    /// `endpoint.raw`; the cold equality builder validates that drift against
    /// the already-applied native prefix before accepting it.
    creation_raw: Option<Value>,
}

impl<'a> TermProjector<'a> {
    fn new(
        arena: &'a ReceiptArena,
        binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
        term_recipes: &'a StaticTermRecipeStore,
        replay_terms: &'a ReplayTermStore,
        next_term: &'a AtomicU32,
    ) -> Self {
        Self {
            arena,
            binding_recipes,
            term_recipes,
            replay_terms,
            next_term,
            fact_memo: HashMap::default(),
            match_memo: HashMap::default(),
            visiting_facts: HashSet::default(),
            visiting_matches: HashSet::default(),
        }
    }

    fn fact_term(&mut self, fact_id: FactId, column: usize) -> Result<ReplayTermId, String> {
        if let Some(term) = self.fact_memo.get(&(fact_id, column)).copied() {
            return Ok(term);
        }
        #[cfg(test)]
        TERM_PROJECTOR_FACT_EXPANSIONS.set(TERM_PROJECTOR_FACT_EXPANSIONS.get() + 1);
        if !self.visiting_facts.insert((fact_id, column)) {
            return Err(format!(
                "cyclic causal term origin at {fact_id:?} column {column}"
            ));
        }
        let result = (|| {
            let fact = self
                .arena
                .facts
                .get((fact_id.get().checked_sub(1).ok_or("missing FactId")?) as usize)
                .and_then(Option::as_ref)
                .ok_or_else(|| format!("unknown causal fact {fact_id:?}"))?;
            let owner = self
                .arena
                .originating_rule(fact.cause)
                .map(TemplateOwner::Durable);
            let merge_cells = match fact.origin {
                Some(FactOrigin::Merge { cells, .. }) => {
                    Some(self.arena.durable_merge_cell_origins[cells.as_range()].to_vec())
                }
                _ => None,
            };
            let (table, origin) = (fact.table, fact.origin);
            match origin {
                Some(FactOrigin::Site(site)) => self.site_term(site, table, column, owner.as_ref()),
                Some(FactOrigin::Fact(source)) => self.fact_term(source, column),
                Some(FactOrigin::Merge {
                    incoming, prior, ..
                }) => {
                    let cell = *merge_cells
                        .as_deref()
                        .and_then(|cells| cells.get(column))
                        .ok_or_else(|| {
                            format!("merge origin for {fact_id:?} has no column {column}")
                        })?;
                    let incoming_term = |this: &mut Self| match incoming {
                        Some(RowOriginRef::Site(site)) => {
                            this.site_term(site, table, column, owner.as_ref())
                        }
                        Some(RowOriginRef::Fact(source)) => this.fact_term(source, column),
                        None => Err(format!(
                            "reached unattributed incoming syntax for {fact_id:?} column {column}"
                        )),
                    };
                    match cell {
                        MergeCellOrigin::Incoming(source) => match incoming {
                            Some(RowOriginRef::Site(site)) => {
                                self.site_term(site, table, source as usize, owner.as_ref())
                            }
                            Some(RowOriginRef::Fact(source_fact)) => {
                                self.fact_term(source_fact, source as usize)
                            }
                            None => incoming_term(self),
                        },
                        MergeCellOrigin::Prior(source) => self.fact_term(prior, source as usize),
                        MergeCellOrigin::Unsupported => Err(format!(
                            "merge of {fact_id:?} column {column} synthesized unsupported syntax"
                        )),
                    }
                }
                None => Err(format!(
                    "causal fact {fact_id:?} column {column} has no structural origin"
                )),
            }
        })();
        self.visiting_facts.remove(&(fact_id, column));
        let term = result?;
        self.fact_memo.insert((fact_id, column), term);
        Ok(term)
    }

    fn site_term(
        &mut self,
        site: RowOriginSiteId,
        table: TableId,
        column: usize,
        owner: Option<&TemplateOwner>,
    ) -> Result<ReplayTermId, String> {
        let spec = self
            .term_recipes
            .row_origins
            .get((site.get() - 1) as usize)
            .ok_or_else(|| format!("unknown row-origin site {site:?}"))?;
        if spec.table != table {
            return Err(format!(
                "row-origin site {site:?} belongs to {:?}, not {table:?}",
                spec.table
            ));
        }
        let template = spec
            .cells
            .get(column)
            .and_then(Option::as_ref)
            .ok_or_else(|| {
                format!("reached unsupported causal row origin {site:?} column {column}")
            })?;
        self.template(template, owner)
    }

    fn match_term(
        &mut self,
        match_id: RuleMatchId,
        binding: usize,
    ) -> Result<ReplayTermId, String> {
        if let Some(term) = self.match_memo.get(&(match_id, binding)).copied() {
            return Ok(term);
        }
        if !self.visiting_matches.insert((match_id, binding)) {
            return Err(format!(
                "cyclic causal match term at {match_id:?} binding {binding}"
            ));
        }
        let result = (|| {
            let record = self
                .arena
                .durable_matches
                .get((match_id.get().checked_sub(1).ok_or("missing RuleMatchId")?) as usize)
                .and_then(Option::as_ref)
                .ok_or_else(|| format!("unknown causal match {match_id:?}"))?;
            let rule = record.rule;
            let premises: Arc<[FactId]> =
                self.arena.durable_premises[record.premises.as_range()].into();
            self.binding_term(rule, &premises, binding, &TemplateOwner::Durable(match_id))
        })();
        self.visiting_matches.remove(&(match_id, binding));
        let term = result?;
        self.match_memo.insert((match_id, binding), term);
        Ok(term)
    }

    fn binding_term(
        &mut self,
        rule: u32,
        premises: &[FactId],
        binding: usize,
        owner: &TemplateOwner,
    ) -> Result<ReplayTermId, String> {
        let sources = self
            .binding_recipes
            .get(&rule)
            .ok_or_else(|| format!("rule {rule} has no binding recipe"))?;
        let source = sources
            .get(binding)
            .ok_or_else(|| format!("rule {rule} has no binding slot {binding}"))?;
        match source {
            ReplayBindingSource::Premise { representative, .. } => {
                let fact = *premises.get(representative.premise).ok_or_else(|| {
                    format!(
                        "rule {rule} match has no premise {}",
                        representative.premise
                    )
                })?;
                self.fact_term(fact, representative.column)
            }
            ReplayBindingSource::Constant { term } => Ok(*term),
            ReplayBindingSource::Current { residual, .. } => {
                let recipe = self
                    .term_recipes
                    .rules
                    .get(&rule)
                    .ok_or_else(|| format!("rule {rule} has no current-term recipe"))?;
                let template = recipe
                    .current_roots
                    .get(*residual as usize)
                    .and_then(Option::as_ref)
                    .ok_or_else(|| {
                        format!("reached unsupported current binding {residual} for rule {rule}")
                    })?;
                self.template(template, Some(owner))
            }
        }
    }

    fn template(
        &mut self,
        template: &TermTemplate,
        owner: Option<&TemplateOwner>,
    ) -> Result<ReplayTermId, String> {
        match template {
            TermTemplate::Binding { binding } => match owner.ok_or_else(|| {
                format!("source row origin unexpectedly references binding {binding}")
            })? {
                TemplateOwner::Durable(match_id) => self.match_term(*match_id, *binding as usize),
            },
            TermTemplate::PremiseCell { premise, column } => {
                let owner = owner.ok_or_else(|| {
                    format!(
                        "source row origin unexpectedly references premise {premise} column {column}"
                    )
                })?;
                let fact = match owner {
                    TemplateOwner::Durable(match_id) => {
                        let record = self
                            .arena
                            .durable_matches
                            .get(
                                (match_id.get().checked_sub(1).ok_or("missing RuleMatchId")?)
                                    as usize,
                            )
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown causal match {match_id:?}"))?;
                        *self
                            .arena
                            .durable_premises
                            .get(record.premises.as_range())
                            .and_then(|premises| premises.get(*premise as usize))
                            .ok_or_else(|| {
                                format!("causal match {match_id:?} has no premise {premise}")
                            })?
                    }
                };
                self.fact_term(fact, *column as usize)
            }
            TermTemplate::Static { term } => Ok(*term),
            TermTemplate::Call { sort, op, children } => {
                let children = children
                    .iter()
                    .map(|child| self.template(child, owner))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.replay_terms.intern(
                    self.next_term,
                    ReplayTerm::Call {
                        sort: *sort,
                        op: *op,
                        children: children.into(),
                    },
                ))
            }
        }
    }

    fn runtime_anchor_template(
        &mut self,
        template: &TermTemplate,
        binding_sources: &[ReplayBindingSource],
        premises: &[FactId],
    ) -> Result<ReplayTermId, String> {
        match template {
            TermTemplate::Binding { binding } => {
                let source = binding_sources.get(*binding as usize).ok_or_else(|| {
                    format!("container anchor references unknown binding {binding}")
                })?;
                match source {
                    ReplayBindingSource::Premise { representative, .. } => {
                        let fact = *premises.get(representative.premise).ok_or_else(|| {
                            format!(
                                "container anchor binding {binding} has no premise {}",
                                representative.premise
                            )
                        })?;
                        self.fact_term(fact, representative.column)
                    }
                    ReplayBindingSource::Constant { term } => Ok(*term),
                    ReplayBindingSource::Current { residual, .. } => Err(format!(
                        "container anchor reached unsupported current binding {binding} (residual {residual})"
                    )),
                }
            }
            TermTemplate::PremiseCell { premise, column } => {
                let fact = *premises
                    .get(*premise as usize)
                    .ok_or_else(|| format!("container anchor has no premise {premise}"))?;
                self.fact_term(fact, *column as usize)
            }
            TermTemplate::Static { term } => Ok(*term),
            TermTemplate::Call { sort, op, children } => {
                let children = children
                    .iter()
                    .map(|child| self.runtime_anchor_template(child, binding_sources, premises))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.replay_terms.intern(
                    self.next_term,
                    ReplayTerm::Call {
                        sort: *sort,
                        op: *op,
                        children: children.into(),
                    },
                ))
            }
        }
    }

    fn equality_endpoint(
        &mut self,
        endpoint: PendingEqualityEndpoint,
        cause: CauseRef,
    ) -> Result<ProjectedEqualityEndpoint, String> {
        let (term, creation_raw) = match endpoint.term {
            EqualityTermRef::Exact(term) => (term, None),
            EqualityTermRef::Site(site) => {
                let owner = self
                    .arena
                    .originating_rule(cause)
                    .map(TemplateOwner::Durable);
                let spec = self
                    .term_recipes
                    .term_origins
                    .get((site.get() - 1) as usize)
                    .ok_or_else(|| format!("unknown term-origin site {site:?}"))?;
                if spec.sort != endpoint.sort {
                    return Err(format!(
                        "term-origin site {site:?} belongs to {:?}, not {:?}",
                        spec.sort, endpoint.sort
                    ));
                }
                (self.template(&spec.term, owner.as_ref())?, None)
            }
            EqualityTermRef::Cell {
                origin,
                table,
                column,
            } => match origin {
                RowOriginRef::Fact(fact) => {
                    let (fact_table, values) = self
                        .arena
                        .fact_values(fact)
                        .ok_or_else(|| format!("unknown equality endpoint fact {fact:?}"))?;
                    if fact_table != table {
                        return Err(format!(
                            "equality endpoint fact {fact:?} belongs to {fact_table:?}, not {table:?}"
                        ));
                    }
                    let creation_raw = *values.get(column as usize).ok_or_else(|| {
                        format!("equality endpoint fact {fact:?} has no column {column}")
                    })?;
                    (self.fact_term(fact, column as usize)?, Some(creation_raw))
                }
                RowOriginRef::Site(site) => {
                    let owner = self
                        .arena
                        .originating_rule(cause)
                        .map(TemplateOwner::Durable);
                    (
                        self.site_term(site, table, column as usize, owner.as_ref())?,
                        None,
                    )
                }
            },
        };
        let node = self
            .replay_terms
            .node(term)
            .ok_or_else(|| format!("equality endpoint owns unknown term {term:?}"))?;
        if node.sort() != endpoint.sort {
            return Err(format!(
                "equality endpoint term sort {:?} differs from {:?}",
                node.sort(),
                endpoint.sort
            ));
        }
        Ok(ProjectedEqualityEndpoint {
            endpoint: EqualityEndpoint {
                sort: endpoint.sort,
                term,
                raw: endpoint.raw,
            },
            creation_raw,
        })
    }
}

type ColdEqualityArtifacts = (
    Vec<EqLeafRecord>,
    Vec<EqNodeRecord>,
    Vec<EqualityRecord>,
    Vec<NativeAliasRecord>,
    Vec<usize>,
    Vec<(EqualityEndpoint, EqualityEndpoint)>,
    Vec<TermAttachment>,
);

#[derive(Default)]
struct ColdEqualityForest {
    parents: HashMap<(ReplaySortId, Value), (ReplaySortId, Value)>,
    components: HashMap<(ReplaySortId, Value), EqComponentRef>,
    /// A trusted Exact alias may leave several native roots pointing at one
    /// logical component. When any owner later grows, advance the shared
    /// component once rather than scanning every native root.
    component_successors: HashMap<EqComponentRef, EqComponentRef>,
    occurrences: HashMap<(ReplaySortId, ReplayTermId, Value), EqLeafId>,
    /// First logical occurrence recorded for one exact historical native
    /// value. A component may have many leaves, so later zero-edge
    /// attachments must use this raw-specific anchor rather than whichever
    /// endpoint happened to be on the left of a prior equality proposal.
    raw_anchors: HashMap<(ReplaySortId, Value), EqLeafId>,
    exact_occurrences: HashMap<(ReplaySortId, ReplayTermId), ((ReplaySortId, Value), EqLeafId)>,
    leaves: Vec<EqLeafRecord>,
}

impl ColdEqualityForest {
    fn resolve_component(&mut self, component: EqComponentRef) -> EqComponentRef {
        let mut root = component;
        while let Some(parent) = self.component_successors.get(&root).copied() {
            root = parent;
        }
        let mut current = component;
        while let Some(parent) = self.component_successors.get(&current).copied() {
            if parent == root {
                break;
            }
            self.component_successors.insert(current, root);
            current = parent;
        }
        root
    }

    fn root_component(&mut self, root: (ReplaySortId, Value)) -> Option<EqComponentRef> {
        let component = self.components.get(&root).copied()?;
        let component = self.resolve_component(component);
        self.components.insert(root, component);
        Some(component)
    }

    fn advance_component(&mut self, old: EqComponentRef, new: EqComponentRef) {
        if old != new {
            assert!(
                self.component_successors.insert(old, new).is_none(),
                "cold equality component acquired two logical parents"
            );
        }
    }

    fn find(&mut self, value: (ReplaySortId, Value)) -> (ReplaySortId, Value) {
        let mut root = value;
        while let Some(parent) = self.parents.get(&root).copied() {
            if parent == root {
                break;
            }
            root = parent;
        }
        let mut current = value;
        while let Some(parent) = self.parents.get(&current).copied() {
            if parent == root {
                break;
            }
            self.parents.insert(current, root);
            current = parent;
        }
        root
    }

    fn alias_component(left: EqComponentRef, right: EqComponentRef) -> Option<EqComponentRef> {
        // Only an already-shared occurrence component is a native-only alias.
        // Identical syntax in distinct native components remains two leaves
        // and the applied bridge becomes a logical edge.
        (left == right).then_some(left)
    }

    fn new_leaf(&mut self, position: HistoryPosition, endpoint: EqualityEndpoint) -> EqLeafId {
        let id = EqLeafId::new(self.leaves.len() as u64 + 1);
        self.leaves.push(EqLeafRecord {
            id,
            position,
            endpoint,
        });
        self.raw_anchors
            .entry((endpoint.sort, endpoint.raw))
            .or_insert(id);
        id
    }

    fn attach_fact_term(
        &mut self,
        position: HistoryPosition,
        dependency: TermAttachmentDependency,
        endpoint: EqualityEndpoint,
    ) -> Result<Option<TermAttachment>, String> {
        let root = self.find((endpoint.sort, endpoint.raw));
        let key = (endpoint.sort, endpoint.term, endpoint.raw);
        let leaf = if let Some(leaf) = self.occurrences.get(&key).copied() {
            leaf
        } else if self.root_component(root).is_some() {
            let leaf = self
                .raw_anchors
                .get(&(endpoint.sort, endpoint.raw))
                .copied()
                .ok_or("native value has a cold component but no raw-specific anchor")?;
            self.occurrences.insert(key, leaf);
            leaf
        } else {
            let leaf = self.new_leaf(position, endpoint);
            self.components.insert(root, EqComponentRef::Leaf(leaf));
            self.occurrences.insert(key, leaf);
            leaf
        };
        Ok(Some(TermAttachment {
            position,
            sort: endpoint.sort,
            raw: endpoint.raw,
            term: endpoint.term,
            leaf,
            dependency,
        }))
    }

    /// Carry one immutable fact term across a native rekey without changing
    /// its logical occurrence. Choosing the destination component's generic
    /// anchor would erase the equality edge that made the rekey possible
    /// (for example B@B -> B@A after A=B), producing an empty explanation for
    /// a later check of A=B.
    fn attach_rekey_term(
        &mut self,
        position: HistoryPosition,
        fact: FactId,
        old: EqualityEndpoint,
        new: EqualityEndpoint,
    ) -> Result<TermAttachment, String> {
        if old.sort != new.sort || old.term != new.term {
            return Err("one rekey changed the immutable fact term or its sort".into());
        }
        let old_root = self.find((old.sort, old.raw));
        let new_root = self.find((new.sort, new.raw));
        if old_root != new_root {
            return Err("rekey endpoints are disconnected in the cold equality history".into());
        }
        self.root_component(new_root)
            .ok_or("rekey destination has no cold equality component")?;
        let prior_leaf = self
            .occurrences
            .get(&(old.sort, old.term, old.raw))
            .copied()
            .ok_or("rekey source term has no prior cold occurrence")?;
        let key = (new.sort, new.term, new.raw);
        // If the exact same syntax already exists at the destination value,
        // that occurrence is semantically interchangeable and keeps the
        // forest minimal. Otherwise preserve this fact's prior occurrence so
        // the equality that moved it remains visible to later explanations.
        let leaf = self.occurrences.get(&key).copied().unwrap_or_else(|| {
            self.occurrences.insert(key, prior_leaf);
            prior_leaf
        });
        Ok(TermAttachment {
            position,
            sort: new.sort,
            raw: new.raw,
            term: new.term,
            leaf,
            dependency: TermAttachmentDependency::Rekey { position, fact },
        })
    }

    fn attach_equality_endpoint(
        &mut self,
        position: HistoryPosition,
        cause: CauseRef,
        endpoint: EqualityEndpoint,
        exact: bool,
        attachments: &mut Vec<TermAttachment>,
    ) -> Result<EqLeafId, String> {
        let root = self.find((endpoint.sort, endpoint.raw));
        let key = (endpoint.sort, endpoint.term, endpoint.raw);
        if let Some(leaf) = self.occurrences.get(&key).copied() {
            return Ok(leaf);
        }
        if exact
            && let Some((owner, leaf)) = self
                .exact_occurrences
                .get(&(endpoint.sort, endpoint.term))
                .copied()
        {
            let owner_root = self.find(owner);
            let component = self
                .root_component(owner_root)
                .ok_or("trusted exact occurrence has no cold component")?;
            // A certified Exact mapping may catch an otherwise-empty native
            // component up to its already-recorded structural occurrence.
            // It must never replace or locally shadow a different component:
            // replacement orphans that component's equality history, while
            // local attachment leaves one Exact term in two disconnected
            // logical components. Supporting that case requires an explicit
            // zero-edge component join, which this minimal forest does not
            // model, so fail closed before mutating the cold projection.
            if self
                .root_component(root)
                .is_some_and(|current| current != component)
            {
                return Err(
                    "trusted exact occurrence collides with an independently recorded native component"
                        .into(),
                );
            }
            self.components.insert(root, component);
            self.occurrences.insert(key, leaf);
            self.raw_anchors
                .entry((endpoint.sort, endpoint.raw))
                .or_insert(leaf);
            attachments.push(TermAttachment {
                position,
                sort: endpoint.sort,
                raw: endpoint.raw,
                term: endpoint.term,
                leaf,
                dependency: TermAttachmentDependency::Trusted,
            });
            return Ok(leaf);
        }
        let (leaf, zero_edge_attachment) = if self.root_component(root).is_some() {
            (
                self.raw_anchors
                    .get(&(endpoint.sort, endpoint.raw))
                    .copied()
                    .ok_or("native value has a cold component but no raw-specific anchor")?,
                true,
            )
        } else {
            let leaf = self.new_leaf(position, endpoint);
            self.components.insert(root, EqComponentRef::Leaf(leaf));
            (leaf, false)
        };
        self.occurrences.insert(key, leaf);
        if exact {
            self.exact_occurrences
                .entry((endpoint.sort, endpoint.term))
                .or_insert(((endpoint.sort, endpoint.raw), leaf));
        }
        if zero_edge_attachment {
            attachments.push(TermAttachment {
                position,
                sort: endpoint.sort,
                raw: endpoint.raw,
                term: endpoint.term,
                leaf,
                dependency: TermAttachmentDependency::Cause(cause.public()),
            });
        }
        Ok(leaf)
    }

    fn union(
        &mut self,
        left: (ReplaySortId, Value),
        right: (ReplaySortId, Value),
        component: EqComponentRef,
    ) -> (Value, Value) {
        assert_eq!(left.0, right.0, "cold equality union crosses logical sorts");
        let (parent, child) = if left.1 <= right.1 {
            (left, right)
        } else {
            (right, left)
        };
        self.parents.insert(child, parent);
        self.components.remove(&child);
        self.components.insert(parent, component);
        (parent.1, child.1)
    }
}

fn attach_fact_terms(
    projector: &mut TermProjector<'_>,
    forest: &mut ColdEqualityForest,
    fact_id: FactId,
    position: HistoryPosition,
    attachments: &mut Vec<TermAttachment>,
) -> Result<(), String> {
    let fact = projector
        .arena
        .facts
        .get((fact_id.get() - 1) as usize)
        .and_then(Option::as_ref)
        .ok_or_else(|| format!("cannot attach unknown fact {fact_id:?}"))?;
    let table = fact.table;
    let values = projector.arena.durable_fact_values[fact.values.as_range()].to_vec();
    let layout: Vec<Option<ReplaySortId>> = projector
        .replay_terms
        .table_layout(table)
        .ok_or_else(|| format!("fact {fact_id:?} table has no replay layout"))?
        .to_vec();
    if layout.len() != values.len() {
        return Err(format!(
            "fact {fact_id:?} row and replay layout have different arities"
        ));
    }
    for (column, (sort, raw)) in layout.into_iter().zip(values).enumerate() {
        let Some(sort) = sort else {
            continue;
        };
        let term = projector.fact_term(fact_id, column)?;
        if let Some(attachment) = forest.attach_fact_term(
            position,
            TermAttachmentDependency::Fact(fact_id),
            EqualityEndpoint { sort, term, raw },
        )? {
            attachments.push(attachment);
        }
    }
    Ok(())
}

fn attach_rekey_terms(
    projector: &mut TermProjector<'_>,
    forest: &mut ColdEqualityForest,
    rekey: &RekeyRecord,
    attachments: &mut Vec<TermAttachment>,
) -> Result<(), String> {
    for pair in &rekey.equalities.pairs {
        let term = projector.fact_term(rekey.fact, pair.column.index())?;
        attachments.push(forest.attach_rekey_term(
            rekey.position,
            rekey.fact,
            EqualityEndpoint {
                sort: pair.left.sort,
                term,
                raw: pair.left.raw,
            },
            EqualityEndpoint {
                sort: pair.right.sort,
                term,
                raw: pair.right.raw,
            },
        )?);
    }
    Ok(())
}

fn build_cold_equality_forest(
    projector: &mut TermProjector<'_>,
    history: &[DurableEquality],
) -> Result<ColdEqualityArtifacts, String> {
    let mut forest = ColdEqualityForest::default();
    let mut nodes = Vec::new();
    let mut equalities = Vec::new();
    let mut aliases = Vec::new();
    let mut prefix = Vec::with_capacity(history.len());
    let mut projected_history = Vec::with_capacity(history.len());
    let mut attachments = Vec::new();
    #[derive(Clone, Copy)]
    enum NavigationEvent {
        Fact(FactId),
        Rekey(usize),
    }
    let mut navigation_events = projector
        .arena
        .facts
        .iter()
        .enumerate()
        .map(|(index, slot)| match slot {
            Some(fact) => Ok((
                fact.position,
                NavigationEvent::Fact(FactId::new(index as u64 + 1)),
            )),
            None => Err("cold equality projection saw a missing dense FactId"),
        })
        .collect::<Result<Vec<_>, _>>()?;
    navigation_events.extend(
        projector
            .arena
            .rekeys
            .iter()
            .enumerate()
            .map(|(index, rekey)| (rekey.position, NavigationEvent::Rekey(index))),
    );
    navigation_events.sort_by_key(|(position, _)| *position);

    // One global position orders every effective cross-stream event. Rekeys
    // Checks do not mutate the cold forest, but including them in the
    // uniqueness audit prevents a landmark from silently aliasing a fact,
    // rekey navigation, or equality event.
    let mut positions = navigation_events
        .iter()
        .map(|(position, _)| *position)
        .chain(history.iter().map(|event| event.position))
        .chain(
            projector
                .arena
                .check_roots
                .values()
                .map(|event| event.position),
        )
        .collect::<Vec<_>>();
    positions.sort_unstable();
    if positions.iter().any(|position| position.get() == 0)
        || positions.windows(2).any(|pair| pair[0] == pair[1])
    {
        return Err("causal logical history positions are missing or duplicated".into());
    }

    let mut navigation_cursor = 0usize;
    for (history_index, event) in history.iter().enumerate() {
        if event.history.get() as usize != history_index + 1 {
            return Err("raw equality history is not one dense chronological prefix".into());
        }
        if history_index > 0 && history[history_index - 1].position >= event.position {
            return Err("applied equality positions are not strictly chronological".into());
        }
        while let Some((position, navigation)) = navigation_events.get(navigation_cursor).copied() {
            if position >= event.position {
                break;
            }
            match navigation {
                NavigationEvent::Fact(fact) => {
                    attach_fact_terms(projector, &mut forest, fact, position, &mut attachments)?
                }
                NavigationEvent::Rekey(index) => {
                    let rekey = projector.arena.rekeys[index].clone();
                    attach_rekey_terms(projector, &mut forest, &rekey, &mut attachments)?
                }
            }
            navigation_cursor += 1;
        }
        let left = projector.equality_endpoint(event.proposal.left, event.cause)?;
        let right = projector.equality_endpoint(event.proposal.right, event.cause)?;
        for endpoint in [&left, &right] {
            let Some(creation_raw) = endpoint.creation_raw else {
                continue;
            };
            if creation_raw != endpoint.endpoint.raw
                && forest.find((endpoint.endpoint.sort, creation_raw))
                    != forest.find((endpoint.endpoint.sort, endpoint.endpoint.raw))
            {
                return Err(format!(
                    "fact-origin equality endpoint {:?} is not connected to its creation value {:?} before event {}",
                    endpoint.endpoint.raw,
                    creation_raw,
                    history_index + 1
                ));
            }
        }
        let left = left.endpoint;
        let right = right.endpoint;
        projected_history.push((left, right));
        if left.sort != right.sort {
            return Err("one raw equality event crosses logical sorts".into());
        }
        let left_leaf = forest.attach_equality_endpoint(
            event.position,
            event.cause,
            left,
            matches!(event.proposal.left.term, EqualityTermRef::Exact(_)),
            &mut attachments,
        )?;
        let right_leaf = forest.attach_equality_endpoint(
            event.position,
            event.cause,
            right,
            matches!(event.proposal.right.term, EqualityTermRef::Exact(_)),
            &mut attachments,
        )?;
        let left_root = forest.find((left.sort, left.raw));
        let right_root = forest.find((right.sort, right.raw));
        if left_root == right_root {
            return Err("raw applied equality history contains a redundant event".into());
        }
        let left_component = forest
            .root_component(left_root)
            .ok_or("left equality occurrence has no cold component")?;
        let right_component = forest
            .root_component(right_root)
            .ok_or("right equality occurrence has no cold component")?;
        let component = if let Some(component) =
            ColdEqualityForest::alias_component(left_component, right_component)
        {
            aliases.push(NativeAliasRecord {
                wave: event.proposal.wave,
                position: event.position,
                left,
                right,
                native_parent: event.native_parent,
                native_child: event.native_child,
                reason: event.reason.clone(),
            });
            component
        } else {
            if left.term == right.term {
                let prior_fact = match event
                    .cause
                    .cause_node()
                    .and_then(|cause| projector.arena.durable_cause(cause))
                {
                    Some(DurableCause::Merge {
                        prior: DurablePrior::Fact(fact),
                        ..
                    }) if projector.arena.originating_rule(event.cause).is_some() => Some(*fact),
                    _ => None,
                };
                let endpoint_cells = [event.proposal.left.term, event.proposal.right.term];
                let witnessed = prior_fact.is_some_and(|prior_fact| {
                    endpoint_cells
                        .iter()
                        .all(|term| matches!(term, EqualityTermRef::Cell { .. }))
                        && endpoint_cells.iter().any(|term| {
                            matches!(
                                term,
                                EqualityTermRef::Cell {
                                    origin: RowOriginRef::Fact(fact),
                                    ..
                                } if *fact == prior_fact
                            )
                        })
                });
                if !witnessed {
                    return Err(format!(
                        "same-term native bridge at event {} has no exact fact/rule merge witness",
                        history_index + 1
                    ));
                }
            }
            let id = EqNodeId::new(nodes.len() as u64 + 1);
            nodes.push(EqNodeRecord {
                id,
                left: left_component,
                right: right_component,
                left_anchor: left_leaf,
                right_anchor: right_leaf,
                edge: id,
            });
            equalities.push(EqualityRecord {
                id,
                wave: event.proposal.wave,
                position: event.position,
                left,
                right,
                native_parent: event.native_parent,
                native_child: event.native_child,
                reason: event.reason.clone(),
            });
            EqComponentRef::Node(id)
        };
        forest.advance_component(left_component, component);
        forest.advance_component(right_component, component);
        let (parent, child) = forest.union(left_root, right_root, component);
        if (parent, child) != (event.native_parent, event.native_child) {
            return Err("raw equality history parent/child disagrees with native union".into());
        }
        prefix.push(nodes.len());
    }
    for (position, navigation) in navigation_events.into_iter().skip(navigation_cursor) {
        match navigation {
            NavigationEvent::Fact(fact) => {
                attach_fact_terms(projector, &mut forest, fact, position, &mut attachments)?
            }
            NavigationEvent::Rekey(index) => {
                let rekey = projector.arena.rekeys[index].clone();
                attach_rekey_terms(projector, &mut forest, &rekey, &mut attachments)?
            }
        }
    }
    attachments.sort_by_key(|attachment| attachment.position);
    Ok((
        forest.leaves,
        nodes,
        equalities,
        aliases,
        prefix,
        projected_history,
        attachments,
    ))
}

fn project_rebuild_equalities(
    projector: &mut TermProjector<'_>,
    equality_history: &[(EqualityEndpoint, EqualityEndpoint)],
    prior_fact: FactId,
    as_of_edges: EqualityEdgeCount,
    pairs: &[TypedCellEquality],
) -> Result<Box<[TypedCellEquality]>, String> {
    let cutoff: usize = as_of_edges
        .get()
        .try_into()
        .map_err(|_| "rebuild equality cutoff exceeds addressable storage")?;
    let history = equality_history
        .get(..cutoff)
        .ok_or_else(|| "rebuild equality cutoff exceeds raw history".to_owned())?;
    pairs
        .iter()
        .map(|pair| {
            let column = pair.column.index();
            let left_term = projector.fact_term(prior_fact, column)?;
            let left_node = projector
                .replay_terms
                .node(left_term)
                .ok_or_else(|| format!("rebuild prior fact owns unknown term {left_term:?}"))?;
            if left_node.sort() != pair.left.sort {
                return Err("rebuild prior fact term has the wrong logical sort".into());
            }
            let right_term = history
                .iter()
                .rev()
                .flat_map(|(left, right)| [*left, *right])
                .find(|endpoint| endpoint.sort == pair.right.sort && endpoint.raw == pair.right.raw)
                .map(|endpoint| endpoint.term)
                .ok_or_else(|| {
                    format!(
                        "rebuild target {:?} has no exact endpoint at its historical cutoff",
                        pair.right.raw
                    )
                })?;
            Ok(TypedCellEquality {
                column: pair.column,
                left: EqualityEndpoint {
                    term: left_term,
                    ..pair.left
                },
                right: EqualityEndpoint {
                    term: right_term,
                    ..pair.right
                },
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Vec::into_boxed_slice)
}

fn project_container_equalities(
    projector: &TermProjector<'_>,
    equality_history: &[(EqualityEndpoint, EqualityEndpoint)],
    as_of_edges: EqualityEdgeCount,
    pairs: &[TypedCellEquality],
) -> Result<Box<[TypedCellEquality]>, String> {
    let cutoff: usize = as_of_edges
        .get()
        .try_into()
        .map_err(|_| "container equality cutoff exceeds addressable storage")?;
    let history = equality_history
        .get(..cutoff)
        .ok_or_else(|| "container equality cutoff exceeds raw history".to_owned())?;
    let resolve = |endpoint: EqualityEndpoint| -> Result<EqualityEndpoint, String> {
        if !endpoint.term.is_missing() {
            let node = projector.replay_terms.node(endpoint.term).ok_or_else(|| {
                format!("container landmark owns unknown term {:?}", endpoint.term)
            })?;
            if node.sort() != endpoint.sort {
                return Err("container landmark term has the wrong logical sort".into());
            }
            return Ok(endpoint);
        }
        history
            .iter()
            .rev()
            .flat_map(|(left, right)| [*left, *right])
            .find(|candidate| candidate.sort == endpoint.sort && candidate.raw == endpoint.raw)
            .ok_or_else(|| {
                format!(
                    "container child {:?} has no exact endpoint at its historical cutoff",
                    endpoint.raw
                )
            })
    };
    pairs
        .iter()
        .map(|pair| {
            Ok(TypedCellEquality {
                column: pair.column,
                left: resolve(pair.left)?,
                right: resolve(pair.right)?,
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Vec::into_boxed_slice)
}

fn project_fact_cause(
    projector: &mut TermProjector<'_>,
    arena: &ReceiptArena,
    equality_history: &[(EqualityEndpoint, EqualityEndpoint)],
    root: CauseRef,
) -> Result<FactCause, String> {
    if let Some(rule) = root.rule_match() {
        return Ok(FactCause::Rule(rule));
    }
    let root = root
        .cause_node()
        .ok_or_else(|| "missing durable cause".to_owned())?;
    let root_node = arena
        .durable_cause(root)
        .ok_or_else(|| format!("unknown durable cause {root:?}"))?;
    Ok(match root_node {
        DurableCause::Source(source) => FactCause::Source(source.clone()),
        DurableCause::Rebuild {
            wave,
            prior_fact,
            as_of_edges,
            position,
            equalities,
        } => FactCause::Rebuild {
            wave: *wave,
            prior_fact: *prior_fact,
            equalities: EqualityLandmark {
                as_of_edges: *as_of_edges,
                position: *position,
                pairs: project_rebuild_equalities(
                    projector,
                    equality_history,
                    *prior_fact,
                    *as_of_edges,
                    &arena.durable_rebuild_equalities[equalities.as_range()],
                )?,
            },
        },
        DurableCause::ContainerCanonicalize { .. } => {
            return Err("container canonicalization cannot justify an effective table fact".into());
        }
        DurableCause::ContainerRefresh {
            wave,
            prior_fact,
            as_of_edges,
            position,
            equalities,
        } => FactCause::ContainerRefresh {
            wave: *wave,
            prior_fact: *prior_fact,
            equalities: EqualityLandmark {
                as_of_edges: *as_of_edges,
                position: *position,
                pairs: project_container_equalities(
                    projector,
                    equality_history,
                    *as_of_edges,
                    &arena.durable_rebuild_equalities[equalities.as_range()],
                )?,
            },
        },
        DurableCause::Merge { .. } => FactCause::Merge {
            cause: root.public(),
        },
    })
}

struct ReceiptShared {
    next_fact: AtomicU64,
    next_rule_match: AtomicU64,
    next_term: AtomicU32,
    next_equality: AtomicU64,
    next_history: AtomicU64,
    next_cause_draft: AtomicU64,
    open_fragments: AtomicUsize,
    open_native_leases: AtomicUsize,
    abandoned_fragments: AtomicU64,
    poisoned_rule_executions: AtomicU64,
    replay_terms: ReplayTermStore,
    equality_value_sorts: Mutex<HashMap<Value, ReplaySortId>>,
    equality_wave_timestamp: Mutex<Option<(CausalWave, Value)>>,
    /// One canonical source-order binding recipe per source-level rule.
    rule_binding_recipes: RwLock<HashMap<u32, Arc<[ReplayBindingSource]>>>,
    /// Cold compile-time recipes shared by every seminaive/decomposed variant.
    static_term_recipes: Mutex<StaticTermRecipeStore>,
    arena: Mutex<ReceiptArena>,
}

impl Default for ReceiptShared {
    fn default() -> Self {
        Self {
            next_fact: AtomicU64::new(0),
            next_rule_match: AtomicU64::new(0),
            next_term: AtomicU32::new(0),
            next_equality: AtomicU64::new(0),
            next_history: AtomicU64::new(0),
            next_cause_draft: AtomicU64::new(0),
            open_fragments: AtomicUsize::new(0),
            open_native_leases: AtomicUsize::new(0),
            abandoned_fragments: AtomicU64::new(0),
            poisoned_rule_executions: AtomicU64::new(0),
            replay_terms: ReplayTermStore::default(),
            equality_value_sorts: Mutex::new(HashMap::default()),
            equality_wave_timestamp: Mutex::new(None),
            rule_binding_recipes: RwLock::new(HashMap::default()),
            static_term_recipes: Mutex::new(StaticTermRecipeStore::default()),
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
    draft_summaries: HashMap<CauseDraftId, EqualityCauseSummary>,
    facts: Vec<(FactId, PendingFact)>,
    fact_values: Vec<Value>,
    merge_cell_origins: Vec<MergeCellOrigin>,
    equalities: Vec<(EqNodeId, PendingEquality)>,
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
            draft_summaries: HashMap::default(),
            facts: Vec::new(),
            fact_values: Vec::new(),
            merge_cell_origins: Vec::new(),
            equalities: Vec::new(),
            redundant_unions: 0,
            unattributed_commits: 0,
            published: false,
        }
    }

    pub(crate) fn merge_draft_capability(
        &mut self,
        incoming: CauseRef,
        prior_fact: FactId,
    ) -> CauseCapability {
        assert!(
            !incoming.is_unattributed(),
            "merge receipt is missing its incoming cause"
        );
        assert!(
            !prior_fact.is_missing(),
            "merge receipt is missing its prior FactId"
        );
        let equality = self.cause_summary(incoming).with_prior_fact(prior_fact);
        self.add_draft(
            CauseDraft::Merge {
                incoming,
                prior: PriorVersion::Fact(prior_fact),
            },
            equality,
        )
    }

    #[cfg(test)]
    pub(crate) fn merge_drafts(
        &mut self,
        incoming: impl Into<CauseRef>,
        prior: impl Into<CauseRef>,
    ) -> ReceiptCauseRef {
        self.merge_drafts_capability(incoming.into(), prior.into())
            .cause_ref()
            .public()
    }

    pub(crate) fn merge_drafts_capability(
        &mut self,
        incoming: CauseRef,
        prior: CauseRef,
    ) -> CauseCapability {
        assert!(
            !incoming.is_unattributed() && !prior.is_unattributed(),
            "same-wave merge receipt is missing an exact proposal cause"
        );
        let equality = self
            .cause_summary(incoming)
            .merge(self.cause_summary(prior));
        self.add_draft(
            CauseDraft::Merge {
                incoming,
                prior: PriorVersion::Cause(prior),
            },
            equality,
        )
    }

    fn cause_summary(&self, cause: CauseRef) -> EqualityCauseSummary {
        if cause.rule_match().is_some() {
            return EqualityCauseSummary::Rule;
        }
        let cause = cause.cause_node().expect("merge cause is unattributed");
        if let Some(summary) = self.draft_summaries.get(&cause).copied() {
            return summary;
        }
        let arena = self.shared.arena.lock().unwrap();
        arena
            .cause_summary(cause)
            .unwrap_or_else(|error| panic!("cannot classify merge input cause: {error}"))
    }

    /// Prime published cause classifications once for an entire native row
    /// batch. Merge callbacks then consult only this worker-local map, avoiding
    /// one global arena lock for every colliding row.
    pub(crate) fn preload_cause_summaries(&mut self, causes: &[CauseRef]) {
        for cause in causes {
            assert!(
                !cause.is_unattributed(),
                "receipt-enabled table proposal has no exact cause"
            );
        }
        let mut error = None;
        {
            let shared = Arc::clone(&self.shared);
            let arena = shared.arena.lock().unwrap();
            for cause in causes {
                if cause.rule_match().is_some() {
                    continue;
                }
                let cause = cause.cause_node().expect("merge cause is unattributed");
                if self.draft_summaries.contains_key(&cause) {
                    continue;
                }
                match arena.cause_summary(cause) {
                    Ok(summary) => {
                        self.draft_summaries.insert(cause, summary);
                    }
                    Err(cause_error) => {
                        error = Some(cause_error);
                        break;
                    }
                }
            }
        }
        if let Some(error) = error {
            panic!("cannot preload merge input cause: {error}");
        }
    }

    fn add_draft(&mut self, draft: CauseDraft, equality: EqualityCauseSummary) -> CauseCapability {
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.shared.next_cause_draft, 1));
        self.drafts.push((id, draft));
        assert!(self.draft_summaries.insert(id, equality).is_none());
        CauseCapability { id, equality }
    }

    pub(crate) fn record_fact(
        &mut self,
        table: TableId,
        cause: impl Into<CauseRef>,
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
        cause: impl Into<CauseRef>,
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
        cause: impl Into<CauseRef>,
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
        cause: impl Into<CauseRef>,
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
        cause: CauseRef,
        row: &[Value],
        origin: Option<FactOrigin>,
    ) -> FactId {
        assert!(
            !cause.is_unattributed(),
            "effective commit is missing exact causal attribution"
        );
        let id = FactId::new(ReceiptShared::alloc_u64(&self.shared.next_fact, 1));
        let position = HistoryPosition::new(ReceiptShared::alloc_u64(&self.shared.next_history, 1));
        if let Some((last, _)) = self.facts.last() {
            debug_assert!(
                *last < id,
                "ReceiptBatch FactIds must remain strictly increasing"
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
        cause: CauseRef,
    ) -> EqNodeId {
        assert!(
            !cause.is_unattributed(),
            "applied union is missing exact causal attribution"
        );
        let id = EqNodeId::new(ReceiptShared::alloc_u64(&self.shared.next_equality, 1));
        let position = HistoryPosition::new(ReceiptShared::alloc_u64(&self.shared.next_history, 1));
        self.equalities.push((
            id,
            PendingEquality {
                history: EqualityEdgeCount::new(id.get()),
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
            for (id, draft) in self.drafts.drain(..) {
                let equality = self
                    .draft_summaries
                    .remove(&id)
                    .expect("local merge draft has no cached equality classification");
                let durable = match draft {
                    #[cfg(test)]
                    CauseDraft::Source(source) => DurableCause::Source(source),
                    CauseDraft::Merge { incoming, prior } => DurableCause::Merge {
                        incoming,
                        prior: match prior {
                            PriorVersion::Fact(fact) if !fact.is_missing() => {
                                DurablePrior::Fact(fact)
                            }
                            PriorVersion::Fact(_) => {
                                panic!("merge cause references a missing prior FactId")
                            }
                            PriorVersion::Cause(cause) => DurablePrior::Cause(cause),
                        },
                    },
                };
                arena.install_cause(id, durable, equality);
            }
            // Published input summaries are only a worker-local lookup cache;
            // the arena already owns their canonical entries.
            self.draft_summaries.clear();
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
                let summary = if equality.cause.rule_match().is_some() {
                    EqualityCauseSummary::Rule
                } else {
                    arena
                        .cause_summary(
                            equality
                                .cause
                                .cause_node()
                                .expect("equality cause is unattributed"),
                        )
                        .expect("applied equality cause has no classification")
                };
                let reason = arena.equality_reason(equality.cause, summary);
                arena.install_equality(
                    id,
                    DurableEquality {
                        history: equality.history,
                        position: equality.position,
                        proposal: equality.proposal,
                        native_parent: equality.native_parent,
                        native_child: equality.native_child,
                        cause: equality.cause,
                        reason,
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

impl Drop for ReceiptBatch {
    fn drop(&mut self) {
        if self.published {
            return;
        }
        if !self.drafts.is_empty()
            || !self.facts.is_empty()
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

/// Shared read/finalization handle to the database's causal receipt arena.
#[derive(Clone, Default)]
pub struct CausalReceipts(Arc<ReceiptShared>);

impl CausalReceipts {
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

    fn equality_boundary(&self) -> EqualityEdgeCount {
        EqualityEdgeCount::new(self.0.next_equality.load(Ordering::Acquire))
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
        wave: CausalWave,
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

    #[cfg(test)]
    pub(crate) fn rule_term_recipe(&self, rule: u32) -> Option<Arc<TermRecipe>> {
        self.0
            .static_term_recipes
            .lock()
            .unwrap()
            .rules
            .get(&rule)
            .cloned()
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
                        "rule receipt Current slots must be dense in source order"
                    );
                    next_residual += 1;
                }
                ReplayBindingSource::Constant { term } => {
                    assert!(!term.is_missing(), "rule receipt constant term is missing");
                }
                ReplayBindingSource::Premise {
                    representative,
                    occurrences,
                } => {
                    assert!(
                        !occurrences.is_empty(),
                        "rule receipt premise binding has no occurrences"
                    );
                    assert!(
                        occurrences.contains(representative),
                        "rule receipt representative is not one of its premise occurrences"
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

    pub(crate) fn pending_native_lease(&self, wave: CausalWave) -> PendingNativeLease {
        self.0.open_native_leases.fetch_add(1, Ordering::Relaxed);
        PendingNativeLease(Arc::new(PendingNativeLeaseInner {
            receipts: self.clone(),
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
    pub(crate) fn equality_edge_count(&self) -> Result<EqualityEdgeCount, &'static str> {
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild with open receipt fragments");
        }
        if self.0.abandoned_fragments.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild after an abandoned receipt fragment");
        }
        let count = self.0.next_equality.load(Ordering::Acquire);
        let arena = self.0.arena.lock().unwrap();
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err("receipt fragment opened while capturing rebuild equality cutoff");
        }
        if count != arena.published_equalities {
            return Err("rebuild equality cutoff is not one complete dense prefix");
        }
        Ok(EqualityEdgeCount::new(count))
    }

    pub(crate) fn validate_deferred_equality_cause(
        &self,
        cause: &DeferredEqualityCause,
    ) -> Result<(), &'static str> {
        cause.equality_summary(self).validate()
    }

    pub(crate) fn pending_merge_cause(
        &self,
        incoming: DeferredEqualityCause,
        prior_fact: FactId,
    ) -> DeferredEqualityCause {
        assert!(
            !prior_fact.is_missing(),
            "deferred merge receipt is missing its prior FactId"
        );
        let equality = incoming.equality_summary(self).with_prior_fact(prior_fact);
        DeferredEqualityCause(DeferredEqualityCauseKind::Merge(Arc::new(
            PendingMergeCause {
                receipts: self.clone(),
                incoming,
                prior_fact,
                equality,
                cause: OnceLock::new(),
            },
        )))
    }

    fn promote_pending_merge_cause(&self, cause: &PendingMergeCause) -> CauseRef {
        assert!(Arc::ptr_eq(&self.0, &cause.receipts.0));
        let incoming = cause.incoming.promote();
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
        let mut arena = self.0.arena.lock().unwrap();
        arena.install_cause(
            id,
            DurableCause::Merge {
                incoming,
                prior: DurablePrior::Fact(cause.prior_fact),
            },
            cause.equality,
        );
        CauseRef::node(id)
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
        wave: CausalWave,
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
        wave: CausalWave,
        prior_fact: FactId,
        old_row: &[Value],
        new_row: &[Value],
        rebuild_columns: &[crate::ColumnId],
        as_of_edges: EqualityEdgeCount,
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
            return Err("rebuild receipt has no changed semantic column");
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
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
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
        let position = HistoryPosition::new(ReceiptShared::alloc_u64(&self.0.next_history, 1));
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
        wave: CausalWave,
        before: &[Value],
        after: &[Value],
        as_of_edges: EqualityEdgeCount,
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
                // raw typed values and resolve terms only for a cold snapshot.
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
        wave: CausalWave,
        left: Value,
        right: Value,
        as_of_edges: EqualityEdgeCount,
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
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
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
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
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

    /// Test-only capability for modeling a current-value mapping that a
    /// certified source, constructor, or replay-safe producer installed before
    /// an equality proposal was staged. Production callers must establish
    /// this capability through their typed producer paths instead.
    #[cfg(test)]
    pub(crate) fn install_trusted_value_term(
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

    pub(crate) fn check_premise_terms(
        &self,
        premises: &[FactId],
        requests: &[(CheckTermSource, ReplaySortId)],
    ) -> Result<SmallVec<[ReplayTermId; 8]>, String> {
        enum Lookup {
            Direct {
                term: ReplayTermId,
                sort: ReplaySortId,
            },
            Constructor {
                premise: usize,
                fact: FactId,
                column: usize,
                term: ReplayTermId,
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
                        lookups.push(Lookup::Direct { term, sort });
                    }
                    CheckTermSource::Constructor {
                        premise,
                        input_columns,
                        op,
                    } => {
                        let fact = *premises.get(premise).ok_or_else(|| {
                            "check endpoint cites a missing premise slot".to_owned()
                        })?;
                        let term = projector.fact_term(fact, input_columns).map_err(|_| {
                            "check constructor producer has an unreconstructible output term"
                                .to_owned()
                        })?;
                        lookups.push(Lookup::Constructor {
                            premise,
                            fact,
                            column: input_columns,
                            term,
                            sort,
                            op,
                        });
                    }
                    CheckTermSource::Current => {
                        return Err(
                            "current-value check endpoint was requested as a premise term".into(),
                        );
                    }
                }
            }
            lookups
        };

        let mut terms = SmallVec::<[ReplayTermId; 8]>::new();
        for lookup in lookups {
            let term = match lookup {
                Lookup::Direct { term, sort } => {
                    let node = self.0.replay_terms.node(term).ok_or_else(|| {
                        "check endpoint fact owns an unknown ReplayTermId".to_owned()
                    })?;
                    if node.sort() != sort {
                        return Err("check endpoint fact term has the wrong declared sort".into());
                    }
                    term
                }
                Lookup::Constructor {
                    premise,
                    fact,
                    column,
                    term,
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
                    term
                }
            };
            terms.push(term);
        }
        Ok(terms)
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

    #[cfg(test)]
    pub(crate) fn test_container_anchors(
        &self,
        sort: ReplaySortId,
        value: Value,
    ) -> SmallVec<[ReplayTermId; 2]> {
        self.0.replay_terms.container_anchors(sort, value)
    }

    /// Publish one fully-resolved check root atomically. Runtime values and
    /// their independently-selected structural terms are validated before the
    /// applied-equality cutoff or root storage is changed.
    pub(crate) fn record_check_root(
        &self,
        check: u32,
        wave: CausalWave,
        premises: &[FactId],
        equalities: &[(EqualityEndpoint, EqualityEndpoint)],
        as_of_edges: EqualityEdgeCount,
    ) -> Result<(), &'static str> {
        if premises.iter().any(|fact| fact.is_missing()) {
            return Err("check root has a missing exact premise FactId");
        }
        for (left, right) in equalities {
            if left.sort != right.sort {
                return Err("one check equality crosses logical sorts");
            }
            if left.term == right.term {
                return Err(
                    "causal equality endpoints collapsed to one structural term; exact source terms are unavailable",
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
                || current
                    .equalities
                    .iter()
                    .map(|(left, _)| left.sort)
                    .ne(equalities.iter().map(|(left, _)| left.sort))
            {
                return Err("stable check id was reused with a different receipt layout");
            }
            // Causal capture is serial-only: the first successful native
            // witness is the check root. A repeated callback for the same
            // check is diagnostic duplication, not a later replacement.
            return Ok(());
        }
        let position = HistoryPosition::new(ReceiptShared::alloc_u64(&self.0.next_history, 1));
        arena.check_roots.insert(
            check,
            CheckRoot {
                check,
                wave,
                position,
                premises: premises.into(),
                equalities: equalities.into(),
                as_of_edges,
            },
        );
        Ok(())
    }

    pub(crate) fn typed_equality_proposal(
        &self,
        wave: CausalWave,
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
        wave: CausalWave,
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
        wave: CausalWave,
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

    fn validate_pending_premises(&self, premises: &[FactId]) -> Result<(), String> {
        let arena = self.0.arena.lock().unwrap();
        for fact in premises.iter().copied() {
            if !arena.has_fact(fact) {
                return Err(format!(
                    "observed match references unavailable premise {fact:?}"
                ));
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn install_observed_matches(
        &self,
        rule: u32,
        wave: CausalWave,
        position: HistoryPosition,
        as_of_edges: EqualityEdgeCount,
        first_match: RuleMatchId,
        premise_arity: usize,
        premises: &[FactId],
        lanes: usize,
        binding_arity: usize,
    ) {
        let mut arena = self.0.arena.lock().unwrap();
        let premise_start = arena.durable_premises.len();
        arena.durable_premises.extend_from_slice(premises);
        for lane in 0..lanes {
            let id = first_match.get() + lane as u64;
            let index = (id - 1) as usize;
            if arena.durable_matches.len() <= index {
                arena.durable_matches.resize_with(index + 1, || None);
            }
            assert!(
                arena.durable_matches[index].is_none(),
                "duplicate RuleMatchId publication"
            );
            arena.durable_matches[index] = Some(DurableMatch {
                rule,
                wave,
                position,
                as_of_edges,
                premises: FlatRange::new(premise_start + lane * premise_arity, premise_arity),
            });
        }
        arena.published_matches += lanes as u64;
        arena.counters.premise_handles += premises.len() as u64;
        arena.record_match_term_storage(lanes * binding_arity, 0);
        arena.counters.observed_matches += lanes as u64;
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
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
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
        let first = ReceiptShared::alloc_u64(&self.0.next_cause_draft, lanes.len());
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
        let first = ReceiptShared::alloc_u64(&self.0.next_cause_draft, sources.len());
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
    /// returns its first stable match id.
    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn pending_rule_batch(
        &self,
        rule: u32,
        wave: CausalWave,
        premise_arity: usize,
        binding_sources: &[ReplayBindingSource],
        flat_premises: &[FactId],
        lanes: usize,
    ) -> ObservedMatchBatch {
        assert!(lanes > 0, "observed match batch cannot be empty");
        assert_eq!(
            flat_premises.len(),
            lanes * premise_arity,
            "pending match premises must be dense and lane-aligned"
        );
        self.validate_pending_premises(flat_premises)
            .unwrap_or_else(|error| panic!("cannot observe test rule batch: {error}"));
        let first_native_ordinal = self.reserve_native_match_ordinals(lanes);
        let binding_sources = self.register_rule_binding_recipe(rule, binding_sources);
        self.observe_rule_batch_at(
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
    pub(crate) fn observe_rule_batch_at(
        &self,
        rule: u32,
        wave: CausalWave,
        first_native_ordinal: u64,
        premise_arity: usize,
        binding_sources: Arc<[ReplayBindingSource]>,
        flat_premises: &[FactId],
        lanes: usize,
    ) -> ObservedMatchBatch {
        assert!(first_native_ordinal > 0);
        assert_eq!(
            flat_premises.len(),
            lanes
                .checked_mul(premise_arity)
                .expect("pending match premise slab exceeds usize"),
            "observed match premises must be dense and lane-aligned"
        );
        let position = self.history_boundary();
        let as_of_edges = self.equality_boundary();
        let premises: Box<[FactId]> = flat_premises.into();
        self.validate_pending_premises(&premises)
            .unwrap_or_else(|error| panic!("cannot observe rule batch: {error}"));
        let first_match = RuleMatchId::new(first_native_ordinal);
        self.install_observed_matches(
            rule,
            wave,
            position,
            as_of_edges,
            first_match,
            premise_arity,
            &premises,
            lanes,
            binding_sources.len(),
        );
        ObservedMatchBatch {
            receipts: self.clone(),
            first: first_match,
            lanes: lanes
                .try_into()
                .expect("observed match batch exceeds u32 lanes"),
            wave,
        }
    }

    /// Resolve compact join witnesses once when head execution begins, then
    /// publish the complete native observation batch eagerly.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn observe_rule_batch_lazy(
        &self,
        rule: u32,
        wave: CausalWave,
        first_native_ordinal: u64,
        premise_arity: usize,
        binding_sources: Arc<[ReplayBindingSource]>,
        resolver: Arc<dyn PendingPremiseResolver>,
        witness_lanes: &[u32],
    ) -> ObservedMatchBatch {
        let lanes = witness_lanes.len();
        assert!(lanes > 0, "observed match batch cannot be empty");
        assert!(first_native_ordinal > 0);
        let premises = resolver.resolve_batch(witness_lanes, premise_arity);
        self.validate_pending_premises(&premises)
            .unwrap_or_else(|error| panic!("cannot observe rule batch: {error}"));
        let position = self.history_boundary();
        let as_of_edges = self.equality_boundary();
        let first_match = RuleMatchId::new(first_native_ordinal);
        self.install_observed_matches(
            rule,
            wave,
            position,
            as_of_edges,
            first_match,
            premise_arity,
            &premises,
            lanes,
            binding_sources.len(),
        );
        ObservedMatchBatch {
            receipts: self.clone(),
            first: first_match,
            lanes: lanes
                .try_into()
                .expect("observed match batch exceeds u32 lanes"),
            wave,
        }
    }

    pub(crate) fn reserve_native_match_ordinals(&self, lanes: usize) -> u64 {
        ReceiptShared::alloc_u64(&self.0.next_rule_match, lanes)
    }

    pub(crate) fn pending_rule_cause(
        &self,
        observed: &ObservedMatchBatch,
        lane: usize,
    ) -> PendingRuleCause {
        assert!(
            Arc::ptr_eq(&self.0, &observed.receipts.0),
            "observed match batch belongs to another causal receipt arena"
        );
        assert!(
            lane < observed.lanes as usize,
            "observed match lane {lane} is outside a {}-lane batch",
            observed.lanes
        );
        let matched = RuleMatchId::new(
            observed
                .first
                .get()
                .checked_add(lane as u64)
                .expect("observed match id overflow"),
        );
        assert!(
            matched.get() <= self.0.next_rule_match.load(Ordering::Acquire),
            "observed match batch references unreserved match {matched:?}"
        );
        PendingRuleCause {
            receipts: self.clone(),
            matched,
            wave: observed.wave,
        }
    }

    #[cfg(test)]
    pub(crate) fn observed_match_batch_for_test(
        &self,
        first: RuleMatchId,
        lanes: u32,
        wave: CausalWave,
    ) -> ObservedMatchBatch {
        ObservedMatchBatch {
            receipts: self.clone(),
            first,
            lanes,
            wave,
        }
    }

    fn prepare_observed_rule_match(
        &self,
        matched: RuleMatchId,
        expected_wave: CausalWave,
    ) -> Result<(), String> {
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0 {
            return Err("rule observation belongs to a panicking execution".into());
        }
        let arena = self.0.arena.lock().unwrap();
        let Some(record) = matched
            .get()
            .checked_sub(1)
            .and_then(|index| arena.durable_matches.get(index as usize))
            .and_then(Option::as_ref)
        else {
            return Err(format!("unknown observed match {matched:?}"));
        };
        if record.wave != expected_wave {
            return Err(format!(
                "observed match {matched:?} from wave {:?} was used in wave {:?}",
                record.wave, expected_wave
            ));
        }
        Ok(())
    }

    fn record_observed_match_merge_read(&self, matched: RuleMatchId, prior_fact: FactId) {
        assert!(
            !prior_fact.is_missing(),
            "receipt-enabled table merge read a row without an immutable FactId"
        );
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0 {
            panic!("cannot record merge read: rule observation belongs to a panicking execution");
        }
        self.0
            .arena
            .lock()
            .unwrap()
            .merge_reads
            .entry(matched)
            .or_default()
            .push(prior_fact);
    }

    /// Test-only eager registration helper for low-level receipt fixtures.
    /// Production rule execution always uses pending batches.
    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn register_rule_matches(
        &self,
        rule: u32,
        wave: CausalWave,
        premise_arity: usize,
        binding_sources: &[ReplayBindingSource],
        flat_premises: &[FactId],
        lanes: &[usize],
    ) -> Vec<(usize, CauseRef)> {
        if lanes.is_empty() {
            return Vec::new();
        }
        let binding_sources = self.register_rule_binding_recipe(rule, binding_sources);
        let first_match = RuleMatchId::new(self.reserve_native_match_ordinals(lanes.len()));
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
        self.install_observed_matches(
            rule,
            wave,
            position,
            as_of_edges,
            first_match,
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
                    CauseRef::rule(RuleMatchId::new(first_match.get() + offset as u64)),
                )
            })
            .collect()
    }

    pub(crate) fn finalize_wave(&self) {
        assert_eq!(
            self.0.poisoned_rule_executions.load(Ordering::Acquire),
            0,
            "cannot finalize causal receipts after a panicking rule execution"
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
            arena.published_matches,
            self.0.next_rule_match.load(Ordering::Acquire),
            "observed match publication left an ID hole"
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

    pub fn snapshot(&self) -> ReceiptSnapshot {
        assert_eq!(
            self.0.poisoned_rule_executions.load(Ordering::Acquire),
            0,
            "cannot snapshot causal receipts after a panicking rule execution"
        );
        assert_eq!(
            self.0.open_fragments.load(Ordering::Acquire),
            0,
            "cannot snapshot causal receipts with open worker fragments"
        );
        assert_eq!(
            self.0.open_native_leases.load(Ordering::Acquire),
            0,
            "cannot snapshot causal receipts with queued transactional native mutations"
        );
        assert_eq!(
            self.0.abandoned_fragments.load(Ordering::Acquire),
            0,
            "cannot snapshot causal receipts after an unpublished worker fragment"
        );
        let recipes = self.0.rule_binding_recipes.read().unwrap();
        let term_recipes = self.0.static_term_recipes.lock().unwrap();
        let arena = self.0.arena.lock().unwrap();
        assert_eq!(
            arena.published_facts,
            self.0.next_fact.load(Ordering::Acquire),
            "finalize the causal wave before taking a durable snapshot"
        );
        let durable_equalities = arena
            .durable_equalities
            .iter()
            .map(|event| {
                event
                    .clone()
                    .expect("snapshot observed an equality ID hole")
            })
            .collect::<Vec<_>>();
        let mut projector = TermProjector::new(
            &arena,
            &recipes,
            &term_recipes,
            &self.0.replay_terms,
            &self.0.next_term,
        );
        let cold_equalities = build_cold_equality_forest(&mut projector, &durable_equalities);
        let (
            equality_leaves,
            equality_nodes,
            equalities,
            native_aliases,
            equality_history_prefix,
            projected_equality_history,
            term_attachments,
        ) = match cold_equalities {
            Ok(artifacts) => artifacts,
            Err(error) => {
                // A cold projection error is fail-closed, but it must not
                // poison the durable receipt arena or recipe registry. Drop
                // every guard before surfacing the named diagnostic so the
                // immutable history remains inspectable/retryable.
                drop(projector);
                drop(arena);
                drop(term_recipes);
                drop(recipes);
                panic!("cannot project equality history: {error}");
            }
        };
        let cited_matches = arena
            .cited_matches()
            .unwrap_or_else(|error| panic!("cannot select cited matches: {error}"));
        let matches = arena
            .durable_matches
            .iter()
            .enumerate()
            .filter_map(|(index, record)| {
                let match_id = RuleMatchId::new(index as u64 + 1);
                if !cited_matches.contains(&match_id) {
                    return None;
                }
                let record = record
                    .as_ref()
                    .expect("snapshot observed a RuleMatchId publication hole");
                let premises = &arena.durable_premises[record.premises.as_range()];
                let recipe = recipes
                    .get(&record.rule)
                    .unwrap_or_else(|| panic!("rule {} has no binding recipe", record.rule));
                let terms = (0..recipe.len())
                    .map(|binding| {
                        projector
                            .match_term(match_id, binding)
                            .unwrap_or_else(|error| panic!("cannot project match term: {error}"))
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                Some(MatchRecord {
                    id: match_id,
                    rule: record.rule,
                    wave: record.wave,
                    position: record.position,
                    as_of_edges: record.as_of_edges,
                    premises: premises.into(),
                    terms,
                    merge_reads: arena
                        .merge_reads
                        .get(&match_id)
                        .cloned()
                        .unwrap_or_default()
                        .into_vec()
                        .into_boxed_slice(),
                })
            })
            .collect();
        let facts = arena
            .facts
            .iter()
            .enumerate()
            .map(|(index, slot)| {
                let fact = slot.as_ref().expect("snapshot observed a FactId hole");
                let cause = project_fact_cause(
                    &mut projector,
                    &arena,
                    &projected_equality_history,
                    fact.cause,
                )
                .unwrap_or_else(|error| panic!("cannot project fact cause: {error}"));
                let values: Box<[Value]> = arena.durable_fact_values[fact.values.as_range()].into();
                let layout = self
                    .0
                    .replay_terms
                    .table_layout(fact.table)
                    .expect("durable fact table has no replay layout");
                let fact_id = FactId::new(index as u64 + 1);
                let terms = layout
                    .iter()
                    .enumerate()
                    .map(|(column, sort)| {
                        sort.map_or(ReplayTermId::MISSING, |_| {
                            projector
                                .fact_term(fact_id, column)
                                .unwrap_or_else(|error| panic!("cannot project fact term: {error}"))
                        })
                    })
                    .collect();
                FactRecord {
                    id: fact_id,
                    table: fact.table,
                    position: fact.position,
                    cause,
                    values,
                    terms,
                }
            })
            .collect();
        let rekeys = arena
            .rekeys
            .iter()
            .map(|record| RekeyRecord {
                fact: record.fact,
                table: record.table,
                wave: record.wave,
                position: record.position,
                equalities: EqualityLandmark {
                    as_of_edges: record.equalities.as_of_edges,
                    position: record.equalities.position,
                    pairs: project_rebuild_equalities(
                        &mut projector,
                        &projected_equality_history,
                        record.fact,
                        record.equalities.as_of_edges,
                        &record.equalities.pairs,
                    )
                    .unwrap_or_else(|error| panic!("cannot project rekey landmark: {error}")),
                },
                outcome: record.outcome,
            })
            .collect();
        let causes = arena
            .durable_causes
            .iter()
            .map(|entry| {
                match entry
                    .as_ref()
                    .expect("snapshot observed a cause-node ID hole")
                {
                    DurableCause::Source(source) => ReceiptCauseRecord::Source(source.clone()),
                    DurableCause::Rebuild {
                        wave,
                        prior_fact,
                        as_of_edges,
                        position,
                        equalities,
                    } => ReceiptCauseRecord::Rebuild {
                        wave: *wave,
                        prior_fact: *prior_fact,
                        equalities: EqualityLandmark {
                            as_of_edges: *as_of_edges,
                            position: *position,
                            pairs: project_rebuild_equalities(
                                &mut projector,
                                &projected_equality_history,
                                *prior_fact,
                                *as_of_edges,
                                &arena.durable_rebuild_equalities[equalities.as_range()],
                            )
                            .unwrap_or_else(|error| {
                                panic!("cannot project rebuild cause landmark: {error}")
                            }),
                        },
                    },
                    DurableCause::ContainerCanonicalize {
                        wave,
                        as_of_edges,
                        position,
                        equalities,
                    } => ReceiptCauseRecord::ContainerCanonicalize {
                        wave: *wave,
                        equalities: EqualityLandmark {
                            as_of_edges: *as_of_edges,
                            position: *position,
                            pairs: project_container_equalities(
                                &projector,
                                &projected_equality_history,
                                *as_of_edges,
                                &arena.durable_rebuild_equalities[equalities.as_range()],
                            )
                            .unwrap_or_else(|error| {
                                panic!("cannot project container canonicalization: {error}")
                            }),
                        },
                    },
                    DurableCause::ContainerRefresh {
                        wave,
                        prior_fact,
                        as_of_edges,
                        position,
                        equalities,
                    } => ReceiptCauseRecord::ContainerRefresh {
                        wave: *wave,
                        prior_fact: *prior_fact,
                        equalities: EqualityLandmark {
                            as_of_edges: *as_of_edges,
                            position: *position,
                            pairs: project_container_equalities(
                                &projector,
                                &projected_equality_history,
                                *as_of_edges,
                                &arena.durable_rebuild_equalities[equalities.as_range()],
                            )
                            .unwrap_or_else(|error| {
                                panic!("cannot project container refresh: {error}")
                            }),
                        },
                    },
                    DurableCause::Merge { incoming, prior } => ReceiptCauseRecord::Merge {
                        incoming: incoming.public(),
                        prior: match prior {
                            DurablePrior::Fact(fact) => ReceiptCausePrior::Fact(*fact),
                            DurablePrior::Cause(cause) => ReceiptCausePrior::Cause(cause.public()),
                        },
                    },
                }
            })
            .collect();
        let mut check_roots = arena.check_roots.values().cloned().collect::<Vec<_>>();
        check_roots.sort_by_key(|root| root.check);
        let mut counters = arena.counters;
        counters.promoted_matches = cited_matches.len() as u64;
        counters.native_alias_unions = native_aliases.len() as u64;
        ReceiptSnapshot {
            facts,
            matches,
            equality_leaves,
            equality_nodes,
            equalities,
            native_aliases,
            rekeys,
            causes,
            check_roots,
            counters,
            equality_history_prefix: equality_history_prefix.into_boxed_slice(),
            equality_history_positions: arena
                .durable_equalities
                .iter()
                .map(|event| event.as_ref().expect("equality ID hole").position)
                .collect(),
            term_attachments: term_attachments.into_boxed_slice(),
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
        let recipes = self.0.rule_binding_recipes.read().unwrap();
        let term_recipes = self.0.static_term_recipes.lock().unwrap();
        let arena = self.0.arena.lock().unwrap();
        assert_eq!(
            arena.published_facts,
            self.0.next_fact.load(Ordering::Acquire),
            "finalize the causal wave before reading durable facts"
        );
        let fact = arena.facts.get((id.get() - 1) as usize)?.as_ref()?;
        let mut projector = TermProjector::new(
            &arena,
            &recipes,
            &term_recipes,
            &self.0.replay_terms,
            &self.0.next_term,
        );
        let durable_equalities = arena
            .durable_equalities
            .iter()
            .map(|event| {
                event
                    .clone()
                    .expect("fact lookup observed an equality ID hole")
            })
            .collect::<Vec<_>>();
        let (_, _, _, _, _, projected_equality_history, _) =
            build_cold_equality_forest(&mut projector, &durable_equalities)
                .unwrap_or_else(|error| panic!("cannot project equality history: {error}"));
        let cause = project_fact_cause(
            &mut projector,
            &arena,
            &projected_equality_history,
            fact.cause,
        )
        .unwrap_or_else(|error| panic!("cannot project fact cause: {error}"));
        let values: Box<[Value]> = arena.durable_fact_values[fact.values.as_range()].into();
        let layout = self
            .0
            .replay_terms
            .table_layout(fact.table)
            .expect("durable fact table has no replay layout");
        let terms = layout
            .iter()
            .enumerate()
            .map(|(column, sort)| {
                sort.map_or(ReplayTermId::MISSING, |_| {
                    projector
                        .fact_term(id, column)
                        .unwrap_or_else(|error| panic!("cannot project fact term: {error}"))
                })
            })
            .collect();
        Some(FactRecord {
            id,
            table: fact.table,
            position: fact.position,
            cause,
            values,
            terms,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cited_match_walk_rejects_a_dangling_rule_reference() {
        let mut arena = ReceiptArena::default();
        arena.facts.push(Some(DurableFact {
            table: TableId::new_const(1),
            position: HistoryPosition::new(1),
            cause: CauseRef::rule(RuleMatchId::new(999)),
            values: FlatRange::new(0, 0),
            origin: None,
        }));

        assert_eq!(
            arena.cited_matches().unwrap_err(),
            "cited dependency references missing observed match RuleMatchId(999)",
            "cold cited-match traversal must fail closed with the dangling id named"
        );
    }

    #[test]
    fn recipe_counters_distinguish_supported_and_missing_current_roots() {
        let receipts = CausalReceipts::default();
        let recipe = TermRecipe {
            current_roots: vec![Some(Arc::new(TermTemplate::Binding { binding: 0 })), None].into(),
        };
        receipts.register_rule_term_recipe(7, recipe.clone());
        receipts.register_rule_term_recipe(7, recipe);

        let counters = receipts.snapshot().counters;
        assert_eq!(counters.supported_current_recipe_roots, 1);
        assert_eq!(counters.missing_current_recipe_roots, 1);
    }

    #[test]
    fn receipt_batches_publish_out_of_order_without_holes() {
        let receipts = CausalReceipts::default();
        let mut lower = receipts.new_batch();
        let lower_id = lower
            .add_draft(
                CauseDraft::Source(SourceRef::Synthetic(1)),
                EqualityCauseSummary::Source,
            )
            .id();
        let mut higher = receipts.new_batch();
        let higher_id = higher
            .add_draft(
                CauseDraft::Source(SourceRef::Synthetic(2)),
                EqualityCauseSummary::Source,
            )
            .id();
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
        let origin = receipts.install_source_row(table, &row, &terms).unwrap();
        let source_cause = receipts.source_draft(SourceRef::Synthetic(0));
        let mut source_batch = receipts.new_batch();
        let source = source_batch.record_fact_with_origin(table, source_cause, &row, origin);
        source_batch.publish();
        receipts.finalize_wave();
        assert_eq!(receipts.fact_record(source).unwrap().terms.as_ref(), &terms);

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
        let [(lane, rule_cause)] = receipts
            .register_rule_matches(7, CausalWave::new(1), 1, &binding_sources, &[source], &[0])
            .try_into()
            .unwrap();
        assert_eq!(lane, 0);
        let mut derived_batch = receipts.new_batch();
        let derived = derived_batch.record_fact_with_origin(table, rule_cause, &row, origin);
        derived_batch.publish();
        receipts.finalize_wave();

        assert_eq!(
            receipts.fact_record(derived).unwrap().terms.as_ref(),
            &terms,
            "fact terms belong to the immutable committed row, not its Source cause"
        );

        let [(lane, next_cause)] = receipts
            .register_rule_matches(8, CausalWave::new(2), 1, &binding_sources, &[derived], &[0])
            .try_into()
            .unwrap();
        assert_eq!(lane, 0);
        let mut next_batch = receipts.new_batch();
        next_batch.record_fact_with_origin(table, next_cause, &row, origin);
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
    fn promoted_matches_reconstruct_current_terms_from_static_recipes() {
        let receipts = CausalReceipts::default();
        let table = TableId::new_const(0);
        let sort = ReplaySortId::new(1);
        receipts
            .register_table_layout(table, &[Some(sort)])
            .unwrap();

        let source_row = [Value::new_const(7)];
        let source_term = receipts.intern_literal(sort, ReplayLiteral::I64(7), source_row[0]);
        let source_origin = receipts
            .install_source_row(table, &source_row, &[source_term])
            .unwrap();
        let source_cause = receipts.source_draft(SourceRef::Synthetic(0));
        let mut source_batch = receipts.new_batch();
        let source_fact =
            source_batch.record_fact_with_origin(table, source_cause, &source_row, source_origin);
        source_batch.publish();
        receipts.finalize_wave();

        let constant_value = Value::new_const(8);
        let constant_term = receipts.intern_literal(sort, ReplayLiteral::I64(8), constant_value);
        let current_value = Value::new_const(9);
        let current_term = receipts.intern_literal(sort, ReplayLiteral::I64(9), current_value);
        let derived_row = [Value::new_const(10)];
        let derived_term = receipts.intern_literal(sort, ReplayLiteral::I64(10), derived_row[0]);
        let derived_origin = receipts
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
        receipts.register_rule_term_recipe(
            11,
            TermRecipe {
                current_roots: [Some(Arc::new(TermTemplate::Static { term: current_term }))].into(),
            },
        );
        let [(_, rule_cause)] = receipts
            .register_rule_matches(
                11,
                CausalWave::new(1),
                1,
                &binding_sources,
                &[source_fact],
                &[0],
            )
            .try_into()
            .unwrap();
        let mut derived_batch = receipts.new_batch();
        derived_batch.record_fact_with_origin(table, rule_cause, &derived_row, derived_origin);
        derived_batch.publish();
        receipts.finalize_wave();

        let snapshot = receipts.snapshot();
        assert_eq!(
            snapshot.matches[0].terms.as_ref(),
            &[source_term, constant_term, current_term],
            "lazy expansion must preserve the historical public MatchRecord layout"
        );
        assert_eq!(snapshot.counters.logical_match_term_handles, 3);
        assert_eq!(snapshot.counters.stored_match_term_handles, 0);
        assert_eq!(
            snapshot.counters.logical_match_term_bytes,
            3 * mem::size_of::<ReplayTermId>() as u64
        );
        assert_eq!(snapshot.counters.stored_match_term_bytes, 0);
        assert_eq!(snapshot.counters.term_handles, 3);
        assert_eq!(
            receipts.replay_term(derived_term),
            Some(ReplayTerm::Literal {
                sort,
                literal: ReplayLiteral::I64(10),
            })
        );
    }

    #[test]
    fn container_anchor_projects_only_referenced_bindings_and_memoizes_repeated_leaves() {
        let receipts = CausalReceipts::default();
        let table = TableId::new_const(0);
        let source_sort = ReplaySortId::new(10);
        let current_sort = ReplaySortId::new(11);
        let container_sort = ReplaySortId::new(12);
        let pure_op = ReplayOpId::new(10);
        let container_op = ReplayOpId::new(11);
        receipts
            .register_table_layout(table, &[Some(source_sort)])
            .unwrap();

        let used_value = Value::new_const(10);
        let unused_value = Value::new_const(11);
        let used_term = receipts.intern_literal(source_sort, ReplayLiteral::I64(10), used_value);
        let unused_term =
            receipts.intern_literal(source_sort, ReplayLiteral::I64(11), unused_value);
        let used_origin = receipts
            .install_source_row(table, &[used_value], &[used_term])
            .unwrap();
        let unused_origin = receipts
            .install_source_row(table, &[unused_value], &[unused_term])
            .unwrap();
        let cause = receipts.source_draft(SourceRef::Synthetic(10));
        let mut facts = receipts.new_batch();
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
        let site = receipts.register_term_origin(TermOriginSpec {
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
        let installed = receipts
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
        let ReplayTerm::Call { children, .. } = receipts.replay_term(installed).unwrap() else {
            panic!("container anchor did not produce a structural call")
        };
        assert_eq!(children.len(), 2);
        assert_eq!(
            children[0], children[1],
            "the repeated Current producer diverged"
        );
        assert_eq!(
            receipts.lookup_term(current_sort, current_value),
            Some(children[0]),
            "the exact nested Current producer was not installed for its runtime value"
        );
    }

    #[test]
    fn wave_finalization_visits_only_current_pending_facts() {
        let receipts = CausalReceipts::default();
        let table = TableId::new_const(0);
        let sort = ReplaySortId::new(20);
        receipts
            .register_table_layout(table, &[Some(sort)])
            .unwrap();
        let value = Value::new_const(20);
        let term = receipts.intern_literal(sort, ReplayLiteral::I64(20), value);
        let origin = receipts
            .install_source_row(table, &[value], &[term])
            .unwrap();

        let mut old = receipts.new_batch();
        let old_cause = receipts.source_draft(SourceRef::Synthetic(20));
        for _ in 0..100 {
            old.record_fact_with_origin(table, old_cause, &[value], origin);
        }
        old.publish();
        receipts.finalize_wave();

        let mut current = receipts.new_batch();
        let current_cause = receipts.source_draft(SourceRef::Synthetic(21));
        current.record_fact_with_origin(table, current_cause, &[value], origin);
        current.publish();
        reset_finalize_fact_slot_visits();
        receipts.finalize_wave();

        assert_eq!(
            finalize_fact_slot_visits(),
            0,
            "the direct-publication finalizer must not scan any fact slots"
        );
    }

    #[test]
    fn snapshot_rejects_an_unpublished_worker_fragment() {
        let receipts = CausalReceipts::default();
        let mut abandoned = receipts.new_batch();
        abandoned.add_draft(
            CauseDraft::Source(SourceRef::Synthetic(22)),
            EqualityCauseSummary::Source,
        );
        drop(abandoned);

        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| receipts.snapshot()));
        assert!(failed.is_err());
    }

    #[test]
    fn snapshot_rejects_a_dropped_redundant_only_fragment() {
        let receipts = CausalReceipts::default();
        let mut abandoned = receipts.new_batch();
        abandoned.record_redundant_union();
        drop(abandoned);

        let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| receipts.snapshot()));
        assert!(
            failed.is_err(),
            "dropping a diagnostics-only receipt fragment must fail closed"
        );
    }

    #[test]
    fn identical_rule_binding_recipe_registration_reuses_one_layout() {
        let receipts = CausalReceipts::default();
        let sort = ReplaySortId::new(1);
        let sources = [
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
            ReplayBindingSource::Current {
                variable: Variable::new(2),
                sort,
                residual: 0,
            },
        ];
        let first = receipts.register_rule_binding_recipe(12, &sources);
        let second = receipts.register_rule_binding_recipe(12, &sources);
        assert!(
            Arc::ptr_eq(&first, &second),
            "cached/decomposed variants must share one canonical recipe allocation"
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
        let low_origin = receipts
            .install_source_row(table, &low_row, &[low_term])
            .unwrap();
        let high_origin = receipts
            .install_source_row(table, &high_row, &[high_term])
            .unwrap();

        let low_cause = receipts.source_draft(SourceRef::Synthetic(10));
        let high_cause = receipts.source_draft(SourceRef::Synthetic(20));
        let mut low = receipts.new_batch();
        let low_fact = low.record_fact_with_origin(table, low_cause, &low_row, low_origin);
        let mut high = receipts.new_batch();
        let high_fact = high.record_fact_with_origin(table, high_cause, &high_row, high_origin);
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

    #[test]
    fn concurrent_replay_term_interning_deduplicates_identical_nodes() {
        let receipts = CausalReceipts::default();
        let sort = ReplaySortId::new(42);
        let value = Value::new_const(42);
        let terms = std::thread::scope(|scope| {
            (0..4)
                .map(|_| {
                    scope.spawn(|| receipts.intern_literal(sort, ReplayLiteral::I64(42), value))
                })
                .collect::<Vec<_>>()
                .into_iter()
                .map(|thread| thread.join().unwrap())
                .collect::<Vec<_>>()
        });

        assert!(terms.iter().all(|term| *term == terms[0]));
        assert_eq!(receipts.lookup_term(sort, value), Some(terms[0]));
        let counters = receipts.replay_term_counters();
        assert_eq!(counters.interned_nodes, 1);
        assert_eq!(counters.installed_values, 1);
    }
}
