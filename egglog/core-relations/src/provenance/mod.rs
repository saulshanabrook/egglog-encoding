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
        atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering},
    },
};

use dashmap::mapref::entry::Entry;
use smallvec::SmallVec;

use crate::{
    AtomId, QueryEntry, TableId, Value, Variable,
    common::{DashMap, HashMap, HashSet},
    numeric_id::{DenseIdMap, NumericId},
};

struct ActiveReceiptViewGuard<'a> {
    active: &'a AtomicBool,
}

impl<'a> ActiveReceiptViewGuard<'a> {
    fn enter(active: &'a AtomicBool) -> Result<Self, ReceiptViewError> {
        active
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .map(|_| Self { active })
            .map_err(|_| {
                ReceiptViewError::Invalid("causal receipt inspection is not reentrant".into())
            })
    }
}

impl Drop for ActiveReceiptViewGuard<'_> {
    fn drop(&mut self) {
        self.active.store(false, Ordering::Release);
    }
}

#[cfg(test)]
thread_local! {
    static TERM_PROJECTOR_FACT_EXPANSIONS: std::cell::Cell<usize> =
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
// Dense identity of one effective native union in raw receipt history,
// including same-syntax alias joins.
handle!(AppliedEqualityId, u64);
handle!(EqualityEdgeCount, u64);
handle!(CausalWave, u64);
handle!(HistoryPosition, u64);
handle!(RowOriginSiteId, u32);
handle!(TermOriginSiteId, u32);
handle!(CauseDraftId, u64);
handle!(ReceiptCauseId, u32);

/// Replay-observable keyed-table semantics.
///
/// Constructor and value-function removals can change a later grounded write
/// or lookup-or-insert. Presence relations have no merge-bearing cell, so
/// their removals are retained only as diagnostics.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReplayTableKind {
    PresenceRelation,
    Constructor,
    ValueFunction,
}

/// Stable index into the shared causal DAG.
/// A dependency can point directly at an observed rule match or at a shared
/// non-rule cause node. Keeping the tagged distinction public avoids
/// manufacturing one cause-arena node for every native match.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReceiptCauseRef {
    Rule(RuleMatchId),
    Cause(ReceiptCauseId),
}

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

    #[cfg(test)]
    fn into_public(self) -> ReceiptCauseRef {
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

#[cfg(test)]
impl From<CauseRef> for ReceiptCauseRef {
    fn from(value: CauseRef) -> Self {
        value.into_public()
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
    table_kinds: DashMap<TableId, ReplayTableKind>,
    table_key_columns: DashMap<TableId, u16>,
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

    fn register_table_kind(
        &self,
        table: TableId,
        kind: ReplayTableKind,
    ) -> Result<(), &'static str> {
        match self.table_kinds.entry(table) {
            Entry::Occupied(entry) if *entry.get() == kind => Ok(()),
            Entry::Occupied(_) => Err("table already has a different replay-table kind"),
            Entry::Vacant(entry) => {
                entry.insert(kind);
                Ok(())
            }
        }
    }

    fn register_table_key_columns(
        &self,
        table: TableId,
        key_columns: usize,
    ) -> Result<(), &'static str> {
        let key_columns = key_columns
            .try_into()
            .map_err(|_| "table key arity exceeds u16")?;
        match self.table_key_columns.entry(table) {
            Entry::Occupied(entry) if *entry.get() == key_columns => Ok(()),
            Entry::Occupied(_) => Err("table already has a different key arity"),
            Entry::Vacant(entry) => {
                entry.insert(key_columns);
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReplayEqualitySource {
    Premise(PremiseOccurrence),
    Constant(EqualityEndpoint),
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
    /// Read the exact value column of an earlier zero-key source/global fact.
    /// This is resolved against immutable receipt history, never final state.
    FactLookup {
        table: TableId,
        column: u16,
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
        atom: AtomId,
        input_columns: usize,
        op: ReplayOpId,
        origin: Option<TermOriginSiteId>,
    },
    Constant {
        term: ReplayTermId,
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
pub(crate) struct RekeyRecord {
    pub(crate) fact: FactId,
    pub(crate) table: TableId,
    pub(crate) wave: CausalWave,
    pub(crate) position: HistoryPosition,
    pub(crate) equalities: EqualityLandmark,
    pub(crate) outcome: RekeyOutcome,
}

/// Exact positional child changes produced by one serial container rebuild.
///
/// The container's structural replay term remains immutable. Re-executing the
/// child equalities makes that same term denote the rebuilt native container.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContainerDependency {
    pub(crate) wave: CausalWave,
    pub(crate) equalities: EqualityLandmark,
}

/// Receipt-only logical identity for one container version. Borrowed views
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
pub enum EqualityReason {
    RuleUnion(RuleMatchId),
    SourceUnion {
        cause: ReceiptCauseId,
    },
    MergeFn {
        /// Shared exact cause root. Dependencies are unfolded lazily through
        /// [`CausalReceiptView::cause`].
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
            EqualityReason::SourceUnion { .. } => None,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EqualityEndpoint {
    pub sort: ReplaySortId,
    pub term: ReplayTermId,
    pub raw: crate::Value,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckEndpointOccurrence {
    FactCell(FactCellRef),
    Current,
}

/// Exact native support retained for the first successful match of one check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckRoot {
    pub check: u32,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub premises: Box<[FactId]>,
    pub equalities: Box<[(EqualityEndpoint, EqualityEndpoint)]>,
    pub equality_occurrences: Box<[(CheckEndpointOccurrence, CheckEndpointOccurrence)]>,
    pub as_of_edges: EqualityEdgeCount,
}

/// One effective replay-observable keyed-row removal.
///
/// The immutable victim fact retains the historical table/key row, so the
/// event needs no copied key payload. `cause` is the exact rule lane whose
/// head staged the removal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RemovalRecord {
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub as_of_edges: EqualityEdgeCount,
    pub removed_fact: FactId,
    pub cause: RuleMatchId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypedCellEquality {
    pub column: crate::ColumnId,
    pub left: EqualityEndpoint,
    pub right: EqualityEndpoint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EqualityLandmark {
    /// Dense applied-edge prefix visible at this exact global history point.
    pub(crate) as_of_edges: EqualityEdgeCount,
    /// Cross-stream cutoff for zero-edge fact/rekey/alias attachments.
    pub(crate) position: HistoryPosition,
    pub(crate) pairs: Box<[TypedCellEquality]>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReceiptCounters {
    /// Every normal-return native rule lane, including inert observations.
    pub observed_matches: u64,
    pub premise_handles: u64,
    /// Logical match-term handles exposed by [`CausalReceiptView::match_terms`].
    pub logical_match_term_handles: u64,
    /// Match-term handles physically retained by the receipt arena.
    pub stored_match_term_handles: u64,
    /// Logical bytes exposed by [`CausalReceiptView::match_terms`].
    pub logical_match_term_bytes: u64,
    /// Match-term bytes physically retained by the receipt arena.
    pub stored_match_term_bytes: u64,
    pub unattributed_commits: u64,
    pub redundant_unions: u64,
    /// Effective constructor/value-function removals retained for slicing.
    pub effective_removals: u64,
    /// Effective presence-relation removals observed but not retained.
    pub relation_removals: u64,
    /// Semantic rows for which an exact rebuild cause was captured.
    pub rebuild_causes: u64,
    /// Changed typed cells stored across those rebuild causes.
    pub rebuild_equalities: u64,
    /// Logical bytes of rebuild cause and changed-cell payload captured.
    pub rebuild_bytes: u64,
    /// `Current` binding slots with a complete replay-safe structural recipe.
    pub supported_current_recipe_roots: u64,
    /// `Current` binding slots whose structural producer remains unsupported.
    /// Reached slots fail closed during slicing; this counter makes cohort
    /// coverage visible before replay is wired.
    pub missing_current_recipe_roots: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CausalReceiptTotals {
    pub facts: u64,
    pub matches: u64,
    pub causes: u64,
    pub applied_equalities: u64,
    pub rekeys: u64,
    pub removals: u64,
    pub check_roots: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplayTableSchema {
    pub table: TableId,
    pub kind: ReplayTableKind,
    pub key_columns: usize,
    pub columns: Arc<[Option<ReplaySortId>]>,
    pub constructor: Option<ReplayConstructorSpec>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FactCellRef {
    pub fact: FactId,
    pub column: crate::ColumnId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HistoricalFactCell {
    pub occurrence: FactCellRef,
    pub created: EqualityEndpoint,
    pub endpoint: EqualityEndpoint,
    pub rekeys: Box<[HistoryPosition]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawEqualitySupport {
    pub applied: Box<[AppliedEqualityId]>,
    pub facts: Box<[FactId]>,
    pub causes: Box<[ReceiptCauseRef]>,
    pub rekeys: Box<[HistoryPosition]>,
}

/// The exact support and capture lower bounds for one structural checked
/// alias. Once established, the persistent alias lets a later grounded firing
/// reuse an e-class value after its constructor row has been deleted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawTermAvailability {
    pub support: RawEqualitySupport,
    pub aliases: Box<[RawAliasWindow]>,
}

/// Earliest native point after which one structural Call occurrence can be
/// captured by a persistent checked alias. Entries are emitted child-first in
/// structural occurrence order; equal `term` ids may therefore appear more
/// than once with different lower bounds. Bounds belong only to the exact
/// constructor row that names this occurrence; causal support facts are not
/// alias liveness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawAliasWindow {
    pub term: ReplayTermId,
    pub available_after: HistoryPosition,
    /// A refreshed ordered-container spelling and its structural descendants
    /// cannot canonicalize back to aliases from an earlier container version.
    pub fresh_after: Option<HistoryPosition>,
}

fn combine_raw_equality_support(
    parts: impl IntoIterator<Item = RawEqualitySupport>,
) -> RawEqualitySupport {
    let mut applied = Vec::new();
    let mut facts = Vec::new();
    let mut causes = Vec::new();
    let mut rekeys = Vec::new();
    for part in parts {
        applied.extend(part.applied);
        facts.extend(part.facts);
        causes.extend(part.causes);
        rekeys.extend(part.rekeys);
    }
    applied.sort_unstable();
    applied.dedup();
    facts.sort_unstable();
    facts.dedup();
    causes.sort_unstable();
    causes.dedup();
    rekeys.sort_unstable();
    rekeys.dedup();
    RawEqualitySupport {
        applied: applied.into_boxed_slice(),
        facts: facts.into_boxed_slice(),
        causes: causes.into_boxed_slice(),
        rekeys: rekeys.into_boxed_slice(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReceiptPremiseOccurrence {
    pub premise: usize,
    pub column: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiptBindingSource {
    Premise {
        representative: ReceiptPremiseOccurrence,
        occurrences: Box<[ReceiptPremiseOccurrence]>,
    },
    Current {
        sort: ReplaySortId,
        residual: u32,
        replay_safe: bool,
    },
    Constant {
        term: ReplayTermId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReceiptEqualitySource {
    Premise(ReceiptPremiseOccurrence),
    Constant(EqualityEndpoint),
}

#[derive(Clone, Copy, Debug)]
pub struct RawFactRecord<'a> {
    pub id: FactId,
    pub table: TableId,
    pub position: HistoryPosition,
    pub cause: ReceiptCauseRef,
    pub values: &'a [Value],
}

#[derive(Clone, Copy, Debug)]
pub struct RawMatchRecord<'a> {
    pub id: RuleMatchId,
    pub rule: u32,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub as_of_edges: EqualityEdgeCount,
    pub premises: &'a [FactId],
    pub merge_reads: &'a [FactId],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawReceiptCause<'a> {
    Source(&'a SourceRef),
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
    Merge {
        incoming: ReceiptCauseRef,
        prior: ReceiptCausePrior,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawEqualityEndpoint {
    pub sort: ReplaySortId,
    pub raw: Value,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawAppliedEquality {
    pub id: AppliedEqualityId,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub left: RawEqualityEndpoint,
    pub right: RawEqualityEndpoint,
    pub native_parent: Value,
    pub native_child: Value,
    pub reason: EqualityReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectedAppliedEquality {
    pub id: AppliedEqualityId,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub left: EqualityEndpoint,
    pub right: EqualityEndpoint,
    pub native_parent: Value,
    pub native_child: Value,
    pub reason: EqualityReason,
}

#[derive(Clone, Copy, Debug)]
pub struct RawRekeyRecord<'a> {
    pub fact: FactId,
    pub table: TableId,
    pub wave: CausalWave,
    pub position: HistoryPosition,
    pub as_of_edges: EqualityEdgeCount,
    pub equality_position: HistoryPosition,
    pub equalities: &'a [TypedCellEquality],
    pub outcome: RekeyOutcome,
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ReceiptViewError {
    #[error("causal receipt history is not finalized: {0}")]
    NotFinalized(&'static str),
    #[error("causal receipt lock is poisoned: {0}")]
    Poisoned(&'static str),
    #[error("unknown causal fact {0:?}")]
    UnknownFact(FactId),
    #[error("unknown causal match {0:?}")]
    UnknownMatch(RuleMatchId),
    #[error("unknown causal cause {0:?}")]
    UnknownCause(ReceiptCauseId),
    #[error("unknown applied equality {0:?}")]
    UnknownEquality(AppliedEqualityId),
    #[error("unknown causal rekey at {0:?}")]
    UnknownRekey(HistoryPosition),
    #[error("unknown causal removal {0}")]
    UnknownRemoval(usize),
    #[error("unknown successful check {0}")]
    UnknownCheck(u32),
    #[error("unknown replay table {0:?}")]
    UnknownTable(TableId),
    #[error("invalid causal receipt history: {0}")]
    Invalid(String),
    #[error(
        "causal fact {fact:?} ended at {ended_at:?} with successor {successor:?}; it is not live at {position:?}"
    )]
    FactNoLongerLive {
        fact: FactId,
        position: HistoryPosition,
        ended_at: HistoryPosition,
        successor: Option<FactId>,
    },
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

    fn originating_rule(&self) -> Option<RuleMatchId> {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => cause.rule_match(),
            DeferredEqualityCauseKind::Pending(cause) => Some(cause.matched),
            DeferredEqualityCauseKind::Merge(cause) => cause.incoming.originating_rule(),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreparedRemoval {
    Tracked {
        removed_fact: FactId,
        cause: RuleMatchId,
    },
    PresenceRelation,
}

#[derive(Clone, Debug)]
enum CauseDraft {
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
    position: HistoryPosition,
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    cause: CauseRef,
}

struct DurableEquality {
    position: HistoryPosition,
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    cause: CauseRef,
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
    durable_causes: Vec<Option<(DurableCause, EqualityCauseSummary)>>,
    durable_equalities: Vec<Option<DurableEquality>>,
    rekeys: Vec<RekeyRecord>,
    removals: Vec<RemovalRecord>,
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

    fn record_match_term_storage(&mut self, logical: usize, stored: usize) {
        let logical = logical as u64;
        let stored = stored as u64;
        let handle_bytes = mem::size_of::<ReplayTermId>() as u64;
        self.counters.logical_match_term_handles += logical;
        self.counters.stored_match_term_handles += stored;
        self.counters.logical_match_term_bytes += logical * handle_bytes;
        self.counters.stored_match_term_bytes += stored * handle_bytes;
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

    fn equality_reason(&self, root: CauseRef) -> EqualityReason {
        let summary = if root.rule_match().is_some() {
            EqualityCauseSummary::Rule
        } else {
            self.cause_summary(root.cause_node().expect("equality cause is unattributed"))
                .expect("applied equality cause has no classification")
        };
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

/// Lazy receipt-view projector. Native capture stores raw creation rows and
/// compact static origin sites; selected reads expand only the requested
/// references into the historical replay-term DAG.
#[derive(Clone)]
enum TemplateOwner {
    Durable(RuleMatchId),
    Fact(FactId),
    History {
        position: HistoryPosition,
        inclusive: bool,
    },
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
                .map(TemplateOwner::Durable)
                .unwrap_or(TemplateOwner::Fact(fact_id));
            let merge_cells = match fact.origin {
                Some(FactOrigin::Merge { cells, .. }) => {
                    Some(self.arena.durable_merge_cell_origins[cells.as_range()].to_vec())
                }
                _ => None,
            };
            let (table, origin) = (fact.table, fact.origin);
            match origin {
                Some(FactOrigin::Site(site)) => self.site_term(site, table, column, Some(&owner)),
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
                            this.site_term(site, table, column, Some(&owner))
                        }
                        Some(RowOriginRef::Fact(source)) => this.fact_term(source, column),
                        None => Err(format!(
                            "reached unattributed incoming syntax for {fact_id:?} column {column}"
                        )),
                    };
                    match cell {
                        MergeCellOrigin::Incoming(source) => match incoming {
                            Some(RowOriginRef::Site(site)) => {
                                self.site_term(site, table, source as usize, Some(&owner))
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
                TemplateOwner::Fact(fact) => Err(format!(
                    "source fact {fact:?} unexpectedly references binding {binding}"
                )),
                TemplateOwner::History { .. } => Err(format!(
                    "historical term origin unexpectedly references binding {binding}"
                )),
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
                    TemplateOwner::Fact(fact) => {
                        return Err(format!(
                            "source fact {fact:?} unexpectedly references premise {premise} column {column}"
                        ));
                    }
                    TemplateOwner::History { .. } => {
                        return Err(format!(
                            "historical term origin unexpectedly references premise {premise} column {column}"
                        ));
                    }
                };
                self.fact_term(fact, *column as usize)
            }
            TermTemplate::Static { term } => Ok(*term),
            TermTemplate::FactLookup { table, column } => {
                let (position, inclusive) = match owner
                    .ok_or_else(|| format!("historical lookup of {table:?} has no owning event"))?
                {
                    TemplateOwner::Durable(match_id) => (
                        self.arena
                            .durable_matches
                            .get(
                                (match_id.get().checked_sub(1).ok_or("missing RuleMatchId")?)
                                    as usize,
                            )
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown causal match {match_id:?}"))?
                            .position,
                        true,
                    ),
                    TemplateOwner::Fact(fact) => (
                        self.arena
                            .facts
                            .get((fact.get().checked_sub(1).ok_or("missing FactId")?) as usize)
                            .and_then(Option::as_ref)
                            .ok_or_else(|| format!("unknown causal fact {fact:?}"))?
                            .position,
                        false,
                    ),
                    TemplateOwner::History {
                        position,
                        inclusive,
                    } => (*position, *inclusive),
                };
                let (fact, _) = self
                    .arena
                    .facts
                    .iter()
                    .enumerate()
                    .filter_map(|(index, slot)| {
                        let candidate = slot.as_ref()?;
                        let visible = if inclusive {
                            candidate.position <= position
                        } else {
                            candidate.position < position
                        };
                        (candidate.table == *table && visible)
                            .then_some((FactId::new(index as u64 + 1), candidate.position))
                    })
                    .filter(|(fact, _)| {
                        !self.arena.removals.iter().any(|removal| {
                            removal.removed_fact == *fact && removal.position <= position
                        }) && !self.arena.rekeys.iter().any(|rekey| {
                            rekey.fact == *fact
                                && rekey.position <= position
                                && rekey.outcome != RekeyOutcome::Moved
                        })
                    })
                    .max_by_key(|(_, fact_position)| *fact_position)
                    .ok_or_else(|| {
                        format!(
                            "zero-key historical lookup of {table:?} has no live fact at {position:?}"
                        )
                    })?;
                self.fact_term(fact, *column as usize)
            }
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
            TermTemplate::FactLookup { table, .. } => Err(format!(
                "container runtime anchor unexpectedly references zero-key table {table:?}"
            )),
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
        position: HistoryPosition,
    ) -> Result<EqualityEndpoint, String> {
        let term = match endpoint.term {
            EqualityTermRef::Exact(term) => term,
            EqualityTermRef::Site(site) => {
                let owner = self
                    .arena
                    .originating_rule(cause)
                    .map(TemplateOwner::Durable)
                    .unwrap_or(TemplateOwner::History {
                        position,
                        inclusive: true,
                    });
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
                self.template(&spec.term, Some(&owner))?
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
                    values.get(column as usize).ok_or_else(|| {
                        format!("equality endpoint fact {fact:?} has no column {column}")
                    })?;
                    self.fact_term(fact, column as usize)?
                }
                RowOriginRef::Site(site) => {
                    let owner = self
                        .arena
                        .originating_rule(cause)
                        .map(TemplateOwner::Durable)
                        .unwrap_or(TemplateOwner::History {
                            position,
                            inclusive: true,
                        });
                    self.site_term(site, table, column as usize, Some(&owner))?
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
        Ok(EqualityEndpoint {
            sort: endpoint.sort,
            term,
            raw: endpoint.raw,
        })
    }
}

/// Borrowed, non-escaping view of one finalized raw receipt arena.
///
/// Accessors project structural terms only for explicitly selected facts,
/// matches, or equality events.
pub struct CausalReceiptView<'a> {
    arena: &'a ReceiptArena,
    binding_recipes: &'a HashMap<u32, Arc<[ReplayBindingSource]>>,
    equality_recipes: &'a HashMap<u32, Arc<[(ReplayEqualitySource, ReplayEqualitySource)]>>,
    term_recipes: &'a StaticTermRecipeStore,
    replay_terms: &'a ReplayTermStore,
    projector: TermProjector<'a>,
    history_boundary: HistoryPosition,
    equality_index: Option<RawEqualityIndex>,
    rekey_index: Option<RekeyIndex>,
    constructor_occurrence_index: Option<ConstructorOccurrenceIndex>,
    occurrence_support_cache: HashMap<StructuralOccurrenceQuery, Option<RawEqualitySupport>>,
    exact_occurrence_support_cache: HashMap<StructuralOccurrenceQuery, Option<RawEqualitySupport>>,
    counters: CausalReceiptViewCounters,
}

struct RawEqualityIndex {
    parents: HashMap<(ReplaySortId, Value), (Value, AppliedEqualityId)>,
}

struct RekeyIndex {
    by_fact: HashMap<FactId, Arc<[usize]>>,
    by_position: HashMap<HistoryPosition, usize>,
}

struct ConstructorOccurrenceIndex {
    facts: HashMap<(ReplaySortId, ReplayOpId), Arc<[FactId]>>,
    registered: HashSet<(ReplaySortId, ReplayOpId)>,
    /// Non-table calls that were emitted by a frontend-certified static term
    /// recipe. Only these calls may be recomputed by `let-check` without a
    /// constructor FactId. Building this set is deliberately cold: receipt
    /// capture never walks term recipes.
    certified_calls: HashSet<(ReplaySortId, ReplayOpId)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct StructuralOccurrenceQuery {
    term: ReplayTermId,
    sort: ReplaySortId,
    raw: Value,
    position: HistoryPosition,
    excluded_fact: FactId,
}

#[derive(Clone, Copy)]
struct StructuralAvailabilityContext<'a> {
    desired: Option<RawEqualityEndpoint>,
    anchor: Option<&'a HistoricalFactCell>,
    fresh_after: Option<HistoryPosition>,
}

enum ObservedEqualitySupport {
    Support(RawEqualitySupport),
    Missing(ReplayTermId),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CausalReceiptViewCounters {
    pub equality_index_builds: u64,
    pub equality_events_indexed: u64,
    pub equality_positions_validated: u64,
    pub equality_explanation_queries: u64,
    pub equality_parent_steps: u64,
    pub equality_occurrence_facts_scanned: u64,
    pub equality_occurrence_terms_projected: u64,
    pub rekey_lookups: u64,
    pub rekey_records_scanned: u64,
}

impl<'a> CausalReceiptView<'a> {
    fn collect_certified_replay_term_calls(
        &self,
        term: ReplayTermId,
        calls: &mut HashSet<(ReplaySortId, ReplayOpId)>,
        visited: &mut HashSet<ReplayTermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        let Some(node) = self.replay_terms.node(term) else {
            // A malformed static reference certifies nothing. If it is ever
            // reached, ordinary term projection reports the unknown id; an
            // unrelated malformed recipe remains lazy and harmless.
            return;
        };
        let ReplayTerm::Call { sort, op, children } = node else {
            return;
        };
        calls.insert((sort, op));
        for child in children.iter().copied() {
            self.collect_certified_replay_term_calls(child, calls, visited);
        }
    }

    fn collect_certified_template_calls(
        &self,
        template: &TermTemplate,
        calls: &mut HashSet<(ReplaySortId, ReplayOpId)>,
        visited_terms: &mut HashSet<ReplayTermId>,
    ) {
        match template {
            TermTemplate::Binding { .. }
            | TermTemplate::PremiseCell { .. }
            | TermTemplate::FactLookup { .. } => {}
            TermTemplate::Static { term } => {
                self.collect_certified_replay_term_calls(*term, calls, visited_terms);
            }
            TermTemplate::Call { sort, op, children } => {
                calls.insert((*sort, *op));
                for child in children.iter() {
                    self.collect_certified_template_calls(child, calls, visited_terms);
                }
            }
        }
    }

    fn public_cause(cause: CauseRef) -> Result<ReceiptCauseRef, ReceiptViewError> {
        if cause.is_unattributed() {
            return Err(ReceiptViewError::Invalid(
                "durable event has an unattributed cause".into(),
            ));
        }
        if let Some(rule) = cause.rule_match() {
            return Ok(ReceiptCauseRef::Rule(rule));
        }
        let draft = cause.cause_node().ok_or_else(|| {
            ReceiptViewError::Invalid("durable event has no cause identity".into())
        })?;
        let id = u32::try_from(draft.get())
            .map_err(|_| ReceiptViewError::Invalid("receipt cause identity exceeds u32".into()))?;
        Ok(ReceiptCauseRef::Cause(ReceiptCauseId::new(id)))
    }

    pub fn totals(&self) -> CausalReceiptTotals {
        CausalReceiptTotals {
            facts: self.arena.published_facts,
            matches: self.arena.published_matches,
            causes: self.arena.published_causes,
            applied_equalities: self.arena.published_equalities,
            rekeys: self.arena.rekeys.len() as u64,
            removals: self.arena.removals.len() as u64,
            check_roots: self.arena.check_roots.len() as u64,
        }
    }

    pub fn view_counters(&self) -> CausalReceiptViewCounters {
        self.counters
    }

    pub fn counters(&self) -> ReceiptCounters {
        self.arena.counters
    }

    pub fn fact(&self, id: FactId) -> Result<RawFactRecord<'a>, ReceiptViewError> {
        if id.is_missing() {
            return Err(ReceiptViewError::UnknownFact(id));
        }
        let fact = self
            .arena
            .facts
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownFact(id))?;
        Ok(RawFactRecord {
            id,
            table: fact.table,
            position: fact.position,
            cause: Self::public_cause(fact.cause)?,
            values: &self.arena.durable_fact_values[fact.values.as_range()],
        })
    }

    fn rekey_index(&mut self) -> &RekeyIndex {
        if self.rekey_index.is_none() {
            let mut by_fact = HashMap::<FactId, Vec<usize>>::default();
            let mut by_position = HashMap::default();
            for (index, rekey) in self.arena.rekeys.iter().enumerate() {
                by_fact.entry(rekey.fact).or_default().push(index);
                assert!(
                    by_position.insert(rekey.position, index).is_none(),
                    "two logical rekeys share one history position"
                );
            }
            self.rekey_index = Some(RekeyIndex {
                by_fact: by_fact
                    .into_iter()
                    .map(|(fact, indexes)| (fact, Arc::from(indexes)))
                    .collect(),
                by_position,
            });
        }
        self.rekey_index.as_ref().unwrap()
    }

    pub fn matched(&self, id: RuleMatchId) -> Result<RawMatchRecord<'a>, ReceiptViewError> {
        if id.get() == 0 {
            return Err(ReceiptViewError::UnknownMatch(id));
        }
        let matched = self
            .arena
            .durable_matches
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownMatch(id))?;
        let merge_reads = self
            .arena
            .merge_reads
            .get(&id)
            .map_or(&[][..], SmallVec::as_slice);
        Ok(RawMatchRecord {
            id,
            rule: matched.rule,
            wave: matched.wave,
            position: matched.position,
            as_of_edges: matched.as_of_edges,
            premises: &self.arena.durable_premises[matched.premises.as_range()],
            merge_reads,
        })
    }

    pub fn cause(&self, id: ReceiptCauseId) -> Result<RawReceiptCause<'a>, ReceiptViewError> {
        if id.get() == 0 {
            return Err(ReceiptViewError::UnknownCause(id));
        }
        let cause = self
            .arena
            .durable_cause(CauseDraftId::new(id.get() as u64))
            .ok_or(ReceiptViewError::UnknownCause(id))?;
        Ok(match cause {
            DurableCause::Source(source) => RawReceiptCause::Source(source),
            DurableCause::Rebuild {
                wave,
                prior_fact,
                as_of_edges,
                position,
                equalities,
            } => RawReceiptCause::Rebuild {
                wave: *wave,
                prior_fact: *prior_fact,
                as_of_edges: *as_of_edges,
                position: *position,
                equalities: &self.arena.durable_rebuild_equalities[equalities.as_range()],
            },
            DurableCause::ContainerCanonicalize {
                wave,
                as_of_edges,
                position,
                equalities,
            } => RawReceiptCause::ContainerCanonicalize {
                wave: *wave,
                as_of_edges: *as_of_edges,
                position: *position,
                equalities: &self.arena.durable_rebuild_equalities[equalities.as_range()],
            },
            DurableCause::ContainerRefresh {
                wave,
                prior_fact,
                as_of_edges,
                position,
                equalities,
            } => RawReceiptCause::ContainerRefresh {
                wave: *wave,
                prior_fact: *prior_fact,
                as_of_edges: *as_of_edges,
                position: *position,
                equalities: &self.arena.durable_rebuild_equalities[equalities.as_range()],
            },
            DurableCause::Merge { incoming, prior } => RawReceiptCause::Merge {
                incoming: Self::public_cause(*incoming)?,
                prior: match prior {
                    DurablePrior::Fact(fact) => ReceiptCausePrior::Fact(*fact),
                    DurablePrior::Cause(cause) => {
                        ReceiptCausePrior::Cause(Self::public_cause(*cause)?)
                    }
                },
            },
        })
    }

    pub fn applied_equality(
        &self,
        id: AppliedEqualityId,
    ) -> Result<RawAppliedEquality, ReceiptViewError> {
        if id.get() == 0 {
            return Err(ReceiptViewError::UnknownEquality(id));
        }
        let event = self
            .arena
            .durable_equalities
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownEquality(id))?;
        Ok(RawAppliedEquality {
            id,
            wave: event.proposal.wave,
            position: event.position,
            left: RawEqualityEndpoint {
                sort: event.proposal.left.sort,
                raw: event.proposal.left.raw,
            },
            right: RawEqualityEndpoint {
                sort: event.proposal.right.sort,
                raw: event.proposal.right.raw,
            },
            native_parent: event.native_parent,
            native_child: event.native_child,
            reason: self.arena.equality_reason(event.cause),
        })
    }

    pub fn project_applied_equality(
        &mut self,
        id: AppliedEqualityId,
    ) -> Result<ProjectedAppliedEquality, ReceiptViewError> {
        if id.get() == 0 {
            return Err(ReceiptViewError::UnknownEquality(id));
        }
        let event = self
            .arena
            .durable_equalities
            .get((id.get() - 1) as usize)
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownEquality(id))?;
        let left = self
            .projector
            .equality_endpoint(event.proposal.left, event.cause, event.position)
            .map_err(ReceiptViewError::Invalid)?;
        let right = self
            .projector
            .equality_endpoint(event.proposal.right, event.cause, event.position)
            .map_err(ReceiptViewError::Invalid)?;
        Ok(ProjectedAppliedEquality {
            id,
            wave: event.proposal.wave,
            position: event.position,
            left,
            right,
            native_parent: event.native_parent,
            native_child: event.native_child,
            reason: self.arena.equality_reason(event.cause),
        })
    }

    pub fn rekey_at(
        &mut self,
        position: HistoryPosition,
    ) -> Result<RawRekeyRecord<'a>, ReceiptViewError> {
        self.counters.rekey_lookups += 1;
        let index = self
            .rekey_index()
            .by_position
            .get(&position)
            .copied()
            .ok_or(ReceiptViewError::UnknownRekey(position))?;
        self.counters.rekey_records_scanned += 1;
        let record = &self.arena.rekeys[index];
        Ok(RawRekeyRecord {
            fact: record.fact,
            table: record.table,
            wave: record.wave,
            position: record.position,
            as_of_edges: record.equalities.as_of_edges,
            equality_position: record.equalities.position,
            equalities: &record.equalities.pairs,
            outcome: record.outcome,
        })
    }

    pub fn removal(&self, index: usize) -> Result<&'a RemovalRecord, ReceiptViewError> {
        self.arena
            .removals
            .get(index)
            .ok_or(ReceiptViewError::UnknownRemoval(index))
    }

    pub fn check_root(&self, check: u32) -> Result<&'a CheckRoot, ReceiptViewError> {
        self.arena
            .check_roots
            .get(&check)
            .ok_or(ReceiptViewError::UnknownCheck(check))
    }

    pub fn check_roots(&self) -> Vec<&'a CheckRoot> {
        let mut roots = self.arena.check_roots.values().collect::<Vec<_>>();
        roots.sort_unstable_by_key(|root| root.check);
        roots
    }

    pub fn table_schema(&self, table: TableId) -> Result<ReplayTableSchema, ReceiptViewError> {
        let columns = self
            .replay_terms
            .table_layout(table)
            .ok_or(ReceiptViewError::UnknownTable(table))?;
        let kind = self
            .replay_terms
            .table_kinds
            .get(&table)
            .map(|kind| *kind)
            .ok_or(ReceiptViewError::UnknownTable(table))?;
        let key_columns = self
            .replay_terms
            .table_key_columns
            .get(&table)
            .map(|columns| *columns as usize)
            .ok_or(ReceiptViewError::UnknownTable(table))?;
        let constructor = self
            .replay_terms
            .table_constructors
            .get(&table)
            .map(|constructor| constructor.clone());
        Ok(ReplayTableSchema {
            table,
            kind,
            key_columns,
            columns,
            constructor,
        })
    }

    pub fn rule_binding_layout(
        &self,
        rule: u32,
    ) -> Result<Box<[ReceiptBindingSource]>, ReceiptViewError> {
        let bindings = self.binding_recipes.get(&rule).ok_or_else(|| {
            ReceiptViewError::Invalid(format!("rule {rule} has no binding recipe"))
        })?;
        let current_roots = self
            .term_recipes
            .rules
            .get(&rule)
            .map(|recipe| recipe.current_roots.as_ref())
            .unwrap_or(&[]);
        bindings
            .iter()
            .map(|binding| {
                Ok(match binding {
                    ReplayBindingSource::Premise {
                        representative,
                        occurrences,
                    } => ReceiptBindingSource::Premise {
                        representative: ReceiptPremiseOccurrence {
                            premise: representative.premise,
                            column: representative.column,
                        },
                        occurrences: occurrences
                            .iter()
                            .map(|occurrence| ReceiptPremiseOccurrence {
                                premise: occurrence.premise,
                                column: occurrence.column,
                            })
                            .collect(),
                    },
                    ReplayBindingSource::Current { sort, residual, .. } => {
                        ReceiptBindingSource::Current {
                            sort: *sort,
                            residual: *residual,
                            replay_safe: current_roots
                                .get(*residual as usize)
                                .is_some_and(Option::is_some),
                        }
                    }
                    ReplayBindingSource::Constant { term } => {
                        ReceiptBindingSource::Constant { term: *term }
                    }
                })
            })
            .collect::<Result<Vec<_>, ReceiptViewError>>()
            .map(Vec::into_boxed_slice)
    }

    pub fn rule_equality_layout(
        &self,
        rule: u32,
    ) -> Result<Box<[(ReceiptEqualitySource, ReceiptEqualitySource)]>, ReceiptViewError> {
        let equalities = self.equality_recipes.get(&rule).ok_or_else(|| {
            ReceiptViewError::Invalid(format!("rule {rule} has no equality-obligation recipe"))
        })?;
        Ok(equalities
            .iter()
            .map(|&(left, right)| {
                let public = |source| match source {
                    ReplayEqualitySource::Premise(occurrence) => {
                        ReceiptEqualitySource::Premise(ReceiptPremiseOccurrence {
                            premise: occurrence.premise,
                            column: occurrence.column,
                        })
                    }
                    ReplayEqualitySource::Constant(endpoint) => {
                        ReceiptEqualitySource::Constant(endpoint)
                    }
                };
                (public(left), public(right))
            })
            .collect::<Vec<_>>()
            .into_boxed_slice())
    }

    pub fn fact_terms(&mut self, id: FactId) -> Result<Box<[ReplayTermId]>, ReceiptViewError> {
        let fact = self.fact(id)?;
        let layout = self
            .replay_terms
            .table_layout(fact.table)
            .ok_or(ReceiptViewError::UnknownTable(fact.table))?;
        layout
            .iter()
            .enumerate()
            .map(|(column, sort)| {
                sort.map_or(Ok(ReplayTermId::MISSING), |_| {
                    self.projector
                        .fact_term(id, column)
                        .map_err(ReceiptViewError::Invalid)
                })
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Vec::into_boxed_slice)
    }

    pub fn match_terms(
        &mut self,
        id: RuleMatchId,
    ) -> Result<Box<[ReplayTermId]>, ReceiptViewError> {
        let matched = self.matched(id)?;
        let binding_count = self
            .binding_recipes
            .get(&matched.rule)
            .ok_or_else(|| {
                ReceiptViewError::Invalid(format!("rule {} has no binding recipe", matched.rule))
            })?
            .len();
        (0..binding_count)
            .map(|binding| {
                self.projector
                    .match_term(id, binding)
                    .map_err(ReceiptViewError::Invalid)
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Vec::into_boxed_slice)
    }

    /// Prove that one complete grounded binding can be named by `let-check`
    /// at the match's historical position. Unlike equality explanation this
    /// asks only for structural availability: pure calls and ordered
    /// containers are recomputed from their children, while every table
    /// constructor must have one exact live producer row.
    pub fn explain_match_term_availability(
        &mut self,
        id: RuleMatchId,
        binding: usize,
    ) -> Result<RawTermAvailability, ReceiptViewError> {
        let (rule, position, as_of_edges, premises) = {
            let matched = self.matched(id)?;
            (
                matched.rule,
                matched.position,
                matched.as_of_edges,
                matched.premises.to_vec(),
            )
        };
        let binding_source = self
            .binding_recipes
            .get(&rule)
            .and_then(|sources| sources.get(binding))
            .cloned()
            .ok_or_else(|| {
                ReceiptViewError::Invalid(format!("rule {rule} has no binding source {binding}"))
            })?;
        let anchor = match &binding_source {
            ReplayBindingSource::Premise { representative, .. } => {
                let fact = *premises.get(representative.premise).ok_or_else(|| {
                    ReceiptViewError::Invalid(format!(
                        "match {id:?} has no premise {}",
                        representative.premise
                    ))
                })?;
                Some(self.fact_cell_at(
                    FactCellRef {
                        fact,
                        column: crate::ColumnId::from_usize(representative.column),
                    },
                    position,
                )?)
            }
            ReplayBindingSource::Current { .. } | ReplayBindingSource::Constant { .. } => None,
        };
        let term = self
            .projector
            .match_term(id, binding)
            .map_err(ReceiptViewError::Invalid)?;
        let availability = (|| {
            if let Some(anchor) = anchor {
                let endpoint = EqualityEndpoint {
                    sort: anchor.endpoint.sort,
                    term,
                    raw: anchor.endpoint.raw,
                };
                self.explain_anchored_term_availability_at(
                    endpoint,
                    anchor,
                    as_of_edges,
                    position,
                )
            } else {
                let mut aliases = Vec::new();
                let support = self.explain_structural_term_availability_at(
                    term,
                    position,
                    0,
                    &mut aliases,
                    None,
                    None,
                )?;
                Ok(RawTermAvailability {
                    support,
                    aliases: aliases.into_boxed_slice(),
                })
            }
        })()
            .map_err(|error| {
                ReceiptViewError::Invalid(format!(
                    "match {id:?} rule {rule} binding {binding} ({binding_source:?}) availability failed: {error}"
                ))
            })?;
        Ok(availability)
    }

    pub fn explain_fact_endpoint_availability_at(
        &mut self,
        occurrence: FactCellRef,
        endpoint: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawTermAvailability, ReceiptViewError> {
        let anchor = self.fact_cell_at(occurrence, position)?;
        self.explain_anchored_term_availability_at(endpoint, anchor, as_of, position)
    }

    fn explain_anchored_term_availability_at(
        &mut self,
        endpoint: EqualityEndpoint,
        anchor: HistoricalFactCell,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawTermAvailability, ReceiptViewError> {
        self.validate_equality_cutoff(as_of, position)?;
        if endpoint.sort != anchor.endpoint.sort {
            return Err(ReceiptViewError::Invalid(
                "anchored structural term has the wrong logical sort".into(),
            ));
        }
        let mut aliases = Vec::new();
        let structural = self.explain_structural_term_availability_at(
            endpoint.term,
            position,
            0,
            &mut aliases,
            Some(RawEqualityEndpoint {
                sort: endpoint.sort,
                raw: endpoint.raw,
            }),
            Some(&anchor),
        )?;
        let bridge = if endpoint.raw == anchor.endpoint.raw {
            RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            }
        } else {
            self.explain_raw_equality_support_at(
                RawEqualityEndpoint {
                    sort: endpoint.sort,
                    raw: endpoint.raw,
                },
                RawEqualityEndpoint {
                    sort: anchor.endpoint.sort,
                    raw: anchor.endpoint.raw,
                },
                as_of,
                position,
            )?
        };
        let anchor = RawEqualitySupport {
            applied: Box::new([]),
            facts: Box::new([anchor.occurrence.fact]),
            causes: Box::new([]),
            rekeys: anchor.rekeys,
        };
        Ok(RawTermAvailability {
            support: combine_raw_equality_support([structural, bridge, anchor]),
            aliases: aliases.into_boxed_slice(),
        })
    }

    pub fn replay_term(&self, term: ReplayTermId) -> Result<ReplayTerm, ReceiptViewError> {
        self.replay_terms
            .node(term)
            .ok_or_else(|| ReceiptViewError::Invalid(format!("unknown replay term {term:?}")))
    }

    fn live_fact_at(
        &self,
        fact: FactId,
        position: HistoryPosition,
    ) -> Result<RawFactRecord<'a>, ReceiptViewError> {
        if position > self.history_boundary {
            return Err(ReceiptViewError::Invalid(
                "fact query exceeds the captured receipt history".into(),
            ));
        }
        let record = self.fact(fact)?;
        if record.position > position {
            return Err(ReceiptViewError::Invalid(format!(
                "fact {fact:?} was created after {position:?}"
            )));
        }
        if let Some(removal) = self
            .arena
            .removals
            .iter()
            .find(|removal| removal.removed_fact == fact && removal.position <= position)
        {
            return Err(ReceiptViewError::FactNoLongerLive {
                fact,
                position,
                ended_at: removal.position,
                successor: None,
            });
        }
        Ok(record)
    }

    pub fn fact_cell_at(
        &mut self,
        occurrence: FactCellRef,
        position: HistoryPosition,
    ) -> Result<HistoricalFactCell, ReceiptViewError> {
        let fact = self.live_fact_at(occurrence.fact, position)?;
        let column = occurrence.column.index();
        let sort = self
            .replay_terms
            .table_layout(fact.table)
            .ok_or(ReceiptViewError::UnknownTable(fact.table))?
            .get(column)
            .copied()
            .flatten()
            .ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "fact {:?} column {column} has no logical replay sort",
                    occurrence.fact
                ))
            })?;
        let term = self
            .projector
            .fact_term(occurrence.fact, column)
            .map_err(ReceiptViewError::Invalid)?;
        let creation_raw = *fact.values.get(column).ok_or_else(|| {
            ReceiptViewError::Invalid(format!("fact {:?} has no column {column}", occurrence.fact))
        })?;
        let mut raw = creation_raw;
        let mut rekeys = Vec::new();
        let fact_rekeys = self
            .rekey_index()
            .by_fact
            .get(&occurrence.fact)
            .cloned()
            .unwrap_or_else(|| Arc::from([]));
        for index in fact_rekeys.iter().copied() {
            let rekey = &self.arena.rekeys[index];
            if rekey.position > position {
                break;
            }
            for pair in rekey
                .equalities
                .pairs
                .iter()
                .filter(|pair| pair.column == occurrence.column)
            {
                if pair.left.raw != raw || pair.left.sort != sort || pair.right.sort != sort {
                    return Err(ReceiptViewError::Invalid(format!(
                        "rekey {:?} does not continue fact-cell occurrence {:?}: expected {:?}/{:?}, observed {:?}, outcome {:?}",
                        rekey.position, occurrence, sort, raw, pair, rekey.outcome
                    )));
                }
                raw = pair.right.raw;
                rekeys.push(rekey.position);
            }
            if rekey.outcome != RekeyOutcome::Moved {
                let successor = match rekey.outcome {
                    RekeyOutcome::Moved => unreachable!(),
                    RekeyOutcome::Absorbed(fact) | RekeyOutcome::Replaced(fact) => fact,
                };
                return Err(ReceiptViewError::FactNoLongerLive {
                    fact: occurrence.fact,
                    position,
                    ended_at: rekey.position,
                    successor: Some(successor),
                });
            }
        }
        Ok(HistoricalFactCell {
            occurrence,
            created: EqualityEndpoint {
                sort,
                term,
                raw: creation_raw,
            },
            endpoint: EqualityEndpoint { sort, term, raw },
            rekeys: rekeys.into_boxed_slice(),
        })
    }

    pub fn fact_key_at(
        &mut self,
        fact: FactId,
        position: HistoryPosition,
    ) -> Result<Box<[Value]>, ReceiptViewError> {
        let record = self.live_fact_at(fact, position)?;
        let schema = self.table_schema(record.table)?;
        (0..schema.key_columns)
            .map(|column| {
                if schema.columns[column].is_some() {
                    self.fact_cell_at(
                        FactCellRef {
                            fact,
                            column: crate::ColumnId::new(column.try_into().map_err(|_| {
                                ReceiptViewError::Invalid("table key column exceeds u32".into())
                            })?),
                        },
                        position,
                    )
                    .map(|cell| cell.endpoint.raw)
                } else {
                    record.values.get(column).copied().ok_or_else(|| {
                        ReceiptViewError::Invalid(format!(
                            "fact {fact:?} has no key column {column}"
                        ))
                    })
                }
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Vec::into_boxed_slice)
    }

    fn validate_equality_cutoff(
        &self,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<usize, ReceiptViewError> {
        let cutoff: usize = as_of.get().try_into().map_err(|_| {
            ReceiptViewError::Invalid("equality cutoff exceeds addressable storage".into())
        })?;
        if cutoff > self.arena.durable_equalities.len() {
            return Err(ReceiptViewError::Invalid(
                "equality cutoff exceeds the raw applied-event history".into(),
            ));
        }
        if position > self.history_boundary {
            return Err(ReceiptViewError::Invalid(
                "equality query exceeds the captured receipt history".into(),
            ));
        }
        let previous_visible = cutoff
            .checked_sub(1)
            .map(|index| {
                self.arena.durable_equalities[index]
                    .as_ref()
                    .ok_or_else(|| {
                        ReceiptViewError::Invalid(
                            "raw applied-equality history has an ID hole".into(),
                        )
                    })
                    .map(|event| event.position <= position)
            })
            .transpose()?
            .unwrap_or(true);
        let next_hidden = self
            .arena
            .durable_equalities
            .get(cutoff)
            .map(|event| {
                event
                    .as_ref()
                    .ok_or_else(|| {
                        ReceiptViewError::Invalid(
                            "raw applied-equality history has an ID hole".into(),
                        )
                    })
                    .map(|event| event.position > position)
            })
            .transpose()?
            .unwrap_or(true);
        if !previous_visible || !next_hidden {
            return Err(ReceiptViewError::Invalid(
                "equality cutoff disagrees with the global history position".into(),
            ));
        }
        Ok(cutoff)
    }

    fn raw_equality_index(&mut self) -> Result<&RawEqualityIndex, ReceiptViewError> {
        if self.equality_index.is_none() {
            let mut parents = HashMap::default();
            let mut previous_position = None;
            for (index, event) in self.arena.durable_equalities.iter().enumerate() {
                let event = event.as_ref().ok_or_else(|| {
                    ReceiptViewError::Invalid("raw applied-equality history has an ID hole".into())
                })?;
                if previous_position.is_some_and(|previous| event.position <= previous) {
                    return Err(ReceiptViewError::Invalid(
                        "raw applied-equality positions are not strictly increasing".into(),
                    ));
                }
                previous_position = Some(event.position);
                if event.proposal.left.sort != event.proposal.right.sort {
                    return Err(ReceiptViewError::Invalid(
                        "one applied equality crosses logical sorts".into(),
                    ));
                }
                let sort = event.proposal.left.sort;
                if parents
                    .insert(
                        (sort, event.native_child),
                        (
                            event.native_parent,
                            AppliedEqualityId::new(index as u64 + 1),
                        ),
                    )
                    .is_some()
                {
                    return Err(ReceiptViewError::Invalid(
                        "one native equality child acquired two historical parents".into(),
                    ));
                }
            }
            self.counters.equality_index_builds += 1;
            self.counters.equality_events_indexed += self.arena.durable_equalities.len() as u64;
            self.counters.equality_positions_validated +=
                self.arena.durable_equalities.len() as u64;
            self.equality_index = Some(RawEqualityIndex { parents });
        }
        Ok(self
            .equality_index
            .as_ref()
            .expect("initialized raw equality index disappeared"))
    }

    pub fn explain_raw_equality_support_at(
        &mut self,
        left: RawEqualityEndpoint,
        right: RawEqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        self.raw_equality_support_if_connected_at(left, right, as_of, position)?
            .ok_or_else(|| {
                ReceiptViewError::Invalid(
                    "equality endpoints were disconnected at the historical landmark".into(),
                )
            })
    }

    /// Return the historical child equalities required to replay one
    /// congruence edge between two structural calls.
    ///
    /// The applied edge records the parent equality and its cause, but the
    /// parent's congruence also depends on each unequal child pair already
    /// being equal at the recorded cutoff. Reconstruct those dependencies
    /// from the projected terms and the existing equality forest.
    pub fn explain_congruence_child_support_at(
        &mut self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        self.validate_equality_cutoff(as_of, position)?;
        self.validate_equality_endpoints(left, right)?;
        let (
            ReplayTerm::Call {
                sort: left_sort,
                op: left_op,
                children: left_children,
            },
            ReplayTerm::Call {
                sort: right_sort,
                op: right_op,
                children: right_children,
            },
        ) = (self.replay_term(left.term)?, self.replay_term(right.term)?)
        else {
            return Err(ReceiptViewError::Invalid(
                "congruence equality endpoints are not structural calls".into(),
            ));
        };
        if left_sort != right_sort
            || left_op != right_op
            || left_children.len() != right_children.len()
        {
            return Err(ReceiptViewError::Invalid(
                "congruence equality endpoints have incompatible structure".into(),
            ));
        }
        let left_candidates = self.congruence_call_child_candidates(left, as_of, position)?;
        let right_candidates = self.congruence_call_child_candidates(right, as_of, position)?;
        for left_children in &left_candidates {
            for right_children in &right_candidates {
                if left_children.len() != right_children.len() {
                    continue;
                }
                let mut support = Vec::with_capacity(left_children.len());
                let mut connected = true;
                for (left_child, right_child) in left_children.iter().zip(right_children.iter()) {
                    if left_child.sort != right_child.sort {
                        connected = false;
                        break;
                    }
                    let Some(child_support) = self.raw_equality_support_if_connected_at(
                        *left_child,
                        *right_child,
                        as_of,
                        position,
                    )?
                    else {
                        connected = false;
                        break;
                    };
                    support.push(child_support);
                }
                if connected {
                    return Ok(combine_raw_equality_support(support));
                }
            }
        }
        Err(ReceiptViewError::Invalid(
            "congruence equality has no exact historically connected constructor occurrences"
                .into(),
        ))
    }

    fn congruence_call_child_candidates(
        &mut self,
        endpoint: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<Vec<Box<[RawEqualityEndpoint]>>, ReceiptViewError> {
        let ReplayTerm::Call { sort, op, children } = self.replay_term(endpoint.term)? else {
            return Err(ReceiptViewError::Invalid(
                "congruence equality endpoint is not a structural call".into(),
            ));
        };
        let facts = self.constructor_occurrence_facts(sort, op);
        let mut candidates = Vec::new();
        for producer in facts.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if fact.position > position {
                continue;
            }
            let table = fact.table;
            let values = fact.values.to_vec();
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&table)
                .map(|entry| entry.clone())
                .ok_or(ReceiptViewError::UnknownTable(table))?;
            let output = constructor.child_sorts.len();
            if output != children.len() || values.len() <= output {
                return Err(ReceiptViewError::Invalid(format!(
                    "constructor fact {producer:?} has an invalid replay arity"
                )));
            }
            let projected = self
                .projector
                .fact_term(producer, output)
                .map_err(ReceiptViewError::Invalid)?;
            if projected != endpoint.term {
                continue;
            }
            if self
                .raw_equality_support_if_connected_at(
                    RawEqualityEndpoint {
                        sort,
                        raw: values[output],
                    },
                    RawEqualityEndpoint {
                        sort,
                        raw: endpoint.raw,
                    },
                    as_of,
                    position,
                )?
                .is_none()
            {
                continue;
            }
            candidates.push(
                constructor
                    .child_sorts
                    .iter()
                    .copied()
                    .zip(values.into_iter())
                    .map(|(sort, raw)| RawEqualityEndpoint { sort, raw })
                    .collect(),
            );
        }
        if candidates.is_empty() {
            return Err(ReceiptViewError::Invalid(format!(
                "congruence endpoint term {:?} has no exact historical constructor occurrence",
                endpoint.term
            )));
        }
        Ok(candidates)
    }

    fn raw_equality_support_if_connected_at(
        &mut self,
        left: RawEqualityEndpoint,
        right: RawEqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<Option<RawEqualitySupport>, ReceiptViewError> {
        if left.sort != right.sort {
            return Err(ReceiptViewError::Invalid(
                "cannot explain equality across logical sorts".into(),
            ));
        }
        let cutoff = self.validate_equality_cutoff(as_of, position)?;
        self.counters.equality_explanation_queries += 1;
        let parents = &self.raw_equality_index()?.parents;
        let edge_is_visible = |edge: AppliedEqualityId| edge.get() as usize <= cutoff;
        let mut left_ancestors = HashMap::<Value, usize>::default();
        let mut left_edges = Vec::new();
        let mut cursor = left.raw;
        loop {
            left_ancestors.insert(cursor, left_edges.len());
            let Some((parent, edge)) = parents.get(&(left.sort, cursor)).copied() else {
                break;
            };
            if !edge_is_visible(edge) {
                break;
            }
            left_edges.push(edge);
            cursor = parent;
        }
        let mut right_edges = Vec::new();
        let mut cursor = right.raw;
        let left_depth = loop {
            if let Some(depth) = left_ancestors.get(&cursor).copied() {
                break depth;
            }
            let Some((parent, edge)) = parents.get(&(right.sort, cursor)).copied() else {
                return Ok(None);
            };
            if !edge_is_visible(edge) {
                return Ok(None);
            }
            right_edges.push(edge);
            cursor = parent;
        };
        self.counters.equality_parent_steps += (left_edges.len() + right_edges.len()) as u64;
        let mut edges = left_edges[..left_depth].to_vec();
        edges.extend(right_edges);
        edges.sort_unstable();
        edges.dedup();
        Ok(Some(RawEqualitySupport {
            applied: edges.into_boxed_slice(),
            facts: Box::new([]),
            causes: Box::new([]),
            rekeys: Box::new([]),
        }))
    }

    pub fn explain_equality_support_at(
        &mut self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        match self.observed_equality_support(left, right, as_of, position)? {
            ObservedEqualitySupport::Support(support) => Ok(support),
            ObservedEqualitySupport::Missing(term) => Err(ReceiptViewError::Invalid(format!(
                "endpoint term {term:?} has no supported historical native occurrence"
            ))),
        }
    }

    /// Return exact endpoint equality support when both source terms own a
    /// historical native occurrence. A structurally available checked term
    /// may deliberately have no standalone occurrence; callers that already
    /// retain anchored availability can distinguish that case from malformed
    /// receipt history without weakening other validation errors.
    pub fn explain_equality_support_if_observed_at(
        &mut self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<Option<RawEqualitySupport>, ReceiptViewError> {
        match self.observed_equality_support(left, right, as_of, position)? {
            ObservedEqualitySupport::Support(support) => Ok(Some(support)),
            ObservedEqualitySupport::Missing(_) => Ok(None),
        }
    }

    fn observed_equality_support(
        &mut self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<ObservedEqualitySupport, ReceiptViewError> {
        self.validate_equality_cutoff(as_of, position)?;
        self.validate_equality_endpoints(left, right)?;
        let Some(left_support) =
            self.explain_endpoint_term_occurrence_if_observed(left, position)?
        else {
            return Ok(ObservedEqualitySupport::Missing(left.term));
        };
        let Some(right_support) =
            self.explain_endpoint_term_occurrence_if_observed(right, position)?
        else {
            return Ok(ObservedEqualitySupport::Missing(right.term));
        };
        let raw_support = if left.raw == right.raw {
            RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            }
        } else {
            self.explain_raw_equality_support_at(
                RawEqualityEndpoint {
                    sort: left.sort,
                    raw: left.raw,
                },
                RawEqualityEndpoint {
                    sort: right.sort,
                    raw: right.raw,
                },
                as_of,
                position,
            )?
        };
        Ok(ObservedEqualitySupport::Support(
            combine_raw_equality_support([left_support, right_support, raw_support]),
        ))
    }

    fn validate_equality_endpoints(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
    ) -> Result<(), ReceiptViewError> {
        if left.term.is_missing() || right.term.is_missing() {
            return Err(ReceiptViewError::Invalid(
                "cannot explain equality with a missing ReplayTermId".into(),
            ));
        }
        for endpoint in [left, right] {
            let node = self.replay_terms.node(endpoint.term).ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "equality endpoint owns unknown term {:?}",
                    endpoint.term
                ))
            })?;
            if node.sort() != endpoint.sort {
                return Err(ReceiptViewError::Invalid(
                    "equality endpoint term has the wrong logical sort".into(),
                ));
            }
        }
        if left.sort != right.sort {
            return Err(ReceiptViewError::Invalid(
                "cannot explain equality across logical sorts".into(),
            ));
        }
        Ok(())
    }

    fn explain_endpoint_term_occurrence(
        &mut self,
        endpoint: EqualityEndpoint,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        self.explain_endpoint_term_occurrence_if_observed(endpoint, position)?
            .ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "endpoint term {:?} has no supported historical native occurrence",
                    endpoint.term
                ))
            })
    }

    fn explain_endpoint_term_occurrence_if_observed(
        &mut self,
        endpoint: EqualityEndpoint,
        position: HistoryPosition,
    ) -> Result<Option<RawEqualitySupport>, ReceiptViewError> {
        match self.replay_term(endpoint.term)? {
            ReplayTerm::Literal { .. } => Ok(Some(RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            })),
            ReplayTerm::Call { .. } => self.explain_term_occurrence_at(
                endpoint.term,
                endpoint.sort,
                endpoint.raw,
                position,
                FactId::MISSING,
                0,
            ),
        }
    }

    pub fn explain_fact_cell_support_at(
        &mut self,
        left: FactCellRef,
        right: FactCellRef,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        self.validate_equality_cutoff(as_of, position)?;
        let left = self.fact_cell_at(left, position)?;
        let right = self.fact_cell_at(right, position)?;
        if left.created.sort != right.created.sort {
            return Err(ReceiptViewError::Invalid(
                "cannot explain fact-cell equality across logical sorts".into(),
            ));
        }
        let support = if left.created.raw == right.created.raw
            && left.occurrence != right.occurrence
        {
            // Equal structural ids do not imply equal native occurrences:
            // delete/recreate can place one hash-consed term in two roots.
            self.explain_same_raw_fact_occurrences(&left, &right)?
        } else if left.created.raw == right.created.raw {
            self.explain_fact_term_occurrence(&left)?.ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "{} has no supported historical native occurrence",
                    self.describe_fact_cell(&left),
                ))
            })?
        } else {
            // The two exact fact cells are the structural occurrences that
            // satisfied the check.  Do not discard them and search globally
            // for another occurrence of the same ReplayTermId; retain each
            // cell's own producer, then explain only their historical native
            // connectivity.
            let left_support = self.explain_fact_term_occurrence(&left)?.ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "left {} has no supported historical native occurrence",
                    self.describe_fact_cell(&left),
                ))
            })?;
            let right_support = self.explain_fact_term_occurrence(&right)?.ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "right {} has no supported historical native occurrence",
                    self.describe_fact_cell(&right),
                ))
            })?;
            let raw_support = self.explain_raw_equality_support_at(
                RawEqualityEndpoint {
                    sort: left.created.sort,
                    raw: left.created.raw,
                },
                RawEqualityEndpoint {
                    sort: right.created.sort,
                    raw: right.created.raw,
                },
                as_of,
                position,
            )?;
            combine_raw_equality_support([left_support, right_support, raw_support])
        };
        let mut facts = vec![left.occurrence.fact, right.occurrence.fact];
        facts.extend(support.facts);
        facts.sort_unstable();
        facts.dedup();
        let mut rekeys = left.rekeys.into_vec();
        rekeys.extend(right.rekeys);
        rekeys.extend(support.rekeys);
        rekeys.sort_unstable();
        rekeys.dedup();
        Ok(RawEqualitySupport {
            applied: support.applied,
            facts: facts.into_boxed_slice(),
            causes: support.causes,
            rekeys: rekeys.into_boxed_slice(),
        })
    }

    pub fn explain_fact_endpoint_support_at(
        &mut self,
        fact: FactCellRef,
        endpoint: EqualityEndpoint,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        self.validate_equality_cutoff(as_of, position)?;
        let fact = self.fact_cell_at(fact, position)?;
        if fact.created.sort != endpoint.sort {
            return Err(ReceiptViewError::Invalid(
                "cannot explain fact/endpoint equality across logical sorts".into(),
            ));
        }
        // Native root connectivity alone does not establish either exact
        // structural occurrence. A direct outer union can connect a fact to a
        // parent created with structurally different-but-equal children; the
        // check may then read its requested parent through a no-op canonical
        // lookup. Retain both occurrence witnesses at every raw-path shape.
        let fact_support = self.explain_fact_term_occurrence(&fact)?.ok_or_else(|| {
            ReceiptViewError::Invalid(format!(
                "{} has no supported historical native occurrence",
                self.describe_fact_cell(&fact),
            ))
        })?;
        let endpoint_support = self.explain_endpoint_term_occurrence(endpoint, position)?;
        let raw_support = if fact.created.raw == endpoint.raw {
            RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            }
        } else {
            self.explain_raw_equality_support_at(
                RawEqualityEndpoint {
                    sort: fact.created.sort,
                    raw: fact.created.raw,
                },
                RawEqualityEndpoint {
                    sort: endpoint.sort,
                    raw: endpoint.raw,
                },
                as_of,
                position,
            )?
        };
        let support = combine_raw_equality_support([fact_support, endpoint_support, raw_support]);
        let mut facts = vec![fact.occurrence.fact];
        facts.extend(support.facts);
        facts.sort_unstable();
        facts.dedup();
        let mut rekeys = fact.rekeys.into_vec();
        rekeys.extend(support.rekeys);
        rekeys.sort_unstable();
        rekeys.dedup();
        Ok(RawEqualitySupport {
            applied: support.applied,
            facts: facts.into_boxed_slice(),
            causes: support.causes,
            rekeys: rekeys.into_boxed_slice(),
        })
    }

    fn equality_edge_count_at(
        &mut self,
        position: HistoryPosition,
    ) -> Result<EqualityEdgeCount, ReceiptViewError> {
        // Building the forest validates ID density and strictly increasing
        // positions once. Every later historical cutoff is then a binary
        // search instead of another full equality-history walk.
        let _ = self.raw_equality_index()?;
        let count = self
            .arena
            .durable_equalities
            .partition_point(|event| event.as_ref().unwrap().position <= position);
        Ok(EqualityEdgeCount::new(count as u64))
    }

    fn constructor_occurrence_facts(
        &mut self,
        sort: ReplaySortId,
        op: ReplayOpId,
    ) -> Arc<[FactId]> {
        if self.constructor_occurrence_index.is_none() {
            let mut facts = HashMap::<(ReplaySortId, ReplayOpId), Vec<FactId>>::default();
            let registered = self
                .replay_terms
                .table_constructors
                .iter()
                .map(|entry| (entry.value().result_sort, entry.value().op))
                .collect();
            let mut certified_calls = HashSet::default();
            let mut visited_terms = HashSet::default();
            for recipe in self.term_recipes.rules.values() {
                for template in recipe.current_roots.iter().flatten() {
                    self.collect_certified_template_calls(
                        template,
                        &mut certified_calls,
                        &mut visited_terms,
                    );
                }
            }
            for origin in &self.term_recipes.row_origins {
                for template in origin.cells.iter().flatten() {
                    self.collect_certified_template_calls(
                        template,
                        &mut certified_calls,
                        &mut visited_terms,
                    );
                }
            }
            for origin in &self.term_recipes.term_origins {
                self.collect_certified_template_calls(
                    &origin.term,
                    &mut certified_calls,
                    &mut visited_terms,
                );
            }
            self.counters.equality_occurrence_facts_scanned += self.arena.facts.len() as u64;
            for (index, slot) in self.arena.facts.iter().enumerate() {
                let Some(fact) = slot.as_ref() else {
                    continue;
                };
                let Some(constructor) = self
                    .replay_terms
                    .table_constructors
                    .get(&fact.table)
                    .map(|entry| entry.clone())
                else {
                    continue;
                };
                facts
                    .entry((constructor.result_sort, constructor.op))
                    .or_default()
                    .push(FactId::new(index as u64 + 1));
            }
            self.constructor_occurrence_index = Some(ConstructorOccurrenceIndex {
                facts: facts
                    .into_iter()
                    .map(|(key, facts)| (key, Arc::from(facts)))
                    .collect(),
                registered,
                certified_calls,
            });
        }
        self.constructor_occurrence_index
            .as_ref()
            .expect("initialized constructor occurrence index disappeared")
            .facts
            .get(&(sort, op))
            .cloned()
            .unwrap_or_else(|| Arc::from([]))
    }

    fn is_registered_constructor_call(&mut self, sort: ReplaySortId, op: ReplayOpId) -> bool {
        let _ = self.constructor_occurrence_facts(sort, op);
        self.constructor_occurrence_index
            .as_ref()
            .expect("initialized constructor occurrence index disappeared")
            .registered
            .contains(&(sort, op))
    }

    fn is_certified_replay_call(&mut self, sort: ReplaySortId, op: ReplayOpId) -> bool {
        let _ = self.constructor_occurrence_facts(sort, op);
        self.constructor_occurrence_index
            .as_ref()
            .expect("initialized constructor occurrence index disappeared")
            .certified_calls
            .contains(&(sort, op))
    }

    fn is_equality_sort(&mut self, sort: ReplaySortId, seed_op: ReplayOpId) -> bool {
        let _ = self.constructor_occurrence_facts(sort, seed_op);
        self.constructor_occurrence_index
            .as_ref()
            .expect("initialized constructor occurrence index disappeared")
            .registered
            .iter()
            .any(|(constructor_sort, _)| *constructor_sort == sort)
    }

    fn explain_structural_term_availability_at(
        &mut self,
        term: ReplayTermId,
        position: HistoryPosition,
        depth: usize,
        aliases: &mut Vec<RawAliasWindow>,
        desired: Option<RawEqualityEndpoint>,
        anchor: Option<&HistoricalFactCell>,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        if let Some(support) = self.try_explain_structural_term_availability_at(
            term,
            position,
            depth,
            aliases,
            StructuralAvailabilityContext {
                desired,
                anchor,
                fresh_after: None,
            },
        )? {
            return Ok(support);
        }
        Err(ReceiptViewError::Invalid(format!(
            "structural term {term:?} ({:?}, desired {desired:?}) has no exact historical producer by {position:?}",
            self.replay_term(term)?
        )))
    }

    fn try_explain_structural_term_availability_at(
        &mut self,
        term: ReplayTermId,
        position: HistoryPosition,
        depth: usize,
        aliases: &mut Vec<RawAliasWindow>,
        context: StructuralAvailabilityContext<'_>,
    ) -> Result<Option<RawEqualitySupport>, ReceiptViewError> {
        let StructuralAvailabilityContext {
            desired,
            anchor,
            fresh_after: inherited_fresh_after,
        } = context;
        if depth > 256 {
            return Err(ReceiptViewError::Invalid(
                "structural term availability exceeds 256 call levels".into(),
            ));
        }
        let ReplayTerm::Call { sort, op, children } = self.replay_term(term)? else {
            return Ok(Some(RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            }));
        };

        if !self.is_registered_constructor_call(sort, op) {
            if !self.is_certified_replay_call(sort, op) {
                return Err(ReceiptViewError::Invalid(format!(
                    "structural call {op:?} for {sort:?} has no replay-safe availability producer"
                )));
            }
            let equality_sort = self.is_equality_sort(sort, op);
            let mut fresh_after = inherited_fresh_after;
            if self.replay_terms.container_child_sorts.contains_key(&sort)
                && let (Some(desired), Some(anchor)) = (desired, anchor)
            {
                let versions = self.replay_terms.container_anchors(sort, desired.raw);
                if versions.len() > 1 && versions.contains(&term) {
                    let anchor_position = self.fact(anchor.occurrence.fact)?.position;
                    fresh_after = Some(
                        fresh_after.map_or(anchor_position, |current| current.max(anchor_position)),
                    );
                }
            }
            let mut parts = Vec::with_capacity(children.len() + usize::from(desired.is_some()));
            if equality_sort && let Some(desired) = desired {
                parts.push(self.explain_pure_eqsort_call_occurrence(
                    sort,
                    &children,
                    desired.raw,
                    position,
                    depth,
                )?);
            }
            let alias_checkpoint = aliases.len();
            for child in children.iter().copied() {
                let child_desired = match self.replay_term(child)? {
                    ReplayTerm::Call {
                        sort: child_sort,
                        op: child_op,
                        ..
                    } if self.is_equality_sort(child_sort, child_op) => self
                        .replay_terms
                        .original_value(child_sort, child)
                        .map(|raw| RawEqualityEndpoint {
                            sort: child_sort,
                            raw,
                        }),
                    ReplayTerm::Literal { .. } | ReplayTerm::Call { .. } => None,
                };
                let Some(support) = self.try_explain_structural_term_availability_at(
                    child,
                    position,
                    depth + 1,
                    aliases,
                    StructuralAvailabilityContext {
                        desired: child_desired,
                        anchor: None,
                        fresh_after,
                    },
                )?
                else {
                    aliases.truncate(alias_checkpoint);
                    return Ok(None);
                };
                parts.push(support);
            }
            // Pure calls and the allowed ordered containers can be evaluated
            // whenever their child aliases are available. The replay
            // scheduler enforces that topological dependency separately.
            aliases.push(RawAliasWindow {
                term,
                available_after: fresh_after.unwrap_or(HistoryPosition::new(0)),
                fresh_after,
            });
            return Ok(Some(combine_raw_equality_support(parts)));
        }

        let possible = self.constructor_occurrence_facts(sort, op);
        // ReplayTermId identifies syntax, not one native occurrence. Prefer
        // an exact structural producer and use the historical equality
        // prefix only to bridge that occurrence to the row value requested by
        // its parent. The second pass is the narrow spelling fallback for a
        // row whose source recipe contains a pure expression but whose
        // committed child column stores the evaluated base value.
        let passes = if desired.is_some() { 2 } else { 1 };
        let preferred = anchor
            .filter(|anchor| anchor.occurrence.column.index() == children.len())
            .map(|anchor| anchor.occurrence.fact)
            .filter(|fact| possible.binary_search(fact).is_ok());
        for pass in 0..passes {
            for offset in 0..possible.len() + usize::from(preferred.is_some()) {
                let producer = if offset == 0
                    && let Some(preferred) = preferred
                {
                    preferred
                } else {
                    let ordinary_offset = offset - usize::from(preferred.is_some());
                    let index = if desired.is_some() {
                        ordinary_offset
                    } else {
                        possible.len() - ordinary_offset - 1
                    };
                    let producer = possible[index];
                    if Some(producer) == preferred {
                        continue;
                    }
                    producer
                };
                let fact_position = self.fact(producer)?.position;
                if fact_position > position {
                    continue;
                }
                let constructor = self
                    .replay_terms
                    .table_constructors
                    .get(&self.fact(producer)?.table)
                    .map(|entry| entry.clone())
                    .ok_or_else(|| {
                        ReceiptViewError::Invalid(format!(
                            "constructor occurrence {producer:?} lost its replay metadata"
                        ))
                    })?;
                let output = constructor.child_sorts.len();
                self.counters.equality_occurrence_terms_projected += 1;
                let produced_term = self
                    .projector
                    .fact_term(producer, output)
                    .map_err(ReceiptViewError::Invalid)?;
                let exact_term = produced_term == term;
                if (pass == 0) != exact_term {
                    continue;
                }
                let occurrence = FactCellRef {
                    fact: producer,
                    column: crate::ColumnId::from_usize(output),
                };
                let (output_cell, occurrence_position) =
                    match self.fact_cell_at(occurrence, position) {
                        Ok(cell) => (cell, position),
                        Err(ReceiptViewError::FactNoLongerLive { .. }) => {
                            (self.fact_cell_at(occurrence, fact_position)?, fact_position)
                        }
                        Err(error) => return Err(error),
                    };
                let output_support = if let Some(desired) = desired {
                    if desired.sort != output_cell.endpoint.sort {
                        continue;
                    }
                    if desired.raw == output_cell.endpoint.raw {
                        None
                    } else if exact_term || anchor.is_some() {
                        let as_of = self.equality_edge_count_at(position)?;
                        let created = anchor.map(|anchor| RawEqualityEndpoint {
                            sort: anchor.created.sort,
                            raw: anchor.created.raw,
                        });
                        let mut support = None;
                        let mut connected = false;
                        for target in std::iter::once(desired)
                            .chain(created.filter(|created| *created != desired))
                        {
                            if target.sort != output_cell.endpoint.sort {
                                continue;
                            }
                            if target.raw == output_cell.endpoint.raw {
                                connected = true;
                                break;
                            }
                            if let Some(candidate) = self.raw_equality_support_if_connected_at(
                                RawEqualityEndpoint {
                                    sort: output_cell.endpoint.sort,
                                    raw: output_cell.endpoint.raw,
                                },
                                target,
                                as_of,
                                position,
                            )? {
                                support = Some(candidate);
                                connected = true;
                                break;
                            }
                        }
                        if !connected {
                            continue;
                        }
                        support
                    } else {
                        continue;
                    }
                } else {
                    None
                };
                if children.len() != constructor.child_sorts.len() {
                    return Err(ReceiptViewError::Invalid(format!(
                        "constructor term {term:?} has {} children but its producer expects {}",
                        children.len(),
                        constructor.child_sorts.len()
                    )));
                }
                let mut parts = Vec::with_capacity(children.len() + 2);
                let alias_checkpoint = aliases.len();
                let mut compatible = true;
                if let Some(support) = output_support {
                    parts.push(support);
                }
                for (column, (child, child_sort)) in children
                    .iter()
                    .copied()
                    .zip(constructor.child_sorts.iter().copied())
                    .enumerate()
                {
                    let child_cell = self.fact_cell_at(
                        FactCellRef {
                            fact: producer,
                            column: crate::ColumnId::from_usize(column),
                        },
                        occurrence_position,
                    )?;
                    if child_cell.endpoint.sort != child_sort {
                        return Err(ReceiptViewError::Invalid(format!(
                            "constructor producer {producer:?} child {column} changed replay sort"
                        )));
                    }
                    let Some(support) = self.try_explain_structural_term_availability_at(
                        child,
                        position,
                        depth + 1,
                        aliases,
                        StructuralAvailabilityContext {
                            desired: Some(RawEqualityEndpoint {
                                sort: child_sort,
                                raw: child_cell.endpoint.raw,
                            }),
                            anchor: Some(&child_cell),
                            fresh_after: inherited_fresh_after,
                        },
                    )?
                    else {
                        aliases.truncate(alias_checkpoint);
                        compatible = false;
                        break;
                    };
                    parts.push(support);
                    parts.push(RawEqualitySupport {
                        applied: Box::new([]),
                        facts: Box::new([child_cell.occurrence.fact]),
                        causes: Box::new([]),
                        rekeys: child_cell.rekeys,
                    });
                }
                if !compatible {
                    continue;
                }
                // Capture at the earliest retained boundary after creation.
                // Child facts may be published later in the same native batch;
                // replay scheduling also waits for every child alias.
                let available_after = anchor
                    .map(|anchor| self.fact(anchor.occurrence.fact).map(|fact| fact.position))
                    .transpose()?
                    .map_or(fact_position, |anchor| anchor.max(fact_position));
                aliases.push(RawAliasWindow {
                    term,
                    available_after: inherited_fresh_after
                        .map_or(available_after, |fresh| fresh.max(available_after)),
                    fresh_after: inherited_fresh_after,
                });
                parts.push(RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    causes: Box::new([]),
                    rekeys: output_cell.rekeys,
                });
                return Ok(Some(combine_raw_equality_support(parts)));
            }
        }
        Ok(None)
    }

    fn explain_pure_eqsort_call_occurrence(
        &mut self,
        result_sort: ReplaySortId,
        children: &[ReplayTermId],
        desired_raw: Value,
        position: HistoryPosition,
        depth: usize,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        struct WalkContext {
            result_sort: ReplaySortId,
            desired_raw: Value,
            position: HistoryPosition,
        }

        fn walk(
            view: &mut CausalReceiptView<'_>,
            context: &WalkContext,
            term: ReplayTermId,
            depth: usize,
            visited: &mut HashSet<ReplayTermId>,
            supports: &mut Vec<RawEqualitySupport>,
        ) -> Result<(), ReceiptViewError> {
            if depth > 256 {
                return Err(ReceiptViewError::Invalid(
                    "pure-call occurrence explanation exceeds 256 structural levels".into(),
                ));
            }
            if !visited.insert(term) {
                return Ok(());
            }
            let ReplayTerm::Call { sort, op, children } = view.replay_term(term)? else {
                return Ok(());
            };
            if sort == context.result_sort
                && view.is_registered_constructor_call(sort, op)
                && let Some(support) = view.explain_term_occurrence_at(
                    term,
                    sort,
                    context.desired_raw,
                    context.position,
                    FactId::MISSING,
                    depth + 1,
                )?
            {
                supports.push(support);
            }
            for child in children.iter().copied() {
                walk(view, context, child, depth + 1, visited, supports)?;
            }
            Ok(())
        }

        let mut visited = HashSet::default();
        let mut supports = Vec::new();
        let context = WalkContext {
            result_sort,
            desired_raw,
            position,
        };
        for child in children.iter().copied() {
            walk(
                self,
                &context,
                child,
                depth + 1,
                &mut visited,
                &mut supports,
            )?;
        }
        if supports.is_empty() {
            return Err(ReceiptViewError::Invalid(format!(
                "certified pure call for {result_sort:?} has no supported same-sort constructor descendant"
            )));
        }
        Ok(combine_raw_equality_support(supports))
    }

    /// A container builder has no table FactId, but two structural container
    /// terms can denote the same registry value only because their positional
    /// EqSort children were equal when they were interned. Reconcile the
    /// requested term with every known structural anchor for that value and
    /// retain those child equalities lazily. Ordinary pure primitives do not
    /// need this step because they do not hash-cons an identity over EqSort
    /// children.
    #[allow(clippy::too_many_arguments)]
    fn explain_container_call_occurrence(
        &mut self,
        sort: ReplaySortId,
        op: ReplayOpId,
        target_children: &[ReplayTermId],
        desired_raw: Value,
        position: HistoryPosition,
        depth: usize,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        let anchors = self.replay_terms.container_anchors(sort, desired_raw);
        let mut parts = Vec::new();
        let mut found_compatible_anchor = false;
        for candidate in anchors {
            let ReplayTerm::Call {
                sort: candidate_sort,
                op: candidate_op,
                children: candidate_children,
            } = self.replay_term(candidate)?
            else {
                continue;
            };
            if candidate_sort != sort
                || candidate_op != op
                || candidate_children.len() != target_children.len()
            {
                continue;
            }
            let mut candidate_parts = Vec::new();
            let mut compatible = true;
            for (&target_child, &candidate_child) in
                target_children.iter().zip(candidate_children.iter())
            {
                if target_child == candidate_child {
                    continue;
                }
                let target_node = self.replay_term(target_child)?;
                let candidate_node = self.replay_term(candidate_child)?;
                let child_sort = target_node.sort();
                if candidate_node.sort() != child_sort {
                    compatible = false;
                    break;
                }
                let ReplayTerm::Call { .. } = target_node else {
                    // Base literals are canonical values. Distinct literal
                    // nodes cannot explain one positional container identity.
                    compatible = false;
                    break;
                };
                let Some(candidate_raw) = self
                    .replay_terms
                    .original_value(child_sort, candidate_child)
                else {
                    compatible = false;
                    break;
                };
                let Some(target_support) = self.explain_term_occurrence_at(
                    target_child,
                    child_sort,
                    candidate_raw,
                    position,
                    FactId::MISSING,
                    depth + 1,
                )?
                else {
                    compatible = false;
                    break;
                };
                let Some(candidate_support) = self.explain_term_occurrence_at(
                    candidate_child,
                    child_sort,
                    candidate_raw,
                    position,
                    FactId::MISSING,
                    depth + 1,
                )?
                else {
                    compatible = false;
                    break;
                };
                // The target establishes why the source child could be read
                // at this registry value; the candidate establishes the
                // historical anchor that made the no-op container lookup hit.
                // Keeping only the former loses zero-edge constructor
                // attachments such as A/Alias and makes replay mint a
                // different container identity.
                candidate_parts.push(target_support);
                candidate_parts.push(candidate_support);
            }
            if compatible {
                found_compatible_anchor = true;
                parts.extend(candidate_parts);
            }
        }
        if !found_compatible_anchor {
            return Err(ReceiptViewError::Invalid(format!(
                "container call {op:?} for {sort:?} has no compatible structural anchor at {desired_raw:?}"
            )));
        }
        Ok(combine_raw_equality_support(parts))
    }

    fn producer_output_support(
        &mut self,
        producer: FactId,
        output: usize,
        sort: ReplaySortId,
        desired_raw: Value,
        as_of: EqualityEdgeCount,
        position: HistoryPosition,
    ) -> Result<Option<(HistoricalFactCell, RawEqualitySupport)>, ReceiptViewError> {
        let output_cell = match self.fact_cell_at(
            FactCellRef {
                fact: producer,
                column: crate::ColumnId::from_usize(output),
            },
            position,
        ) {
            Ok(cell) => cell,
            Err(ReceiptViewError::FactNoLongerLive { .. }) => return Ok(None),
            Err(error) => return Err(error),
        };
        let output_support = match self.explain_raw_equality_support_at(
            RawEqualityEndpoint {
                sort,
                raw: output_cell.endpoint.raw,
            },
            RawEqualityEndpoint {
                sort,
                raw: desired_raw,
            },
            as_of,
            position,
        ) {
            Ok(support) => support,
            Err(ReceiptViewError::Invalid(message))
                if message == "equality endpoints were disconnected at the historical landmark" =>
            {
                return Ok(None);
            }
            Err(error) => return Err(error),
        };
        Ok(Some((output_cell, output_support)))
    }

    /// Retain every exact structural occurrence connected to `desired_raw`
    /// at this landmark. Replay aliases name structural terms, not native
    /// occurrence IDs, so a hash-consed term that was created in multiple
    /// native components must keep every connected creator and the bridges
    /// between them. This is deliberately cold and only runs for selected
    /// structural terms.
    fn explain_exact_term_occurrences_at(
        &mut self,
        term: ReplayTermId,
        sort: ReplaySortId,
        desired_raw: Value,
        position: HistoryPosition,
        excluded_fact: FactId,
    ) -> Result<Option<RawEqualitySupport>, ReceiptViewError> {
        let query = StructuralOccurrenceQuery {
            term,
            sort,
            raw: desired_raw,
            position,
            excluded_fact,
        };
        if let Some(cached) = self.exact_occurrence_support_cache.get(&query) {
            return Ok(cached.clone());
        }
        let ReplayTerm::Call {
            sort: term_sort,
            op,
            ..
        } = self.replay_term(term)?
        else {
            let support = RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            };
            self.exact_occurrence_support_cache
                .insert(query, Some(support.clone()));
            return Ok(Some(support));
        };
        if term_sort != sort {
            return Err(ReceiptViewError::Invalid(
                "exact occurrence term has the wrong logical sort".into(),
            ));
        }

        let as_of = self.equality_edge_count_at(position)?;
        let possible = self.constructor_occurrence_facts(sort, op);
        let mut supports = Vec::new();
        let mut first_projection_error = None;
        for producer in possible.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if producer == excluded_fact || fact.position > position {
                continue;
            }
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
                .ok_or(ReceiptViewError::UnknownTable(fact.table))?;
            let output = constructor.child_sorts.len();
            self.counters.equality_occurrence_terms_projected += 1;
            let produced_term = match self.projector.fact_term(producer, output) {
                Ok(term) => term,
                Err(error) => {
                    first_projection_error.get_or_insert(error);
                    continue;
                }
            };
            if produced_term != term {
                continue;
            }
            let creation_raw = *fact.values.get(output).ok_or_else(|| {
                ReceiptViewError::Invalid(format!(
                    "constructor fact {producer:?} has no output column {output}"
                ))
            })?;
            let raw_support = match self.explain_raw_equality_support_at(
                RawEqualityEndpoint {
                    sort,
                    raw: creation_raw,
                },
                RawEqualityEndpoint {
                    sort,
                    raw: desired_raw,
                },
                as_of,
                position,
            ) {
                Ok(support) => support,
                Err(ReceiptViewError::Invalid(message))
                    if message
                        == "equality endpoints were disconnected at the historical landmark" =>
                {
                    continue;
                }
                Err(error) => return Err(error),
            };
            supports.push(combine_raw_equality_support([
                raw_support,
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    causes: Box::new([]),
                    rekeys: Box::new([]),
                },
            ]));
        }
        if supports.is_empty() {
            if let Some(error) = first_projection_error {
                return Err(ReceiptViewError::Invalid(error));
            }
            self.exact_occurrence_support_cache.insert(query, None);
            return Ok(None);
        }
        let support = combine_raw_equality_support(supports);
        self.exact_occurrence_support_cache
            .insert(query, Some(support.clone()));
        Ok(Some(support))
    }

    fn explain_fact_term_occurrence(
        &mut self,
        cell: &HistoricalFactCell,
    ) -> Result<Option<RawEqualitySupport>, ReceiptViewError> {
        let fact = self.fact(cell.occurrence.fact)?;
        let schema = self.table_schema(fact.table)?;
        if cell.occurrence.column.index() >= schema.key_columns
            && schema.kind == ReplayTableKind::Constructor
        {
            return Ok(Some(RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([cell.occurrence.fact]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            }));
        }
        if matches!(
            self.replay_term(cell.created.term)?,
            ReplayTerm::Literal { .. }
        ) {
            return Ok(Some(RawEqualitySupport {
                applied: Box::new([]),
                facts: Box::new([cell.occurrence.fact]),
                causes: Box::new([]),
                rekeys: Box::new([]),
            }));
        }
        let origin =
            self.exact_fact_cell_origin(cell.occurrence.fact, cell.occurrence.column.index(), 0)?;
        let origin = RawEqualitySupport {
            applied: Box::new([]),
            facts: Box::new([origin]),
            causes: Box::new([]),
            rekeys: Box::new([]),
        };
        let structural = self.explain_term_occurrence_at(
            cell.created.term,
            cell.created.sort,
            cell.created.raw,
            fact.position,
            cell.occurrence.fact,
            0,
        )?;
        Ok(Some(match structural {
            Some(structural) => combine_raw_equality_support([structural, origin]),
            None => origin,
        }))
    }

    fn exact_fact_cell_origin(
        &self,
        fact: FactId,
        column: usize,
        depth: usize,
    ) -> Result<FactId, ReceiptViewError> {
        if depth > 256 {
            return Err(ReceiptViewError::Invalid(
                "fact-cell structural origin exceeds 256 links".into(),
            ));
        }
        let record = self
            .arena
            .facts
            .get(
                (fact.get().checked_sub(1).ok_or_else(|| {
                    ReceiptViewError::Invalid("missing FactId has no structural origin".into())
                })?) as usize,
            )
            .and_then(Option::as_ref)
            .ok_or(ReceiptViewError::UnknownFact(fact))?;
        match record.origin {
            Some(FactOrigin::Site(_)) => Ok(fact),
            Some(FactOrigin::Fact(source)) => {
                self.exact_fact_cell_origin(source, column, depth + 1)
            }
            Some(FactOrigin::Merge {
                incoming,
                prior,
                cells,
            }) => {
                let cell = *self
                    .arena
                    .durable_merge_cell_origins
                    .get(cells.as_range())
                    .and_then(|cells| cells.get(column))
                    .ok_or_else(|| {
                        ReceiptViewError::Invalid(format!(
                            "merge origin for {fact:?} has no column {column}"
                        ))
                    })?;
                match cell {
                    MergeCellOrigin::Incoming(source) => match incoming {
                        Some(RowOriginRef::Site(_)) => Ok(fact),
                        Some(RowOriginRef::Fact(source_fact)) => {
                            self.exact_fact_cell_origin(source_fact, source as usize, depth + 1)
                        }
                        None => Err(ReceiptViewError::Invalid(format!(
                            "merge origin for {fact:?} lost incoming column {column}"
                        ))),
                    },
                    MergeCellOrigin::Prior(source) => {
                        self.exact_fact_cell_origin(prior, source as usize, depth + 1)
                    }
                    MergeCellOrigin::Unsupported => Err(ReceiptViewError::Invalid(format!(
                        "merge origin for {fact:?} synthesized column {column}"
                    ))),
                }
            }
            None => Err(ReceiptViewError::Invalid(format!(
                "fact {fact:?} column {column} has no structural origin"
            ))),
        }
    }

    /// Explain how one structural Call could be read at `desired_raw` without
    /// trusting final `(sort, value)` state. Exact producer facts are the base
    /// case. A constructor lookup that was a native no-op is reconstructed
    /// against a live compatible producer row, recursively retaining the
    /// child equalities that made its canonical key hit that row. This is a
    /// cold fact-graph walk over retained terms, not rule matching or replay.
    fn explain_term_occurrence_at(
        &mut self,
        term: ReplayTermId,
        sort: ReplaySortId,
        desired_raw: Value,
        position: HistoryPosition,
        excluded_fact: FactId,
        depth: usize,
    ) -> Result<Option<RawEqualitySupport>, ReceiptViewError> {
        if depth > 256 {
            return Err(ReceiptViewError::Invalid(
                "structural occurrence explanation exceeds 256 constructor levels".into(),
            ));
        }
        let ReplayTerm::Call {
            sort: term_sort,
            op,
            children: target_children,
        } = self.replay_term(term)?
        else {
            return Ok(None);
        };
        if term_sort != sort {
            return Err(ReceiptViewError::Invalid(
                "structural occurrence term has the wrong logical sort".into(),
            ));
        }
        let query = StructuralOccurrenceQuery {
            term,
            sort,
            raw: desired_raw,
            position,
            excluded_fact,
        };
        if let Some(cached) = self.occurrence_support_cache.get(&query) {
            return Ok(cached.clone());
        }

        // Production Call nodes have exactly two origins: registered table
        // constructors, or frontend-certified pure primitives with validators.
        // The latter are recomputed by `let-check` and deliberately have no
        // constructor FactId of their own. Ordered container builders are the
        // one structural exception: their identity depends on positional
        // EqSort children, so reconcile those child equalities through the
        // container anchor index before treating the call as available.
        if !self.is_registered_constructor_call(sort, op) {
            if !self.is_certified_replay_call(sort, op) {
                return Err(ReceiptViewError::Invalid(format!(
                    "structural call {op:?} for {sort:?} has no registered constructor or certified replay recipe"
                )));
            }
            let support = if self.replay_terms.container_child_sorts.contains_key(&sort) {
                self.explain_container_call_occurrence(
                    sort,
                    op,
                    &target_children,
                    desired_raw,
                    position,
                    depth,
                )?
            } else if self.is_equality_sort(sort, op) {
                self.explain_pure_eqsort_call_occurrence(
                    sort,
                    &target_children,
                    desired_raw,
                    position,
                    depth,
                )?
            } else {
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([]),
                    causes: Box::new([]),
                    rekeys: Box::new([]),
                }
            };
            self.occurrence_support_cache
                .insert(query, Some(support.clone()));
            return Ok(Some(support));
        }

        let possible = self.constructor_occurrence_facts(sort, op);
        let as_of = self.equality_edge_count_at(position)?;
        let sibling_cause = (!excluded_fact.is_missing())
            .then(|| self.fact(excluded_fact).map(|fact| fact.cause))
            .transpose()?;
        // Prefer an exact producer occurrence. This is the overwhelmingly
        // common path and needs no recursive child reconciliation. Iterate
        // newest-first because it is usually closest to the consumer's
        // historical landmark and therefore has the shortest raw path.
        for producer in possible.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if producer == excluded_fact {
                continue;
            }
            let later_sibling = fact.position > position && Some(fact.cause) == sibling_cause;
            if fact.position > position && !later_sibling {
                continue;
            }
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
                .ok_or(ReceiptViewError::UnknownTable(fact.table))?;
            let output = constructor.child_sorts.len();
            self.counters.equality_occurrence_terms_projected += 1;
            let produced_term = self
                .projector
                .fact_term(producer, output)
                .map_err(ReceiptViewError::Invalid)?;
            if produced_term != term {
                continue;
            }
            let output_support = if later_sibling {
                let creation_raw = *fact.values.get(output).ok_or_else(|| {
                    ReceiptViewError::Invalid(format!(
                        "constructor fact {producer:?} has no output column {output}"
                    ))
                })?;
                let support = match self.explain_raw_equality_support_at(
                    RawEqualityEndpoint {
                        sort,
                        raw: creation_raw,
                    },
                    RawEqualityEndpoint {
                        sort,
                        raw: desired_raw,
                    },
                    as_of,
                    position,
                ) {
                    Ok(support) => support,
                    Err(ReceiptViewError::Invalid(message))
                        if message
                            == "equality endpoints were disconnected at the historical landmark" =>
                    {
                        continue;
                    }
                    Err(error) => return Err(error),
                };
                (support, Vec::new().into_boxed_slice())
            } else {
                let Some((output_cell, support)) = self.producer_output_support(
                    producer,
                    output,
                    sort,
                    desired_raw,
                    as_of,
                    position,
                )?
                else {
                    continue;
                };
                (support, output_cell.rekeys)
            };
            let support = combine_raw_equality_support([
                output_support.0,
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    causes: Box::new([]),
                    rekeys: output_support.1,
                },
            ]);
            self.occurrence_support_cache
                .insert(query, Some(support.clone()));
            return Ok(Some(support));
        }

        // A successful constructor lookup may have inserted nothing because
        // canonicalized children hit a compatible older row. Reconstruct
        // only that case, recursively, and stop at the first exact support;
        // slicing needs a sound witness, not a minimum one.
        for producer in possible.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if producer == excluded_fact || fact.position > position {
                continue;
            }
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
                .ok_or(ReceiptViewError::UnknownTable(fact.table))?;
            let output = constructor.child_sorts.len();
            self.counters.equality_occurrence_terms_projected += 1;
            let produced_term = self
                .projector
                .fact_term(producer, output)
                .map_err(ReceiptViewError::Invalid)?;
            let ReplayTerm::Call {
                sort: produced_sort,
                op: produced_op,
                children: produced_children,
            } = self.replay_term(produced_term)?
            else {
                continue;
            };
            if produced_sort != sort
                || produced_op != op
                || produced_children.len() != target_children.len()
            {
                continue;
            }
            let Some((output_cell, output_support)) =
                self.producer_output_support(producer, output, sort, desired_raw, as_of, position)?
            else {
                continue;
            };
            let mut parts = vec![
                output_support,
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    causes: Box::new([]),
                    rekeys: output_cell.rekeys,
                },
            ];
            let mut compatible = true;
            for (column, (&target_child, &produced_child)) in target_children
                .iter()
                .zip(produced_children.iter())
                .enumerate()
            {
                if target_child == produced_child {
                    continue;
                }
                let target_node = self.replay_term(target_child)?;
                let produced_node = self.replay_term(produced_child)?;
                let (
                    ReplayTerm::Call {
                        sort: child_sort, ..
                    },
                    ReplayTerm::Call {
                        sort: produced_child_sort,
                        ..
                    },
                ) = (&target_node, &produced_node)
                else {
                    compatible = false;
                    break;
                };
                if child_sort != produced_child_sort
                    || constructor.child_sorts.get(column) != Some(child_sort)
                {
                    compatible = false;
                    break;
                }
                let child_cell = match self.fact_cell_at(
                    FactCellRef {
                        fact: producer,
                        column: crate::ColumnId::from_usize(column),
                    },
                    position,
                ) {
                    Ok(cell) => cell,
                    Err(ReceiptViewError::FactNoLongerLive { .. }) => {
                        compatible = false;
                        break;
                    }
                    Err(error) => return Err(error),
                };
                let child_support = self.explain_term_occurrence_at(
                    target_child,
                    *child_sort,
                    child_cell.endpoint.raw,
                    position,
                    producer,
                    depth + 1,
                )?;
                let Some(mut child_support) = child_support else {
                    compatible = false;
                    break;
                };
                let mut rekeys = child_support.rekeys.into_vec();
                rekeys.extend(child_cell.rekeys);
                child_support.rekeys = rekeys.into_boxed_slice();
                parts.push(child_support);
            }
            if !compatible {
                continue;
            }
            let support = combine_raw_equality_support(parts);
            self.occurrence_support_cache
                .insert(query, Some(support.clone()));
            return Ok(Some(support));
        }
        self.occurrence_support_cache.insert(query, None);
        Ok(None)
    }

    fn explain_equal_term_child_occurrences(
        &mut self,
        cell: &HistoricalFactCell,
    ) -> Result<Option<RawEqualitySupport>, ReceiptViewError> {
        let ReplayTerm::Call { sort, op, children } = self.replay_term(cell.created.term)? else {
            return Ok(None);
        };
        let position = self.fact(cell.occurrence.fact)?.position;
        let as_of = self.equality_edge_count_at(position)?;
        let possible = self.constructor_occurrence_facts(sort, op);
        let mut first_projection_error = None;
        for producer in possible.iter().rev().copied() {
            let fact = self.fact(producer)?;
            if producer == cell.occurrence.fact || fact.position > position {
                continue;
            }
            let constructor = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
                .ok_or(ReceiptViewError::UnknownTable(fact.table))?;
            let output = constructor.child_sorts.len();
            self.counters.equality_occurrence_terms_projected += 1;
            let produced_term = match self.projector.fact_term(producer, output) {
                Ok(term) => term,
                Err(error) => {
                    first_projection_error.get_or_insert(error);
                    continue;
                }
            };
            if produced_term != cell.created.term {
                continue;
            }
            let Some((output_cell, output_support)) = self.producer_output_support(
                producer,
                output,
                sort,
                cell.created.raw,
                as_of,
                position,
            )?
            else {
                continue;
            };
            let mut parts = vec![
                output_support,
                RawEqualitySupport {
                    applied: Box::new([]),
                    facts: Box::new([producer]),
                    causes: Box::new([]),
                    rekeys: output_cell.rekeys,
                },
            ];
            for (column, (&child, &child_sort)) in children
                .iter()
                .zip(constructor.child_sorts.iter())
                .enumerate()
            {
                let child_cell = self.fact_cell_at(
                    FactCellRef {
                        fact: producer,
                        column: crate::ColumnId::from_usize(column),
                    },
                    position,
                )?;
                if let Some(mut support) = self.explain_exact_term_occurrences_at(
                    child,
                    child_sort,
                    child_cell.endpoint.raw,
                    position,
                    producer,
                )? {
                    let mut rekeys = support.rekeys.into_vec();
                    rekeys.extend(child_cell.rekeys);
                    support.rekeys = rekeys.into_boxed_slice();
                    parts.push(support);
                }
            }
            return Ok(Some(combine_raw_equality_support(parts)));
        }
        if let Some(error) = first_projection_error {
            return Err(ReceiptViewError::Invalid(error));
        }
        Ok(None)
    }

    fn explain_same_raw_fact_occurrences(
        &mut self,
        left: &HistoricalFactCell,
        right: &HistoricalFactCell,
    ) -> Result<RawEqualitySupport, ReceiptViewError> {
        let left_support = match self.explain_fact_term_occurrence(left)? {
            Some(support) => support,
            None => {
                let producers = self.exact_term_producer_diagnostics(left.created.term);
                return Err(ReceiptViewError::Invalid(format!(
                    "left {} has no supported historical native occurrence; exact producers: {producers:?}",
                    self.describe_fact_cell(left),
                )));
            }
        };
        let right_support = match self.explain_fact_term_occurrence(right)? {
            Some(support) => support,
            None => {
                let producers = self.exact_term_producer_diagnostics(right.created.term);
                return Err(ReceiptViewError::Invalid(format!(
                    "right {} has no supported historical native occurrence; exact producers: {producers:?}",
                    self.describe_fact_cell(right),
                )));
            }
        };
        let mut parts = vec![left_support, right_support];
        if left.created.term == right.created.term {
            if let Some(support) = self.explain_equal_term_child_occurrences(left)? {
                parts.push(support);
            }
            if let Some(support) = self.explain_equal_term_child_occurrences(right)? {
                parts.push(support);
            }
        }
        Ok(combine_raw_equality_support(parts))
    }

    fn exact_term_producer_diagnostics(&mut self, term: ReplayTermId) -> Vec<String> {
        let Ok(ReplayTerm::Call { sort, op, .. }) = self.replay_term(term) else {
            return Vec::new();
        };
        let mut result = Vec::new();
        for producer in self.constructor_occurrence_facts(sort, op).iter().copied() {
            let Ok(fact) = self.fact(producer) else {
                continue;
            };
            let Some(constructor) = self
                .replay_terms
                .table_constructors
                .get(&fact.table)
                .map(|entry| entry.clone())
            else {
                continue;
            };
            let output = constructor.child_sorts.len();
            if self.projector.fact_term(producer, output).ok() == Some(term) {
                result.push(format!(
                    "{producer:?}@{:?} cause={:?}",
                    fact.position, fact.cause
                ));
                if result.len() == 16 {
                    break;
                }
            }
        }
        result
    }

    fn describe_fact_cell(&self, cell: &HistoricalFactCell) -> String {
        let fallback = || {
            format!(
                "fact cell {:?}:{} term {:?} at raw {:?}",
                cell.occurrence.fact,
                cell.occurrence.column.index(),
                cell.created.term,
                cell.created.raw,
            )
        };
        let Ok(fact) = self.fact(cell.occurrence.fact) else {
            return fallback();
        };
        let Ok(schema) = self.table_schema(fact.table) else {
            return fallback();
        };
        let Ok(term) = self.replay_term(cell.created.term) else {
            return fallback();
        };
        format!(
            "fact cell {:?}:{} in table {:?} ({:?}, {} key columns), term {:?}={term:?} at raw {:?}, created at {:?}, cause {:?}, row {:?}",
            cell.occurrence.fact,
            cell.occurrence.column.index(),
            fact.table,
            schema.kind,
            schema.key_columns,
            cell.created.term,
            cell.created.raw,
            fact.position,
            fact.cause,
            fact.values,
        )
    }
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
    view_active: AtomicBool,
    replay_terms: ReplayTermStore,
    equality_value_sorts: Mutex<HashMap<Value, ReplaySortId>>,
    equality_wave_timestamp: Mutex<Option<(CausalWave, Value)>>,
    /// One canonical source-order binding recipe per source-level rule.
    rule_binding_recipes: RwLock<HashMap<u32, Arc<[ReplayBindingSource]>>>,
    /// Every exact premise-cell/constant equality enforced by the lowered
    /// native query, including compiler-generated variables.
    rule_equality_recipes:
        RwLock<HashMap<u32, Arc<[(ReplayEqualitySource, ReplayEqualitySource)]>>>,
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
            view_active: AtomicBool::new(false),
            replay_terms: ReplayTermStore::default(),
            equality_value_sorts: Mutex::new(HashMap::default()),
            equality_wave_timestamp: Mutex::new(None),
            rule_binding_recipes: RwLock::new(HashMap::default()),
            rule_equality_recipes: RwLock::new(HashMap::default()),
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
    equalities: Vec<(AppliedEqualityId, PendingEquality)>,
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
            .into()
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
    ) -> AppliedEqualityId {
        assert!(
            !cause.is_unattributed(),
            "applied union is missing exact causal attribution"
        );
        let id = AppliedEqualityId::new(ReceiptShared::alloc_u64(&self.shared.next_equality, 1));
        let position = HistoryPosition::new(ReceiptShared::alloc_u64(&self.shared.next_history, 1));
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
            for (id, draft) in self.drafts.drain(..) {
                let equality = self
                    .draft_summaries
                    .remove(&id)
                    .expect("local merge draft has no cached equality classification");
                let durable = match draft {
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
    /// FactId and does not promote its rule match.
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

    /// Validate one effective keyed-row removal before native state changes.
    /// Missing rows never reach this method. Source/top-level removals have no
    /// originating rule and therefore fail closed before staging can commit.
    pub(crate) fn prepare_removal(
        &self,
        table: TableId,
        wave: CausalWave,
        removed_fact: FactId,
        cause: &DeferredEqualityCause,
    ) -> Result<PreparedRemoval, String> {
        if removed_fact.is_missing() {
            return Err("effective removal has no immutable victim FactId".into());
        }
        cause.prepare(self, wave)?;
        let cause = cause.originating_rule().ok_or_else(|| {
            "causal receipts support named-rule removals only; source/top-level removal is unsupported"
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
        wave: CausalWave,
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
                } => tracked.push(RemovalRecord {
                    wave,
                    position: HistoryPosition::new(ReceiptShared::alloc_u64(
                        &self.0.next_history,
                        1,
                    )),
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
        wave: CausalWave,
        premises: &[FactId],
        equalities: &[(EqualityEndpoint, EqualityEndpoint)],
        equality_occurrences: &[(CheckEndpointOccurrence, CheckEndpointOccurrence)],
        as_of_edges: EqualityEdgeCount,
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
                    CheckEndpointOccurrence::FactCell(left),
                    CheckEndpointOccurrence::FactCell(right),
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
                CheckEndpointOccurrence::FactCell(cell) => Some(cell.fact),
                CheckEndpointOccurrence::Current => None,
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
                equality_occurrences: equality_occurrences.into(),
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

    /// Borrow a checked view of finalized raw receipts. The closure cannot
    /// return references tied to the arena guards, so no receipt storage or
    /// static recipe can escape its read boundary.
    pub fn with_view<R>(
        &self,
        inspect: impl for<'view> FnOnce(&mut CausalReceiptView<'view>) -> Result<R, ReceiptViewError>,
    ) -> Result<R, ReceiptViewError> {
        let _active = ActiveReceiptViewGuard::enter(&self.0.view_active)?;
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0 {
            return Err(ReceiptViewError::NotFinalized("a rule execution panicked"));
        }
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err(ReceiptViewError::NotFinalized(
                "worker receipt fragments remain open",
            ));
        }
        if self.0.open_native_leases.load(Ordering::Acquire) != 0 {
            return Err(ReceiptViewError::NotFinalized(
                "transactional native mutations remain queued",
            ));
        }
        if self.0.abandoned_fragments.load(Ordering::Acquire) != 0 {
            return Err(ReceiptViewError::NotFinalized(
                "a worker receipt fragment was abandoned",
            ));
        }
        let recipes = self
            .0
            .rule_binding_recipes
            .read()
            .map_err(|_| ReceiptViewError::Poisoned("rule binding recipes"))?;
        let equality_recipes = self
            .0
            .rule_equality_recipes
            .read()
            .map_err(|_| ReceiptViewError::Poisoned("rule equality recipes"))?;
        let term_recipes = self
            .0
            .static_term_recipes
            .lock()
            .map_err(|_| ReceiptViewError::Poisoned("static term recipes"))?;
        let arena = self
            .0
            .arena
            .lock()
            .map_err(|_| ReceiptViewError::Poisoned("receipt arena"))?;
        if self.0.poisoned_rule_executions.load(Ordering::Acquire) != 0
            || self.0.open_fragments.load(Ordering::Acquire) != 0
            || self.0.open_native_leases.load(Ordering::Acquire) != 0
            || self.0.abandoned_fragments.load(Ordering::Acquire) != 0
        {
            return Err(ReceiptViewError::NotFinalized(
                "capture state changed while acquiring the receipt view",
            ));
        }
        let expected = [
            (
                arena.published_facts,
                self.0.next_fact.load(Ordering::Acquire),
                "fact",
            ),
            (
                arena.published_matches,
                self.0.next_rule_match.load(Ordering::Acquire),
                "match",
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
            return Err(ReceiptViewError::NotFinalized(match kind {
                "fact" => "fact publication has an ID hole",
                "match" => "match publication has an ID hole",
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
            .ok_or_else(|| ReceiptViewError::Invalid("receipt history count overflow".into()))?;
        if history_boundary.get() != expected_history {
            return Err(ReceiptViewError::NotFinalized(
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
        let mut view = CausalReceiptView {
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
            counters: CausalReceiptViewCounters::default(),
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn receipt_view_rejects_reentrancy_without_poisoning_capture() {
        let receipts = CausalReceipts::default();
        let error = receipts
            .with_view(|_| receipts.with_view(|_| Ok(())))
            .unwrap_err();
        assert!(matches!(
            error,
            ReceiptViewError::Invalid(ref message) if message.contains("not reentrant")
        ));
        receipts
            .with_view(|_| {
                std::thread::scope(|scope| {
                    let nested = scope
                        .spawn(|| receipts.with_view(|_| Ok(())))
                        .join()
                        .unwrap();
                    assert!(matches!(
                        nested,
                        Err(ReceiptViewError::Invalid(ref message))
                            if message.contains("not reentrant")
                    ));
                });
                Ok(())
            })
            .unwrap();
        assert!(receipts.with_view(|_| Ok(())).is_ok());
    }

    #[test]
    fn panicking_receipt_view_callback_does_not_poison_capture_locks() {
        let receipts = CausalReceipts::default();
        let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = receipts
                .with_view(|_| -> Result<(), ReceiptViewError> { panic!("inspection panic") });
        }));
        assert!(failure.is_err());
        assert!(receipts.with_view(|_| Ok(())).is_ok());
    }

    #[test]
    fn physical_rekey_collision_with_same_fact_records_no_logical_transition() {
        let receipts = CausalReceipts::default();
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
                CausalWave::new(2),
                fact,
                EqualityEdgeCount::new(1),
                HistoryPosition::new(9),
                &[pair],
            )
        };

        receipts.commit_prepared_rekey(prepared(), RekeyOutcome::Absorbed(fact));
        receipts.commit_prepared_rekey(prepared(), RekeyOutcome::Replaced(fact));

        assert!(receipts.0.arena.lock().unwrap().rekeys.is_empty());
        assert_eq!(receipts.history_boundary(), HistoryPosition::new(0));

        receipts.commit_prepared_rekey(prepared(), RekeyOutcome::Absorbed(FactId::new(18)));
        assert_eq!(receipts.0.arena.lock().unwrap().rekeys.len(), 1);
        assert_eq!(receipts.history_boundary(), HistoryPosition::new(1));
    }

    #[test]
    fn structural_occurrence_rejects_uncertified_non_table_calls() {
        let receipts = CausalReceipts::default();
        let sort = ReplaySortId::new(1);
        let certified_op = ReplayOpId::new(10);
        let unknown_op = ReplayOpId::new(11);
        let certified_raw = Value::new_const(10);
        let unknown_raw = Value::new_const(11);
        let certified_term = receipts
            .intern_call(sort, certified_op, &[], certified_raw)
            .unwrap();
        let unknown_term = receipts
            .intern_call(sort, unknown_op, &[], unknown_raw)
            .unwrap();
        receipts.register_rule_term_recipe(
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

        receipts
            .with_view(|view| {
                let support = view.explain_term_occurrence_at(
                    certified_term,
                    sort,
                    certified_raw,
                    HistoryPosition::new(0),
                    FactId::MISSING,
                    0,
                )?;
                assert!(
                    support.is_some(),
                    "a certified pure call reexecutes in replay"
                );
                Ok(())
            })
            .unwrap();

        let error = receipts
            .with_view(|view| {
                view.explain_term_occurrence_at(
                    unknown_term,
                    sort,
                    unknown_raw,
                    HistoryPosition::new(0),
                    FactId::MISSING,
                    0,
                )
            })
            .unwrap_err();
        assert!(
            matches!(error, ReceiptViewError::Invalid(ref message) if message.contains("no registered constructor or certified replay recipe")),
            "unknown non-table calls must fail closed: {error:?}"
        );
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
        receipts
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
        let [(lane, rule_cause)] = receipts
            .register_rule_matches(7, CausalWave::new(1), 1, &binding_sources, &[source], &[0])
            .try_into()
            .unwrap();
        assert_eq!(lane, 0);
        let mut derived_batch = receipts.new_batch();
        let derived = derived_batch.record_fact_with_origin(table, rule_cause, &row, origin);
        derived_batch.publish();
        receipts.finalize_wave();

        receipts
            .with_view(|view| {
                assert_eq!(
                    view.fact_terms(derived)?.as_ref(),
                    &terms,
                    "fact terms belong to the immutable committed row, not its Source cause"
                );
                Ok(())
            })
            .unwrap();

        let [(lane, next_cause)] = receipts
            .register_rule_matches(8, CausalWave::new(2), 1, &binding_sources, &[derived], &[0])
            .try_into()
            .unwrap();
        assert_eq!(lane, 0);
        let mut next_batch = receipts.new_batch();
        next_batch.record_fact_with_origin(table, next_cause, &row, origin);
        next_batch.publish();
        receipts.finalize_wave();
        receipts
            .with_view(|view| {
                let next_match = (1..=view.totals().matches)
                    .map(RuleMatchId::new)
                    .find(|id| view.matched(*id).is_ok_and(|matched| matched.rule == 8))
                    .unwrap();
                assert_eq!(
                    view.match_terms(next_match)?.as_ref(),
                    &terms,
                    "a later rule must resolve terms through a derived FactId"
                );
                Ok(())
            })
            .unwrap();
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

        receipts
            .with_view(|view| {
                assert_eq!(
                    view.match_terms(RuleMatchId::new(1))?.as_ref(),
                    &[source_term, constant_term, current_term],
                    "lazy expansion must preserve the complete binding layout"
                );
                let counters = view.counters();
                assert_eq!(counters.logical_match_term_handles, 3);
                assert_eq!(counters.stored_match_term_handles, 0);
                assert_eq!(
                    counters.logical_match_term_bytes,
                    3 * mem::size_of::<ReplayTermId>() as u64
                );
                assert_eq!(counters.stored_match_term_bytes, 0);
                assert_eq!(counters.logical_match_term_handles, 3);
                Ok(())
            })
            .unwrap();
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
