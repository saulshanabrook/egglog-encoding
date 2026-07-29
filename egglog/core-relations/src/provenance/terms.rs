//! Typed structural terms and their concurrent trace-time interner.

use super::*;

/// Backend-neutral payload for one structural literal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReplayLiteral {
    /// The unit literal.
    Unit,
    /// A Boolean literal.
    Bool(
        /// Source-level Boolean value.
        bool,
    ),
    /// A signed 64-bit integer literal.
    I64(
        /// Source-level integer value.
        i64,
    ),
    /// A 64-bit floating-point literal stored by bits to preserve exact identity.
    F64(
        /// [`f64::to_bits`] representation of the source-level value.
        u64,
    ),
    /// An owned source-level string literal.
    String(
        /// Shared string contents independent of the native value arena.
        Arc<str>,
    ),
}

/// One compact typed node in the replay-term DAG.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReplayTerm {
    /// A typed leaf whose payload has a source-independent representation.
    Literal {
        /// Logical sort of the literal.
        sort: ReplaySortId,
        /// Backend-neutral literal payload.
        literal: ReplayLiteral,
    },
    /// A typed structural operation applied to ordered child terms.
    Call {
        /// Logical result sort of the call.
        sort: ReplaySortId,
        /// Frontend-assigned operation or constructor identity.
        op: ReplayOpId,
        /// Ordered child nodes in the shared replay-term DAG.
        children: Arc<[ReplayTermId]>,
    },
}

/// Static typing and capture policy for one structural call producer.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReplayConstructorSpec {
    /// Logical sort produced by the call.
    pub result_sort: ReplaySortId,
    /// Frontend identity of the operation or constructor.
    pub op: ReplayOpId,
    /// Logical sorts of the call arguments in evaluation order.
    pub child_sorts: Box<[ReplaySortId]>,
    /// Whether a container primitive's structural version is anchored as soon
    /// as the primitive returns, before later query guards can reject the lane.
    anchor_on_primitive_return: bool,
    /// Physical registry type for a container result. This is intentionally
    /// absent for ordinary e-class constructors and base-value primitives and
    /// does not itself imply return-time anchoring.
    pub(super) container_type: Option<TypeId>,
}

impl ReplayConstructorSpec {
    /// Creates a static structural call specification with no container registry type.
    pub fn new(
        result_sort: ReplaySortId,
        op: ReplayOpId,
        child_sorts: impl IntoIterator<Item = ReplaySortId>,
    ) -> Self {
        Self {
            result_sort,
            op,
            child_sorts: child_sorts.into_iter().collect(),
            anchor_on_primitive_return: false,
            container_type: None,
        }
    }

    /// Registers the physical container registry used for versioned anchor tracking.
    ///
    /// This only identifies container storage; it does not request return-time
    /// anchoring before later query guards.
    pub fn with_container_type(mut self, container_type: TypeId) -> Self {
        self.container_type = Some(container_type);
        self
    }

    /// Mark a container-producing primitive for return-time version anchoring.
    ///
    /// Combining the timing policy with its physical container type makes the
    /// invalid state “return-time anchoring without a container” unrepresentable.
    pub fn with_primitive_return_anchor(mut self, container_type: TypeId) -> Self {
        self.container_type = Some(container_type);
        self.anchor_on_primitive_return = true;
        self
    }

    /// Whether this specification anchors a container primitive on return.
    pub fn anchors_on_primitive_return(&self) -> bool {
        self.anchor_on_primitive_return
    }
}

/// Static structural origin of one column in an effective merge result.
/// The bridge derives this once from the source merge expression; native
/// capture stores only the resolved column references for changed facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MergeOriginSelector {
    /// The merged output cell preserves one cell of the incoming row.
    Incoming {
        /// Physical incoming-row column supplying the structural origin.
        column: u16,
    },
    /// The merged output cell preserves one cell of the previously live row.
    Prior {
        /// Physical prior-row column supplying the structural origin.
        column: u16,
    },
    /// `UnionId` returns the lower native id, choosing the prior value when
    /// both inputs are already identical.
    NativeMin {
        /// Incoming-row column compared by native id.
        incoming_column: u16,
        /// Prior-row column compared by native id.
        prior_column: u16,
    },
    /// The callback result must be exactly one of its two input cells. The
    /// native result decides which structural origin won; equal inputs choose
    /// the prior origin deterministically. This supports semantic min/max on
    /// base values without comparing their opaque runtime Value ids.
    PriorOrIncoming {
        /// Incoming-row column that may have supplied the callback result.
        incoming_column: u16,
        /// Prior-row column that may have supplied the callback result.
        prior_column: u16,
    },
    /// The merge expression has no exact structural-origin rule and must fail closed if needed.
    Unsupported,
}

impl ReplayTerm {
    /// Returns the logical result sort stored by either term variant.
    pub fn sort(&self) -> ReplaySortId {
        match self {
            Self::Literal { sort, .. } | Self::Call { sort, .. } => *sort,
        }
    }
}

#[derive(Default)]
pub(super) struct TermInterner {
    by_node: RwLock<HashMap<ReplayTerm, ReplayTermId>>,
    nodes: RwLock<HashMap<ReplayTermId, ReplayTerm>>,
    by_value: RwLock<HashMap<(ReplaySortId, Value), ReplayTermId>>,
    /// Sparse exact structural versions for mutable ordered-container ids.
    /// Ordinary `by_value` remains first-wins for cheap generic lookup; only
    /// supported container paths enumerate this side index.
    container_anchors: RwLock<HashMap<(ReplaySortId, Value), SmallVec<[ReplayTermId; 2]>>>,
    original_value_by_term: RwLock<HashMap<(ReplaySortId, ReplayTermId), Value>>,
    pub(super) table_layouts: DashMap<TableId, Arc<[Option<ReplaySortId>]>>,
    pub(super) table_kinds: DashMap<TableId, ReplayTableKind>,
    pub(super) table_key_columns: DashMap<TableId, u16>,
    pub(super) table_constructors: DashMap<TableId, ReplayConstructorSpec>,
    pub(super) table_merge_origins: DashMap<TableId, Arc<[MergeOriginSelector]>>,
    pub(super) table_merge_identity_guards: DashMap<TableId, (u16, u16)>,
    pub(super) container_type_by_sort: DashMap<ReplaySortId, TypeId>,
    pub(super) container_child_sorts: DashMap<ReplaySortId, Arc<[ReplaySortId]>>,
}

impl TermInterner {
    pub(super) fn intern(&self, next_term: &AtomicU32, node: ReplayTerm) -> ReplayTermId {
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

    pub(super) fn node(&self, id: ReplayTermId) -> Option<ReplayTerm> {
        self.nodes.read().unwrap().get(&id).cloned()
    }

    pub(super) fn install_value(
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

    pub(super) fn lookup(&self, sort: ReplaySortId, value: Value) -> Option<ReplayTermId> {
        self.by_value.read().unwrap().get(&(sort, value)).copied()
    }

    pub(super) fn install_container_anchor(
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

    pub(super) fn container_anchors(
        &self,
        sort: ReplaySortId,
        value: Value,
    ) -> SmallVec<[ReplayTermId; 2]> {
        self.container_anchors
            .read()
            .unwrap()
            .get(&(sort, value))
            .cloned()
            .unwrap_or_default()
    }

    pub(super) fn container_anchors_with_journal(
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

    pub(super) fn stage_container_anchor_transfer(
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

    pub(super) fn validate_container_anchor_journal(
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

    pub(super) fn publish_container_anchor_journal(&self, journal: ContainerAnchorJournal) {
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

    pub(super) fn compatible_call_pairs(
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

    pub(super) fn original_value(&self, sort: ReplaySortId, term: ReplayTermId) -> Option<Value> {
        self.original_value_by_term
            .read()
            .unwrap()
            .get(&(sort, term))
            .copied()
    }

    pub(super) fn table_layout(&self, table: TableId) -> Option<Arc<[Option<ReplaySortId>]>> {
        self.table_layouts
            .get(&table)
            .map(|layout| Arc::clone(&layout))
    }

    pub(super) fn register_table_layout(
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

    pub(super) fn register_table_kind(
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

    pub(super) fn register_table_key_columns(
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

    pub(super) fn register_table_constructor(
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

    pub(super) fn register_table_merge_origins(
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

    pub(super) fn register_container_type(
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

    pub(super) fn register_container_sort(
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

    pub(super) fn install_source_row(
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
}

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
    /// This is resolved against immutable trace history, never final state.
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
pub(super) struct StaticTermRecipeStore {
    pub(super) rules: HashMap<u32, Arc<TermRecipe>>,
    pub(super) row_origins: Vec<RowOriginSpec>,
    pub(super) term_origins: Vec<TermOriginSpec>,
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
        representative: PremiseOccurrence,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ActionCaptureKind {
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
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CheckEndpointSpec {
    pub(crate) value: QueryEntry,
    pub(crate) sort: ReplaySortId,
    pub(crate) term: CheckTermSource,
}

#[derive(Clone, Debug)]
pub(crate) struct ActionCaptureSpec {
    pub(crate) kind: ActionCaptureKind,
    pub(crate) premise_count: usize,
    pub(crate) premise_slots: Arc<DenseIdMap<AtomId, PremiseSlot>>,
    /// One exact term source for every ordinary variable, in source order.
    pub(crate) binding_sources: Arc<[ReplayBindingSource]>,
}

impl ActionCaptureSpec {
    pub(crate) fn captures_witness(&self) -> bool {
        self.premise_count != 0
    }
}
