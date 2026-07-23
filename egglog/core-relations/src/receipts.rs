//! Compact causal receipts recorded at native execution sites.
//!
//! Provisional matches and cause nodes are wave-local. Native workers append
//! to local [`ReceiptBatch`] fragments and publish once at an existing table
//! or union-find barrier. Finalization promotes only cause nodes reachable from
//! effective facts and applied unions, then drops the complete provisional
//! segment.

use std::{
    any::TypeId,
    mem,
    sync::{
        Arc, Mutex, OnceLock,
        atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering},
    },
};

use dashmap::mapref::entry::Entry;
use smallvec::SmallVec;

use crate::{
    AtomId, QueryEntry, TableId, Value, Variable,
    common::{DashMap, HashMap},
    numeric_id::{DenseIdMap, NumericId},
};

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
handle!(EqualityEdgeCount, u64);
handle!(CausalWave, u64);
handle!(CauseDraftId, u64);
handle!(MatchDraftId, u64);
handle!(DurableCauseId, u32);

/// Stable index into the snapshot-owned, shared causal DAG.
pub type ReceiptCauseId = DurableCauseId;

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
    sorts_by_value: DashMap<Value, SmallVec<[ReplaySortId; 2]>>,
    original_value_by_term: DashMap<(ReplaySortId, ReplayTermId), Value>,
    table_layouts: DashMap<TableId, Arc<[Option<ReplaySortId>]>>,
    table_constructors: DashMap<TableId, ReplayConstructorSpec>,
    container_type_by_sort: DashMap<ReplaySortId, TypeId>,
    container_child_sorts: DashMap<ReplaySortId, Arc<[ReplaySortId]>>,
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

    fn lookup_node(&self, node: &ReplayTerm) -> Option<ReplayTermId> {
        self.by_node.get(node).map(|term| *term)
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
        let installed = match self.by_value.entry((sort, value)) {
            Entry::Occupied(entry) => Ok(*entry.get()),
            Entry::Vacant(entry) => {
                entry.insert(term);
                Ok(term)
            }
        }?;
        let mut sorts = self.sorts_by_value.entry(value).or_default();
        if !sorts.contains(&sort) {
            sorts.push(sort);
        }
        self.original_value_by_term
            .entry((sort, term))
            .or_insert(value);
        Ok(installed)
    }

    fn lookup(&self, sort: ReplaySortId, value: Value) -> Option<ReplayTermId> {
        self.by_value.get(&(sort, value)).map(|term| *term)
    }

    fn common_compatible_call_sorts(
        &self,
        left: Value,
        right: Value,
    ) -> Result<SmallVec<[ReplaySortId; 2]>, &'static str> {
        let Some(left_sorts) = self.sorts_by_value.get(&left) else {
            return Err("left container id has no installed replay sort");
        };
        let Some(right_sorts) = self.sorts_by_value.get(&right) else {
            return Err("right container id has no installed replay sort");
        };
        let common = left_sorts
            .iter()
            .copied()
            .filter(|sort| right_sorts.contains(sort))
            .filter(|sort| {
                let Some(left_term) = self.lookup(*sort, left) else {
                    return false;
                };
                let Some(right_term) = self.lookup(*sort, right) else {
                    return false;
                };
                matches!(
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
                )
            })
            .collect::<SmallVec<[_; 2]>>();
        Ok(common)
    }

    fn original_value(&self, sort: ReplaySortId, term: ReplayTermId) -> Option<Value> {
        self.original_value_by_term
            .get(&(sort, term))
            .map(|value| *value)
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

    fn validate_row_terms(
        &self,
        table: TableId,
        row: &[Value],
        terms: &[ReplayTermId],
    ) -> Result<(), &'static str> {
        let Some(layout) = self.table_layouts.get(&table) else {
            return Err("table has no replay-term layout");
        };
        if layout.len() != row.len() || row.len() != terms.len() {
            return Err("committed row, structural terms, and table layout have different arities");
        }
        for (sort, term) in layout.iter().copied().zip(terms) {
            match sort {
                Some(sort) => {
                    let node = self
                        .nodes
                        .get(term)
                        .ok_or("committed row owns an unknown ReplayTermId")?;
                    if node.sort() != sort {
                        return Err("committed row term has the wrong logical sort");
                    }
                }
                None if !term.is_missing() => {
                    return Err("engine-only committed row column has a replay term");
                }
                None => {}
            }
        }
        if let Some(constructor) = self.table_constructors.get(&table) {
            let output_column = constructor.child_sorts.len();
            let output_term = *terms
                .get(output_column)
                .ok_or("constructor row has no structural result term")?;
            let Some(ReplayTerm::Call { sort, op, children }) = self.node(output_term) else {
                return Err("constructor row result does not name a structural Call");
            };
            if sort != constructor.result_sort
                || op != constructor.op
                || children.as_ref() != &terms[..output_column]
            {
                return Err("constructor row terms are not one coherent structural Call");
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
        if let Some(constructor) = self.table_constructors.get(&table) {
            let output_column = constructor.child_sorts.len();
            let output = *row
                .get(output_column)
                .ok_or("constructor row has no result column")?;
            let output_term = self
                .lookup(constructor.result_sort, output)
                .ok_or("constructor row result has no producer-installed ReplayTermId")?;
            let Some(ReplayTerm::Call { sort, op, children }) = self.node(output_term) else {
                out.truncate(start);
                return Err("constructor row result does not name a structural Call");
            };
            if sort != constructor.result_sort
                || op != constructor.op
                || children.len() != constructor.child_sorts.len()
            {
                out.truncate(start);
                return Err("constructor row result has incompatible structural Call metadata");
            }
            for (child, expected_sort) in children
                .iter()
                .copied()
                .zip(constructor.child_sorts.iter().copied())
            {
                let child_sort = self
                    .node(child)
                    .ok_or("constructor row Call has an unknown child ReplayTermId")?
                    .sort();
                if child_sort != expected_sort {
                    out.truncate(start);
                    return Err("constructor row Call child has the wrong logical sort");
                }
            }
            out[start..start + output_column].copy_from_slice(&children);
            out[start + output_column] = output_term;
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
pub(crate) enum ReplayBindingSource {
    Premise {
        premise: usize,
        column: usize,
    },
    Current {
        variable: Variable,
        sort: ReplaySortId,
    },
    Constant {
        term: ReplayTermId,
    },
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
    pub(crate) binding_sources: Box<[ReplayBindingSource]>,
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
    pub(crate) dependency: ContainerDependency,
}

#[derive(Clone)]
pub(crate) struct ContainerParentCandidate {
    pub(crate) endpoint: EqualityEndpoint,
    pub(crate) child_sorts: Arc<[ReplaySortId]>,
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
    pub cause: FactCause,
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
    Cause(ReceiptCauseId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiptCauseRecord {
    Source(SourceRef),
    Rule(RuleMatchId),
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
        incoming: ReceiptCauseId,
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
        equalities: &'a [TypedCellEquality],
    },
    ContainerCanonicalize {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        equalities: &'a [TypedCellEquality],
    },
    ContainerRefresh {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        equalities: &'a [TypedCellEquality],
    },
}

enum CauseDependencyItem {
    Cause(ReceiptCauseId),
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
                CauseDependencyItem::Cause(cause) => {
                    match &self.causes[(cause.get() - 1) as usize] {
                        ReceiptCauseRecord::Source(source) => {
                            return Some(ReceiptCauseDependency::Source(source));
                        }
                        ReceiptCauseRecord::Rule(rule) => {
                            return Some(ReceiptCauseDependency::Rule(*rule));
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
                                equalities: &equalities.pairs,
                            });
                        }
                        ReceiptCauseRecord::ContainerCanonicalize { wave, equalities } => {
                            return Some(ReceiptCauseDependency::ContainerCanonicalize {
                                wave: *wave,
                                as_of_edges: equalities.as_of_edges,
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
    /// Dense applied-edge prefix visible when this rebuild row was recorded.
    pub as_of_edges: EqualityEdgeCount,
    pub pairs: Box<[TypedCellEquality]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EqComponentRef {
    Term(ReplayTermId),
    Node(EqNodeId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqNodeRecord {
    pub id: EqNodeId,
    pub left: EqComponentRef,
    pub right: EqComponentRef,
    pub edge: EqualityEdgeId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualityRecord {
    pub id: EqualityEdgeId,
    pub wave: CausalWave,
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
    pub left: EqualityEndpoint,
    pub right: EqualityEndpoint,
    pub native_parent: crate::Value,
    pub native_child: crate::Value,
    pub reason: EqualityReason,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReceiptCounters {
    pub provisional_matches: u64,
    pub promoted_matches: u64,
    pub premise_handles: u64,
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
}

#[derive(Clone, Debug, Default)]
pub struct ReceiptSnapshot {
    pub facts: Vec<FactRecord>,
    pub matches: Vec<MatchRecord>,
    pub equality_nodes: Vec<EqNodeRecord>,
    pub equalities: Vec<EqualityRecord>,
    pub native_aliases: Vec<NativeAliasRecord>,
    pub causes: Vec<ReceiptCauseRecord>,
    pub check_roots: Vec<CheckRoot>,
    pub counters: ReceiptCounters,
}

impl ReceiptSnapshot {
    pub fn cause_dependencies(&self, root: ReceiptCauseId) -> ReceiptCauseDependencies<'_> {
        assert!(
            root.get() > 0 && root.get() as usize <= self.causes.len(),
            "receipt cause root is outside this snapshot"
        );
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
    pub fn explain_equality(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
        as_of: EqualityEdgeCount,
    ) -> Result<Box<[EqualityEdgeId]>, &'static str> {
        self.equality_explanation_index(as_of)?
            .explain_equality(left, right)
    }

    /// Build one immutable forest index for a historical cutoff. A slicer
    /// should reuse this value for every changed-cell pair at that cutoff;
    /// membership checks during explanation are constant-time interval tests.
    pub fn equality_explanation_index(
        &self,
        as_of: EqualityEdgeCount,
    ) -> Result<EqualityExplanationIndex<'_>, &'static str> {
        EqualityExplanationIndex::new(self, as_of)
    }
}

pub struct EqualityExplanationIndex<'a> {
    snapshot: &'a ReceiptSnapshot,
    cutoff: usize,
    term_positions: HashMap<ReplayTermId, (EqNodeId, usize)>,
    node_intervals: Vec<Option<(usize, usize)>>,
}

impl<'a> EqualityExplanationIndex<'a> {
    fn new(snapshot: &'a ReceiptSnapshot, as_of: EqualityEdgeCount) -> Result<Self, &'static str> {
        let cutoff: usize = as_of
            .get()
            .try_into()
            .map_err(|_| "equality landmark exceeds addressable receipt storage")?;
        if cutoff > snapshot.equality_nodes.len() || cutoff > snapshot.equalities.len() {
            return Err("equality landmark exceeds the recorded applied-edge prefix");
        }

        let mut term_parents = HashMap::default();
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
                    EqComponentRef::Term(term) => {
                        if term.is_missing() || term_parents.insert(term, node.id).is_some() {
                            return Err("equality forest term has multiple parents");
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
        let mut term_positions = HashMap::default();
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
                    Visit::Enter(EqComponentRef::Term(term), root) => {
                        if term_positions.insert(term, (root, next_position)).is_some() {
                            return Err("equality forest term occurs in more than one leaf");
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

        Ok(Self {
            snapshot,
            cutoff,
            term_positions,
            node_intervals,
        })
    }

    pub fn explain_equality(
        &self,
        left: EqualityEndpoint,
        right: EqualityEndpoint,
    ) -> Result<Box<[EqualityEdgeId]>, &'static str> {
        if left.sort != right.sort {
            return Err("cannot explain equality across logical sorts");
        }
        if left.term.is_missing() || right.term.is_missing() {
            return Err("cannot explain equality with a missing ReplayTermId");
        }
        if left.term == right.term {
            return Ok(Box::new([]));
        }

        let Some(left_root) = self.root(left.term) else {
            return Err("left equality endpoint is absent from the historical forest");
        };
        let Some(right_root) = self.root(right.term) else {
            return Err("right equality endpoint is absent from the historical forest");
        };
        if left_root != right_root {
            return Err("equality endpoints were disconnected at the historical landmark");
        }
        self.explain(left_root, left.term, right.term, left.sort)
    }

    fn root(&self, term: ReplayTermId) -> Option<EqComponentRef> {
        self.term_positions
            .get(&term)
            .map(|(root, _)| EqComponentRef::Node(*root))
    }

    fn contains(&self, component: EqComponentRef, term: ReplayTermId) -> bool {
        match component {
            EqComponentRef::Term(expected) => expected == term,
            EqComponentRef::Node(node) => {
                let Some((_, position)) = self.term_positions.get(&term) else {
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
        left: ReplayTermId,
        right: ReplayTermId,
        sort: ReplaySortId,
    ) -> Result<Box<[EqualityEdgeId]>, &'static str> {
        enum Task {
            Pair {
                component: EqComponentRef,
                left: ReplayTermId,
                right: ReplayTermId,
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
                return Err("distinct terms reached one leaf in the equality forest");
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
            if !self.contains(node.left, equality.left.term)
                || !self.contains(node.right, equality.right.term)
            {
                return Err("applied edge endpoints do not belong to their recorded components");
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
                    left: equality.right.term,
                    right,
                });
                tasks.push(Task::Edge(equality.id));
                tasks.push(Task::Pair {
                    component: node.left,
                    left,
                    right: equality.left.term,
                });
            } else if left_in_right && right_in_left {
                tasks.push(Task::Pair {
                    component: node.left,
                    left: equality.left.term,
                    right,
                });
                tasks.push(Task::Edge(equality.id));
                tasks.push(Task::Pair {
                    component: node.right,
                    left,
                    right: equality.right.term,
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
#[doc(hidden)]
pub struct TypedEqualityProposal {
    wave: CausalWave,
    left: EqualityEndpoint,
    right: EqualityEndpoint,
}

impl TypedEqualityProposal {
    pub(crate) fn wave(self) -> CausalWave {
        self.wave
    }

    pub(crate) fn left(self) -> EqualityEndpoint {
        self.left
    }

    pub(crate) fn right(self) -> EqualityEndpoint {
        self.right
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct AppliedEqualityProposal {
    pub(crate) wave: CausalWave,
    pub(crate) left: EqualityEndpoint,
    pub(crate) right: EqualityEndpoint,
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
    native_ordinal: u64,
    premises: FlatRange,
    terms: FlatRange,
    merge_reads: Option<PendingMergeReadRef>,
}

/// One compact sidecar shared by every lane in an action batch. Only lanes
/// that actually invoke a merge callback allocate map entries; ordinary
/// candidates and unchanged-merge-only firings allocate no durable data.
#[derive(Debug, Default)]
struct PendingMergeReads {
    by_lane: Mutex<HashMap<u32, SmallVec<[FactId; 2]>>>,
}

impl PendingMergeReads {
    fn record(&self, lane: u32, prior_fact: FactId) {
        assert!(
            !prior_fact.is_missing(),
            "receipt-enabled table merge read a row without an immutable FactId"
        );
        self.by_lane
            .lock()
            .unwrap()
            .entry(lane)
            .or_default()
            .push(prior_fact);
    }

    fn lane(&self, lane: u32) -> SmallVec<[FactId; 2]> {
        self.by_lane
            .lock()
            .unwrap()
            .get(&lane)
            .cloned()
            .unwrap_or_default()
    }
}

#[derive(Clone, Debug)]
struct PendingMergeReadRef {
    batch: Arc<PendingMergeReads>,
    lane: u32,
}

/// An action-batch-owned resolver for compact join witnesses. Implementations
/// retain the immutable materialization DAGs needed by their lanes; the
/// receipt arena asks for ordered premise ids only when a lane is promoted.
pub(crate) trait PendingPremiseResolver: Send + Sync {
    fn resolve(&self, lane: u32) -> SmallVec<[FactId; 4]>;
}

enum PendingPremises {
    Flat(Box<[FactId]>),
    Lazy {
        resolver: Arc<dyn PendingPremiseResolver>,
        lanes: Box<[u32]>,
    },
}

impl PendingPremises {
    fn resolve(&self, lane: usize, premise_arity: usize) -> SmallVec<[FactId; 4]> {
        match self {
            Self::Flat(premises) => {
                let start = lane * premise_arity;
                SmallVec::from_slice(&premises[start..start + premise_arity])
            }
            Self::Lazy { resolver, lanes } => {
                let premises = resolver.resolve(lanes[lane]);
                assert_eq!(
                    premises.len(),
                    premise_arity,
                    "pending witness resolved with the wrong premise arity"
                );
                premises
            }
        }
    }
}

/// One action-batch-local set of exact native match witnesses. Equality
/// proposals retain only an `Arc` plus a lane index until union preflight has
/// proved that the proposal is effective. Redundant proposals therefore never
/// allocate provisional match/cause nodes or expand premise-owned terms.
pub(crate) struct PendingMatchBatch {
    receipts: CausalReceipts,
    rule: u32,
    wave: CausalWave,
    first_native_ordinal: u64,
    premise_arity: usize,
    binding_sources: Box<[ReplayBindingSource]>,
    premises: PendingPremises,
    current_terms: Box<[ReplayTermId]>,
    merge_reads: Arc<PendingMergeReads>,
    prepared: Box<[OnceLock<PreparedMatch>]>,
    causes: Box<[OnceLock<CauseDraftId>]>,
}

struct PreparedMatch {
    premises: Box<[FactId]>,
    terms: Box<[ReplayTermId]>,
}

impl Drop for PendingMatchBatch {
    fn drop(&mut self) {
        self.receipts
            .0
            .open_pending_batches
            .fetch_sub(1, Ordering::Release);
    }
}

/// A compact, cloneable cause handle carried by one staged equality proposal.
/// Promotion is memoized in the owning batch, so several effects from one
/// native firing share exactly one match and cause draft.
#[derive(Clone)]
pub(crate) struct PendingRuleCause {
    batch: Arc<PendingMatchBatch>,
    lane: u32,
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
    fn lane(&self) -> usize {
        self.lane as usize
    }

    pub(crate) fn promote(&self) -> CauseDraftId {
        let lane = self.lane();
        *self.batch.causes[lane].get_or_init(|| {
            self.batch
                .receipts
                .promote_pending_rule_match(&self.batch, lane)
        })
    }

    fn prepare(&self) -> Result<(), String> {
        self.batch
            .receipts
            .prepare_pending_rule_match(&self.batch, self.lane())
            .map(|_| ())
    }

    fn record_merge_read(&self, prior_fact: FactId) {
        self.batch.merge_reads.record(self.lane, prior_fact);
    }
}

/// Cause representation accepted by the equality staging path. Existing
/// rebuild/container callers keep their ready draft; ordinary rule unions use
/// the pending form until preflight proves them effective.
#[derive(Clone)]
enum DeferredEqualityCauseKind {
    Ready {
        cause: CauseDraftId,
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
    cause: OnceLock<CauseDraftId>,
}

#[doc(hidden)]
#[derive(Clone)]
pub struct DeferredEqualityCause(DeferredEqualityCauseKind);

impl DeferredEqualityCause {
    pub(crate) fn ready(cause: CauseDraftId) -> Self {
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
            cause: cause.id,
            equality: Some(cause.equality),
        })
    }

    pub(crate) fn promote(&self) -> CauseDraftId {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { cause, .. } => *cause,
            DeferredEqualityCauseKind::Pending(cause) => cause.promote(),
            DeferredEqualityCauseKind::Merge(cause) => *cause
                .cause
                .get_or_init(|| cause.receipts.promote_pending_merge_cause(cause)),
        }
    }

    pub(crate) fn ready_id(&self) -> Option<CauseDraftId> {
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
                let arena = receipts.0.arena.lock().unwrap();
                arena
                    .cause_summary(*cause)
                    .unwrap_or_else(|error| panic!("cannot classify deferred cause: {error}"))
            }
            DeferredEqualityCauseKind::Pending(_) => EqualityCauseSummary::Rule,
            DeferredEqualityCauseKind::Merge(cause) => cause.equality,
        }
    }

    pub(crate) fn prepare(&self, receipts: &CausalReceipts) -> Result<(), String> {
        self.equality_summary(receipts)
            .validate()
            .map_err(str::to_owned)?;
        self.prepare_dependencies(receipts)
    }

    fn prepare_dependencies(&self, receipts: &CausalReceipts) -> Result<(), String> {
        match &self.0 {
            DeferredEqualityCauseKind::Ready { .. } => Ok(()),
            DeferredEqualityCauseKind::Pending(cause) => cause.prepare(),
            // A direct rebuild is invalid as a root equality cause but valid
            // beneath a merge that supplies its prior fact. Prepare its lazy
            // payload without re-validating the child as a standalone root.
            DeferredEqualityCauseKind::Merge(cause) => {
                cause.incoming.prepare_dependencies(receipts)
            }
        }
    }
}

#[derive(Clone, Debug)]
enum CauseDraft {
    Source(SourceRef),
    Rule(MatchDraftId),
    Rebuild {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        equalities: FlatRange,
    },
    ContainerCanonicalize {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        equalities: FlatRange,
    },
    ContainerRefresh {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        equalities: FlatRange,
    },
    Merge {
        incoming: CauseDraftId,
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
    },
    Rebuild {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        complete: bool,
    },
    Invalid(EqualityCauseError),
}

impl EqualityCauseSummary {
    fn for_leaf(cause: &CauseDraft) -> Self {
        match cause {
            CauseDraft::Source(_) => Self::Source,
            CauseDraft::Rule(_) => Self::Rule,
            CauseDraft::Rebuild {
                wave,
                prior_fact,
                as_of_edges,
                ..
            } => {
                if prior_fact.is_missing() {
                    Self::Invalid(EqualityCauseError::MissingFact)
                } else {
                    Self::Rebuild {
                        wave: *wave,
                        as_of_edges: *as_of_edges,
                        complete: false,
                    }
                }
            }
            CauseDraft::ContainerCanonicalize {
                wave, as_of_edges, ..
            } => Self::Container {
                wave: *wave,
                as_of_edges: *as_of_edges,
            },
            CauseDraft::ContainerRefresh { .. } => Self::Invalid(EqualityCauseError::Mixed),
            CauseDraft::Merge { .. } => {
                unreachable!("merge summaries require their child summaries")
            }
        }
    }

    fn with_prior_fact(self, fact: FactId) -> Self {
        if fact.is_missing() {
            return Self::Invalid(EqualityCauseError::MissingFact);
        }
        match self {
            Self::Rule => Self::Rule,
            Self::Container { .. } => Self::Invalid(EqualityCauseError::Mixed),
            Self::Rebuild {
                wave, as_of_edges, ..
            } => Self::Rebuild {
                wave,
                as_of_edges,
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
                    ..
                },
                Self::Rebuild {
                    wave: prior_wave,
                    as_of_edges: prior_edges,
                    ..
                },
            ) if incoming_wave == prior_wave && incoming_edges == prior_edges => Self::Rebuild {
                wave: incoming_wave,
                as_of_edges: incoming_edges,
                complete: true,
            },
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
    pub(crate) fn id(self) -> CauseDraftId {
        self.id
    }
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
    Rebuild {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        equalities: FlatRange,
    },
    ContainerCanonicalize {
        wave: CausalWave,
        as_of_edges: EqualityEdgeCount,
        equalities: FlatRange,
    },
    ContainerRefresh {
        wave: CausalWave,
        prior_fact: FactId,
        as_of_edges: EqualityEdgeCount,
        equalities: FlatRange,
    },
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
    node: EqNodeRecord,
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    cause: CauseDraftId,
}

#[derive(Clone, Debug)]
struct DurableEquality {
    node: EqNodeRecord,
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    reason: EqualityReason,
}

#[derive(Clone, Debug)]
struct PendingNativeAlias {
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    cause: CauseDraftId,
}

#[derive(Clone, Debug)]
struct DurableNativeAlias {
    proposal: AppliedEqualityProposal,
    native_parent: crate::Value,
    native_child: crate::Value,
    reason: EqualityReason,
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
    /// Only merge drafts need cached classification; leaf summaries are
    /// recoverable directly from their compact cause node.
    equality_summaries: HashMap<CauseDraftId, EqualityCauseSummary>,
    premises: Vec<FactId>,
    terms: Vec<ReplayTermId>,
    fact_terms: Vec<ReplayTermId>,
    rebuild_equalities: Vec<TypedCellEquality>,
    pending_equalities: IdSegment<PendingEquality>,
    pending_native_aliases: Vec<PendingNativeAlias>,
}

impl ProvisionalArena {
    fn is_empty(&self) -> bool {
        self.matches.present() == 0
            && self.causes.present() == 0
            && self.equality_summaries.is_empty()
            && self.premises.is_empty()
            && self.terms.is_empty()
            && self.fact_terms.is_empty()
            && self.rebuild_equalities.is_empty()
            && self.pending_equalities.present() == 0
            && self.pending_native_aliases.is_empty()
    }
}

#[derive(Clone, Debug)]
struct DurableMatch {
    rule: u32,
    wave: CausalWave,
    premises: FlatRange,
    terms: FlatRange,
    merge_reads: FlatRange,
}

#[derive(Default)]
struct ReceiptArena {
    provisional: ProvisionalArena,
    facts: Vec<Option<FactSlot>>,
    durable_matches: Vec<DurableMatch>,
    durable_premises: Vec<FactId>,
    durable_terms: Vec<ReplayTermId>,
    durable_merge_reads: Vec<FactId>,
    durable_fact_terms: Vec<ReplayTermId>,
    durable_rebuild_equalities: Vec<TypedCellEquality>,
    durable_causes: Vec<DurableCause>,
    durable_equalities: Vec<DurableEquality>,
    durable_native_aliases: Vec<DurableNativeAlias>,
    check_roots: HashMap<u32, CheckRoot>,
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

    fn add_live_bytes(&mut self, bytes: usize) {
        self.counters.live_provisional_bytes += bytes as u64;
        self.counters.peak_provisional_bytes = self
            .counters
            .peak_provisional_bytes
            .max(self.counters.live_provisional_bytes);
    }

    fn fact_term(&self, id: FactId, column: usize) -> Option<ReplayTermId> {
        self.fact_terms(id)?
            .1
            .get(column)
            .copied()
            .filter(|term| !term.is_missing())
    }

    fn fact_terms(&self, id: FactId) -> Option<(TableId, &[ReplayTermId])> {
        if id.is_missing() {
            return None;
        }
        let slot = self.facts.get((id.get() - 1) as usize)?.as_ref()?;
        Some(match slot {
            FactSlot::Pending(fact) => (
                fact.table,
                &self.provisional.fact_terms[fact.terms.as_range()],
            ),
            FactSlot::Durable(fact) => {
                (fact.table, &self.durable_fact_terms[fact.terms.as_range()])
            }
        })
    }

    fn cause_draft(&self, id: CauseDraftId) -> Result<&CauseDraft, &'static str> {
        let Some(index) = self.provisional.causes.index(id.get()) else {
            return Err("cause draft does not belong to the current causal wave");
        };
        self.provisional
            .causes
            .slots
            .get(index)
            .and_then(Option::as_ref)
            .ok_or("cause draft has not been published")
    }

    fn cause_summary(&self, id: CauseDraftId) -> Result<EqualityCauseSummary, &'static str> {
        let cause = self.cause_draft(id)?;
        if matches!(cause, CauseDraft::Merge { .. }) {
            self.provisional
                .equality_summaries
                .get(&id)
                .copied()
                .ok_or("merge cause draft has no cached equality classification")
        } else {
            Ok(EqualityCauseSummary::for_leaf(cause))
        }
    }

    fn unfold_cause(&self, root: DurableCauseId) -> Option<FactCause> {
        let root_node = self.durable_causes.get((root.get() - 1) as usize)?;
        match root_node {
            DurableCause::Source(source) => Some(FactCause::Source(source.clone())),
            DurableCause::Rule(rule) => Some(FactCause::Rule(*rule)),
            DurableCause::Rebuild {
                wave,
                prior_fact,
                as_of_edges,
                equalities,
            } => Some(FactCause::Rebuild {
                wave: *wave,
                prior_fact: *prior_fact,
                equalities: EqualityLandmark {
                    as_of_edges: *as_of_edges,
                    pairs: self.durable_rebuild_equalities[equalities.as_range()].into(),
                },
            }),
            DurableCause::ContainerCanonicalize { .. } => {
                panic!("container canonicalization cannot justify an effective table fact")
            }
            DurableCause::ContainerRefresh {
                wave,
                prior_fact,
                as_of_edges,
                equalities,
            } => Some(FactCause::ContainerRefresh {
                wave: *wave,
                prior_fact: *prior_fact,
                equalities: EqualityLandmark {
                    as_of_edges: *as_of_edges,
                    pairs: self.durable_rebuild_equalities[equalities.as_range()].into(),
                },
            }),
            DurableCause::Merge { .. } => Some(FactCause::Merge { cause: root }),
        }
    }

    fn equality_reason(
        &self,
        root: DurableCauseId,
        summary: EqualityCauseSummary,
    ) -> EqualityReason {
        summary.validate().unwrap_or_else(|error| panic!("{error}"));
        match (&self.durable_causes[(root.get() - 1) as usize], summary) {
            (DurableCause::Rule(rule), _) => EqualityReason::RuleUnion(*rule),
            (_, EqualityCauseSummary::Rule) => EqualityReason::MergeFn { cause: root },
            (
                _,
                EqualityCauseSummary::Container {
                    wave, as_of_edges, ..
                },
            ) => EqualityReason::Congruence {
                cause: root,
                wave,
                as_of_edges,
            },
            (
                _,
                EqualityCauseSummary::Rebuild {
                    wave, as_of_edges, ..
                },
            ) => EqualityReason::Congruence {
                cause: root,
                wave,
                as_of_edges,
            },
            _ => unreachable!("validated equality cause has no public reason"),
        }
    }

    fn validate_equality_cause_draft(&self, root_id: CauseDraftId) -> Result<(), &'static str> {
        self.cause_summary(root_id)?.validate()
    }
}

struct ReceiptShared {
    next_fact: AtomicU64,
    next_match_draft: AtomicU64,
    next_native_match: AtomicU64,
    next_rule_match: AtomicU64,
    next_term: AtomicU32,
    next_equality: AtomicU64,
    next_cause_draft: AtomicU64,
    open_fragments: AtomicUsize,
    open_pending_batches: AtomicUsize,
    open_native_leases: AtomicUsize,
    abandoned_fragments: AtomicU64,
    replay_terms: ReplayTermStore,
    equality_value_sorts: Mutex<HashMap<Value, ReplaySortId>>,
    equality_wave_timestamp: Mutex<Option<(CausalWave, Value)>>,
    arena: Mutex<ReceiptArena>,
}

impl Default for ReceiptShared {
    fn default() -> Self {
        Self {
            next_fact: AtomicU64::new(0),
            next_match_draft: AtomicU64::new(0),
            next_native_match: AtomicU64::new(0),
            next_rule_match: AtomicU64::new(0),
            next_term: AtomicU32::new(0),
            next_equality: AtomicU64::new(0),
            next_cause_draft: AtomicU64::new(0),
            open_fragments: AtomicUsize::new(0),
            open_pending_batches: AtomicUsize::new(0),
            open_native_leases: AtomicUsize::new(0),
            abandoned_fragments: AtomicU64::new(0),
            replay_terms: ReplayTermStore::default(),
            equality_value_sorts: Mutex::new(HashMap::default()),
            equality_wave_timestamp: Mutex::new(None),
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
    fact_terms: Vec<ReplayTermId>,
    /// Prior fact-owned terms copied only when a direct rebuild/container
    /// refresh or effective constructor merge commits a new fact.
    rebuild_term_ranges: HashMap<CauseDraftId, (TableId, FlatRange)>,
    rebuild_terms: Vec<ReplayTermId>,
    equalities: Vec<(EqNodeId, PendingEquality)>,
    native_aliases: Vec<PendingNativeAlias>,
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
            fact_terms: Vec::new(),
            rebuild_term_ranges: HashMap::default(),
            rebuild_terms: Vec::new(),
            equalities: Vec::new(),
            native_aliases: Vec::new(),
            redundant_unions: 0,
            unattributed_commits: 0,
            published: false,
        }
    }

    pub(crate) fn merge_draft_capability(
        &mut self,
        incoming: CauseDraftId,
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

    /// Copy coherent constructor terms only after the native merge reports an
    /// effective replacement. No-op collisions never call this method.
    pub(crate) fn inherit_prior_fact_terms(
        &mut self,
        cause: CauseDraftId,
        prior_fact: FactId,
        table: TableId,
    ) {
        if !self
            .shared
            .replay_terms
            .table_constructors
            .contains_key(&table)
        {
            return;
        }
        let copied = self.cache_prior_fact_terms(cause, prior_fact, table);
        if copied == 0 {
            return;
        }
        let mut arena = self.shared.arena.lock().unwrap();
        arena.counters.merge_prior_term_copies += copied as u64;
    }

    /// Cache one prior fact's immutable syntax for a single effective commit.
    /// Callers decide whether the cause requires inheritance; this helper does
    /// no candidate-wide preload and copies from either the current fragment or
    /// the durable/provisional shared fact arena.
    fn cache_prior_fact_terms(
        &mut self,
        cause: CauseDraftId,
        prior_fact: FactId,
        table: TableId,
    ) -> usize {
        if self.rebuild_term_ranges.contains_key(&cause) {
            return 0;
        }
        let local = match (self.facts.first(), self.facts.last()) {
            (Some((first, _)), Some((last, _))) if *first <= prior_fact && prior_fact <= *last => {
                self.facts
                    .binary_search_by_key(&prior_fact, |(fact, _)| *fact)
                    .ok()
                    .map(|index| &self.facts[index])
                    .map(|(_, fact)| (fact.table, self.fact_terms[fact.terms.as_range()].to_vec()))
            }
            _ => None,
        };
        let (prior_table, terms) = if let Some(local) = local {
            local
        } else {
            let arena = self.shared.arena.lock().unwrap();
            let (prior_table, terms) = arena
                .fact_terms(prior_fact)
                .expect("constructor merge references a missing prior FactId");
            (prior_table, terms.to_vec())
        };
        assert_eq!(prior_table, table, "constructor merge changed tables");
        let range = FlatRange::new(self.rebuild_terms.len(), terms.len());
        self.rebuild_terms.extend_from_slice(&terms);
        assert!(
            self.rebuild_term_ranges
                .insert(cause, (table, range))
                .is_none(),
            "duplicate effective-commit prior-term cache"
        );
        terms.len()
    }

    #[cfg(test)]
    pub(crate) fn merge_drafts(
        &mut self,
        incoming: CauseDraftId,
        prior: CauseDraftId,
    ) -> CauseDraftId {
        self.merge_drafts_capability(incoming, prior).id()
    }

    pub(crate) fn merge_drafts_capability(
        &mut self,
        incoming: CauseDraftId,
        prior: CauseDraftId,
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
                prior: PriorVersion::Draft(prior),
            },
            equality,
        )
    }

    fn cause_summary(&self, cause: CauseDraftId) -> EqualityCauseSummary {
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
    pub(crate) fn preload_cause_summaries(&mut self, causes: &[CauseDraftId]) {
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
                if self.draft_summaries.contains_key(cause) {
                    continue;
                }
                match arena.cause_summary(*cause) {
                    Ok(summary) => {
                        self.draft_summaries.insert(*cause, summary);
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
        cause: CauseDraftId,
        row: &[Value],
    ) -> FactId {
        self.record_fact_with_terms(table, cause, row, None)
    }

    pub(crate) fn record_fact_with_terms(
        &mut self,
        table: TableId,
        cause: CauseDraftId,
        row: &[Value],
        explicit_terms: Option<&[ReplayTermId]>,
    ) -> FactId {
        assert!(
            !cause.is_unattributed(),
            "effective commit is missing exact causal attribution"
        );
        if explicit_terms.is_none() && !self.rebuild_term_ranges.contains_key(&cause) {
            let local_prior = self.drafts.iter().find_map(|(id, draft)| {
                (*id == cause)
                    .then_some(draft)
                    .and_then(|draft| match draft {
                        CauseDraft::Rebuild { prior_fact, .. }
                        | CauseDraft::ContainerRefresh { prior_fact, .. } => Some(*prior_fact),
                        _ => None,
                    })
            });
            let prior_fact = local_prior.or_else(|| {
                let arena = self.shared.arena.lock().unwrap();
                match arena.cause_draft(cause).ok()? {
                    CauseDraft::Rebuild { prior_fact, .. }
                    | CauseDraft::ContainerRefresh { prior_fact, .. } => Some(*prior_fact),
                    _ => None,
                }
            });
            if let Some(prior_fact) = prior_fact {
                self.cache_prior_fact_terms(cause, prior_fact, table);
            }
        }
        // A semantic rekey creates a new immutable fact version, but its
        // syntax remains the syntax owned by the prior fact. The rebuild cause
        // records the old/new raw equality endpoints separately. Looking the
        // rebuilt row up in the global value map here would instead replace a
        // term such as `B(2)` with its later canonical representative `A(1)`,
        // erasing exactly the temporal identity needed by checks and replay.
        let term_range =
            if let Some((prior_table, inherited)) = self.rebuild_term_ranges.get(&cause).copied() {
                assert_eq!(prior_table, table, "rebuild fact changed tables");
                let terms = &self.rebuild_terms[inherited.as_range()];
                assert_eq!(
                    terms.len(),
                    row.len(),
                    "rebuild fact changed its registered replay arity"
                );
                let range = FlatRange::new(self.fact_terms.len(), terms.len());
                self.fact_terms.extend_from_slice(terms);
                range
            } else if let Some(terms) = explicit_terms {
                self.shared
                    .replay_terms
                    .validate_row_terms(table, row, terms)
                    .unwrap_or_else(|error| {
                        panic!("cannot record explicit committed fact terms: {error}")
                    });
                let range = FlatRange::new(self.fact_terms.len(), terms.len());
                self.fact_terms.extend_from_slice(terms);
                range
            } else {
                self.shared
                    .replay_terms
                    .append_row_terms(table, row, &mut self.fact_terms)
                    .unwrap_or_else(|error| {
                        panic!("cannot record exact committed fact for {table:?}: {error}")
                    })
            };
        let id = FactId::new(ReceiptShared::alloc_u64(&self.shared.next_fact, 1));
        if let Some((last, _)) = self.facts.last() {
            debug_assert!(
                *last < id,
                "ReceiptBatch FactIds must remain strictly increasing"
            );
        }
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

    pub(crate) fn record_redundant_union(&mut self) {
        self.redundant_unions += 1;
    }

    pub(crate) fn record_applied_union(
        &mut self,
        proposal: AppliedEqualityProposal,
        left_component: EqComponentRef,
        right_component: EqComponentRef,
        native_parent: crate::Value,
        native_child: crate::Value,
        cause: CauseDraftId,
    ) -> EqNodeId {
        assert!(
            !cause.is_unattributed(),
            "applied union is missing exact causal attribution"
        );
        let id = EqNodeId::new(ReceiptShared::alloc_u64(&self.shared.next_equality, 1));
        self.equalities.push((
            id,
            PendingEquality {
                node: EqNodeRecord {
                    id,
                    left: left_component,
                    right: right_component,
                    edge: id,
                },
                proposal,
                native_parent,
                native_child,
                cause,
            },
        ));
        id
    }

    pub(crate) fn record_native_alias(
        &mut self,
        proposal: AppliedEqualityProposal,
        native_parent: crate::Value,
        native_child: crate::Value,
        cause: CauseDraftId,
    ) {
        assert!(
            !cause.is_unattributed(),
            "native alias union is missing exact causal attribution"
        );
        assert_eq!(
            proposal.left.sort, proposal.right.sort,
            "native alias endpoints cross logical sorts"
        );
        assert_ne!(
            native_parent, native_child,
            "native alias did not merge distinct runtime roots"
        );
        self.native_aliases.push(PendingNativeAlias {
            proposal,
            native_parent,
            native_child,
            cause,
        });
    }

    pub(crate) fn publish(mut self) {
        {
            let mut arena = self.shared.arena.lock().unwrap();
            let mut added_bytes = self.drafts.len() * mem::size_of::<CauseDraft>()
                + self.facts.len() * mem::size_of::<PendingFact>()
                + self.fact_terms.len() * mem::size_of::<ReplayTermId>()
                + self.equalities.len() * mem::size_of::<PendingEquality>()
                + self.native_aliases.len() * mem::size_of::<PendingNativeAlias>();
            for (id, draft) in self.drafts.drain(..) {
                let equality = self
                    .draft_summaries
                    .remove(&id)
                    .expect("local merge draft has no cached equality classification");
                if matches!(draft, CauseDraft::Merge { .. }) {
                    assert!(
                        arena
                            .provisional
                            .equality_summaries
                            .insert(id, equality)
                            .is_none(),
                        "duplicate merge-cause classification"
                    );
                    added_bytes +=
                        mem::size_of::<CauseDraftId>() + mem::size_of::<EqualityCauseSummary>();
                }
                arena.provisional.causes.install(id.get(), draft);
            }
            // Published input summaries are only a worker-local lookup cache;
            // the arena already owns their canonical entries.
            self.draft_summaries.clear();
            let fact_term_base = arena.provisional.fact_terms.len();
            arena.provisional.fact_terms.append(&mut self.fact_terms);
            for (id, mut fact) in self.facts.drain(..) {
                fact.terms = fact.terms.shifted(fact_term_base);
                arena.install_fact(id, fact);
            }
            for (id, equality) in self.equalities.drain(..) {
                arena
                    .provisional
                    .pending_equalities
                    .install(id.get(), equality);
            }
            arena
                .provisional
                .pending_native_aliases
                .append(&mut self.native_aliases);
            arena.counters.redundant_unions += self.redundant_unions;
            arena.counters.unattributed_commits += self.unattributed_commits;
            arena.add_live_bytes(added_bytes);
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
            || !self.native_aliases.is_empty()
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

    pub(crate) fn table_column_sort(&self, table: TableId, column: usize) -> Option<ReplaySortId> {
        self.0
            .replay_terms
            .table_layouts
            .get(&table)?
            .get(column)
            .copied()
            .flatten()
    }

    /// Capture one complete applied-edge prefix at the native rebuild
    /// barrier. A bare counter read is insufficient: every allocated edge up
    /// to the cutoff must already have been published without holes.
    pub(crate) fn equality_edge_count(&self) -> Result<EqualityEdgeCount, &'static str> {
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild with open receipt fragments");
        }
        if self.0.open_pending_batches.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild with unresolved pending match batches");
        }
        if self.0.abandoned_fragments.load(Ordering::Acquire) != 0 {
            return Err("cannot start rebuild after an abandoned receipt fragment");
        }
        let count = self.0.next_equality.load(Ordering::Acquire);
        let arena = self.0.arena.lock().unwrap();
        if self.0.open_fragments.load(Ordering::Acquire) != 0 {
            return Err("receipt fragment opened while capturing rebuild equality cutoff");
        }
        if arena
            .provisional
            .pending_equalities
            .slots
            .iter()
            .any(Option::is_none)
        {
            return Err("rebuild equality cutoff contains an unpublished edge hole");
        }
        let durable = u64::try_from(arena.durable_equalities.len())
            .map_err(|_| "durable equality count exceeds u64")?;
        let pending = u64::try_from(arena.provisional.pending_equalities.slots.len())
            .map_err(|_| "pending equality count exceeds u64")?;
        if count != durable + pending {
            return Err("rebuild equality cutoff is not one complete dense prefix");
        }
        if pending > 0 && arena.provisional.pending_equalities.base != Some(durable + 1) {
            return Err("pending equality segment does not follow the durable prefix");
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

    fn promote_pending_merge_cause(&self, cause: &PendingMergeCause) -> CauseDraftId {
        assert!(Arc::ptr_eq(&self.0, &cause.receipts.0));
        let incoming = cause.incoming.promote();
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
        let mut arena = self.0.arena.lock().unwrap();
        arena.provisional.causes.install(
            id.get(),
            CauseDraft::Merge {
                incoming,
                prior: PriorVersion::Fact(cause.prior_fact),
            },
        );
        assert!(
            arena
                .provisional
                .equality_summaries
                .insert(id, cause.equality)
                .is_none(),
            "duplicate pending merge-cause classification"
        );
        arena.add_live_bytes(
            mem::size_of::<CauseDraft>()
                + mem::size_of::<CauseDraftId>()
                + mem::size_of::<EqualityCauseSummary>(),
        );
        id
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

    /// Validate and register one exact semantic table rebuild before its
    /// removal/insertion is staged. This deliberately takes the existing arena
    /// lock once per changed row; the H1 counters expose the resulting logical
    /// payload until rebuild-local batching is justified by measurement.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn rebuild_draft(
        &self,
        table: TableId,
        wave: CausalWave,
        prior_fact: FactId,
        old_row: &[Value],
        new_row: &[Value],
        rebuild_columns: &[crate::ColumnId],
        as_of_edges: EqualityEdgeCount,
    ) -> Result<CauseDraftId, &'static str> {
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

        // Resolve every new typed endpoint before entering the receipt arena.
        // The prior fact-owned terms are validated under the one arena lock
        // below; no table mutation has been staged at either point.
        let mut pairs = SmallVec::<[TypedCellEquality; 4]>::new();
        for (index, declared_sort) in layout.iter().copied().enumerate() {
            let column = crate::ColumnId::from_usize(index);
            if !rebuild_columns.contains(&column) || old_row[index] == new_row[index] {
                continue;
            }
            let Some(sort) = declared_sort else {
                return Err("changed rebuild column has no replay sort");
            };
            let raw = new_row[index];
            let Some(term) = self.0.replay_terms.lookup(sort, raw) else {
                return Err("rebuilt cell has no ReplayTermId for its declared sort");
            };
            pairs.push(TypedCellEquality {
                column,
                left: EqualityEndpoint {
                    sort,
                    term: ReplayTermId::MISSING,
                    raw: old_row[index],
                },
                right: EqualityEndpoint { sort, term, raw },
            });
        }
        if pairs.is_empty() {
            return Err("rebuild receipt has no changed semantic column");
        }

        let mut arena = self.0.arena.lock().unwrap();
        let Some(slot) = arena
            .facts
            .get((prior_fact.get() - 1) as usize)
            .and_then(Option::as_ref)
        else {
            return Err("rebuild row references an unknown prior FactId");
        };
        let (fact_table, terms) = match slot {
            FactSlot::Pending(fact) => (
                fact.table,
                &arena.provisional.fact_terms[fact.terms.as_range()],
            ),
            FactSlot::Durable(fact) => {
                (fact.table, &arena.durable_fact_terms[fact.terms.as_range()])
            }
        };
        if fact_table != table {
            return Err("rebuild row prior FactId belongs to another table");
        }
        if terms.len() != layout.len() {
            return Err("rebuild row prior fact and table layout have different arities");
        }

        for pair in &mut pairs {
            let term = terms[pair.column.index()];
            if term.is_missing() {
                return Err("changed rebuild column has no fact-owned ReplayTermId");
            }
            let Some(node) = self.0.replay_terms.node(term) else {
                return Err("changed rebuild column fact term is not installed");
            };
            if node.sort() != pair.left.sort {
                return Err("changed rebuild column fact term has the wrong declared sort");
            }
            pair.left.term = term;
        }

        let equalities = FlatRange::new(arena.provisional.rebuild_equalities.len(), pairs.len());
        arena
            .provisional
            .rebuild_equalities
            .extend_from_slice(&pairs);
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
        let cause = CauseDraft::Rebuild {
            wave,
            prior_fact,
            as_of_edges,
            equalities,
        };
        arena.provisional.causes.install(id.get(), cause);
        arena.add_live_bytes(
            mem::size_of::<CauseDraft>() + pairs.len() * mem::size_of::<TypedCellEquality>(),
        );
        Ok(id)
    }

    /// Resolve the positional equality dependencies of one ordered container
    /// value before the registry mutates it. No explanation path is walked
    /// here; the immutable forest is unfolded lazily by the slicer.
    pub(crate) fn container_dependency(
        &self,
        container_type: TypeId,
        outer_raw: Value,
        wave: CausalWave,
        before: &[Value],
        after: &[Value],
        as_of_edges: EqualityEdgeCount,
    ) -> Result<Option<ContainerVersionDependency>, &'static str> {
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
                left: self.equality_endpoint(sort, left)?,
                right: self.equality_endpoint(sort, right)?,
            });
        }
        if pairs.is_empty() {
            return Ok(None);
        }
        let mut outer_candidates = SmallVec::<[EqualityEndpoint; 2]>::new();
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
            let Some(term) = self.0.replay_terms.lookup(sort, outer_raw) else {
                continue;
            };
            if !matches!(
                self.0.replay_terms.node(term),
                Some(ReplayTerm::Call { .. })
            ) {
                continue;
            }
            outer_candidates.push(EqualityEndpoint {
                sort,
                term,
                raw: outer_raw,
            });
        }
        let outer = match outer_candidates.as_slice() {
            [outer] => *outer,
            [] => return Err("changed container has no exact typed structural producer"),
            _ => return Err("changed container has multiple exact logical replay sorts"),
        };
        Ok(Some(ContainerVersionDependency {
            outer,
            dependency: ContainerDependency {
                wave,
                equalities: EqualityLandmark {
                    as_of_edges,
                    pairs: pairs.into_vec().into_boxed_slice(),
                },
            },
        }))
    }

    /// Resolve one raw reverse-index candidate to an exact logical parent.
    /// The physical registry type and exact child term both have to agree;
    /// raw `Value` equality alone is never container ancestry.
    pub(crate) fn container_parent_candidates(
        &self,
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
            let Some(term) = self.0.replay_terms.lookup(sort, parent_raw) else {
                continue;
            };
            if !matches!(
                self.0.replay_terms.node(term),
                Some(ReplayTerm::Call { .. })
            ) {
                continue;
            }
            candidates.push(ContainerParentCandidate {
                endpoint: EqualityEndpoint {
                    sort,
                    term,
                    raw: parent_raw,
                },
                child_sorts,
            });
        }
        candidates
    }

    /// Register one exact container-registry collision cause and return the
    /// only logical outer sort shared by its native ids.
    pub(crate) fn container_canonicalization_cause(
        &self,
        wave: CausalWave,
        left: Value,
        right: Value,
        as_of_edges: EqualityEdgeCount,
    ) -> Result<(CauseCapability, ReplaySortId), &'static str> {
        let common_sorts = self
            .0
            .replay_terms
            .common_compatible_call_sorts(left, right)?;
        let value_sorts = self.0.equality_value_sorts.lock().unwrap();
        let mut candidates =
            SmallVec::<[(ReplaySortId, SmallVec<[TypedCellEquality; 4]>); 2]>::new();
        for sort in common_sorts {
            let left_term = self
                .0
                .replay_terms
                .lookup(sort, left)
                .expect("common Call sort must have a left term");
            let right_term = self
                .0
                .replay_terms
                .lookup(sort, right)
                .expect("common Call sort must have a right term");
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
                candidates.push((sort, pairs));
            }
        }
        drop(value_sorts);
        let (sort, pairs) = match candidates.as_slice() {
            [(sort, pairs)] => (*sort, pairs.clone()),
            [] => return Err("container ids have no exact typed Call collision"),
            _ => return Err("container ids have multiple exact typed Call collisions"),
        };
        let mut arena = self.0.arena.lock().unwrap();
        let equalities = FlatRange::new(arena.provisional.rebuild_equalities.len(), pairs.len());
        arena
            .provisional
            .rebuild_equalities
            .extend_from_slice(&pairs);
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
        arena.provisional.causes.install(
            id.get(),
            CauseDraft::ContainerCanonicalize {
                wave,
                as_of_edges,
                equalities,
            },
        );
        arena.add_live_bytes(
            mem::size_of::<CauseDraft>() + pairs.len() * mem::size_of::<TypedCellEquality>(),
        );
        Ok((
            CauseCapability {
                id,
                equality: EqualityCauseSummary::Container { wave, as_of_edges },
            },
            sort,
        ))
    }

    /// Register the exact prior fact and child equality landmark for one
    /// same-id container parent-row refresh.
    pub(crate) fn container_refresh_draft(
        &self,
        prior_fact: FactId,
        candidates: &[(crate::ColumnId, &[ContainerVersionDependency])],
    ) -> Result<Option<CauseDraftId>, &'static str> {
        if prior_fact.is_missing() {
            return Err("container refresh row has no immutable prior FactId");
        }
        let mut arena = self.0.arena.lock().unwrap();
        let (_, fact_terms) = arena
            .fact_terms(prior_fact)
            .ok_or("container refresh references an unknown prior FactId")?;
        let mut selected: Option<ContainerDependency> = None;
        for &(column, dependencies) in candidates {
            let Some(fact_term) = fact_terms.get(column.index()).copied() else {
                return Err("container refresh column is outside its prior fact");
            };
            for version in dependencies {
                if version.outer.term != fact_term {
                    continue;
                }
                let dependency = &version.dependency;
                match &mut selected {
                    None => selected = Some(dependency.clone()),
                    Some(current) => {
                        if (current.wave, current.equalities.as_of_edges)
                            != (dependency.wave, dependency.equalities.as_of_edges)
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
            return Ok(None);
        };
        if dependency.equalities.pairs.is_empty() {
            return Err("container refresh has no child dependency");
        }
        let equalities = FlatRange::new(
            arena.provisional.rebuild_equalities.len(),
            dependency.equalities.pairs.len(),
        );
        arena
            .provisional
            .rebuild_equalities
            .extend_from_slice(&dependency.equalities.pairs);
        let id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
        arena.provisional.causes.install(
            id.get(),
            CauseDraft::ContainerRefresh {
                wave: dependency.wave,
                prior_fact,
                as_of_edges: dependency.equalities.as_of_edges,
                equalities,
            },
        );
        arena.add_live_bytes(
            mem::size_of::<CauseDraft>()
                + dependency.equalities.pairs.len() * mem::size_of::<TypedCellEquality>(),
        );
        Ok(Some(id))
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
        self.intern_call(constructor.result_sort, constructor.op, children, value)
    }

    pub(crate) fn register_spec_container_type(
        &self,
        constructor: &ReplayConstructorSpec,
    ) -> Result<(), &'static str> {
        self.0.replay_terms.register_container_type(constructor)
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

    pub(crate) fn constructor_row_terms(
        &self,
        table: TableId,
        row: &[Value],
    ) -> Result<Option<Box<[ReplayTermId]>>, &'static str> {
        let Some(constructor) = self
            .0
            .replay_terms
            .table_constructors
            .get(&table)
            .map(|entry| entry.clone())
        else {
            return Ok(None);
        };
        let mut children = SmallVec::<[ReplayTermId; 4]>::new();
        for (column, sort) in constructor.child_sorts.iter().copied().enumerate() {
            let value = *row
                .get(column)
                .ok_or("constructor row is missing one of its key columns")?;
            children.push(
                self.lookup_term(sort, value)
                    .ok_or("constructor key has no producer-installed ReplayTermId")?,
            );
        }
        let output = *row
            .get(children.len())
            .ok_or("constructor row is missing its output column")?;
        let call = self.intern_spec_call(&constructor, &children, output)?;
        let mut terms = vec![ReplayTermId::MISSING; row.len()];
        terms[..children.len()].copy_from_slice(&children);
        terms[children.len()] = call;
        Ok(Some(terms.into_boxed_slice()))
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
    ) -> Result<SmallVec<[ReplayTermId; 8]>, &'static str> {
        enum Lookup {
            Direct {
                term: ReplayTermId,
                sort: ReplaySortId,
            },
            Constructor {
                sort: ReplaySortId,
                op: ReplayOpId,
                children: SmallVec<[ReplayTermId; 4]>,
            },
        }

        let lookups = {
            let arena = self.0.arena.lock().unwrap();
            let mut lookups = SmallVec::<[Lookup; 8]>::new();
            for &(request, sort) in requests {
                match request {
                    CheckTermSource::Premise { premise, column } => {
                        let fact = *premises
                            .get(premise)
                            .ok_or("check endpoint cites a missing premise slot")?;
                        let term = arena
                            .fact_term(fact, column)
                            .ok_or("check endpoint has no immutable fact-owned ReplayTermId")?;
                        lookups.push(Lookup::Direct { term, sort });
                    }
                    CheckTermSource::Constructor {
                        premise,
                        input_columns,
                        op,
                    } => {
                        let fact = *premises
                            .get(premise)
                            .ok_or("check endpoint cites a missing premise slot")?;
                        let (_, fact_terms) = arena
                            .fact_terms(fact)
                            .ok_or("check endpoint cites a missing immutable fact")?;
                        let children = fact_terms
                            .get(..input_columns)
                            .ok_or("check constructor input arity exceeds its producer fact")?;
                        if children.iter().any(|term| term.is_missing()) {
                            return Err(
                                "check constructor producer has a missing input ReplayTermId",
                            );
                        }
                        lookups.push(Lookup::Constructor {
                            sort,
                            op,
                            children: SmallVec::from_slice(children),
                        });
                    }
                    CheckTermSource::Current => {
                        return Err("current-value check endpoint was requested as a premise term");
                    }
                }
            }
            lookups
        };

        let mut terms = SmallVec::<[ReplayTermId; 8]>::new();
        for lookup in lookups {
            let term = match lookup {
                Lookup::Direct { term, sort } => {
                    let node = self
                        .0
                        .replay_terms
                        .node(term)
                        .ok_or("check endpoint fact owns an unknown ReplayTermId")?;
                    if node.sort() != sort {
                        return Err("check endpoint fact term has the wrong declared sort");
                    }
                    term
                }
                Lookup::Constructor { sort, op, children } => self
                    .lookup_call(sort, op, &children)
                    .ok_or("check constructor producer has no exact immutable structural call")?,
            };
            terms.push(term);
        }
        Ok(terms)
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
        let replace = if let Some(current) = arena.check_roots.get(&check) {
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
            // Parallel query batches may reach this point in any wall-clock
            // order. "First" is therefore the deterministic native order:
            // earliest cumulative wave, then the ordered FactId/equality
            // witness, then its exact equality cutoff.
            (wave, premises, equalities, as_of_edges)
                < (
                    current.wave,
                    current.premises.as_ref(),
                    current.equalities.as_ref(),
                    current.as_of_edges,
                )
        } else {
            true
        };
        if replace {
            arena.check_roots.insert(
                check,
                CheckRoot {
                    check,
                    wave,
                    premises: premises.into(),
                    equalities: equalities.into(),
                    as_of_edges,
                },
            );
        }
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
        let mut value_sorts = self.0.equality_value_sorts.lock().unwrap();
        for value in [left, right] {
            if value_sorts
                .get(&value)
                .is_some_and(|known_sort| *known_sort != sort)
            {
                return Err("one native equality value was used through different logical sorts");
            }
        }
        value_sorts.entry(left).or_insert(sort);
        value_sorts.entry(right).or_insert(sort);
        Ok(TypedEqualityProposal {
            wave,
            left: left_endpoint,
            right: right_endpoint,
        })
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
        let cause = CauseDraft::Source(source);
        arena.provisional.causes.install(id.get(), cause);
        arena.add_live_bytes(mem::size_of::<CauseDraft>());
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
        let result = lanes
            .iter()
            .copied()
            .enumerate()
            .map(|(offset, lane)| {
                let id = CauseDraftId::new(first + offset as u64);
                arena
                    .provisional
                    .causes
                    .install(id.get(), CauseDraft::Source(source.clone()));
                (lane, id)
            })
            .collect();
        arena.add_live_bytes(lanes.len() * mem::size_of::<CauseDraft>());
        result
    }

    /// Register heterogeneous source rows contiguously under one arena lock.
    pub(crate) fn register_source_rows(&self, sources: &[SourceRef]) -> Vec<CauseDraftId> {
        if sources.is_empty() {
            return Vec::new();
        }
        let first = ReceiptShared::alloc_u64(&self.0.next_cause_draft, sources.len());
        let mut arena = self.0.arena.lock().unwrap();
        let result = sources
            .iter()
            .enumerate()
            .map(|(offset, source)| {
                let id = CauseDraftId::new(first + offset as u64);
                arena
                    .provisional
                    .causes
                    .install(id.get(), CauseDraft::Source(source.clone()));
                id
            })
            .collect();
        arena.add_live_bytes(sources.len() * mem::size_of::<CauseDraft>());
        result
    }

    /// Freeze one action batch's compact match metadata. This does not touch
    /// the provisional receipt arena: only equality proposals that survive UF
    /// preflight call [`PendingRuleCause::promote`].
    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn pending_rule_batch(
        &self,
        rule: u32,
        wave: CausalWave,
        premise_arity: usize,
        binding_sources: &[ReplayBindingSource],
        flat_premises: &[FactId],
        flat_current_terms: &[ReplayTermId],
        lanes: usize,
    ) -> Arc<PendingMatchBatch> {
        assert!(lanes > 0, "pending match batch cannot be empty");
        assert_eq!(
            flat_premises.len(),
            lanes * premise_arity,
            "pending match premises must be dense and lane-aligned"
        );
        let current_arity = binding_sources
            .iter()
            .filter(|source| matches!(source, ReplayBindingSource::Current { .. }))
            .count();
        assert_eq!(
            flat_current_terms.len(),
            lanes * current_arity,
            "pending current terms must be dense and lane-aligned"
        );
        let first_native_ordinal = self.reserve_native_match_ordinals(lanes);
        self.pending_rule_batch_at(
            rule,
            wave,
            first_native_ordinal,
            premise_arity,
            binding_sources,
            flat_premises,
            flat_current_terms,
            lanes,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn pending_rule_batch_at(
        &self,
        rule: u32,
        wave: CausalWave,
        first_native_ordinal: u64,
        premise_arity: usize,
        binding_sources: &[ReplayBindingSource],
        flat_premises: &[FactId],
        flat_current_terms: &[ReplayTermId],
        lanes: usize,
    ) -> Arc<PendingMatchBatch> {
        assert!(first_native_ordinal > 0);
        self.0.open_pending_batches.fetch_add(1, Ordering::Relaxed);
        Arc::new(PendingMatchBatch {
            receipts: self.clone(),
            rule,
            wave,
            first_native_ordinal,
            premise_arity,
            binding_sources: binding_sources.into(),
            premises: PendingPremises::Flat(flat_premises.into()),
            current_terms: flat_current_terms.into(),
            merge_reads: Arc::new(PendingMergeReads::default()),
            prepared: (0..lanes).map(|_| OnceLock::new()).collect(),
            causes: (0..lanes).map(|_| OnceLock::new()).collect(),
        })
    }

    /// Construct a pending batch over compact join witnesses. The resolver is
    /// owned once by the batch; individual lanes carry only a packed index.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn pending_rule_batch_lazy(
        &self,
        rule: u32,
        wave: CausalWave,
        first_native_ordinal: u64,
        premise_arity: usize,
        binding_sources: &[ReplayBindingSource],
        resolver: Arc<dyn PendingPremiseResolver>,
        witness_lanes: &[u32],
        flat_current_terms: &[ReplayTermId],
    ) -> Arc<PendingMatchBatch> {
        let lanes = witness_lanes.len();
        assert!(lanes > 0, "pending match batch cannot be empty");
        let current_arity = binding_sources
            .iter()
            .filter(|source| matches!(source, ReplayBindingSource::Current { .. }))
            .count();
        assert_eq!(
            flat_current_terms.len(),
            lanes * current_arity,
            "pending current terms must be dense and lane-aligned"
        );
        assert!(first_native_ordinal > 0);
        self.0.open_pending_batches.fetch_add(1, Ordering::Relaxed);
        Arc::new(PendingMatchBatch {
            receipts: self.clone(),
            rule,
            wave,
            first_native_ordinal,
            premise_arity,
            binding_sources: binding_sources.into(),
            premises: PendingPremises::Lazy {
                resolver,
                lanes: witness_lanes.into(),
            },
            current_terms: flat_current_terms.into(),
            merge_reads: Arc::new(PendingMergeReads::default()),
            prepared: (0..lanes).map(|_| OnceLock::new()).collect(),
            causes: (0..lanes).map(|_| OnceLock::new()).collect(),
        })
    }

    pub(crate) fn reserve_native_match_ordinals(&self, lanes: usize) -> u64 {
        ReceiptShared::alloc_u64(&self.0.next_native_match, lanes)
    }

    pub(crate) fn pending_rule_cause(
        &self,
        batch: &Arc<PendingMatchBatch>,
        lane: usize,
    ) -> PendingRuleCause {
        assert!(Arc::ptr_eq(&self.0, &batch.receipts.0));
        assert!(
            lane < batch.causes.len(),
            "pending match lane is out of range"
        );
        PendingRuleCause {
            batch: Arc::clone(batch),
            lane: lane.try_into().expect("pending match batch exceeds u32"),
        }
    }

    fn promote_pending_rule_match(&self, batch: &PendingMatchBatch, lane: usize) -> CauseDraftId {
        assert!(Arc::ptr_eq(&self.0, &batch.receipts.0));
        let prepared = self
            .prepare_pending_rule_match(batch, lane)
            .unwrap_or_else(|error| panic!("cannot promote pending rule match: {error}"));
        let premises = &prepared.premises;

        let match_id = MatchDraftId::new(ReceiptShared::alloc_u64(&self.0.next_match_draft, 1));
        let cause_id = CauseDraftId::new(ReceiptShared::alloc_u64(&self.0.next_cause_draft, 1));
        let mut arena = self.0.arena.lock().unwrap();
        let premise_range = FlatRange::new(arena.provisional.premises.len(), premises.len());
        arena.provisional.premises.extend_from_slice(&premises);
        let term_start = arena.provisional.terms.len();
        arena.provisional.terms.extend_from_slice(&prepared.terms);
        let term_range = FlatRange::new(term_start, batch.binding_sources.len());
        arena.provisional.matches.install(
            match_id.get(),
            MatchDraft {
                rule: batch.rule,
                wave: batch.wave,
                native_ordinal: batch.first_native_ordinal + lane as u64,
                premises: premise_range,
                terms: term_range,
                merge_reads: Some(PendingMergeReadRef {
                    batch: Arc::clone(&batch.merge_reads),
                    lane: lane.try_into().expect("pending match batch exceeds u32"),
                }),
            },
        );
        arena
            .provisional
            .causes
            .install(cause_id.get(), CauseDraft::Rule(match_id));
        arena.counters.premise_handles += premises.len() as u64;
        arena.counters.term_handles += batch.binding_sources.len() as u64;
        arena.counters.provisional_matches += 1;
        arena.add_live_bytes(
            mem::size_of::<MatchDraft>()
                + mem::size_of::<CauseDraft>()
                + premises.len() * mem::size_of::<FactId>()
                + batch.binding_sources.len() * mem::size_of::<ReplayTermId>(),
        );
        cause_id
    }

    fn prepare_pending_rule_match<'a>(
        &self,
        batch: &'a PendingMatchBatch,
        lane: usize,
    ) -> Result<&'a PreparedMatch, String> {
        assert!(
            lane < batch.prepared.len(),
            "pending match lane is out of range"
        );
        if batch.prepared[lane].get().is_none() {
            let premises = batch.premises.resolve(lane, batch.premise_arity);
            let current_arity = batch
                .binding_sources
                .iter()
                .filter(|source| matches!(source, ReplayBindingSource::Current { .. }))
                .count();
            let current_start = lane * current_arity;
            let current_terms = &batch.current_terms[current_start..current_start + current_arity];
            let arena = self.0.arena.lock().unwrap();
            let mut terms = Vec::with_capacity(batch.binding_sources.len());
            let mut current = 0;
            for source in batch.binding_sources.iter().copied() {
                let term = match source {
                    ReplayBindingSource::Premise { premise, column } => {
                        let fact = premises[premise];
                        arena.fact_term(fact, column).ok_or_else(|| {
                            format!(
                                "missing producer-installed ReplayTermId for {fact:?} column {column}"
                            )
                        })?
                    }
                    ReplayBindingSource::Current { .. } => {
                        let term = current_terms[current];
                        current += 1;
                        term
                    }
                    ReplayBindingSource::Constant { term } => term,
                };
                if term.is_missing() {
                    return Err("pending match prepared a missing ReplayTermId".into());
                }
                terms.push(term);
            }
            drop(arena);
            let _ = batch.prepared[lane].set(PreparedMatch {
                premises: premises.into_vec().into_boxed_slice(),
                terms: terms.into_boxed_slice(),
            });
        }
        Ok(batch.prepared[lane]
            .get()
            .expect("pending match preparation disappeared"))
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
        let first_native_ordinal = self.reserve_native_match_ordinals(lanes.len());
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
                    ReplayBindingSource::Constant { term } => term,
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
                    native_ordinal: first_native_ordinal + offset as u64,
                    premises: premise_range,
                    terms: term_range,
                    merge_reads: None,
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
        arena.counters.provisional_matches += lanes.len() as u64;
        arena.add_live_bytes(
            lanes.len() * (mem::size_of::<MatchDraft>() + mem::size_of::<CauseDraft>())
                + lanes.len() * premise_arity * mem::size_of::<FactId>()
                + lanes.len() * binding_sources.len() * mem::size_of::<ReplayTermId>(),
        );
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
        assert_eq!(
            self.0.open_pending_batches.load(Ordering::Acquire),
            0,
            "cannot finalize causal wave with unresolved pending match batches"
        );
        assert_eq!(
            self.0.open_native_leases.load(Ordering::Acquire),
            0,
            "cannot finalize causal wave with queued transactional native mutations"
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
        arena
            .provisional
            .pending_equalities
            .assert_complete("equality edge");
        assert!(
            arena.facts.iter().all(Option::is_some),
            "missing dense FactId publication before causal-wave finalization"
        );
        for edge in &arena.provisional.pending_equalities.slots {
            let cause = edge.as_ref().expect("complete equality edge").cause;
            if let Err(error) = arena.validate_equality_cause_draft(cause) {
                panic!("{error}");
            }
        }
        for alias in &arena.provisional.pending_native_aliases {
            if let Err(error) = arena.validate_equality_cause_draft(alias.cause) {
                panic!("{error}");
            }
        }

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
                .slots
                .iter()
                .map(|edge| edge.as_ref().expect("complete equality edge").cause),
        );
        stack.extend(
            arena
                .provisional
                .pending_native_aliases
                .iter()
                .map(|alias| alias.cause),
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
                CauseDraft::Source(_)
                | CauseDraft::Rebuild { .. }
                | CauseDraft::ContainerCanonicalize { .. }
                | CauseDraft::ContainerRefresh { .. } => {}
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
        let mut promotion_order = reachable_matches
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(index, promote)| promote.then_some(index))
            .collect::<Vec<_>>();
        promotion_order.sort_unstable_by_key(|index| {
            arena.provisional.matches.slots[*index]
                .as_ref()
                .expect("reachable match draft")
                .native_ordinal
        });
        for index in promotion_order {
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
            let merge_reads = draft
                .merge_reads
                .as_ref()
                .map(|reads| reads.batch.lane(reads.lane))
                .unwrap_or_default();
            let merge_reads_start = arena.durable_merge_reads.len();
            arena.durable_merge_reads.extend_from_slice(&merge_reads);
            arena.durable_matches.push(DurableMatch {
                rule: draft.rule,
                wave: draft.wave,
                premises: FlatRange::new(premises_start, draft.premises.len as usize),
                terms: FlatRange::new(terms_start, draft.terms.len as usize),
                merge_reads: FlatRange::new(merge_reads_start, merge_reads.len()),
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
                CauseDraft::Rebuild {
                    wave,
                    prior_fact,
                    as_of_edges,
                    equalities,
                } => {
                    if prior_fact.is_missing() {
                        arena.counters.promotion_misses += 1;
                        panic!("rebuild cause references a missing prior FactId");
                    }
                    let pair_range = equalities.as_range();
                    let pair_len = pair_range.len();
                    let start = arena.durable_rebuild_equalities.len();
                    arena.durable_rebuild_equalities.reserve(pair_len);
                    for pair_index in pair_range {
                        let pair = arena.provisional.rebuild_equalities[pair_index];
                        arena.durable_rebuild_equalities.push(pair);
                    }
                    arena.counters.rebuild_causes += 1;
                    arena.counters.rebuild_equalities += pair_len as u64;
                    arena.counters.rebuild_bytes += (mem::size_of::<DurableCause>()
                        + pair_len * mem::size_of::<TypedCellEquality>())
                        as u64;
                    DurableCause::Rebuild {
                        wave,
                        prior_fact,
                        as_of_edges,
                        equalities: FlatRange::new(start, pair_len),
                    }
                }
                CauseDraft::ContainerCanonicalize {
                    wave,
                    as_of_edges,
                    equalities,
                } => {
                    let pair_range = equalities.as_range();
                    let pair_len = pair_range.len();
                    let start = arena.durable_rebuild_equalities.len();
                    arena.durable_rebuild_equalities.reserve(pair_len);
                    for pair_index in pair_range {
                        let pair = arena.provisional.rebuild_equalities[pair_index];
                        arena.durable_rebuild_equalities.push(pair);
                    }
                    arena.counters.container_causes += 1;
                    arena.counters.container_equalities += pair_len as u64;
                    arena.counters.container_bytes += (mem::size_of::<DurableCause>()
                        + pair_len * mem::size_of::<TypedCellEquality>())
                        as u64;
                    DurableCause::ContainerCanonicalize {
                        wave,
                        as_of_edges,
                        equalities: FlatRange::new(start, pair_len),
                    }
                }
                CauseDraft::ContainerRefresh {
                    wave,
                    prior_fact,
                    as_of_edges,
                    equalities,
                } => {
                    if prior_fact.is_missing() {
                        arena.counters.promotion_misses += 1;
                        panic!("container refresh references a missing prior FactId");
                    }
                    let pair_range = equalities.as_range();
                    let pair_len = pair_range.len();
                    let start = arena.durable_rebuild_equalities.len();
                    arena.durable_rebuild_equalities.reserve(pair_len);
                    for pair_index in pair_range {
                        let pair = arena.provisional.rebuild_equalities[pair_index];
                        arena.durable_rebuild_equalities.push(pair);
                    }
                    arena.counters.container_causes += 1;
                    arena.counters.container_equalities += pair_len as u64;
                    arena.counters.container_bytes += (mem::size_of::<DurableCause>()
                        + pair_len * mem::size_of::<TypedCellEquality>())
                        as u64;
                    DurableCause::ContainerRefresh {
                        wave,
                        prior_fact,
                        as_of_edges,
                        equalities: FlatRange::new(start, pair_len),
                    }
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
        for edge in pending_equalities.slots {
            let edge = edge.expect("complete equality edge");
            assert_eq!(
                edge.node.id.get() as usize,
                arena.durable_equalities.len() + 1,
                "equality node IDs must remain dense across wave finalization"
            );
            assert_eq!(
                edge.node.edge, edge.node.id,
                "each equality node and edge must share one 1:1 ID"
            );
            let index = arena
                .provisional
                .causes
                .index(edge.cause.get())
                .expect("equality cause belongs to current segment");
            let cause = cause_map[index].expect("applied equality cause is reachable");
            let summary = arena
                .cause_summary(edge.cause)
                .expect("applied equality cause has a cached classification");
            let reason = arena.equality_reason(cause, summary);
            arena.durable_equalities.push(DurableEquality {
                node: edge.node,
                proposal: edge.proposal,
                native_parent: edge.native_parent,
                native_child: edge.native_child,
                reason,
            });
        }
        let pending_native_aliases = mem::take(&mut arena.provisional.pending_native_aliases);
        for alias in pending_native_aliases {
            let index = arena
                .provisional
                .causes
                .index(alias.cause.get())
                .expect("native alias cause belongs to current segment");
            let cause = cause_map[index].expect("native alias cause is reachable");
            let summary = arena
                .cause_summary(alias.cause)
                .expect("native alias cause has a cached classification");
            let reason = arena.equality_reason(cause, summary);
            arena.durable_native_aliases.push(DurableNativeAlias {
                proposal: alias.proposal,
                native_parent: alias.native_parent,
                native_child: alias.native_child,
                reason,
            });
            arena.counters.native_alias_unions += 1;
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
            self.0.open_pending_batches.load(Ordering::Acquire),
            0,
            "cannot snapshot causal receipts with unresolved pending match batches"
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
                merge_reads: arena.durable_merge_reads[record.merge_reads.as_range()].into(),
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
        let equality_nodes = arena
            .durable_equalities
            .iter()
            .map(|edge| edge.node.clone())
            .collect();
        let equalities = arena
            .durable_equalities
            .iter()
            .map(|edge| EqualityRecord {
                id: edge.node.edge,
                wave: edge.proposal.wave,
                left: edge.proposal.left,
                right: edge.proposal.right,
                native_parent: edge.native_parent,
                native_child: edge.native_child,
                reason: edge.reason.clone(),
            })
            .collect();
        let native_aliases = arena
            .durable_native_aliases
            .iter()
            .map(|alias| NativeAliasRecord {
                wave: alias.proposal.wave,
                left: alias.proposal.left,
                right: alias.proposal.right,
                native_parent: alias.native_parent,
                native_child: alias.native_child,
                reason: alias.reason.clone(),
            })
            .collect();
        let causes = arena
            .durable_causes
            .iter()
            .map(|entry| match entry {
                DurableCause::Source(source) => ReceiptCauseRecord::Source(source.clone()),
                DurableCause::Rule(rule) => ReceiptCauseRecord::Rule(*rule),
                DurableCause::Rebuild {
                    wave,
                    prior_fact,
                    as_of_edges,
                    equalities,
                } => ReceiptCauseRecord::Rebuild {
                    wave: *wave,
                    prior_fact: *prior_fact,
                    equalities: EqualityLandmark {
                        as_of_edges: *as_of_edges,
                        pairs: arena.durable_rebuild_equalities[equalities.as_range()].into(),
                    },
                },
                DurableCause::ContainerCanonicalize {
                    wave,
                    as_of_edges,
                    equalities,
                } => ReceiptCauseRecord::ContainerCanonicalize {
                    wave: *wave,
                    equalities: EqualityLandmark {
                        as_of_edges: *as_of_edges,
                        pairs: arena.durable_rebuild_equalities[equalities.as_range()].into(),
                    },
                },
                DurableCause::ContainerRefresh {
                    wave,
                    prior_fact,
                    as_of_edges,
                    equalities,
                } => ReceiptCauseRecord::ContainerRefresh {
                    wave: *wave,
                    prior_fact: *prior_fact,
                    equalities: EqualityLandmark {
                        as_of_edges: *as_of_edges,
                        pairs: arena.durable_rebuild_equalities[equalities.as_range()].into(),
                    },
                },
                DurableCause::Merge { incoming, prior } => ReceiptCauseRecord::Merge {
                    incoming: *incoming,
                    prior: match prior {
                        DurablePrior::Fact(fact) => ReceiptCausePrior::Fact(*fact),
                        DurablePrior::Cause(cause) => ReceiptCausePrior::Cause(*cause),
                    },
                },
            })
            .collect();
        let mut check_roots = arena.check_roots.values().cloned().collect::<Vec<_>>();
        check_roots.sort_by_key(|root| root.check);
        ReceiptSnapshot {
            facts,
            matches,
            equality_nodes,
            equalities,
            native_aliases,
            causes,
            check_roots,
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
        let lower_id = lower
            .add_draft(
                CauseDraft::Rule(MatchDraftId::new(1)),
                EqualityCauseSummary::Rule,
            )
            .id();
        let mut higher = receipts.new_batch();
        let higher_id = higher
            .add_draft(
                CauseDraft::Rule(MatchDraftId::new(2)),
                EqualityCauseSummary::Rule,
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
    fn batch_local_prior_lookup_handles_interleaved_fact_ids() {
        let receipts = CausalReceipts::default();
        let table = TableId::new_const(2);
        let sort = ReplaySortId::new(31);
        receipts
            .register_table_layout(table, &[Some(sort)])
            .unwrap();

        let first_row = [Value::new_const(31)];
        let gap_row = [Value::new_const(32)];
        let last_row = [Value::new_const(33)];
        let first_term = receipts.intern_literal(sort, ReplayLiteral::I64(31), first_row[0]);
        let gap_term = receipts.intern_literal(sort, ReplayLiteral::I64(32), gap_row[0]);
        let last_term = receipts.intern_literal(sort, ReplayLiteral::I64(33), last_row[0]);

        let mut local = receipts.new_batch();
        let first_fact = local.record_fact_with_terms(
            table,
            receipts.source_draft(SourceRef::Synthetic(31)),
            &first_row,
            Some(&[first_term]),
        );
        let mut interleaved = receipts.new_batch();
        let gap_fact = interleaved.record_fact_with_terms(
            table,
            receipts.source_draft(SourceRef::Synthetic(32)),
            &gap_row,
            Some(&[gap_term]),
        );
        let last_fact = local.record_fact_with_terms(
            table,
            receipts.source_draft(SourceRef::Synthetic(33)),
            &last_row,
            Some(&[last_term]),
        );
        assert!(first_fact < gap_fact && gap_fact < last_fact);

        let first_cache = receipts.source_draft(SourceRef::Synthetic(34));
        let last_cache = receipts.source_draft(SourceRef::Synthetic(35));
        assert_eq!(
            local.cache_prior_fact_terms(first_cache, first_fact, table),
            1
        );
        assert_eq!(
            local.cache_prior_fact_terms(last_cache, last_fact, table),
            1
        );
        let (_, first_range) = local.rebuild_term_ranges[&first_cache];
        let (_, last_range) = local.rebuild_term_ranges[&last_cache];
        assert_eq!(&local.rebuild_terms[first_range.as_range()], &[first_term]);
        assert_eq!(&local.rebuild_terms[last_range.as_range()], &[last_term]);

        interleaved.publish();
        local.publish();
        receipts.finalize_wave();
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
