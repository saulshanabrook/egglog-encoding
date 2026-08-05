#[macro_use]
#[cfg(test)]
pub(crate) mod table_shortcuts;
#[macro_use]
pub(crate) mod action;
pub(crate) mod base_values;
pub(crate) mod common;
pub(crate) mod containers;
pub(crate) mod dependency_graph;
pub(crate) mod free_join;
pub(crate) mod hash_index;
pub(crate) mod offsets;
pub(crate) mod parallel_heuristics;
pub(crate) mod pool;
/// Causal trace records, capture, borrowed views, and cold explanation.
///
/// The module-level reference ties each retained or derived field to the
/// egglog semantic event it represents, its consumer, and its necessity.
pub mod provenance;
pub(crate) mod query;
pub(crate) mod row_buffer;
pub(crate) mod table;

pub(crate) mod table_spec;
pub(crate) mod uf;

#[cfg(test)]
mod tests;

pub use action::{ExecutionState, MergeVal, QueryEntry, WriteVal};
pub use base_values::{BaseValue, BaseValueId, BaseValuePrinter, BaseValues, Boxed};
pub use common::Value;
pub use containers::{
    ContainerRebuildSummary, ContainerValue, ContainerValueId, ContainerValues, TraceCaptureError,
    TraceContainerKind,
};
pub use free_join::{
    AtomId, CounterId, Database, ExternalFunction, ExternalFunctionId, GroundedRuleMatch,
    GroundedRuleRunError, GroundedRuleRunOutcome, TableId, TraceMergeError, Variable,
    make_external_func, plan::PlanStrategy,
};
pub use hash_index::TupleIndex;
pub use offsets::{OffsetRange, RowId, Subset, SubsetRef};
pub use pool::{Pool, PoolSet, Pooled};
pub use provenance::{
    AppliedEqualityId, CauseDraftId, CauseId, CauseRef, Criterion, CriterionCaptureSpec,
    CriterionEndpointOccurrence, CriterionEndpointSource, CriterionEquality, DeferredEqualityCause,
    EqualityEndpoint, EqualityReason, FactCellRef, FactId, Firing, FiringCaptureSpec,
    FiringEqualitySource, FiringId, HistoricalFactCell, HistoryPosition, MergeRead,
    PremiseOccurrence, PreparedRekey, ProjectedEqualityProposal, RawAppliedEquality, RawCause,
    RawEqualityEndpoint, RawEqualitySupport, RawFactRecord, RawRekeyRecord, RawTermAvailability,
    RekeyOutcome, ReplayAliasPlan, ReplayCallSpec, ReplayLiteral, ReplayOpId, ReplaySortId,
    ReplayTableKind, ReplayTableSchema, ReplayTerm, ReplayTermId, RowOriginSiteId, RuleBindingSpec,
    SourceRef, Tombstone, Trace, TraceLifecycleError, TraceTotals, TraceView, TraceViewError,
    TypedCellEquality, TypedEqualityProposal, Wave,
};
pub use query::{
    CachedPlan, CaptureBuildError, GroundedProbe, GroundedRule, QueryBuilder, QueryError,
    RuleBuilder, RuleId, RuleSet, RuleSetBuilder,
};
pub use row_buffer::TaggedRowBuffer;
pub use table::{MergeCallback, SortedWritesTable};
pub use table_spec::{
    ColumnId, Constraint, MutationBuffer, Offset, Rebuilder, Row, Table, TableChange, TableSpec,
    TableVersion, ValueRebuilder, WrappedTable,
};
// These capability types occur in public table extension traits. Their
// constructors remain private, but downstream implementations must be able to
// name the types in method signatures.
#[doc(hidden)]
pub use table_spec::{MaintenanceRemoval, MutationTransaction};
pub use uf::DisplacedTable;

use egglog_numeric_id as numeric_id;
use egglog_union_find as union_find;
