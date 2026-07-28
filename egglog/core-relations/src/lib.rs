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
pub(crate) mod provenance;
pub(crate) mod query;
pub(crate) use provenance as receipts;
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
    CausalContainerKind, ContainerRebuildSummary, ContainerValue, ContainerValueId, ContainerValues,
};
pub use free_join::{
    AtomId, CounterId, Database, ExternalFunction, ExternalFunctionId, GroundedRuleMatch,
    GroundedRuleRunError, GroundedRuleRunOutcome, TableId, Variable, make_external_func,
    plan::PlanStrategy,
};
pub use hash_index::TupleIndex;
pub use offsets::{OffsetRange, RowId, Subset, SubsetRef};
pub use pool::{Pool, PoolSet, Pooled};
pub use query::{
    CachedPlan, GroundedProbe, GroundedRule, QueryBuilder, QueryError, ReceiptBuildError,
    RuleBuilder, RuleId, RuleSet, RuleSetBuilder,
};
pub use receipts::{
    AppliedEqualityId, CausalReceiptTotals, CausalReceiptView, CausalReceiptViewCounters,
    CausalReceipts, CausalWave, CauseDraftId, CheckEndpointOccurrence, CheckEndpointSource,
    CheckReceiptSpec, CheckRoot, DeferredEqualityCause, EqualityEdgeCount, EqualityEndpoint,
    EqualityReason, FactCellRef, FactId, HistoricalFactCell, HistoryPosition, MergeOriginSelector,
    PreparedRekey, ProjectedAppliedEquality, RawAliasWindow, RawAppliedEquality,
    RawEqualityEndpoint, RawEqualitySupport, RawFactRecord, RawMatchRecord, RawReceiptCause,
    RawRekeyRecord, RawTermAvailability, ReceiptCauseId, ReceiptCausePrior, ReceiptCauseRef,
    ReceiptCounters, ReceiptEqualitySource, ReceiptPremiseOccurrence, ReceiptViewError,
    RekeyOutcome, RemovalRecord, ReplayConstructorSpec, ReplayLiteral, ReplayOpId, ReplaySortId,
    ReplayTableKind, ReplayTableSchema, ReplayTerm, ReplayTermCounters, ReplayTermId,
    RowOriginSiteId, RuleBindingSpec, RuleMatchId, RuleReceiptSpec, SourceReceiptSpec, SourceRef,
    TypedCellEquality, TypedEqualityProposal,
};
pub use row_buffer::TaggedRowBuffer;
pub use table::{MergeFn, SortedWritesTable};
pub use table_spec::{
    ColumnId, Constraint, MutationBuffer, Offset, Rebuilder, Row, Table, TableChange, TableSpec,
    TableVersion, ValueRebuilder, WrappedTable,
};
pub use uf::DisplacedTable;

use egglog_numeric_id as numeric_id;
use egglog_union_find as union_find;
