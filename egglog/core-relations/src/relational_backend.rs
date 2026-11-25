//! Backend-neutral relational execution. The frontend retains its schedule and
//! primitive registry; a replacement owns function storage and rule execution.

use std::sync::Arc;

use crate::{
    ColumnId, Constraint, ExecutionState, MergeFn, QueryEntry, TableId, TableSchema, Variable,
    WrappedTable,
};

/// Logical atom before physical planning, including seminaive restrictions.
#[derive(Clone, Debug)]
pub struct RelationalAtom {
    pub table: TableId,
    pub columns: Vec<(ColumnId, Variable)>,
    pub constraints: Vec<Constraint>,
    /// The key occurs in at least one of these columns (a disjunction).
    pub occurrence: Option<(QueryEntry, Vec<ColumnId>)>,
}

/// One seminaive variant. Local, unused body variables are existential.
#[derive(Clone, Debug)]
pub struct RelationalRule {
    pub description: Arc<str>,
    pub atoms: Vec<RelationalAtom>,
    pub inputs: Vec<Variable>,
    pub instructions: Vec<crate::ActionInstruction>,
}

/// Physical function-table layout and its compiled merge callback.
/// Callbacks are host extensions, just like user-defined primitives.
pub struct BackendTable {
    /// Bootstrap identity table: any attempt to write native unions is an error.
    pub read_only: bool,
    pub schema: TableSchema,
    pub timestamp: Option<ColumnId>,
    pub rebuild_columns: Vec<ColumnId>,
    pub merge: Option<Box<MergeFn>>,
}

/// A replacement has no native matcher or table fallback. It may call opaque
/// host primitives through `state`; those calls see its own tables.
pub trait RelationalBackend: Send + Sync {
    fn create_table(&self, definition: BackendTable) -> WrappedTable;

    /// Execute all matches against the committed snapshot, staging actions.
    /// Return the number of successful action executions per supplied rule.
    fn execute(
        &self,
        rules: &[RelationalRule],
        state: &mut ExecutionState,
    ) -> Result<Vec<usize>, String>;

    /// Report storage errors, including failures during the preceding commit.
    fn check_tables(&self, state: &ExecutionState) -> Result<(), String>;
}
