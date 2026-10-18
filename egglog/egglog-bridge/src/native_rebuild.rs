//! Bulk maintenance plans compiled once from encoded table declarations.

use super::*;
use core_relations::{
    EqualityCursor, ExplainedUfTable, RebuildInput, RebuildValues, RowRebuilder, TableVersion,
};
use egglog_reports::PreMergeTiming;

/// Compose the witness for one canonicalized row. Steps contain only columns
/// that changed, each proving old value = new value in this frozen UF snapshot.
/// Implementations stage ordinary proof records; the maintenance engine does
/// not introduce a new trusted proof operation.
pub trait RebuildProof: Send + Sync {
    fn compose(
        &self,
        row: &[Value],
        steps: &[(ColumnId, Value)],
        state: &mut ExecutionState,
    ) -> Value;
}

#[derive(Clone)]
struct UfColumns {
    table: TableId,
    columns: Vec<ColumnId>,
    consumed: Option<EqualityCursor>,
}

#[derive(Clone)]
pub(super) struct NativeRebuildPlan {
    table: TableId,
    timestamp_column: ColumnId,
    sources: Vec<UfColumns>,
    consumed: Option<TableVersion>,
    proof: Option<(ColumnId, Arc<dyn RebuildProof>)>,
}

struct PreparedRebuilder<'a> {
    columns: Vec<(ColumnId, &'a ExplainedUfTable)>,
    proof: Option<&'a (ColumnId, Arc<dyn RebuildProof>)>,
}

impl RowRebuilder for PreparedRebuilder<'_> {
    fn rebuild(&self, row: &[Value], state: &mut ExecutionState, out: &mut Vec<Value>) -> bool {
        let mut changes = SmallVec::<[(usize, Value); 4]>::new();
        let mut steps = SmallVec::<[(ColumnId, Value); 4]>::new();
        for &(column, uf) in &self.columns {
            let index = column.index();
            let canonical = uf.find(row[index]);
            if canonical != row[index] {
                changes.push((index, canonical));
                if self.proof.is_some() {
                    steps.push((column, uf.canonical_reason(row[index], state).unwrap()));
                }
            }
        }
        if changes.is_empty() {
            return false;
        }
        out.extend_from_slice(row);
        for (column, value) in changes {
            out[column] = value;
        }
        if let Some((column, proof)) = self.proof {
            out[column.index()] = proof.compose(row, &steps, state);
        }
        true
    }
}

impl EGraph {
    /// Register scalar equality columns for bulk maintenance. Other columns,
    /// including container payloads, retain their existing maintenance owner.
    pub fn register_native_rebuild(
        &mut self,
        view: FunctionId,
        columns: &[(ColumnId, FunctionId)],
        proof: Option<(ColumnId, Arc<dyn RebuildProof>)>,
    ) {
        if columns.is_empty() {
            return;
        }
        let info = &self.funcs[view];
        assert!(
            !self
                .native_rebuilds
                .iter()
                .any(|plan| plan.table == info.table)
        );
        let mut sources: Vec<UfColumns> = Vec::new();
        for &(column, uf) in columns {
            let table = self.funcs[uf].table;
            assert!(self.db.get_table(table).as_any().is::<ExplainedUfTable>());
            if let Some(source) = sources.iter_mut().find(|source| source.table == table) {
                source.columns.push(column);
            } else {
                sources.push(UfColumns {
                    table,
                    columns: vec![column],
                    consumed: None,
                });
            }
        }
        self.native_rebuilds.push(NativeRebuildPlan {
            table: info.table,
            timestamp_column: ColumnId::from_usize(info.schema.len()),
            sources,
            consumed: None,
            proof,
        });
    }

    /// Execute one wave against a frozen UF snapshot. The enclosing schedule
    /// drives the fixed point and interleaves container maintenance first.
    pub fn run_native_rebuild(&mut self, context: ExternalContext<'_>) -> Result<IterationReport> {
        install_thread_pool(self.thread_pool(), || {
            let timer = Instant::now();
            let mut acknowledgements = Vec::new();
            let mut changed = false;
            let next_ts = self.next_ts().to_value();
            for (index, plan) in self.native_rebuilds.iter().enumerate() {
                let current = self.db.get_table(plan.table).version();
                let mut cursors = Vec::with_capacity(plan.sources.len());
                let mut dirty = Vec::with_capacity(plan.sources.len());
                let mut columns = Vec::new();
                let mut reset = plan.consumed.is_none();
                for source in &plan.sources {
                    let uf = self
                        .db
                        .get_table(source.table)
                        .as_any()
                        .downcast_ref::<ExplainedUfTable>()
                        .unwrap();
                    let cursor = uf.cursor();
                    cursors.push(cursor);
                    let events = source.consumed.and_then(|cursor| uf.events_since(cursor));
                    reset |= events.is_none();
                    let events =
                        events.unwrap_or_else(|| uf.events_since(uf.start_cursor()).unwrap());
                    dirty.push(events.iter().map(|event| event.loser).collect::<Vec<_>>());
                    columns.extend(source.columns.iter().map(|&column| (column, uf)));
                }
                if !reset
                    && plan.consumed.as_ref() == Some(&current)
                    && dirty.iter().all(Vec::is_empty)
                {
                    continue;
                }
                let invalidated: Vec<_> = plan
                    .sources
                    .iter()
                    .zip(&dirty)
                    .map(|(source, values)| RebuildValues {
                        columns: &source.columns,
                        values,
                    })
                    .collect();
                let progress = self.db.rebuild_rows(
                    RebuildInput {
                        table: plan.table,
                        after: if reset { None } else { plan.consumed.as_ref() },
                        invalidated: &invalidated,
                        timestamp_column: plan.timestamp_column,
                        next_timestamp: next_ts,
                    },
                    &PreparedRebuilder {
                        columns,
                        proof: plan.proof.as_ref(),
                    },
                    context,
                );
                changed |= progress.changed;
                acknowledgements.push((index, progress.consumed, cursors));
            }
            changed |= self.db.merge_all();
            if let Some(message) = self.panic_message.lock().unwrap().take() {
                return Err(PanicError(message).into());
            }
            // A failed wave must not acknowledge an uncommitted source batch.
            for (index, consumed, cursors) in acknowledgements {
                let plan = &mut self.native_rebuilds[index];
                plan.consumed = Some(consumed);
                for (source, cursor) in plan.sources.iter_mut().zip(cursors) {
                    source.consumed = Some(cursor);
                }
            }
            self.inc_ts();
            Ok(IterationReport {
                rule_set_report: RuleSetReport {
                    changed,
                    // All work is native maintenance, charged to rebuild_time.
                    // Preserve the serial report's exhaustive phase contract.
                    pre_merge: if egglog_concurrency::current_num_threads() == 1 {
                        PreMergeTiming::Split {
                            search: Duration::ZERO,
                            apply: Duration::ZERO,
                            unattributed: Duration::ZERO,
                        }
                    } else {
                        PreMergeTiming::default()
                    },
                    ..Default::default()
                },
                rebuild_time: timer.elapsed(),
                ..Default::default()
            })
        })
    }
}
