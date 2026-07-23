//! Apply value-level rebuilds to a table.

use std::{cmp, mem};

use crate::numeric_id::NumericId;
use rayon::prelude::*;

use crate::{
    ColumnId, ContainerRebuildSummary, EqualityEdgeCount, ExecutionState, FactId, Offset, RowId,
    Subset, Table, TableId, TaggedRowBuffer, Value, WrappedTable,
    common::HashSet,
    hash_index::{ColumnIndex, Index},
    offsets::Offsets,
    parallel_heuristics::parallelize_rebuild,
    table_spec::{MutationBuffer, MutationTransaction, Rebuilder, WrappedTableRef},
};

use super::SortedWritesTable;

impl SortedWritesTable {
    fn new_rebuild_buffer(
        &self,
        transaction: Option<&MutationTransaction>,
    ) -> Box<dyn MutationBuffer> {
        let mut buffer = self.new_buffer();
        if let Some(transaction) = transaction {
            buffer.defer_until(transaction.clone());
        }
        buffer
    }

    /// Validate and stage one semantic rekey through the existing native
    /// removal/insertion path. Receipt work is entirely absent when capture is
    /// disabled; when enabled, every fallible provenance lookup precedes the
    /// first staged mutation.
    fn stage_rebuilt_row<const RECEIPTS: bool>(
        &self,
        mutation_buf: &mut dyn MutationBuffer,
        row_id: RowId,
        rebuilt_row: &mut [Value],
        next_ts: Value,
        exec_state: &ExecutionState,
        equality_cutoff: Option<EqualityEdgeCount>,
    ) -> bool {
        let Some(current_row) = self.data.get_row(row_id) else {
            return false;
        };
        if let Some(sort_by) = self.sort_by {
            rebuilt_row[sort_by.index()] = next_ts;
        }

        if RECEIPTS {
            let receipts = exec_state
                .causal_receipts()
                .expect("receipt rebuild mode requires an enabled arena");
            let prior_fact = self.data.fact_id(row_id).unwrap_or(FactId::MISSING);
            let cause = receipts
                .rebuild_draft(
                    self.table_id,
                    exec_state.causal_wave(),
                    prior_fact,
                    current_row,
                    rebuilt_row,
                    &self.to_rebuild,
                    equality_cutoff.expect("receipt rebuild is missing its equality landmark"),
                )
                .unwrap_or_else(|error| panic!("cannot record exact table rebuild: {error}"));
            mutation_buf.stage_remove(&current_row[0..self.n_keys]);
            mutation_buf.stage_insert_with_cause(rebuilt_row, cause);
        } else {
            mutation_buf.stage_remove(&current_row[0..self.n_keys]);
            mutation_buf.stage_insert(rebuilt_row);
        }
        true
    }

    fn refresh_rebuild_index(&mut self) {
        let mut index = mem::replace(
            &mut self.rebuild_index,
            Index::new(vec![], ColumnIndex::new()),
        );
        WrappedTableRef::with_wrapper(self, |wrapped| {
            index.refresh(wrapped);
        });
        self.rebuild_index = index;
    }

    pub(super) fn do_rebuild(
        &mut self,
        table_id: TableId,
        table: &WrappedTable,
        next_ts: Value,
        exec_state: &mut ExecutionState,
        equality_cutoff: Option<EqualityEdgeCount>,
        transaction: Option<&MutationTransaction>,
    ) -> bool {
        // Keep receipt selection outside the changed-row loops below.
        if exec_state.causal_receipts().is_none() {
            self.do_rebuild_mode::<false>(
                table_id,
                table,
                next_ts,
                exec_state,
                equality_cutoff,
                transaction,
            )
        } else {
            self.do_rebuild_mode::<true>(
                table_id,
                table,
                next_ts,
                exec_state,
                equality_cutoff,
                transaction,
            )
        }
    }

    fn do_rebuild_mode<const RECEIPTS: bool>(
        &mut self,
        table_id: TableId,
        table: &WrappedTable,
        next_ts: Value,
        exec_state: &mut ExecutionState,
        equality_cutoff: Option<EqualityEdgeCount>,
        transaction: Option<&MutationTransaction>,
    ) -> bool {
        if self.to_rebuild.is_empty() {
            return false;
        }
        let Some(rebuilder) = table.rebuilder(&self.to_rebuild) else {
            return false;
        };
        // First, decide whether to do an incremental or full rebuild.
        if let Some(hint_col) = rebuilder.hint_col() {
            // Incremental rebuilds are possible if we can scan the subset of the columns that are
            // relevant.
            let (to_scan, deferred_cursor) = if transaction.is_some() {
                let (subset, version) = self.subset_tracker.preview_recent_updates(table_id, table);
                (subset, Some(version))
            } else {
                (self.subset_tracker.recent_updates(table_id, table), None)
            };
            let changed = if incremental_rebuild(
                to_scan.size(),
                self.data.next_row().index(),
                parallelize_rebuild(to_scan.size()),
            ) {
                self.rebuild_incremental::<RECEIPTS>(
                    table,
                    &*rebuilder,
                    hint_col,
                    to_scan,
                    next_ts,
                    exec_state,
                    equality_cutoff,
                    transaction,
                )
            } else {
                self.rebuild_nonincremental::<RECEIPTS>(
                    &*rebuilder,
                    next_ts,
                    exec_state,
                    equality_cutoff,
                    transaction,
                )
            };
            if let Some(version) = deferred_cursor {
                transaction
                    .expect("deferred rebuild cursor requires a transaction")
                    .defer_rebuild_cursor(self.table_id, table_id, version);
            }
            changed
        } else {
            self.rebuild_nonincremental::<RECEIPTS>(
                &*rebuilder,
                next_ts,
                exec_state,
                equality_cutoff,
                transaction,
            )
        }
    }

    pub(super) fn refresh_rows_for_values(
        &mut self,
        summary: &ContainerRebuildSummary,
        next_ts: Value,
        exec_state: Option<&ExecutionState>,
        transaction: Option<&MutationTransaction>,
    ) -> bool {
        if summary.dirty_ids().is_empty() || self.to_rebuild.is_empty() {
            return false;
        }
        // Reuse the rebuild index to find rows whose rebuildable columns mention
        // one of the same-id dirty container ids.
        self.refresh_rebuild_index();

        let mut candidate_rows = HashSet::<RowId>::default();
        for value in summary.dirty_ids() {
            let Some(subset) = self.rebuild_index.get_subset(value) else {
                continue;
            };
            subset.offsets(|row_id| {
                candidate_rows.insert(row_id);
            });
        }

        if candidate_rows.is_empty() {
            return false;
        }

        assert_eq!(
            self.data.fact_ids.is_some(),
            exec_state.is_some(),
            "container refresh receipt mode disagrees with the table FactId sidecar"
        );

        let mut changed = false;
        let mut mutation_buf = self.new_rebuild_buffer(transaction);
        let mut refreshed_row = Vec::<Value>::with_capacity(self.n_columns);
        for row_id in candidate_rows {
            let Some(current_row) = self.data.get_row(row_id) else {
                continue;
            };
            let cause = if let Some(exec_state) = exec_state {
                let receipts = exec_state
                    .causal_receipts()
                    .expect("receipt container refresh requires the receipt arena");
                let mut candidates = Vec::new();
                for column in &self.to_rebuild {
                    let value = current_row[column.index()];
                    let sort = exec_state
                        .causal_replay_sort(self.table_id, *column)
                        .unwrap_or_else(|| {
                            panic!(
                                "container refresh table column {} has no replay sort",
                                column.index()
                            )
                        });
                    let Some(dependencies) = summary.dirty_dependency_candidates(sort, value)
                    else {
                        continue;
                    };
                    assert!(
                        receipts.lookup_term(sort, value).is_some(),
                        "container refresh value is not installed for its table-column sort"
                    );
                    for dependency in dependencies {
                        assert_eq!(
                            dependency.dependency.wave,
                            exec_state.causal_wave(),
                            "container refresh dependency belongs to another causal wave"
                        );
                    }
                    candidates.push((*column, dependencies));
                }
                if candidates.is_empty() {
                    // A raw rebuild-index hit in another table-column sort is
                    // not an exact container dependency.
                    continue;
                }
                let prior_fact = self.data.fact_id(row_id).unwrap_or(FactId::MISSING);
                let Some(cause) = receipts
                    .container_refresh_draft(prior_fact, &candidates)
                    .unwrap_or_else(|error| {
                        panic!("cannot record exact container refresh: {error}")
                    })
                else {
                    // The row owns another structural version of the same raw
                    // container candidate. It is unaffected by this exact
                    // dependency.
                    continue;
                };
                Some(cause)
            } else {
                None
            };
            // Preserve the logical row and only advance its sort/timestamp
            // column, so seminaive treats this as a fresh parent-row delta.
            mutation_buf.stage_remove(&current_row[0..self.n_keys]);
            refreshed_row.clear();
            refreshed_row.extend_from_slice(current_row);
            if let Some(sort_by) = self.sort_by {
                refreshed_row[sort_by.index()] = next_ts;
            }
            if let Some(cause) = cause {
                mutation_buf.stage_insert_with_cause(&refreshed_row, cause);
            } else {
                mutation_buf.stage_insert(&refreshed_row);
            }
            changed = true;
        }
        changed
    }

    #[allow(clippy::too_many_arguments)]
    fn rebuild_incremental<const RECEIPTS: bool>(
        &mut self,
        table: &WrappedTable,
        rebuilder: &dyn Rebuilder,
        search_col: ColumnId,
        to_scan: Subset,
        next_ts: Value,
        exec_state: &mut ExecutionState,
        equality_cutoff: Option<EqualityEdgeCount>,
        transaction: Option<&MutationTransaction>,
    ) -> bool {
        self.refresh_rebuild_index();
        let mut buf = TaggedRowBuffer::new(1);
        table.scan_project(
            to_scan.as_ref(),
            &[search_col],
            Offset::new(0),
            usize::MAX,
            &[],
            &mut buf,
        );

        if parallelize_rebuild(to_scan.size()) {
            WrappedTableRef::with_wrapper(self, |wrapped| {
                buf.par_iter()
                    .fold(
                        || {
                            (
                                self.new_rebuild_buffer(transaction),
                                exec_state.clone(),
                                false,
                            )
                        },
                        |(mut mutation_buf, mut exec_state, mut changed), (_, row)| {
                            let Some(subset) = self.rebuild_index.get_subset(&row[0]) else {
                                return (mutation_buf, exec_state, changed);
                            };
                            let mut scanned = TaggedRowBuffer::new(self.n_columns);
                            rebuilder.rebuild_subset(
                                wrapped,
                                subset,
                                &mut scanned,
                                &mut exec_state,
                            );
                            for (row_id, row) in scanned.non_stale_mut() {
                                changed |= self.stage_rebuilt_row::<RECEIPTS>(
                                    &mut *mutation_buf,
                                    row_id,
                                    row,
                                    next_ts,
                                    &exec_state,
                                    equality_cutoff,
                                );
                            }
                            (mutation_buf, exec_state, changed)
                        },
                    )
                    .map(|(_, _, changed)| changed)
                    .max()
                    .unwrap_or(false)
            })
        } else {
            let mut scratch = TaggedRowBuffer::new(self.n_columns);
            let mut changed = false;
            for (_, id) in buf.iter() {
                let Some(subset) = self.rebuild_index.get_subset(&id[0]) else {
                    continue;
                };
                WrappedTableRef::with_wrapper(self, |wrapped| {
                    rebuilder.rebuild_subset(wrapped, subset, &mut scratch, exec_state);
                });
                changed |= subset.size() > 0;
            }
            if !scratch.is_empty() {
                let mut write_buf = self.new_rebuild_buffer(transaction);
                for (row_id, row) in scratch.non_stale_mut() {
                    self.stage_rebuilt_row::<RECEIPTS>(
                        &mut *write_buf,
                        row_id,
                        row,
                        next_ts,
                        exec_state,
                        equality_cutoff,
                    );
                }
            }
            changed
        }
    }

    fn rebuild_nonincremental<const RECEIPTS: bool>(
        &mut self,
        rebuilder: &dyn Rebuilder,
        next_ts: Value,
        exec_state: &mut ExecutionState,
        equality_cutoff: Option<EqualityEdgeCount>,
        transaction: Option<&MutationTransaction>,
    ) -> bool {
        const STEP_SIZE: usize = 2048;
        if parallelize_rebuild(self.data.next_row().index()) {
            (0..self.data.next_row().index())
                .into_par_iter()
                .step_by(STEP_SIZE)
                .fold(
                    || {
                        (
                            self.new_rebuild_buffer(transaction),
                            TaggedRowBuffer::new(self.n_columns),
                            exec_state.clone(),
                            false,
                        )
                    },
                    |(mut mutation_buf, mut buf, mut exec_state, mut changed), start| {
                        rebuilder.rebuild_buf(
                            &self.data.data,
                            RowId::from_usize(start),
                            RowId::from_usize(cmp::min(
                                start + STEP_SIZE,
                                self.data.next_row().index(),
                            )),
                            &mut buf,
                            &mut exec_state,
                        );
                        for (row_id, row) in buf.non_stale_mut() {
                            changed |= self.stage_rebuilt_row::<RECEIPTS>(
                                &mut *mutation_buf,
                                row_id,
                                row,
                                next_ts,
                                &exec_state,
                                equality_cutoff,
                            );
                        }
                        buf.clear();
                        (mutation_buf, buf, exec_state, changed)
                    },
                )
                .map(|(_, _, _, changed)| changed)
                .max()
                .unwrap_or(false)
        } else {
            let mut buf = TaggedRowBuffer::new(self.n_columns);
            let mut changed = false;

            let max_row = self.data.next_row().index();
            for start in (0..max_row).step_by(STEP_SIZE) {
                rebuilder.rebuild_buf(
                    &self.data.data,
                    RowId::from_usize(start),
                    RowId::from_usize(cmp::min(start + STEP_SIZE, max_row)),
                    &mut buf,
                    exec_state,
                );
            }
            if !buf.is_empty() {
                let mut write_buf = self.new_rebuild_buffer(transaction);
                for (row_id, row) in buf.non_stale_mut() {
                    changed |= self.stage_rebuilt_row::<RECEIPTS>(
                        &mut *write_buf,
                        row_id,
                        row,
                        next_ts,
                        exec_state,
                        equality_cutoff,
                    );
                }
            }
            changed
        }
    }
}

fn incremental_rebuild(uf_size: usize, table_size: usize, parallel: bool) -> bool {
    if parallel {
        table_size > 10_000 && uf_size * 8192 <= table_size
    } else {
        table_size > 10000 && uf_size * 8 <= table_size
    }
}
