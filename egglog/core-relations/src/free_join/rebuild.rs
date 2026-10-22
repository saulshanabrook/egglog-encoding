//! Bulk row maintenance over a frozen database view. Candidate discovery uses
//! the same occurrence-index catalog as queries, including its parallel builds.

use super::{Database, get_occurrence_index_from_tableinfo};
use crate::{
    ColumnId, ExecutionState, ExternalContext, Offset, Subset, TableId, TableSchema, TableVersion,
    TaggedRowBuffer, Value, numeric_id::NumericId, offsets::Offsets, parallel,
};

/// Values invalidated in a particular set of columns. Keeping column groups
/// separate lets one row contain values governed by several distinct UFs.
pub struct RebuildValues<'a> {
    pub columns: &'a [ColumnId],
    pub values: &'a [Value],
}

/// The consumed source version is independent of the version after committing
/// rewritten rows. New rows must be visited even without a fresh invalidation.
pub struct RebuildInput<'a> {
    pub table: TableId,
    pub after: Option<&'a TableVersion>,
    pub invalidated: &'a [RebuildValues<'a>],
    pub timestamp_column: ColumnId,
    pub next_timestamp: Value,
}

/// One maintenance wave's progress. A caller acknowledges `consumed` only after
/// successfully committing the staged writes. Rebuilding never commits itself.
pub struct RebuildProgress {
    pub consumed: TableVersion,
    pub changed: bool,
}

/// Transform one live physical row. Return true with a complete replacement in
/// `out`, or false to preserve the row and its witness unchanged. The same
/// scratch vector is reused within a chunk. Implementations may stage proof
/// records through `state`; every invocation reads the same committed database.
pub trait RowRebuilder: Send + Sync {
    fn rebuild(&self, row: &[Value], state: &mut ExecutionState, out: &mut Vec<Value>) -> bool;
}

impl Database {
    /// Discover affected rows, deduplicate across invalidations, and stage their
    /// replacements in parallel. Normal table merge code retains responsibility
    /// for FD collisions, index invalidation, and physical row lifecycle.
    pub fn rebuild_rows(
        &self,
        input: RebuildInput<'_>,
        rebuilder: &dyn RowRebuilder,
        context: ExternalContext<'_>,
    ) -> RebuildProgress {
        let info = &self.tables[input.table];
        let table = &info.table;
        let consumed = table.version();
        let n_keys = match info.spec.schema {
            TableSchema::Fd { n_keys, .. } if info.spec.allows_delete => n_keys,
            _ => panic!("bulk rebuilding requires a mutable keyed table"),
        };
        let all = table.all();
        let new_rows = match input.after {
            Some(previous) if previous.major == consumed.major => {
                table.updates_since(previous.minor)
            }
            _ => all.clone(),
        };
        let scan_threshold = all.size().div_ceil(3);
        let candidates = if new_rows.size() >= scan_threshold {
            all
        } else {
            let mut rows = Vec::new();
            new_rows.offsets(|row| rows.push(row));
            let mut scan_all = false;
            'groups: for invalidation in input.invalidated {
                if invalidation.values.is_empty() {
                    continue;
                }
                let index = get_occurrence_index_from_tableinfo(info, invalidation.columns);
                let index = index.get().unwrap();
                for value in invalidation.values {
                    if let Some(subset) = index.get_subset(value) {
                        // Bound discovery cost too: do not collect and sort a
                        // huge duplicate-heavy candidate list just to choose a
                        // full scan afterwards. Duplicates may trigger a scan
                        // earlier; that changes cost, not the rows' semantics.
                        if rows.len().saturating_add(subset.size()) >= scan_threshold {
                            scan_all = true;
                            break 'groups;
                        }
                        subset.offsets(|row| rows.push(row));
                    }
                }
            }
            if scan_all {
                // Once a substantial fraction is affected, a contiguous scan
                // avoids sparse gathers. This is a cost choice, not semantics.
                all
            } else {
                rows.sort_unstable();
                rows.dedup();
                let mut subset = Subset::empty();
                for row in rows {
                    subset.add_row_sorted(row);
                }
                subset
            }
        };
        let size = candidates.size();
        if size == 0 {
            return RebuildProgress {
                consumed,
                changed: false,
            };
        }
        let chunk_size = size
            .div_ceil(parallel::current_num_threads().max(1) * 2)
            .max(1024);
        let starts: Vec<_> = (0..size).step_by(chunk_size).collect();
        let changed = parallel::map(&starts, |_, &start| {
            self.with_execution_state(context, |state| {
                let mut rows = TaggedRowBuffer::new(info.spec.arity());
                table.scan_bounded(
                    candidates.as_ref(),
                    Offset::from_usize(start),
                    chunk_size,
                    &mut rows,
                );
                let mut out = Vec::with_capacity(info.spec.arity());
                let mut changed = false;
                for (_, row) in rows.iter() {
                    out.clear();
                    if rebuilder.rebuild(row, state, &mut out) {
                        assert_eq!(out.len(), info.spec.arity(), "row rebuilder changed arity");
                        out[input.timestamp_column.index()] = input.next_timestamp;
                        // All removals are staged before the normal merge's
                        // insert phase, including an output-only replacement.
                        state.stage_remove(input.table, &row[..n_keys]);
                        state.stage_insert(input.table, &out);
                        changed = true;
                    }
                }
                changed
            })
        })
        .into_iter()
        .any(|changed| changed);
        RebuildProgress { consumed, changed }
    }
}

#[cfg(test)]
mod tests;
