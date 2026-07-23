//! A generic table implementation supporting sorted writes.
//!
//! The primary difference between this table and the `Function` implementation
//! in egglog is that high level concepts like "timestamp" and "merge function"
//! are abstracted away from the core functionality of the table.

#[cfg(test)]
use std::cell::Cell;
use std::{
    any::Any,
    cmp,
    hash::Hasher,
    mem,
    sync::{
        Arc, Weak,
        atomic::{AtomicU64, AtomicUsize, Ordering},
    },
};

use crate::numeric_id::{DenseIdMap, NumericId};
use crossbeam_queue::SegQueue;
use hashbrown::HashTable;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator};
use rustc_hash::FxHasher;
use sharded_hash_table::ShardedHashTable;

use crate::{
    CauseDraftId, DeferredEqualityCause, EqualityEdgeCount, FactId, Pooled, ReplayTermId,
    TableChange, TableId,
    action::ExecutionState,
    common::{HashMap, ShardData, ShardId, SubsetTracker, Value},
    hash_index::{ColumnIndex, Index},
    offsets::{OffsetRange, Offsets, RowId, Subset, SubsetRef},
    parallel_heuristics::parallelize_table_op,
    pool::with_pool_set,
    receipts::PendingNativeLease,
    row_buffer::{ParallelRowBufWriter, RowBuffer},
    table_spec::{
        ColumnId, Constraint, Generation, MutationBuffer, MutationTransaction, Offset, Row, Table,
        TableSpec, TableVersion,
    },
};

mod rebuild;
mod sharded_hash_table;
#[cfg(test)]
mod tests;

// NB: Having this type def lets us switch between 64 and 32 bits of hashcode.
//
// We should consider just using u64 everywhere though. Hashbrown doesn't play nicely with 32-bit
// hashcodes because it uses both the high and low bits of a 64-bit code.

type HashCode = u64;

#[cfg(test)]
thread_local! {
    static TEST_FACT_ID_LOOKUPS: Cell<usize> = const { Cell::new(0) };
    static TEST_WITNESS_ROW_READS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_causal_lookup_counters() {
    TEST_FACT_ID_LOOKUPS.set(0);
    TEST_WITNESS_ROW_READS.set(0);
}

#[cfg(test)]
pub(crate) fn causal_lookup_counters() -> (usize, usize) {
    (TEST_FACT_ID_LOOKUPS.get(), TEST_WITNESS_ROW_READS.get())
}

/// A pointer to a row in the table.
#[derive(Clone, Debug)]
pub(crate) struct TableEntry {
    hashcode: HashCode,
    row: RowId,
}

impl TableEntry {
    fn hashcode(&self) -> u64 {
        // We keep the cast here to make it easy to switch to HashCode=u32.
        #[allow(clippy::unnecessary_cast)]
        {
            self.hashcode as u64
        }
    }
}

/// The core data for a table.
///
/// This type is a thin wrapper around `RowBuffer`. The big difference is that
/// it keeps track of how many stale rows are present.
#[derive(Clone)]
struct Rows {
    data: RowBuffer,
    scratch: RowBuffer,
    fact_ids: Option<FactSidecars>,
    stale_rows: usize,
}

#[derive(Clone, Default)]
struct FactSidecars {
    data: Vec<FactId>,
    scratch: Vec<FactId>,
}

impl Rows {
    fn new(data: RowBuffer) -> Rows {
        let arity = data.arity();
        Rows {
            data,
            scratch: RowBuffer::new(arity),
            fact_ids: None,
            stale_rows: 0,
        }
    }
    fn clear(&mut self) {
        self.data.clear();
        self.fact_ids = None;
        self.stale_rows = 0;
    }
    fn next_row(&self) -> RowId {
        RowId::from_usize(self.data.len())
    }
    fn set_stale(&mut self, row: RowId) {
        if !self.data.set_stale(row) {
            self.stale_rows += 1;
        }
    }

    fn get_row(&self, row: RowId) -> Option<&[Value]> {
        let row = self.data.get_row(row);
        if row[0].is_stale() { None } else { Some(row) }
    }

    /// A variant of `get_row` without bounds-checking on `row`.
    unsafe fn get_row_unchecked(&self, row: RowId) -> Option<&[Value]> {
        let row = unsafe { self.data.get_row_unchecked(row) };
        if row[0].is_stale() { None } else { Some(row) }
    }

    fn add_row(&mut self, row: &[Value]) -> RowId {
        debug_assert!(
            self.fact_ids.is_none(),
            "ordinary insertion cannot extend a receipt-enabled table"
        );
        if row[0].is_stale() {
            self.stale_rows += 1;
        }
        self.data.add_row(row)
    }

    fn add_row_with_fact(&mut self, row: &[Value], fact: FactId) -> RowId {
        if row[0].is_stale() {
            self.stale_rows += 1;
        }
        let id = self.data.add_row(row);
        let facts = self.fact_ids.get_or_insert_with(|| FactSidecars {
            data: vec![FactId::MISSING; id.index()],
            scratch: Vec::new(),
        });
        debug_assert_eq!(id.index(), facts.data.len());
        facts.data.push(fact);
        id
    }

    fn fact_id(&self, row: RowId) -> Option<FactId> {
        let fact = *self.fact_ids.as_ref()?.data.get(row.index())?;
        (!fact.is_missing()).then_some(fact)
    }

    fn remove_stale(&mut self, mut remap: impl FnMut(&[Value], RowId, RowId)) {
        if let Some(facts) = &mut self.fact_ids {
            let old_facts = mem::take(&mut facts.data);
            let mut new_facts = mem::take(&mut facts.scratch);
            new_facts.clear();
            new_facts.reserve(self.data.len().saturating_sub(self.stale_rows));
            self.data.remove_stale(|row, old, new| {
                debug_assert_eq!(new.index(), new_facts.len());
                new_facts.push(old_facts[old.index()]);
                remap(row, old, new);
            });
            facts.scratch = old_facts;
            facts.data = new_facts;
        } else {
            self.data.remove_stale(remap);
        }
        self.stale_rows = 0;
    }

    #[cfg(test)]
    pub(crate) fn causal_sidecar_bytes(&self) -> usize {
        self.fact_ids.as_ref().map_or(0, |facts| {
            (facts.data.capacity() + facts.scratch.capacity()) * mem::size_of::<FactId>()
        })
    }
}

/// The type of closures that are used to merge values in a [`SortedWritesTable`].
///
/// The first argument grants access to database using an [`ExecutionState`], the second argument
/// is the current value of the tuple. The third argument is the new, or "incoming" value of the
/// tuple. The fourth argument is a mutable reference to a vector that will be used to store the
/// output of the merge function _if_ it changes the value of the tuple. If it does not, then the
/// merge function should return `false`.
pub type MergeFn =
    dyn Fn(&mut ExecutionState, &[Value], &[Value], &mut Vec<Value>) -> bool + Send + Sync;

pub struct SortedWritesTable {
    table_id: TableId,
    generation: Generation,
    data: Rows,
    hash: ShardedHashTable<TableEntry>,

    n_keys: usize,
    n_columns: usize,
    sort_by: Option<ColumnId>,
    offsets: Vec<(Value, RowId)>,

    pending_state: Arc<PendingState>,
    merge: Arc<MergeFn>,
    to_rebuild: Vec<ColumnId>,
    rebuild_index: Index<ColumnIndex>,
    // Used to manage incremental rebuilds.
    subset_tracker: SubsetTracker,
}

impl Clone for SortedWritesTable {
    fn clone(&self) -> SortedWritesTable {
        SortedWritesTable {
            generation: self.generation,
            table_id: self.table_id,
            data: self.data.clone(),
            hash: self.hash.clone(),
            n_keys: self.n_keys,
            n_columns: self.n_columns,
            sort_by: self.sort_by,
            offsets: self.offsets.clone(),
            pending_state: Arc::new(self.pending_state.deep_copy()),
            merge: self.merge.clone(),
            to_rebuild: self.to_rebuild.clone(),
            rebuild_index: Index::new(self.to_rebuild.clone(), ColumnIndex::new()),
            subset_tracker: Default::default(),
        }
    }
}

/// A variant of [`RowBuffer`] that can handle arity 0.
///
/// We use this to handle empty keys, where the deletion API needs to handle "row buffers of empty
/// rows". The goal here is to keep most of the API RowBuffer-centric and avoid complicating the
/// code too much: actual code that was optimized to handle arity 0 would look a bit different.
#[derive(Clone)]
enum ArbitraryRowBuffer {
    NonEmpty(RowBuffer),
    Empty { rows: usize },
}

impl ArbitraryRowBuffer {
    fn new(arity: usize) -> ArbitraryRowBuffer {
        if arity == 0 {
            ArbitraryRowBuffer::Empty { rows: 0 }
        } else {
            ArbitraryRowBuffer::NonEmpty(RowBuffer::new(arity))
        }
    }

    fn add_row(&mut self, row: &[Value]) {
        match self {
            ArbitraryRowBuffer::NonEmpty(buf) => {
                buf.add_row(row);
            }
            ArbitraryRowBuffer::Empty { rows } => {
                *rows += 1;
            }
        }
    }

    fn len(&self) -> usize {
        match self {
            ArbitraryRowBuffer::NonEmpty(buf) => buf.len(),
            ArbitraryRowBuffer::Empty { rows } => *rows,
        }
    }

    fn for_each(&self, mut f: impl FnMut(&[Value])) {
        match self {
            ArbitraryRowBuffer::NonEmpty(buf) => {
                for row in buf.iter() {
                    f(row);
                }
            }
            ArbitraryRowBuffer::Empty { rows } => {
                for _ in 0..*rows {
                    f(&[]);
                }
            }
        }
    }
}

struct Buffer {
    pending_rows: DenseIdMap<ShardId, RowBuffer>,
    receipt: Option<Box<ReceiptBuffer>>,
    pending_removals: DenseIdMap<ShardId, ArbitraryRowBuffer>,
    state: Weak<PendingState>,
    n_cols: u32,
    n_keys: u32,
    shard_data: ShardData,
}

struct ReceiptBuffer {
    causes: DenseIdMap<ShardId, Vec<DeferredEqualityCause>>,
    row_terms: DenseIdMap<ShardId, Vec<Option<Box<[ReplayTermId]>>>>,
    transaction: Option<MutationTransaction>,
}

impl MutationBuffer for Buffer {
    fn defer_until(&mut self, transaction: MutationTransaction) {
        assert!(
            self.pending_rows.iter().all(|(_, rows)| rows.len() == 0)
                && self
                    .pending_removals
                    .iter()
                    .all(|(_, rows)| rows.len() == 0),
            "a rebuild commit guard must be installed before staging mutations"
        );
        let receipt = self.receipt.get_or_insert_with(|| {
            Box::new(ReceiptBuffer {
                causes: DenseIdMap::default(),
                row_terms: DenseIdMap::default(),
                transaction: None,
            })
        });
        assert!(
            receipt.transaction.replace(transaction).is_none(),
            "a mutation buffer received more than one rebuild commit guard"
        );
    }

    fn stage_insert(&mut self, row: &[Value]) {
        let (shard, _) = hash_code(self.shard_data, row, self.n_keys as _);
        self.pending_rows
            .get_or_insert(shard, || RowBuffer::new(self.n_cols as _))
            .add_row(row);
    }
    fn stage_insert_with_cause(&mut self, row: &[Value], cause: CauseDraftId) {
        self.stage_insert_deferred(row, DeferredEqualityCause::ready(cause));
    }
    fn stage_insert_deferred(&mut self, row: &[Value], cause: DeferredEqualityCause) {
        let (shard, _) = hash_code(self.shard_data, row, self.n_keys as _);
        let rows = self
            .pending_rows
            .get_or_insert(shard, || RowBuffer::new(self.n_cols as _))
            .len();
        let receipt = self.receipt.get_or_insert_with(|| {
            Box::new(ReceiptBuffer {
                causes: DenseIdMap::default(),
                row_terms: DenseIdMap::default(),
                transaction: None,
            })
        });
        let causes = receipt.causes.get_or_insert(shard, || {
            assert_eq!(rows, 0, "receipt causes were enabled after ordinary rows");
            Vec::new()
        });
        let row_terms = receipt.row_terms.get_or_insert(shard, || vec![None; rows]);
        debug_assert_eq!(causes.len(), rows);
        debug_assert_eq!(row_terms.len(), rows);
        self.pending_rows[shard].add_row(row);
        causes.push(cause);
        row_terms.push(None);
    }
    fn stage_insert_with_cause_and_terms(
        &mut self,
        row: &[Value],
        cause: CauseDraftId,
        terms: &[ReplayTermId],
    ) {
        self.stage_insert_deferred_with_terms(row, DeferredEqualityCause::ready(cause), terms);
    }
    fn stage_insert_deferred_with_terms(
        &mut self,
        row: &[Value],
        cause: DeferredEqualityCause,
        terms: &[ReplayTermId],
    ) {
        let (shard, _) = hash_code(self.shard_data, row, self.n_keys as _);
        let rows = self
            .pending_rows
            .get_or_insert(shard, || RowBuffer::new(self.n_cols as _))
            .len();
        let receipt = self.receipt.get_or_insert_with(|| {
            Box::new(ReceiptBuffer {
                causes: DenseIdMap::default(),
                row_terms: DenseIdMap::default(),
                transaction: None,
            })
        });
        let causes = receipt.causes.get_or_insert(shard, || {
            assert_eq!(rows, 0, "receipt causes were enabled after ordinary rows");
            Vec::new()
        });
        let row_terms = receipt.row_terms.get_or_insert(shard, || vec![None; rows]);
        debug_assert_eq!(causes.len(), rows);
        debug_assert_eq!(row_terms.len(), rows);
        self.pending_rows[shard].add_row(row);
        causes.push(cause);
        row_terms.push(Some(terms.into()));
    }
    fn stage_remove(&mut self, key: &[Value]) {
        let (shard, _) = hash_code(self.shard_data, key, self.n_keys as _);
        self.pending_removals
            .get_or_insert(shard, || ArbitraryRowBuffer::new(self.n_keys as _))
            .add_row(key);
    }
    fn fresh_handle(&self) -> Box<dyn MutationBuffer> {
        Box::new(Buffer {
            pending_rows: Default::default(),
            receipt: self.receipt.as_ref().and_then(|receipt| {
                receipt.transaction.as_ref().map(|transaction| {
                    Box::new(ReceiptBuffer {
                        causes: DenseIdMap::default(),
                        row_terms: DenseIdMap::default(),
                        transaction: Some(transaction.clone()),
                    })
                })
            }),
            pending_removals: Default::default(),
            state: self.state.clone(),
            n_cols: self.n_cols,
            n_keys: self.n_keys,
            shard_data: self.shard_data,
        })
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        if let Some(state) = self.state.upgrade() {
            if let Some(transaction) = self
                .receipt
                .as_ref()
                .and_then(|receipt| receipt.transaction.clone())
            {
                let mut pending_rows = Vec::new();
                let native_lease = transaction.native_lease();
                let mut row_count = 0;
                for shard_id in 0..self.pending_rows.n_ids() {
                    let shard = ShardId::from_usize(shard_id);
                    let Some(rows) = self.pending_rows.take(shard) else {
                        continue;
                    };
                    row_count += rows.len();
                    let causes = self
                        .receipt
                        .as_mut()
                        .and_then(|receipt| receipt.causes.take(shard));
                    let row_terms = self
                        .receipt
                        .as_mut()
                        .and_then(|receipt| receipt.row_terms.take(shard));
                    pending_rows.push((
                        shard,
                        PendingRowBatch {
                            rows,
                            causes,
                            row_terms,
                            _native_lease: native_lease.clone(),
                        },
                    ));
                }
                let mut pending_removals = Vec::new();
                let mut removal_count = 0;
                for shard_id in 0..self.pending_removals.n_ids() {
                    let shard = ShardId::from_usize(shard_id);
                    let Some(rows) = self.pending_removals.take(shard) else {
                        continue;
                    };
                    removal_count += rows.len();
                    pending_removals.push((shard, rows));
                }
                if row_count == 0 && removal_count == 0 {
                    return;
                }
                transaction.defer_publication(move || {
                    for (shard, batch) in pending_rows {
                        state.pending_rows[shard].push(batch);
                    }
                    state.total_rows.fetch_add(row_count, Ordering::Relaxed);
                    for (shard, rows) in pending_removals {
                        state.pending_removals[shard].push(rows);
                    }
                    state
                        .total_removals
                        .fetch_add(removal_count, Ordering::Relaxed);
                });
                return;
            }

            let mut rows = 0;
            for shard_id in 0..self.pending_rows.n_ids() {
                let shard = ShardId::from_usize(shard_id);
                let Some(buf) = self.pending_rows.take(shard) else {
                    continue;
                };
                rows += buf.len();
                let causes = self
                    .receipt
                    .as_mut()
                    .and_then(|receipt| receipt.causes.take(shard));
                let row_terms = self
                    .receipt
                    .as_mut()
                    .and_then(|receipt| receipt.row_terms.take(shard));
                state.pending_rows[shard].push(PendingRowBatch {
                    rows: buf,
                    causes,
                    row_terms,
                    _native_lease: None,
                });
            }
            state.total_rows.fetch_add(rows, Ordering::Relaxed);

            let mut rows = 0;
            for shard_id in 0..self.pending_removals.n_ids() {
                let shard = ShardId::from_usize(shard_id);
                let Some(buf) = self.pending_removals.take(shard) else {
                    continue;
                };
                rows += buf.len();
                state.pending_removals[shard].push(buf);
            }
            state.total_removals.fetch_add(rows, Ordering::Relaxed);
        }
    }
}

impl Table for SortedWritesTable {
    fn dyn_clone(&self) -> Box<dyn Table> {
        Box::new(self.clone())
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn set_table_id(&mut self, table: TableId) {
        self.table_id = table;
    }
    fn preflight_causal_receipt_activation(&self) -> Result<(), &'static str> {
        if self.len() != 0 {
            return Err("table already contains rows without exact source identities");
        }
        if self.pending_state.total_rows.load(Ordering::Acquire) != 0
            || self.pending_state.total_removals.load(Ordering::Acquire) != 0
        {
            return Err("table has queued receipt-disabled mutations");
        }
        if Arc::weak_count(&self.pending_state) != 0 {
            return Err("table has an outstanding receipt-disabled mutation buffer");
        }
        Ok(())
    }
    fn clear(&mut self) {
        self.pending_state.clear();
        if self.data.data.len() == 0 {
            return;
        }
        self.offsets.clear();
        self.data.clear();
        self.hash.clear();
        self.generation = Generation::from_usize(self.version().major.index() + 1);
    }

    fn spec(&self) -> TableSpec {
        TableSpec {
            n_keys: self.n_keys,
            n_vals: self.n_columns - self.n_keys,
            uncacheable_columns: Default::default(),
            allows_delete: true,
        }
    }

    fn apply_rebuild(
        &mut self,
        table_id: TableId,
        table: &crate::WrappedTable,
        next_ts: Value,
        exec_state: &mut ExecutionState,
        equality_cutoff: Option<EqualityEdgeCount>,
        transaction: Option<&MutationTransaction>,
    ) -> bool {
        self.do_rebuild(
            table_id,
            table,
            next_ts,
            exec_state,
            equality_cutoff,
            transaction,
        )
    }

    fn commit_rebuild_cursor(&mut self, table_id: TableId, version: TableVersion) {
        self.subset_tracker.commit_recent_updates(table_id, version);
    }

    fn refresh_rows_for_values(
        &mut self,
        summary: &crate::ContainerRebuildSummary,
        next_ts: Value,
        exec_state: Option<&ExecutionState>,
        transaction: Option<&MutationTransaction>,
    ) -> bool {
        SortedWritesTable::refresh_rows_for_values(self, summary, next_ts, exec_state, transaction)
    }

    fn version(&self) -> TableVersion {
        TableVersion {
            major: self.generation,
            minor: Offset::from_usize(self.data.next_row().index()),
        }
    }

    fn updates_since(&self, offset: Offset) -> Subset {
        Subset::Dense(OffsetRange::new(
            RowId::from_usize(offset.index()),
            self.data.next_row(),
        ))
    }

    fn all(&self) -> Subset {
        Subset::Dense(OffsetRange::new(RowId::new(0), self.data.next_row()))
    }

    fn has_stale_rows(&self) -> bool {
        self.data.stale_rows > 0
    }

    fn len(&self) -> usize {
        self.data.data.len() - self.data.stale_rows
    }

    fn scan_generic(&self, subset: SubsetRef, mut f: impl FnMut(RowId, &[Value]))
    where
        Self: Sized,
    {
        let Some((_low, hi)) = subset.bounds() else {
            // Empty subset
            return;
        };
        assert!(
            hi.index() <= self.data.data.len(),
            "{} vs. {}",
            hi.index(),
            self.data.data.len()
        );
        if self.data.stale_rows == 0 {
            // Fast path: no stale rows, skip is_stale check per row.
            // SAFETY: subsets are sorted, low must be at most hi, and hi is less
            // than the length of the table.
            // TODO: provide a safe API for this `get_row_unchecked` usage since we have
            // checked the full bounds above.
            subset.offsets(|row| unsafe { f(row, self.data.data.get_row_unchecked(row)) })
        } else {
            // SAFETY: same as above.
            subset.offsets(|row| unsafe {
                if let Some(vals) = self.data.get_row_unchecked(row) {
                    f(row, vals)
                }
            })
        }
    }

    fn scan_generic_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        cs: &[Constraint],
        mut f: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset>
    where
        Self: Sized,
    {
        let Some((_low, hi)) = subset.bounds() else {
            // Empty subset
            return None;
        };
        assert!(
            hi.index() <= self.data.data.len(),
            "{} vs. {}",
            hi.index(),
            self.data.data.len()
        );
        if cs.is_empty() {
            if self.data.stale_rows == 0 {
                // Fast path: no stale rows, skip bounds check and is_stale check.
                // SAFETY: all row IDs are in-bounds.
                subset
                    .iter_bounded(start.index(), start.index() + n, |row| {
                        let entry = unsafe { self.data.data.get_row_unchecked(row) };
                        f(row, entry);
                    })
                    .map(Offset::from_usize)
            } else {
                subset
                    .iter_bounded(start.index(), start.index() + n, |row| {
                        // SAFETY: all row IDs are in-bounds.
                        let Some(entry) = (unsafe { self.data.get_row_unchecked(row) }) else {
                            return;
                        };
                        f(row, entry);
                    })
                    .map(Offset::from_usize)
            }
        } else {
            subset
                .iter_bounded(start.index(), start.index() + n, |row| {
                    // SAFETY: all row IDs are in-bounds.
                    let Some(entry) = (unsafe { self.get_if_unchecked(cs, row) }) else {
                        return;
                    };
                    f(row, entry);
                })
                .map(Offset::from_usize)
        }
    }

    fn fast_subset(&self, constraint: &Constraint) -> Option<Subset> {
        let sort_by = self.sort_by?;
        match constraint {
            Constraint::Eq { .. } => None,
            Constraint::EqConst { col, val } => {
                if col == &sort_by {
                    match self.binary_search_sort_val(*val) {
                        Ok((found, bound)) => Some(Subset::Dense(OffsetRange::new(found, bound))),
                        Err(_) => Some(Subset::empty()),
                    }
                } else {
                    None
                }
            }
            Constraint::LtConst { col, val } => {
                if col == &sort_by {
                    match self.binary_search_sort_val(*val) {
                        Ok((found, _)) => {
                            Some(Subset::Dense(OffsetRange::new(RowId::new(0), found)))
                        }
                        Err(next) => Some(Subset::Dense(OffsetRange::new(RowId::new(0), next))),
                    }
                } else {
                    None
                }
            }
            Constraint::GtConst { col, val } => {
                if col == &sort_by {
                    match self.binary_search_sort_val(*val) {
                        Ok((_, bound)) => {
                            Some(Subset::Dense(OffsetRange::new(bound, self.data.next_row())))
                        }
                        Err(next) => {
                            Some(Subset::Dense(OffsetRange::new(next, self.data.next_row())))
                        }
                    }
                } else {
                    None
                }
            }
            Constraint::LeConst { col, val } => {
                if col == &sort_by {
                    match self.binary_search_sort_val(*val) {
                        Ok((_, bound)) => {
                            Some(Subset::Dense(OffsetRange::new(RowId::new(0), bound)))
                        }
                        Err(next) => Some(Subset::Dense(OffsetRange::new(RowId::new(0), next))),
                    }
                } else {
                    None
                }
            }
            Constraint::GeConst { col, val } => {
                if col == &sort_by {
                    match self.binary_search_sort_val(*val) {
                        Ok((found, _)) => {
                            Some(Subset::Dense(OffsetRange::new(found, self.data.next_row())))
                        }
                        Err(next) => {
                            Some(Subset::Dense(OffsetRange::new(next, self.data.next_row())))
                        }
                    }
                } else {
                    None
                }
            }
        }
    }

    fn refine_one(&self, mut subset: Subset, c: &Constraint) -> Subset {
        // NB: we aren't using any of the `fast_subset` tricks here. We may want
        // to if the higher-level implementations end up using it directly.
        subset.retain(|row| self.eval(std::slice::from_ref(c), row));
        subset
    }

    fn new_buffer(&self) -> Box<dyn MutationBuffer> {
        let n_shards = self.hash.shard_data().n_shards();
        Box::new(Buffer {
            pending_rows: DenseIdMap::with_capacity(n_shards),
            receipt: None,
            pending_removals: DenseIdMap::with_capacity(n_shards),
            state: Arc::downgrade(&self.pending_state),
            n_keys: u32::try_from(self.n_keys).expect("n_keys should fit in u32"),
            n_cols: u32::try_from(self.n_columns).expect("n_columns should fit in u32"),
            shard_data: self.hash.shard_data(),
        })
    }

    fn merge(&mut self, exec_state: &mut ExecutionState) -> TableChange {
        let removed = self.do_delete();
        let added = self.do_insert(exec_state);
        self.maybe_rehash();
        TableChange { removed, added }
    }

    fn get_row(&self, key: &[Value]) -> Option<Row> {
        let id = get_entry(key, self.n_keys, &self.hash, |row| {
            &self.data.get_row(row).unwrap()[0..self.n_keys] == key
        })?;
        let mut vals = with_pool_set(|ps| ps.get::<Vec<Value>>());
        vals.extend_from_slice(self.data.get_row(id).unwrap());
        Some(Row { id, vals })
    }

    fn get_row_column(&self, key: &[Value], col: ColumnId) -> Option<Value> {
        let id = get_entry(key, self.n_keys, &self.hash, |row| {
            &self.data.get_row(row).unwrap()[0..self.n_keys] == key
        })?;
        Some(self.data.get_row(id).unwrap()[col.index()])
    }

    fn fact_id(&self, row: RowId) -> Option<FactId> {
        #[cfg(test)]
        TEST_FACT_ID_LOOKUPS.set(TEST_FACT_ID_LOOKUPS.get() + 1);
        self.data.fact_id(row)
    }

    fn row_at(&self, row: RowId) -> Option<Row> {
        #[cfg(test)]
        TEST_WITNESS_ROW_READS.set(TEST_WITNESS_ROW_READS.get() + 1);
        let values = self.data.get_row(row)?;
        let mut vals = with_pool_set(|ps| ps.get::<Vec<Value>>());
        vals.extend_from_slice(values);
        Some(Row { id: row, vals })
    }
}

impl SortedWritesTable {
    #[cfg(test)]
    pub(crate) fn causal_sidecar_bytes(&self) -> usize {
        self.data.causal_sidecar_bytes()
    }

    /// Create a new [`SortedWritesTable`] with the given number of keys,
    /// columns, and an optional sort column.
    ///
    /// The `merge_fn` is used to evaluate conflicts when more than one row is
    /// inserted with the same primary key. The old and new proposed values are
    /// passed as the second and third arguments, respectively, with the
    /// function filling the final argument with the contents of the new row.
    /// The return value indicates whether or not the contents of the vector
    /// should be used.
    ///
    /// Merge functions can access the database via [`ExecutionState`].
    pub fn new(
        n_keys: usize,
        n_columns: usize,
        sort_by: Option<ColumnId>,
        to_rebuild: Vec<ColumnId>,
        merge_fn: Box<MergeFn>,
    ) -> Self {
        let hash = ShardedHashTable::<TableEntry>::default();
        let shard_data = hash.shard_data();
        let rebuild_index = Index::new(to_rebuild.clone(), ColumnIndex::new());
        SortedWritesTable {
            table_id: TableId::dummy(),
            generation: Generation::new(0),
            data: Rows::new(RowBuffer::new(n_columns)),
            hash,
            n_keys,
            n_columns,
            sort_by,
            offsets: Default::default(),
            pending_state: Arc::new(PendingState::new(shard_data)),
            merge: merge_fn.into(),
            to_rebuild,
            rebuild_index,
            subset_tracker: Default::default(),
        }
    }

    /// Flush all pending removals, in parallel.
    fn parallel_delete(&mut self) -> bool {
        let shard_data = self.hash.shard_data();
        let stale_delta: usize = self
            .hash
            .mut_shards()
            .par_iter_mut()
            .enumerate()
            .filter_map(|(shard_id, shard)| {
                let shard_id = ShardId::from_usize(shard_id);
                if self.pending_state.pending_removals[shard_id].is_empty() {
                    return None;
                }
                Some((shard_id, shard))
            })
            .map(|(shard_id, shard)| {
                let queue = &self.pending_state.pending_removals[shard_id];
                let mut marked_stale = 0;
                while let Some(buf) = queue.pop() {
                    buf.for_each(|to_remove| {
                        let (actual_shard, hc) = hash_code(shard_data, to_remove, self.n_keys);
                        assert_eq!(actual_shard, shard_id);
                        if let Ok(entry) = shard.find_entry(hc, |entry| {
                            entry.hashcode == (hc as HashCode)
                                && &self.data.get_row(entry.row).unwrap()[0..self.n_keys]
                                    == to_remove
                        }) {
                            let (ent, _) = entry.remove();
                            // SAFETY: The safety requirements of
                            // `set_stale_shared` are that there are no
                            // concurrent accesses to `row`. No other threads
                            // can access this row within this method because
                            // different `shards` partition the space
                            // (guaranteed by the assertion above), and we
                            // launch at most one thread per shard.
                            marked_stale +=
                                unsafe { !self.data.data.set_stale_shared(ent.row) } as usize;
                        }
                    });
                }
                marked_stale
            })
            .sum();
        // Update the stale count with the total marked stale.
        self.data.stale_rows += stale_delta;
        stale_delta > 0
    }
    fn serial_delete(&mut self) -> bool {
        let shard_data = self.hash.shard_data();
        let mut changed = false;
        self.hash
            .mut_shards()
            .iter_mut()
            .enumerate()
            .for_each(|(shard_id, shard)| {
                let shard_id = ShardId::from_usize(shard_id);
                let queue = &self.pending_state.pending_removals[shard_id];
                while let Some(buf) = queue.pop() {
                    buf.for_each(|to_remove| {
                        let (actual_shard, hc) = hash_code(shard_data, to_remove, self.n_keys);
                        assert_eq!(actual_shard, shard_id);
                        if let Ok(entry) = shard.find_entry(hc, |entry| {
                            entry.hashcode == (hc as HashCode)
                                && &self.data.get_row(entry.row).unwrap()[0..self.n_keys]
                                    == to_remove
                        }) {
                            let (ent, _) = entry.remove();
                            self.data.set_stale(ent.row);
                            changed = true;
                        }
                    })
                }
            });
        changed
    }

    fn do_delete(&mut self) -> bool {
        let total = self.pending_state.total_removals.swap(0, Ordering::Relaxed);

        if self.data.fact_ids.is_none() && parallelize_table_op(total) {
            self.parallel_delete()
        } else {
            self.serial_delete()
        }
    }

    fn do_insert(&mut self, exec_state: &mut ExecutionState) -> bool {
        let total = self.pending_state.total_rows.swap(0, Ordering::Relaxed);
        self.data.data.reserve(total);
        // Causal capture is a serial-only contract. Keep the already-landed
        // parallel implementation dormant so direct core activation inside a
        // larger Rayon pool cannot accidentally promote candidate-scale
        // receipt causes.
        if exec_state.causal_receipts().is_none() && parallelize_table_op(total) {
            if let Some(col) = self.sort_by {
                self.parallel_insert(
                    exec_state,
                    SortChecker {
                        col,
                        current: None,
                        baseline: self.offsets.last().map(|(v, _)| *v),
                    },
                )
            } else {
                self.parallel_insert(exec_state, ())
            }
        } else {
            self.serial_insert(exec_state)
        }
    }

    fn serial_insert(&mut self, exec_state: &mut ExecutionState) -> bool {
        if exec_state.causal_receipts().is_none() {
            self.serial_insert_mode::<false>(exec_state)
        } else {
            self.serial_insert_mode::<true>(exec_state)
        }
    }

    fn serial_insert_mode<const RECEIPTS: bool>(
        &mut self,
        exec_state: &mut ExecutionState,
    ) -> bool {
        let mut changed = false;
        let n_keys = self.n_keys;
        let mut scratch = with_pool_set(|ps| ps.get::<Vec<Value>>());
        let mut receipt_batch = if RECEIPTS {
            Some(
                exec_state
                    .causal_receipts()
                    .expect("receipt mode requires an enabled arena")
                    .new_batch(),
            )
        } else {
            None
        };
        for (_outer_shard, queue) in self.pending_state.pending_rows.iter() {
            if let Some(sort_by) = self.sort_by {
                while let Some(buf) = queue.pop() {
                    for (proposal_index, query) in buf.rows.iter().enumerate() {
                        if query.first().is_some_and(|value| value.is_stale()) {
                            continue;
                        }
                        let incoming_cause = if RECEIPTS {
                            Some(buf.receipt_cause(proposal_index))
                        } else {
                            None
                        };
                        let key = &query[0..n_keys];
                        let entry = get_entry_mut(query, n_keys, &mut self.hash, |row| {
                            let Some(row) = self.data.get_row(row) else {
                                return false;
                            };
                            &row[0..n_keys] == key
                        });

                        if let Some(row) = entry {
                            // First case: overwriting an existing value. Apply merge
                            // function. Insert new row and update hash table if merge
                            // changes anything.
                            let prior_fact = if RECEIPTS {
                                self.data.fact_id(*row).unwrap_or(FactId::MISSING)
                            } else {
                                FactId::MISSING
                            };
                            let cur = self
                                .data
                                .get_row(*row)
                                .expect("table should not point to stale entry");
                            if let Some(cause) = &incoming_cause {
                                cause.record_merge_read(prior_fact);
                            }
                            let previous_cause = incoming_cause.clone().map(|cause| {
                                exec_state.begin_deferred_merge_cause(cause, prior_fact)
                            });
                            let merged = (self.merge)(exec_state, cur, query, &mut scratch);
                            let merge_cause = previous_cause.map(|previous| {
                                exec_state
                                    .end_deferred_merge_cause(previous, merged)
                                    .filter(|_| merged)
                            });
                            if merged {
                                let merge_cause = merge_cause
                                    .flatten()
                                    .map(|cause| cause.promote())
                                    .unwrap_or(CauseDraftId::UNATTRIBUTED);
                                let sort_val = query[sort_by.index()];
                                let fact =
                                    receipt_batch.as_mut().map_or(FactId::MISSING, |batch| {
                                        batch.inherit_prior_fact_terms(
                                            merge_cause,
                                            prior_fact,
                                            self.table_id,
                                        );
                                        batch.record_fact_with_terms(
                                            self.table_id,
                                            merge_cause,
                                            &scratch,
                                            buf.receipt_terms(proposal_index),
                                        )
                                    });
                                let new = if RECEIPTS {
                                    self.data.add_row_with_fact(&scratch, fact)
                                } else {
                                    self.data.add_row(&scratch)
                                };
                                if let Some(largest) = self.offsets.last().map(|(v, _)| *v) {
                                    assert!(
                                        sort_val >= largest,
                                        "inserting row that violates sort order ({sort_val:?} vs. {largest:?})"
                                    );
                                    if sort_val > largest {
                                        self.offsets.push((sort_val, new));
                                    }
                                } else {
                                    self.offsets.push((sort_val, new));
                                }
                                self.data.set_stale(*row);
                                *row = new;
                                changed = true;
                            }
                            scratch.clear();
                        } else {
                            let sort_val = query[sort_by.index()];
                            // New value: update invariants.
                            let incoming_cause = incoming_cause
                                .as_ref()
                                .map(DeferredEqualityCause::promote)
                                .unwrap_or(CauseDraftId::UNATTRIBUTED);
                            let fact = receipt_batch.as_mut().map_or(FactId::MISSING, |batch| {
                                batch.record_fact_with_terms(
                                    self.table_id,
                                    incoming_cause,
                                    query,
                                    buf.receipt_terms(proposal_index),
                                )
                            });
                            let new = if RECEIPTS {
                                self.data.add_row_with_fact(query, fact)
                            } else {
                                self.data.add_row(query)
                            };
                            if let Some(largest) = self.offsets.last().map(|(v, _)| *v) {
                                assert!(
                                    sort_val >= largest,
                                    "inserting row that violates sort order {sort_val:?} vs. {largest:?}"
                                );
                                if sort_val > largest {
                                    self.offsets.push((sort_val, new));
                                }
                            } else {
                                self.offsets.push((sort_val, new));
                            }
                            let (shard, hc) = hash_code(self.hash.shard_data(), query, self.n_keys);
                            debug_assert_eq!(shard, _outer_shard);
                            self.hash.mut_shards()[shard.index()].insert_unique(
                                hc as _,
                                TableEntry {
                                    hashcode: hc as _,
                                    row: new,
                                },
                                TableEntry::hashcode,
                            );
                            changed = true;
                        }
                    }
                }
            } else {
                // Simplified variant without the sorting constraint.
                while let Some(buf) = queue.pop() {
                    for (proposal_index, query) in buf.rows.iter().enumerate() {
                        if query.first().is_some_and(|value| value.is_stale()) {
                            continue;
                        }
                        let incoming_cause = if RECEIPTS {
                            Some(buf.receipt_cause(proposal_index))
                        } else {
                            None
                        };
                        let key = &query[0..n_keys];
                        let entry = get_entry_mut(query, n_keys, &mut self.hash, |row| {
                            let Some(row) = self.data.get_row(row) else {
                                return false;
                            };
                            &row[0..n_keys] == key
                        });

                        if let Some(row) = entry {
                            let prior_fact = if RECEIPTS {
                                self.data.fact_id(*row).unwrap_or(FactId::MISSING)
                            } else {
                                FactId::MISSING
                            };
                            let cur = self
                                .data
                                .get_row(*row)
                                .expect("table should not point to stale entry");
                            if let Some(cause) = &incoming_cause {
                                cause.record_merge_read(prior_fact);
                            }
                            let previous_cause = incoming_cause.clone().map(|cause| {
                                exec_state.begin_deferred_merge_cause(cause, prior_fact)
                            });
                            let merged = (self.merge)(exec_state, cur, query, &mut scratch);
                            let merge_cause = previous_cause.map(|previous| {
                                exec_state
                                    .end_deferred_merge_cause(previous, merged)
                                    .filter(|_| merged)
                            });
                            if merged {
                                let merge_cause = merge_cause
                                    .flatten()
                                    .map(|cause| cause.promote())
                                    .unwrap_or(CauseDraftId::UNATTRIBUTED);
                                let fact =
                                    receipt_batch.as_mut().map_or(FactId::MISSING, |batch| {
                                        batch.inherit_prior_fact_terms(
                                            merge_cause,
                                            prior_fact,
                                            self.table_id,
                                        );
                                        batch.record_fact_with_terms(
                                            self.table_id,
                                            merge_cause,
                                            &scratch,
                                            buf.receipt_terms(proposal_index),
                                        )
                                    });
                                let new = if RECEIPTS {
                                    self.data.add_row_with_fact(&scratch, fact)
                                } else {
                                    self.data.add_row(&scratch)
                                };
                                self.data.set_stale(*row);
                                *row = new;
                                changed = true;
                            }
                            scratch.clear();
                        } else {
                            // New value: update invariants.
                            let incoming_cause = incoming_cause
                                .as_ref()
                                .map(DeferredEqualityCause::promote)
                                .unwrap_or(CauseDraftId::UNATTRIBUTED);
                            let fact = receipt_batch.as_mut().map_or(FactId::MISSING, |batch| {
                                batch.record_fact_with_terms(
                                    self.table_id,
                                    incoming_cause,
                                    query,
                                    buf.receipt_terms(proposal_index),
                                )
                            });
                            let new = if RECEIPTS {
                                self.data.add_row_with_fact(query, fact)
                            } else {
                                self.data.add_row(query)
                            };
                            let (shard, hc) = hash_code(self.hash.shard_data(), query, self.n_keys);
                            debug_assert_eq!(shard, _outer_shard);
                            self.hash.mut_shards()[shard.index()].insert_unique(
                                hc as _,
                                TableEntry {
                                    hashcode: hc as _,
                                    row: new,
                                },
                                TableEntry::hashcode,
                            );
                            changed = true;
                        }
                    }
                }
            };
        }
        if let Some(batch) = receipt_batch {
            batch.publish();
        }
        changed
    }

    fn parallel_insert<C: OrderingChecker>(
        &mut self,
        exec_state: &ExecutionState,
        checker: C,
    ) -> bool {
        if exec_state.causal_receipts().is_none() {
            self.parallel_insert_mode::<C, false>(exec_state, checker)
        } else {
            self.parallel_insert_mode::<C, true>(exec_state, checker)
        }
    }

    fn parallel_insert_mode<C: OrderingChecker, const RECEIPTS: bool>(
        &mut self,
        exec_state: &ExecutionState,
        checker: C,
    ) -> bool {
        const BATCH_SIZE: usize = 1 << 18;
        // Parallel insert uses one giant parallel foreach. We have updates
        // pre-sharded, and one logical thread can process updates for each
        // shard independently. Updates happen in three phases, which comments
        // describe below.
        let shard_data = self.hash.shard_data();
        let n_keys = self.n_keys;
        let n_cols = self.n_columns;
        let next_offset = RowId::from_usize(self.data.data.len());
        let row_writer = self.data.data.parallel_writer();
        let pending_adds = self
            .hash
            .mut_shards()
            .par_iter_mut()
            .enumerate()
            .map(|(shard_id, shard)| {
                let shard_id = ShardId::from_usize(shard_id);
                let mut checker = checker.clone();
                let mut exec_state = exec_state.clone();
                let mut scratch = with_pool_set(|ps| ps.get::<Vec<Value>>());
                let queue = &self.pending_state.pending_rows[shard_id];
                let mut marked_stale = 0usize;
                let mut staged =
                    StagedOutputs::new::<RECEIPTS>(n_keys, n_cols, BATCH_SIZE);
                let mut receipt_batch = if RECEIPTS {
                    Some(
                        exec_state
                            .causal_receipts()
                            .expect("receipt mode requires an enabled arena")
                            .new_batch(),
                    )
                } else {
                    None
                };
                let mut fact_assignments = receipt_batch
                    .as_ref()
                    .map(|_| HashMap::<RowId, FactId>::default());
                let mut changed = false;
                // The core flush loop: We call once `staged` reaches `BATCH_SIZE` or
                // when we're done.
                macro_rules! flush_staged_outputs {
                    () => {{
                        // Phase 2: Write the staged rows to the row writer. This only
                        // works due to the `ParallelRowBufWriter` machinery.
                        let (start_row, stale) = staged.write_output(&row_writer);
                        marked_stale += stale;
                        // Phase 3: With the values buffered in the row buffer, we can
                        // write them back to the shard, pointed to the correct rows.

                        // In the serial implementation, we do phases 2 and 3 inline with
                        // processing the incoming mutation, but separating them out
                        // this way allows us to do a single write to the shared row
                        // buffer, rather than one per row, which would cause
                        // contention.
                        let mut cur_row = start_row;
                        let read_handle = row_writer.read_handle();
                        for (row_index, row) in staged.rows() {
                            let staged_cause = staged.cause::<RECEIPTS>(row_index);
                            if row.first().map(Value::is_stale).unwrap_or(false) {
                                cur_row = cur_row.inc();
                                continue;
                            }
                            use hashbrown::hash_table::Entry;
                            checker.check_local(row);
                            changed = true;
                            let key = &row[0..n_keys];
                            let (_actual_shard, hc) = hash_code(shard_data, row, n_keys);
                            #[cfg(any(debug_assertions, test))]
                            {
                                unsafe {
                                    // read the value we wrote at this row and
                                    // check that it matches.
                                    assert_eq!(read_handle.get_row_unchecked(cur_row), row);
                                }
                            }
                            debug_assert_eq!(_actual_shard, shard_id);
                            match shard.entry(
                                hc,
                                // SAFETY: `ent` must point to a valid row
                                |ent| unsafe {
                                    ent.hashcode == hc as HashCode
                                        && &read_handle.get_row_unchecked(ent.row)[0..n_keys] == key
                                },
                                TableEntry::hashcode,
                            ) {
                                Entry::Occupied(mut occ) => {
                                    // SAFETY: `occ` must point to a valid row: we only insert valid rows
                                    // into the map.
                                    let cur = unsafe { read_handle.get_row_unchecked(occ.get().row) };

                                    let prior_fact = if RECEIPTS {
                                        let assignments = fact_assignments
                                            .as_ref()
                                            .expect("receipt mode requires fact assignments");
                                        if occ.get().row < next_offset {
                                            self.data
                                                .fact_id(occ.get().row)
                                                .unwrap_or(FactId::MISSING)
                                        } else {
                                            assignments
                                                .get(&occ.get().row)
                                                .copied()
                                                .unwrap_or(FactId::MISSING)
                                        }
                                    } else {
                                        FactId::MISSING
                                    };
                                    let merge_cause = receipt_batch.as_mut().map(|batch| {
                                        batch.merge_draft_capability(staged_cause, prior_fact)
                                    });
                                    let previous_cause = RECEIPTS
                                        .then(|| exec_state.active_cause_capability())
                                        .flatten();
                                    if RECEIPTS {
                                        exec_state.set_active_cause_capability(Some(
                                            merge_cause.expect(
                                                "receipt merge is missing its capability",
                                            ),
                                        ));
                                    }

                                    // SAFETY: The safety requirements of
                                    // `set_stale_shared` are that there are no
                                    // concurrent accesses to `row`. We have
                                    // exclusive access to any row whose hash matches this
                                    // shard.
                                    if (self.merge)(&mut exec_state, cur, row, &mut scratch) {
                                        if let (Some(batch), Some(assignments)) =
                                            (&mut receipt_batch, &mut fact_assignments)
                                        {
                                            let fact = batch.record_fact(
                                                self.table_id,
                                                merge_cause
                                                    .expect(
                                                        "receipt merge is missing its capability",
                                                    )
                                                    .id(),
                                                row,
                                            );
                                            assignments.insert(cur_row, fact);
                                        }
                                        unsafe {
                                            let _was_stale = read_handle.set_stale_shared(occ.get().row);
                                            debug_assert!(!_was_stale);
                                        }
                                        occ.get_mut().row = cur_row;
                                        changed = true;
                                    } else {
                                        // Mark the new row as stale: we didn't end up needing it.
                                        unsafe {
                                            let _was_stale = read_handle.set_stale_shared(cur_row);
                                            debug_assert!(!_was_stale);
                                        }
                                    }
                                    if RECEIPTS {
                                        exec_state.set_active_cause_capability(previous_cause);
                                    }
                                    marked_stale += 1;
                                    scratch.clear();
                                }
                                Entry::Vacant(v) => {
                                    if let (Some(batch), Some(assignments)) =
                                        (&mut receipt_batch, &mut fact_assignments)
                                    {
                                        let fact =
                                            batch.record_fact(self.table_id, staged_cause, row);
                                        assignments.insert(cur_row, fact);
                                    }
                                    changed = true;
                                    v.insert(TableEntry {
                                        hashcode: hc as HashCode,
                                        row: cur_row,
                                    });
                                }
                            }

                            cur_row = cur_row.inc();
                        }
                        staged.clear();
                    }};
                }
                // Phase 1: process all incoming updates:
                // * Add new values to `staged`
                // * Removing entries in `shard` and mark them as stale in
                // `data` if they will be overwritten.
                while let Some(buf) = queue.pop() {
                    let ready_causes = if RECEIPTS {
                        let causes = buf.promoted_receipt_causes();
                        receipt_batch
                            .as_mut()
                            .expect("receipt mode requires an open batch")
                            .preload_cause_summaries(&causes);
                        Some(causes)
                    } else {
                        None
                    };
                    // We create a read_handle once per batch to avoid blocking
                    // too many threads if someone needs to resize the row
                    // writer.
                    for (proposal_index, row) in buf.rows.iter().enumerate() {
                        if row.first().is_some_and(|value| value.is_stale()) {
                            continue;
                        }
                        let cause = if RECEIPTS {
                            ready_causes.as_ref().unwrap()[proposal_index]
                        } else {
                            CauseDraftId::UNATTRIBUTED
                        };
                        staged.insert::<RECEIPTS>(
                            row,
                            cause,
                            |cur, cur_cause, new, incoming_cause, out| {
                            let merge_cause = receipt_batch.as_mut().map(|batch| {
                                batch.merge_drafts_capability(incoming_cause, cur_cause)
                            });
                            let previous = RECEIPTS
                                .then(|| exec_state.active_cause_capability())
                                .flatten();
                            if RECEIPTS {
                                exec_state.set_active_cause_capability(Some(
                                    merge_cause
                                        .expect("receipt merge is missing its capability"),
                                ));
                            }
                            let changed = (self.merge)(&mut exec_state, cur, new, out);
                            if RECEIPTS {
                                exec_state.set_active_cause_capability(previous);
                            }
                            (
                                changed,
                                merge_cause.map_or(CauseDraftId::UNATTRIBUTED, |cause| cause.id()),
                            )
                        });
                        if staged.len() >= BATCH_SIZE {
                            flush_staged_outputs!();
                        }
                    }
                }
                flush_staged_outputs!();
                if let Some(batch) = receipt_batch {
                    batch.publish();
                }
                (checker, marked_stale, changed, fact_assignments)
            })
            .collect_vec_list();
        self.data.data = row_writer.finish();
        if RECEIPTS {
            let fact_ids = self.data.fact_ids.get_or_insert_with(FactSidecars::default);
            fact_ids.data.resize(self.data.data.len(), FactId::MISSING);
            for (_, _, _, assignments) in pending_adds.iter().flatten() {
                let assignments = assignments
                    .as_ref()
                    .expect("receipt mode requires fact assignments");
                for (&row, &fact) in assignments {
                    fact_ids.data[row.index()] = fact;
                }
            }
        }
        // Now we just need to reset our invariants.

        // Confirm none of the writes violated sort order and update the
        // `offsets` vector.
        let checker = C::check_global(
            pending_adds
                .iter()
                .flatten()
                .map(|(checker, _, _, _)| checker),
        );
        checker.update_offsets(next_offset, &mut self.offsets);

        // Update the staleness counters.
        self.data.stale_rows += pending_adds
            .iter()
            .flatten()
            .map(|(_, stale, _, _)| *stale)
            .sum::<usize>();

        // Register any changes.
        pending_adds
            .iter()
            .flatten()
            .any(|(_, _, changed, _)| *changed)
    }

    fn binary_search_sort_val(&self, val: Value) -> Result<(RowId, RowId), RowId> {
        debug_assert!(
            self.offsets.windows(2).all(|x| x[0].1 < x[1].1),
            "{:?}",
            self.offsets
        );

        debug_assert!(
            self.offsets.windows(2).all(|x| x[0].0 < x[1].0),
            "{:?}",
            self.offsets
        );
        match self.offsets.binary_search_by_key(&val, |(v, _)| *v) {
            Ok(got) => Ok((
                self.offsets[got].1,
                self.offsets
                    .get(got + 1)
                    .map(|(_, r)| *r)
                    .unwrap_or(self.data.next_row()),
            )),
            Err(next) => Err(self
                .offsets
                .get(next)
                .map(|(_, id)| *id)
                .unwrap_or(self.data.next_row())),
        }
    }
    fn eval(&self, cs: &[Constraint], row: RowId) -> bool {
        self.get_if(cs, row).is_some()
    }

    fn eval_constraints(cs: &[Constraint], row: &[Value]) -> bool {
        cs.iter().all(|constraint| match constraint {
            Constraint::Eq { l_col, r_col } => row[l_col.index()] == row[r_col.index()],
            Constraint::EqConst { col, val } => row[col.index()] == *val,
            Constraint::LtConst { col, val } => row[col.index()] < *val,
            Constraint::GtConst { col, val } => row[col.index()] > *val,
            Constraint::LeConst { col, val } => row[col.index()] <= *val,
            Constraint::GeConst { col, val } => row[col.index()] >= *val,
        })
    }

    unsafe fn get_if_unchecked(&self, cs: &[Constraint], row: RowId) -> Option<&[Value]> {
        let row = unsafe { self.data.data.get_row_unchecked(row) };
        if Self::eval_constraints(cs, row) {
            Some(row)
        } else {
            None
        }
    }

    fn get_if(&self, cs: &[Constraint], row: RowId) -> Option<&[Value]> {
        let row = self.data.get_row(row)?;
        if Self::eval_constraints(cs, row) {
            Some(row)
        } else {
            None
        }
    }

    fn maybe_rehash(&mut self) {
        if self.data.stale_rows <= cmp::max(16, self.data.data.len() / 2) {
            return;
        }

        if self.data.fact_ids.is_none() && parallelize_table_op(self.data.data.len()) {
            self.parallel_rehash();
        } else {
            self.rehash();
        }
    }
    fn parallel_rehash(&mut self) {
        use rayon::prelude::*;
        // Parallel rehashes go "hash-first" rather than "rows-first".
        //
        // We iterate over each shard and then write out new contents to a fresh row, in parallel.
        let Some(sort_by) = self.sort_by else {
            // Just do a serial rehash for now. We currently do not have a use-case for parallel
            // compaction of unsorted tables.
            //
            // Implementing parallel compaction for an unsorted table is much easier: each shard
            // can write to a contiguous chunk of the `scratch` buffer, with the offsets being
            // pre-chunked based on the size of each shard.
            self.rehash();
            return;
        };
        self.generation = self.generation.inc();
        assert!(!self.offsets.is_empty());
        struct TimestampStats {
            value: Value,
            count: usize,
            histogram: Pooled<DenseIdMap<ShardId, usize>>,
        }
        impl Default for TimestampStats {
            fn default() -> TimestampStats {
                TimestampStats {
                    value: Value::stale(),
                    count: 0,
                    histogram: with_pool_set(|ps| ps.get()),
                }
            }
        }
        let mut results = Vec::<TimestampStats>::with_capacity(self.offsets.len());
        results.resize_with(self.offsets.len() - 1, Default::default);
        // Use a macro rather than a lambda to avoid borrow issues.
        macro_rules! compute_hist {
            ($start_val: expr, $start_row: expr, $end_row: expr) => {{
                let mut histogram: Pooled<DenseIdMap<ShardId, usize>> =
                    with_pool_set(|ps| ps.get());
                let mut cur_row = $start_row;
                let mut count = 0;
                while cur_row < $end_row {
                    if let Some(row) = self.data.get_row(cur_row) {
                        count += 1;
                        let (shard, _) = hash_code(self.hash.shard_data(), row, self.n_keys);
                        *histogram.get_or_default(shard) += 1;
                    }
                    cur_row = cur_row.inc();
                }
                TimestampStats {
                    value: $start_val,
                    count,
                    histogram,
                }
            }};
        }
        let mut last: TimestampStats = Default::default();
        rayon::join(
            || {
                // This closure handles computing all timestamps but the last one.
                self.offsets
                    .windows(2)
                    .zip(results.iter_mut())
                    .par_bridge()
                    .for_each(|(xs, res)| {
                        let [(start_val, start_row), (_, end_row)] = xs else {
                            unreachable!()
                        };
                        *res = compute_hist!(*start_val, *start_row, *end_row);
                    })
            },
            || {
                // And here we handle the final one.
                let (start_val, start_row) = self.offsets.last().unwrap();
                let end_row = self.data.next_row();
                last = compute_hist!(*start_val, *start_row, end_row);
            },
        );
        results.push(last);
        // Now we need to compute cumulative statistics on the row layouts here.
        // We do this serially a we currently don't have a ton of use for cases with thousands
        // of timestamps or more. There are well-known parallel algorithms for computing these
        // cumulative statistics in parallel, but they aren't currently all that well-suited
        // for rayon at the moment.
        let mut prev_count = 0;
        self.offsets.clear();
        for stats in results.iter_mut() {
            if stats.count == 0 {
                continue;
            }
            self.offsets
                .push((stats.value, RowId::from_usize(prev_count)));
            let mut inner = prev_count;
            for (_, count) in stats.histogram.iter_mut() {
                // Each entry in the histogram now points to the start row for that shard's
                // rows for a given timestamp.
                let tmp = *count;
                *count = inner;
                inner += tmp;
            }
            prev_count += stats.count;
            debug_assert_eq!(inner, prev_count)
        }

        // Now the part with some unsafe code.
        // We will iterate over each shard and use the statistics in `results` to guide where
        // each row will go.
        //
        // This involves doing unsynchronized writes to the table (ptr::copy_nonoverlapping)
        // followed by a set_len. The safety of these operations relies on the fact that:
        // * No one grabs a reference to the interior of `scratch` until these operations have
        //   finished.
        // * `scratch` does not overlap `data`.
        // * The sharding function completely partitions the set of objects in the table: one
        //   shard's writes will never stomp on those of another.

        self.data.scratch.clear();
        self.data.scratch.reserve(prev_count);
        let compacted_facts = if self.data.fact_ids.is_some() {
            // Fact identities follow logical rows through physical compaction.
            // This branch is never entered by an ordinary table.
            let compacted_facts = (0..prev_count)
                .map(|_| AtomicU64::new(FactId::MISSING.get()))
                .collect::<Vec<_>>();
            self.hash
                .mut_shards()
                .par_iter_mut()
                .with_max_len(1)
                .enumerate()
                .for_each(|(shard_id, shard)| {
                    let shard_id = ShardId::from_usize(shard_id);
                    let scratch_ptr = self.data.scratch.raw_rows();
                    let mut progress = HashMap::<Value, RowId>::default();
                    progress.reserve(results.len());
                    for stats in &results {
                        let Some(start) = stats.histogram.get(shard_id) else {
                            continue;
                        };
                        progress.insert(stats.value, RowId::from_usize(*start));
                    }
                    for TableEntry { row: row_id, .. } in shard.iter_mut() {
                        let prior_fact = self.data.fact_id(*row_id).unwrap_or(FactId::MISSING);
                        let row = self
                            .data
                            .get_row(*row_id)
                            .expect("shard should not map to a stale value");
                        let val = row[sort_by.index()];
                        let next = progress[&val];
                        unsafe {
                            std::ptr::copy_nonoverlapping(
                                row.as_ptr(),
                                scratch_ptr.add(next.index() * self.n_columns) as *mut Value,
                                self.n_columns,
                            )
                        }
                        compacted_facts[next.index()].store(prior_fact.get(), Ordering::Relaxed);
                        *row_id = next;
                        progress.insert(val, next.inc());
                    }
                });
            Some(compacted_facts)
        } else {
            self.hash
                .mut_shards()
                .par_iter_mut()
                .with_max_len(1)
                .enumerate()
                .for_each(|(shard_id, shard)| {
                    let shard_id = ShardId::from_usize(shard_id);
                    let scratch_ptr = self.data.scratch.raw_rows();
                    let mut progress = HashMap::<Value, RowId>::default();
                    progress.reserve(results.len());
                    for stats in &results {
                        let Some(start) = stats.histogram.get(shard_id) else {
                            continue;
                        };
                        progress.insert(stats.value, RowId::from_usize(*start));
                    }
                    for TableEntry { row: row_id, .. } in shard.iter_mut() {
                        let row = self
                            .data
                            .get_row(*row_id)
                            .expect("shard should not map to a stale value");
                        let val = row[sort_by.index()];
                        let next = progress[&val];
                        unsafe {
                            std::ptr::copy_nonoverlapping(
                                row.as_ptr(),
                                scratch_ptr.add(next.index() * self.n_columns) as *mut Value,
                                self.n_columns,
                            )
                        }
                        *row_id = next;
                        progress.insert(val, next.inc());
                    }
                });
            None
        };
        // SAFETY: see above longer comment.
        unsafe { self.data.scratch.set_len(prev_count) };
        mem::swap(&mut self.data.data, &mut self.data.scratch);
        if let Some(compacted_facts) = compacted_facts {
            let compacted_facts = compacted_facts
                .into_iter()
                .map(|fact| FactId::new(fact.into_inner()))
                .collect::<Vec<_>>();
            let sidecars = self.data.fact_ids.as_mut().unwrap();
            sidecars.scratch = mem::replace(&mut sidecars.data, compacted_facts);
        }
        self.data.stale_rows = 0;
    }
    fn rehash_impl(
        sort_by: Option<ColumnId>,
        n_keys: usize,
        rows: &mut Rows,
        offsets: &mut Vec<(Value, RowId)>,
        hash: &mut ShardedHashTable<TableEntry>,
    ) {
        if let Some(sort_by) = sort_by {
            offsets.clear();
            rows.remove_stale(|row, old, new| {
                let stale_entry = get_entry_mut(row, n_keys, hash, |x| x == old)
                    .expect("non-stale entry not mapped in hash");
                *stale_entry = new;
                let sort_col = row[sort_by.index()];
                if let Some((max, _)) = offsets.last() {
                    if sort_col > *max {
                        offsets.push((sort_col, new));
                    }
                } else {
                    offsets.push((sort_col, new));
                }
            })
        } else {
            rows.remove_stale(|row, old, new| {
                let stale_entry = get_entry_mut(row, n_keys, hash, |x| x == old)
                    .expect("non-stale entry not mapped in hash");
                *stale_entry = new;
            })
        }
    }

    fn rehash(&mut self) {
        self.generation = self.generation.inc();
        Self::rehash_impl(
            self.sort_by,
            self.n_keys,
            &mut self.data,
            &mut self.offsets,
            &mut self.hash,
        )
    }
}

fn get_entry(
    row: &[Value],
    n_keys: usize,
    table: &ShardedHashTable<TableEntry>,
    test: impl Fn(RowId) -> bool,
) -> Option<RowId> {
    let (shard, hash) = hash_code(table.shard_data(), row, n_keys);
    table
        .get_shard(shard)
        .find(hash, |ent| {
            ent.hashcode == hash as HashCode && test(ent.row)
        })
        .map(|ent| ent.row)
}

fn get_entry_mut<'a>(
    row: &[Value],
    n_keys: usize,
    table: &'a mut ShardedHashTable<TableEntry>,
    test: impl Fn(RowId) -> bool,
) -> Option<&'a mut RowId> {
    let (shard, hash) = hash_code(table.shard_data(), row, n_keys);
    table.mut_shards()[shard.index()]
        .find_mut(hash, |ent| {
            ent.hashcode == hash as HashCode && test(ent.row)
        })
        .map(|ent| &mut ent.row)
}

fn hash_code(shard_data: ShardData, row: &[Value], n_keys: usize) -> (ShardId, u64) {
    let mut hasher = FxHasher::default();
    for val in &row[0..n_keys] {
        hasher.write_usize(val.index());
    }
    let full_code = hasher.finish();
    // We keep this cast here to allow for experimenting with HashCode=u32.
    #[allow(clippy::unnecessary_cast)]
    (shard_data.shard_id(full_code), full_code as HashCode as u64)
}

/// A simple struct for packaging up pending mutations to a `SortedWritesTable`.
struct PendingState {
    pending_rows: DenseIdMap<ShardId, SegQueue<PendingRowBatch>>,
    pending_removals: DenseIdMap<ShardId, SegQueue<ArbitraryRowBuffer>>,
    total_removals: AtomicUsize,
    total_rows: AtomicUsize,
}

#[derive(Clone)]
struct PendingRowBatch {
    rows: RowBuffer,
    causes: Option<Vec<DeferredEqualityCause>>,
    row_terms: Option<Vec<Option<Box<[ReplayTermId]>>>>,
    _native_lease: Option<PendingNativeLease>,
}

impl PendingRowBatch {
    fn receipt_causes(&self) -> &[DeferredEqualityCause] {
        let causes = self
            .causes
            .as_deref()
            .expect("receipt-enabled table batch has no cause sidecar");
        assert_eq!(
            causes.len(),
            self.rows.len(),
            "receipt-enabled table batch has incomplete cause sidecar"
        );
        causes
    }

    fn receipt_cause(&self, index: usize) -> DeferredEqualityCause {
        self.receipt_causes()[index].clone()
    }

    fn promoted_receipt_causes(&self) -> Vec<CauseDraftId> {
        self.receipt_causes()
            .iter()
            .map(DeferredEqualityCause::promote)
            .collect()
    }

    fn receipt_terms(&self, index: usize) -> Option<&[ReplayTermId]> {
        let terms = self
            .row_terms
            .as_deref()
            .expect("receipt-enabled table batch has no structural-term sidecar");
        assert_eq!(
            terms.len(),
            self.rows.len(),
            "receipt-enabled table batch has incomplete structural-term sidecar"
        );
        terms[index].as_deref()
    }
}

impl PendingState {
    fn new(shard_data: ShardData) -> PendingState {
        let n_shards = shard_data.n_shards();
        let mut pending_rows = DenseIdMap::with_capacity(n_shards);
        let mut pending_removals = DenseIdMap::with_capacity(n_shards);
        for i in 0..n_shards {
            pending_rows.insert(ShardId::from_usize(i), SegQueue::default());
            pending_removals.insert(ShardId::from_usize(i), SegQueue::default());
        }

        PendingState {
            pending_rows,
            pending_removals,
            total_removals: AtomicUsize::new(0),
            total_rows: AtomicUsize::new(0),
        }
    }
    fn clear(&self) {
        for (_, queue) in self.pending_rows.iter() {
            while queue.pop().is_some() {}
        }

        for (_, queue) in self.pending_removals.iter() {
            while queue.pop().is_some() {}
        }
    }

    /// This is only really used in debugging, but it's annoying enough to write
    /// that it may help to have around.
    ///
    /// We also, however, use it in the clone impl (which should only be called when pending state
    /// is empty).
    fn deep_copy(&self) -> PendingState {
        let mut pending_rows = DenseIdMap::new();
        let mut pending_removals = DenseIdMap::new();
        fn drain_queue<T>(queue: &SegQueue<T>) -> Vec<T> {
            let mut res = Vec::new();
            while let Some(x) = queue.pop() {
                res.push(x);
            }
            res
        }
        for (shard, queue) in self.pending_rows.iter() {
            let contents = drain_queue(queue);
            let new_queue = SegQueue::default();
            for x in contents {
                new_queue.push(x.clone());
                queue.push(x);
            }
            pending_rows.insert(shard, new_queue);
        }

        for (shard, queue) in self.pending_removals.iter() {
            let contents = drain_queue(queue);
            let new_queue = SegQueue::default();
            for x in contents {
                new_queue.push(x.clone());
                queue.push(x);
            }
            pending_removals.insert(shard, new_queue);
        }

        PendingState {
            pending_rows,
            pending_removals,
            total_removals: AtomicUsize::new(self.total_removals.load(Ordering::Acquire)),
            total_rows: AtomicUsize::new(self.total_rows.load(Ordering::Acquire)),
        }
    }
}

/// A trait that encapsulates the logic of potentially checking that written
/// columns appear in sorted order.
///
/// For rows that are sorted by a column, an OrderingChecker asserts that all
/// new rows have the same value in that column, and that the column is greater
/// than or equal to the column value coming in. For rows not sorted, these
/// checks become no-ops.
trait OrderingChecker: Clone + Send + Sync {
    /// Check any invariants locally, updating the state of the checker when
    /// doing so.
    fn check_local(&mut self, row: &[Value]);
    /// Combine the states of multiple checkers, returning a new checker with
    /// all information assimilated. This is the checker that is suitable for
    /// calling `update_offsets` with.
    fn check_global<'a>(checkers: impl Iterator<Item = &'a Self>) -> Self
    where
        Self: 'a;
    /// Update the sorted offset vector with the current state of the checker.
    fn update_offsets(&self, start: RowId, offsets: &mut Vec<(Value, RowId)>);
}

impl OrderingChecker for () {
    fn check_local(&mut self, _: &[Value]) {}
    fn check_global<'a>(_: impl Iterator<Item = &'a ()>) {}
    fn update_offsets(&self, _: RowId, _: &mut Vec<(Value, RowId)>) {}
}

#[derive(Copy, Clone)]
struct SortChecker {
    col: ColumnId,
    baseline: Option<Value>,
    current: Option<Value>,
}

impl OrderingChecker for SortChecker {
    fn check_local(&mut self, row: &[Value]) {
        let val = row[self.col.index()];
        if let Some(cur) = self.current {
            assert_eq!(
                cur, val,
                "concurrently inserting rows with different sort keys"
            );
        } else {
            self.current = Some(val);
            if let Some(baseline) = self.baseline {
                assert!(val >= baseline, "inserted row violates sort order");
            }
        }
    }

    fn check_global<'a>(mut checkers: impl Iterator<Item = &'a Self>) -> Self {
        let Some(start) = checkers.next() else {
            return SortChecker {
                col: ColumnId::new(!0),
                baseline: None,
                current: None,
            };
        };
        let mut expected = start.current;
        for checker in checkers {
            assert_eq!(checker.baseline, start.baseline);
            match (&mut expected, checker.current) {
                (None, None) => {}
                (cur @ None, Some(x)) => {
                    *cur = Some(x);
                }
                (Some(_), None) => {}
                (Some(x), Some(y)) => {
                    assert_eq!(
                        *x, y,
                        "concurrently inserting rows with different sort keys"
                    );
                }
            }
        }
        SortChecker {
            col: start.col,
            baseline: start.baseline,
            current: expected,
        }
    }

    fn update_offsets(&self, start: RowId, offsets: &mut Vec<(Value, RowId)>) {
        if let Some(cur) = self.current {
            if let Some((max, _)) = offsets.last() {
                if cur > *max {
                    offsets.push((cur, start));
                }
            } else {
                offsets.push((cur, start));
            }
        }
    }
}

/// A type similar to a SortedWritesTable used to buffer outputs. The main thing
/// that StagedOutputs handles is running the merge function for a table on
/// multiple updates to the same key that show up in the same round of
/// insertions.
struct StagedOutputs {
    shard_data: ShardData,
    n_keys: usize,
    hash: Pooled<HashTable<TableEntry>>,
    rows: RowBuffer,
    // Receipt causes are a lazy sidecar. The ordinary monomorphization keeps
    // this `None`, so it neither allocates nor writes causal metadata.
    causes: Option<Vec<CauseDraftId>>,
    n_stale: usize,
    scratch: Pooled<Vec<Value>>,
}

impl StagedOutputs {
    fn rows(&self) -> impl Iterator<Item = (usize, &[Value])> {
        self.rows.iter().enumerate()
    }

    fn cause<const RECEIPTS: bool>(&self, row_index: usize) -> CauseDraftId {
        if RECEIPTS {
            self.causes
                .as_ref()
                .expect("receipt staging requires a cause sidecar")[row_index]
        } else {
            CauseDraftId::UNATTRIBUTED
        }
    }

    fn new<const RECEIPTS: bool>(n_keys: usize, n_cols: usize, capacity: usize) -> Self {
        let mut res = with_pool_set(|ps| StagedOutputs {
            shard_data: ShardData::new(1),
            n_keys,
            n_stale: 0,
            hash: ps.get(),
            rows: RowBuffer::new(n_cols),
            // Do not reserve BATCH_SIZE causes (2 MiB) up front. Receipt
            // staging grows only with rows actually observed by this shard.
            causes: RECEIPTS.then(Vec::new),
            scratch: ps.get(),
        });
        res.hash.reserve(capacity, TableEntry::hashcode);
        res.rows.reserve(capacity);
        res
    }

    fn clear(&mut self) {
        self.hash.clear();
        self.rows.clear();
        if let Some(causes) = &mut self.causes {
            causes.clear();
        }
        self.n_stale = 0;
    }

    fn len(&self) -> usize {
        self.rows.len() - self.n_stale
    }

    fn insert<const RECEIPTS: bool>(
        &mut self,
        row: &[Value],
        cause: CauseDraftId,
        mut merge_fn: impl FnMut(
            &[Value],
            CauseDraftId,
            &[Value],
            CauseDraftId,
            &mut Vec<Value>,
        ) -> (bool, CauseDraftId),
    ) {
        if row[0].is_stale() {
            return;
        }
        use hashbrown::hash_table::Entry;
        let (_, hc) = hash_code(self.shard_data, row, self.n_keys);
        let entry = self.hash.entry(
            hc,
            |te| {
                te.hashcode() == hc
                    && self.rows.get_row(te.row)[0..self.n_keys] == row[0..self.n_keys]
            },
            TableEntry::hashcode,
        );
        match entry {
            Entry::Occupied(mut occupied_entry) => {
                let prior_row = occupied_entry.get().row;
                let cur = self.rows.get_row(prior_row);
                let prior_cause = if RECEIPTS {
                    self.causes
                        .as_ref()
                        .expect("receipt staging requires a cause sidecar")[prior_row.index()]
                } else {
                    CauseDraftId::UNATTRIBUTED
                };
                let (changed, merged_cause) =
                    merge_fn(cur, prior_cause, row, cause, &mut self.scratch);
                if changed {
                    let new = self.rows.add_row(&self.scratch);
                    if RECEIPTS {
                        let causes = self
                            .causes
                            .as_mut()
                            .expect("receipt staging requires a cause sidecar");
                        debug_assert_eq!(new.index(), causes.len());
                        causes.push(merged_cause);
                    }
                    self.rows.set_stale(prior_row);
                    self.n_stale += 1;
                    occupied_entry.get_mut().row = new;
                }
                self.scratch.clear();
            }
            Entry::Vacant(vacant_entry) => {
                let next = self.rows.add_row(row);
                if RECEIPTS {
                    let causes = self
                        .causes
                        .as_mut()
                        .expect("receipt staging requires a cause sidecar");
                    debug_assert_eq!(next.index(), causes.len());
                    causes.push(cause);
                }
                vacant_entry.insert(TableEntry {
                    hashcode: hc as _,
                    row: next,
                });
            }
        }
    }

    fn write_output(&self, output: &ParallelRowBufWriter) -> (RowId, usize) {
        (output.append_contents(&self.rows), self.n_stale)
    }
}
