//! High-level types for specifying the behavior and layout of tables.
//!
//! Tables are a mapping from some set of keys to another set of values. Tables
//! can also be "sorted by" a columna dn "partitioned by" another. This can help
//! speed up queries.

use std::{
    any::Any,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    sync::{
        Arc, Mutex,
        atomic::{AtomicU8, Ordering},
    },
};

use crate::numeric_id::{DenseIdMap, NumericId, define_id};
use smallvec::SmallVec;

use crate::{
    CauseDraftId, EqualityEdgeCount, FactId, QueryEntry, TableId, TypedEqualityProposal, Variable,
    action::{
        Bindings, ExecutionState,
        mask::{Mask, MaskIter, ValueSource},
    },
    common::Value,
    hash_index::{ColumnIndex, IndexBase, TupleIndex},
    offsets::{RowId, Subset, SubsetRef},
    pool::{PoolSet, Pooled, with_pool_set},
    row_buffer::{RowBuffer, RowSink, TaggedRowBuffer},
};

define_id!(pub ColumnId, u32, "a particular column in a table", pretty "Col");

const MUTATION_PENDING: u8 = 0;
const MUTATION_COMMITTED: u8 = 1;
const MUTATION_ABORTED: u8 = 2;

/// Shared decision token for one multi-buffer native mutation. Pending
/// batches may be staged concurrently, but no table may consume them until
/// the coordinator records an explicit commit or abort decision.
#[derive(Clone)]
#[doc(hidden)]
pub struct MutationTransaction(Arc<MutationTransactionState>);

struct MutationTransactionState {
    decision: AtomicU8,
    pending: Mutex<PendingMutationTransaction>,
}

#[derive(Default)]
struct PendingMutationTransaction {
    publications: Vec<Box<dyn FnOnce() + Send>>,
    rebuild_cursors: Vec<RebuildCursor>,
    changed_tables: Vec<TableId>,
}

pub(crate) struct RebuildCursor {
    pub(crate) target: TableId,
    pub(crate) source: TableId,
    pub(crate) version: TableVersion,
}

pub(crate) struct MutationCommit {
    pub(crate) rebuild_cursors: Vec<RebuildCursor>,
    pub(crate) changed_tables: Vec<TableId>,
}

impl MutationTransaction {
    pub(crate) fn pending() -> Self {
        Self(Arc::new(MutationTransactionState {
            decision: AtomicU8::new(MUTATION_PENDING),
            pending: Mutex::new(PendingMutationTransaction::default()),
        }))
    }

    pub(crate) fn commit(&self) -> MutationCommit {
        let mut pending = self.0.pending.lock().unwrap();
        assert_eq!(
            self.0.decision.swap(MUTATION_COMMITTED, Ordering::Release),
            MUTATION_PENDING,
            "mutation transaction received more than one terminal decision"
        );
        let publications = std::mem::take(&mut pending.publications);
        let cursors = std::mem::take(&mut pending.rebuild_cursors);
        let changed_tables = std::mem::take(&mut pending.changed_tables);
        drop(pending);
        for publish in publications {
            publish();
        }
        MutationCommit {
            rebuild_cursors: cursors,
            changed_tables,
        }
    }

    pub(crate) fn abort(&self) {
        let mut pending = self.0.pending.lock().unwrap();
        assert_eq!(
            self.0.decision.swap(MUTATION_ABORTED, Ordering::Release),
            MUTATION_PENDING,
            "mutation transaction received more than one terminal decision"
        );
        pending.publications.clear();
        pending.rebuild_cursors.clear();
        pending.changed_tables.clear();
    }

    pub(crate) fn defer_publication(&self, publish: impl FnOnce() + Send + 'static) {
        let mut pending = self.0.pending.lock().unwrap();
        match self.0.decision.load(Ordering::Acquire) {
            MUTATION_PENDING => {
                pending.publications.push(Box::new(publish));
            }
            MUTATION_COMMITTED => {
                drop(pending);
                publish();
            }
            MUTATION_ABORTED => {}
            _ => unreachable!("invalid mutation transaction state"),
        }
    }

    pub(crate) fn defer_rebuild_cursor(
        &self,
        target: TableId,
        source: TableId,
        version: TableVersion,
    ) {
        let mut pending = self.0.pending.lock().unwrap();
        assert_eq!(
            self.0.decision.load(Ordering::Acquire),
            MUTATION_PENDING,
            "rebuild cursor registered after its transaction decision"
        );
        pending.rebuild_cursors.push(RebuildCursor {
            target,
            source,
            version,
        });
    }

    pub(crate) fn defer_changed_table(&self, table: TableId) {
        let mut pending = self.0.pending.lock().unwrap();
        assert_eq!(
            self.0.decision.load(Ordering::Acquire),
            MUTATION_PENDING,
            "changed table registered after its transaction decision"
        );
        pending.changed_tables.push(table);
    }
}

define_id!(
    pub Generation,
    u64,
    "the current version of a table -- used to invalidate any existing RowIds"
);
define_id!(
    pub Offset,
    u64,
    "an opaque offset token -- used to encode iterations over a table (within a generation). These always start at 0."
);

/// The version of a table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableVersion {
    /// New major generations invalidate all existing RowIds for a table.
    pub major: Generation,
    /// New minor generations within a major generation do not invalidate
    /// existing RowIds, but they may indicate that `all` can return a larger
    /// subset than before.
    pub minor: Offset,
    // NB: we may want to make `Offset` and `RowId` the same.
}

#[derive(Clone)]
pub struct TableSpec {
    /// The number of key columns for the table.
    pub n_keys: usize,

    /// The number of non-key (i.e. value) columns in the table.
    ///
    /// The total "arity" of the table is `n_keys + n_vals`.
    pub n_vals: usize,

    /// Columns that cannot be cached across generations.
    ///
    /// These columns should (e.g.) never have indexes built for them, as they
    /// will go out of date too quickly.
    pub uncacheable_columns: DenseIdMap<ColumnId, bool>,

    /// Whether or not deletions are supported for this table.
    ///
    /// Tables where this value is false are allowed to panic on calls to
    /// `stage_remove`.
    pub allows_delete: bool,
}

impl TableSpec {
    /// The total number of columns stored by the table.
    pub fn arity(&self) -> usize {
        self.n_keys + self.n_vals
    }
}

/// A summary of the kinds of changes that a table underwent after a merge operation.
#[derive(Eq, PartialEq, Copy, Clone)]
pub struct TableChange {
    /// Whether or not rows were added to the table.
    pub added: bool,
    /// Whether or not rows were removed from the table.
    pub removed: bool,
}

/// A constraint on the values within a row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    Eq { l_col: ColumnId, r_col: ColumnId },
    EqConst { col: ColumnId, val: Value },
    LtConst { col: ColumnId, val: Value },
    GtConst { col: ColumnId, val: Value },
    LeConst { col: ColumnId, val: Value },
    GeConst { col: ColumnId, val: Value },
}

/// Remap individual values (e.g. to their union-find leaders) — the value-level
/// half of rebuilding, enough to rebuild a single container's contents (see
/// [`crate::ContainerValue::rebuild_contents`]).
pub trait ValueRebuilder: Send + Sync {
    /// Rebuild a single value.
    fn rebuild_val(&self, val: Value) -> Value;
    /// Rebuild a slice of values in place, returning true if any values were changed.
    ///
    /// Defaults to mapping each value through [`ValueRebuilder::rebuild_val`];
    /// implementors may override for efficiency.
    fn rebuild_slice(&self, vals: &mut [Value]) -> bool {
        let mut changed = false;
        for val in vals.iter_mut() {
            let new = self.rebuild_val(*val);
            if new != *val {
                *val = new;
                changed = true;
            }
        }
        changed
    }
}

/// Custom functions used for tables that encode a bulk value-level rebuild of other tables.
///
/// Extends [`ValueRebuilder`] with table-level (bulk) operations.
///
/// The initial use-case for this trait is to support optimized implementations of rebuilding,
/// where `Rebuilder` is implemented as a Union-find.
///
/// Value-level rebuilds are difficult to implement efficiently using rules as they require
/// searching for changes to any column for a table: while it is possible to do, implementing this
/// custom is more efficient in the case of rebuilding.
pub trait Rebuilder: ValueRebuilder {
    /// The column that contains values that should be rebuilt. If this is set, callers can use
    /// this functionality to perform rebuilds incrementally.
    fn hint_col(&self) -> Option<ColumnId>;
    /// Rebuild a contiguous slice of rows in the table.
    fn rebuild_buf(
        &self,
        buf: &RowBuffer,
        start: RowId,
        end: RowId,
        out: &mut TaggedRowBuffer,
        exec_state: &mut ExecutionState,
    );
    /// Rebuild an arbitrary subset of the table.
    fn rebuild_subset(
        &self,
        other: WrappedTableRef,
        subset: SubsetRef,
        out: &mut TaggedRowBuffer,
        exec_state: &mut ExecutionState,
    );
}

/// A row in a table.
pub struct Row {
    /// The id associated with the row.
    pub id: RowId,
    /// The Row itself.
    pub vals: Pooled<Vec<Value>>,
}

/// An interface for a table.
pub trait Table: Any + Send + Sync {
    /// A variant of clone that returns a boxed trait object; this trait object
    /// must contain all of the data associated with the current table.
    fn dyn_clone(&self) -> Box<dyn Table>;

    /// Install the database-local identity used by commit-time receipts.
    fn set_table_id(&mut self, _table: TableId) {}

    /// Mark this table's staging buffers as receipt-enabled. Tables without a
    /// specialized receipt contract may ignore this.
    fn enable_causal_receipts(&mut self) {}

    /// Verify that receipt capture can be enabled without backfilling native
    /// history. Implementations with deferred mutation buffers must also
    /// reject queued or outstanding receipt-disabled buffers here. This pass
    /// is side-effect free and runs for every table before any table changes
    /// mode.
    fn preflight_causal_receipt_activation(&self) -> Result<(), &'static str> {
        if self.len() == 0 {
            Ok(())
        } else {
            Err("table already contains rows without exact source identities")
        }
    }

    /// If this table can perform a table-level rebuild, construct a [`Rebuilder`] for it.
    fn rebuilder<'a>(&'a self, _cols: &[ColumnId]) -> Option<Box<dyn Rebuilder + 'a>> {
        None
    }

    /// Rebuild the table according to the given [`Rebuilder`] implemented by `table`, if
    /// there is one. Applying a rebuild can cause more mutations to be buffered, which can in turn
    /// be flushed by a call to [`Table::merge`].
    ///
    /// Note that value-level rebuilds are only relevant for tables that opt into it. As a result,
    /// tables do nothing by default.
    ///
    /// Returns whether any rows may be removed or inserted.
    fn apply_rebuild(
        &mut self,
        _table_id: TableId,
        _table: &WrappedTable,
        _next_ts: Value,
        _exec_state: &mut ExecutionState,
        _equality_cutoff: Option<EqualityEdgeCount>,
        _transaction: Option<&MutationTransaction>,
    ) -> bool {
        // Default implementation does nothing.
        false
    }

    /// Publish an incremental-rebuild cursor returned through the shared
    /// receipt transaction after every target table validates.
    fn commit_rebuild_cursor(&mut self, _table_id: TableId, _version: TableVersion) {}

    /// Refresh rows whose rebuildable columns mention one of `dirty_ids` by re-inserting the same
    /// logical row with a fresh timestamp.
    ///
    /// This is the narrow escape hatch used when some external rebuild step
    /// changes the semantics of an id in place, so seminaive needs a new
    /// parent-row delta even though the row's key columns do not otherwise
    /// change.
    ///
    /// One source of such ids is [`crate::ContainerRebuildSummary::dirty_ids`].
    ///
    /// Tables that do not maintain rebuildable id columns can use the default
    /// no-op implementation.
    fn refresh_rows_for_values(
        &mut self,
        _summary: &crate::ContainerRebuildSummary,
        _next_ts: Value,
        _exec_state: Option<&ExecutionState>,
        _transaction: Option<&MutationTransaction>,
    ) -> bool {
        false
    }

    /// A boilerplate method to make it easier to downcast values of `Table`.
    ///
    /// Implementors should be able to implement this method by returning
    /// `self`.
    fn as_any(&self) -> &dyn Any;

    /// The schema of the table.
    ///
    /// These are immutable properties of the table; callers can assume they
    /// will never change.
    fn spec(&self) -> TableSpec;

    /// Clear all table contents. If the table is nonempty, this will change the
    /// generation of the table. This method also clears any pending data.
    fn clear(&mut self);

    // Used in queries:

    /// Get a subset corresponding to all rows in the table.
    fn all(&self) -> Subset;

    /// Get the length of the table.
    ///
    /// This is not in general equal to the length of the `all` subset: the size
    /// of a subset is allowed to be larger than the number of table entries in
    /// range of the subset.
    fn len(&self) -> usize;

    /// Check if the table is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the current version for the table. [`RowId`]s and [`Subset`]s are
    /// only valid for a given major generation.
    fn version(&self) -> TableVersion;

    /// Get the subset of the table that has appeared since the last offset.
    fn updates_since(&self, offset: Offset) -> Subset;

    /// Iterate over the given subset of the table, starting at an opaque
    /// `start` token, ending after up to `n` rows, returning the next start
    /// token if more rows remain. Only invoke `f` on rows that match the given
    /// constraints.
    ///
    /// This method is _not_ object safe, but it is used to define various
    /// "default" implementations of object-safe methods like `scan` and
    /// `pivot`.
    fn scan_generic_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        cs: &[Constraint],
        f: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset>
    where
        Self: Sized;

    /// Iterate over the given subset of the table.
    ///
    /// This is a variant of [`Table::scan_generic_bounded`] that iterates over
    /// the entire table.
    fn scan_generic(&self, subset: SubsetRef, mut f: impl FnMut(RowId, &[Value]))
    where
        Self: Sized,
    {
        let mut cur = Offset::new(0);
        while let Some(next) = self.scan_generic_bounded(subset, cur, usize::MAX, &[], |id, row| {
            f(id, row);
        }) {
            cur = next;
        }
    }

    /// Returns true if the table contains any stale rows (rows whose first column
    /// has been set to [`Value::stale()`]). The default implementation returns `true`
    /// (conservative). Tables that track stale-row counts should override this.
    fn has_stale_rows(&self) -> bool {
        true
    }

    /// Filter a given subset of the table for the rows that are live
    fn refine_live(&self, subset: Subset) -> Subset {
        // NB: This relies on Value::stale() being strictly larger than any other value in the table.
        self.refine_one(
            subset,
            &Constraint::LtConst {
                col: ColumnId::new_const(0),
                val: Value::stale(),
            },
        )
    }

    /// Filter a given subset of the table for the rows matching the single constraint.
    ///
    /// Implementors must provide at least one of `refine_one` or `refine`.`
    fn refine_one(&self, subset: Subset, c: &Constraint) -> Subset {
        self.refine(subset, std::slice::from_ref(c))
    }

    /// Filter a given subset of the table for the rows matching the given constraints.
    ///
    /// Implementors must provide at least one of `refine_one` or `refine`.`
    fn refine(&self, subset: Subset, cs: &[Constraint]) -> Subset {
        cs.iter()
            .fold(subset, |subset, c| self.refine_one(subset, c))
    }

    /// An optional method for quickly generating a subset from a constraint.
    /// The standard use-case here is to apply constraints based on a column
    /// that is known to be sorted.
    ///
    /// These constraints are very helpful for query planning; it is a good idea
    /// to implement them.
    fn fast_subset(&self, _: &Constraint) -> Option<Subset> {
        None
    }

    /// A helper routine that leverages the existing `fast_subset` method to
    /// preprocess a set of constraints into "fast" and "slow" ones, returning
    /// the subet of indexes that match the fast one.
    fn split_fast_slow(
        &self,
        cs: &[Constraint],
    ) -> (
        Subset,                  /* the subset of the table matching all fast constraints */
        Pooled<Vec<Constraint>>, /* the fast constraints */
        Pooled<Vec<Constraint>>, /* the slow constraints */
    ) {
        with_pool_set(|ps| {
            let mut fast = ps.get::<Vec<Constraint>>();
            let mut slow = ps.get::<Vec<Constraint>>();
            let mut subset = self.all();
            for c in cs {
                if let Some(sub) = self.fast_subset(c) {
                    subset.intersect(sub.as_ref(), &ps.get_pool());
                    fast.push(c.clone());
                } else {
                    slow.push(c.clone());
                }
            }
            (subset, fast, slow)
        })
    }

    // Used in actions:

    /// Look up a single row by the given key values, if it is in the table.
    ///
    /// The number of values specified by `keys` should match the number of
    /// primary keys for the table.
    fn get_row(&self, key: &[Value]) -> Option<Row>;

    /// Look up the given column of single row by the given key values, if it is
    /// in the table.
    ///
    /// The number of values specified by `keys` should match the number of
    /// primary keys for the table.
    fn get_row_column(&self, key: &[Value], col: ColumnId) -> Option<Value> {
        self.get_row(key).map(|row| row.vals[col.index()])
    }

    /// Return the immutable causal identity associated with a committed row.
    /// Physical compaction may change `row`, but must preserve this identity.
    fn fact_id(&self, _row: RowId) -> Option<FactId> {
        None
    }

    /// Point-read a live committed row by its current physical identifier.
    /// Used only while exact receipt witnesses are enabled.
    fn row_at(&self, _row: RowId) -> Option<Row> {
        None
    }

    /// Merge any updates to the table, and potentially update the generation for
    /// the table.
    fn merge(&mut self, exec_state: &mut ExecutionState) -> TableChange;

    /// Create a new buffer for staging mutations on this table. Mutations staged to a
    /// MutationBuffer that is then dropped may not take effect until the next call to
    /// [`Table::merge`].
    fn new_buffer(&self) -> Box<dyn MutationBuffer>;
}

/// A trait specifying a buffer of pending mutations for a [`Table`].
///
/// Dropping an object implementing this trait should "flush" the pending
/// mutations to the table. Calling  [`Table::merge`] on that table would then
/// apply those mutations, making them visible for future readers.
pub trait MutationBuffer: Any + Send + Sync {
    /// Attach this buffer to one explicit commit/abort decision. Receipt-mode
    /// rebuilds share a token across every row and target table.
    fn defer_until(&mut self, _transaction: MutationTransaction) {
        panic!("this table buffer does not support transactional rebuild staging")
    }

    /// Stage the keyed entries for insertion. Changes may not be visible until
    /// this buffer is dropped, and after `merge` is called on the underlying
    /// table.
    fn stage_insert(&mut self, row: &[Value]);

    /// Stage an insertion with the exact native cause draft already known by
    /// the current execution lane.
    fn stage_insert_with_cause(&mut self, row: &[Value], cause: CauseDraftId);

    /// Stage an insertion together with the coherent structural terms that
    /// produced this exact row. Constructor actions use this when a current
    /// e-class value already has other structural aliases.
    fn stage_insert_with_cause_and_terms(
        &mut self,
        _row: &[Value],
        _cause: CauseDraftId,
        _terms: &[crate::ReplayTermId],
    ) {
        panic!("structural row terms staged into a table without receipt support")
    }

    /// Stage a typed equality proposal. Only the native equality table
    /// implements this receipt-only operation.
    fn stage_typed_union(
        &mut self,
        _row: &[Value],
        _cause: CauseDraftId,
        _proposal: TypedEqualityProposal,
    ) {
        panic!("typed union staged into a non-equality table")
    }

    /// Stage the keyed entries for removal. Changes may not be visible until
    /// this buffer is dropped, and after `merge` is called on the underlying
    /// table.
    fn stage_remove(&mut self, key: &[Value]);

    /// Get a fresh handle to the same table.
    fn fresh_handle(&self) -> Box<dyn MutationBuffer>;
}

struct WrapperImpl<T>(PhantomData<T>);

pub(crate) fn wrapper<T: Table>() -> Box<dyn TableWrapper> {
    Box::new(WrapperImpl::<T>(PhantomData))
}

impl<T: Table> TableWrapper for WrapperImpl<T> {
    fn dyn_clone(&self) -> Box<dyn TableWrapper> {
        Box::new(Self(PhantomData))
    }
    fn scan_bounded(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        table.scan_generic_bounded(subset, start, n, &[], |row_id, row| {
            out.add_row(row_id, row);
        })
    }
    fn group_by_col(&self, table: &dyn Table, subset: SubsetRef, col: ColumnId) -> ColumnIndex {
        let wrapped = WrappedTableRef {
            inner: table,
            wrapper: self,
        };
        ColumnIndex::build_for_subset(wrapped, subset, col)
    }
    fn group_by_key(&self, table: &dyn Table, subset: SubsetRef, cols: &[ColumnId]) -> TupleIndex {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        let mut res = TupleIndex::new(cols.len());
        match cols {
            [] => {}
            [col] => table.scan_generic(subset, |row_id, row| {
                res.add_row(&[row[col.index()]], row_id);
            }),
            [x, y] => table.scan_generic(subset, |row_id, row| {
                res.add_row(&[row[x.index()], row[y.index()]], row_id);
            }),
            [x, y, z] => table.scan_generic(subset, |row_id, row| {
                res.add_row(&[row[x.index()], row[y.index()], row[z.index()]], row_id);
            }),
            _ => {
                let mut scratch = SmallVec::<[Value; 8]>::new();
                table.scan_generic(subset, |row_id, row| {
                    for col in cols {
                        scratch.push(row[col.index()]);
                    }
                    res.add_row(&scratch, row_id);
                    scratch.clear();
                });
            }
        }
        res
    }
    fn for_each_col(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        col: ColumnId,
        f: &mut dyn FnMut(RowId, Value),
    ) {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        let col_idx = col.index();
        table.scan_generic(subset, |row_id, row| {
            f(row_id, row[col_idx]);
        });
    }

    fn scan_project(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut dyn RowSink,
    ) -> Option<Offset> {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        match cols {
            [] => None,
            [col] => table.scan_generic_bounded(subset, start, n, cs, |id, row| {
                out.add_row(id, &[row[col.index()]]);
            }),
            [x, y] => table.scan_generic_bounded(subset, start, n, cs, |id, row| {
                out.add_row(id, &[row[x.index()], row[y.index()]]);
            }),
            [x, y, z] => table.scan_generic_bounded(subset, start, n, cs, |id, row| {
                out.add_row(id, &[row[x.index()], row[y.index()], row[z.index()]]);
            }),
            _ => {
                let mut scratch = SmallVec::<[Value; 8]>::with_capacity(cols.len());
                table.scan_generic_bounded(subset, start, n, cs, |id, row| {
                    for col in cols {
                        scratch.push(row[col.index()]);
                    }
                    out.add_row(id, &scratch);
                    scratch.clear();
                })
            }
        }
    }

    fn lookup_row_vectorized(
        &self,
        table: &dyn Table,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        out_var: Variable,
    ) {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        let mut out = with_pool_set(PoolSet::get::<Vec<Value>>);
        for_each_binding_with_mask!(mask, args, bindings, |iter| {
            iter.fill_vec(&mut out, Value::stale, |_, args| {
                table.get_row_column(args.as_slice(), col)
            })
        });
        bindings.insert(out_var, &out);
    }

    fn lookup_with_default_vectorized(
        &self,
        table: &dyn Table,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        default: QueryEntry,
        out_var: Variable,
    ) {
        let table = table.as_any().downcast_ref::<T>().unwrap();
        let mut out = with_pool_set(|ps| ps.get::<Vec<Value>>());
        for_each_binding_with_mask!(mask, args, bindings, |iter| {
            match default {
                QueryEntry::Var(default) => iter.zip(&bindings[default]).fill_vec(
                    &mut out,
                    Value::stale,
                    |_, (args, default)| {
                        Some(
                            table
                                .get_row_column(args.as_slice(), col)
                                .unwrap_or(*default),
                        )
                    },
                ),
                QueryEntry::Const(default) => iter.fill_vec(&mut out, Value::stale, |_, args| {
                    Some(
                        table
                            .get_row_column(args.as_slice(), col)
                            .unwrap_or(default),
                    )
                }),
            }
        });
        bindings.insert(out_var, &out);
    }
}

/// A WrappedTable takes a Table and extends it with a number of helpful,
/// object-safe methods for accessing a table.
///
/// It essentially acts like an extension trait: it is a separate type to allow
/// object-safe extension methods to call methods that require `Self: Sized`.
/// The implementations here downcast manually to the type used when
/// constructing the WrappedTable.
pub struct WrappedTable {
    inner: Box<dyn Table>,
    wrapper: Box<dyn TableWrapper>,
}

impl WrappedTable {
    pub(crate) fn new<T: Table>(inner: T) -> Self {
        let wrapper = wrapper::<T>();
        let inner = Box::new(inner);
        Self { inner, wrapper }
    }

    /// Clone the contents of the table.
    pub fn dyn_clone(&self) -> Self {
        WrappedTable {
            inner: self.inner.dyn_clone(),
            wrapper: self.wrapper.dyn_clone(),
        }
    }

    pub(crate) fn as_ref(&self) -> WrappedTableRef<'_> {
        WrappedTableRef {
            inner: &*self.inner,
            wrapper: &*self.wrapper,
        }
    }

    /// Starting at the given [`Offset`] into `subset`, scan up to `n` rows and
    /// write them to `out`. Return the next starting offset. If no offset is
    /// returned then the subset has been scanned completely.
    pub fn scan_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        self.as_ref().scan_bounded(subset, start, n, out)
    }

    /// Group the contents of the given subset by the given column.
    pub(crate) fn group_by_col(&self, subset: SubsetRef, col: ColumnId) -> ColumnIndex {
        self.as_ref().group_by_col(subset, col)
    }

    /// A multi-column vairant of [`WrappedTable::group_by_col`].
    pub(crate) fn group_by_key(&self, subset: SubsetRef, cols: &[ColumnId]) -> TupleIndex {
        self.as_ref().group_by_key(subset, cols)
    }

    /// A variant fo [`WrappedTable::scan_bounded`] that projects a subset of
    /// columns and only appends rows that match the given constraints.
    pub fn scan_project(
        &self,
        subset: SubsetRef,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut dyn RowSink,
    ) -> Option<Offset> {
        self.as_ref().scan_project(subset, cols, start, n, cs, out)
    }

    /// Return the contents of the subset as a [`TaggedRowBuffer`].
    pub fn scan(&self, subset: SubsetRef) -> TaggedRowBuffer {
        self.as_ref().scan(subset)
    }

    /// Return the number of rows currently stored in the table.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if the table is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub(crate) fn lookup_row_vectorized(
        &self,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        out_var: Variable,
    ) {
        self.as_ref()
            .lookup_row_vectorized(mask, bindings, args, col, out_var)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn lookup_with_default_vectorized(
        &self,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        default: QueryEntry,
        out_var: Variable,
    ) {
        self.as_ref()
            .lookup_with_default_vectorized(mask, bindings, args, col, default, out_var)
    }
}

impl Deref for WrappedTable {
    type Target = dyn Table;

    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl DerefMut for WrappedTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.inner
    }
}

pub(crate) trait TableWrapper: Send + Sync {
    fn dyn_clone(&self) -> Box<dyn TableWrapper>;
    fn scan_bounded(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset>;
    fn group_by_col(&self, table: &dyn Table, subset: SubsetRef, col: ColumnId) -> ColumnIndex;
    fn group_by_key(&self, table: &dyn Table, subset: SubsetRef, cols: &[ColumnId]) -> TupleIndex;

    /// Scan each row in `subset`, calling `f(row_id, col_value)` for each.
    /// Unlike `scan_project`, this writes directly to the callback with no
    /// intermediate buffer.
    fn for_each_col(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        col: ColumnId,
        f: &mut dyn FnMut(RowId, Value),
    );

    #[allow(clippy::too_many_arguments)]
    fn scan_project(
        &self,
        table: &dyn Table,
        subset: SubsetRef,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut dyn RowSink,
    ) -> Option<Offset>;

    fn scan(&self, table: &dyn Table, subset: SubsetRef) -> TaggedRowBuffer {
        let arity = table.spec().arity();
        let mut buf = TaggedRowBuffer::new(arity);
        assert!(
            self.scan_bounded(table, subset, Offset::new(0), usize::MAX, &mut buf)
                .is_none()
        );
        buf
    }

    #[allow(clippy::too_many_arguments)]
    fn lookup_row_vectorized(
        &self,
        table: &dyn Table,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        out_var: Variable,
    );

    #[allow(clippy::too_many_arguments)]
    fn lookup_with_default_vectorized(
        &self,
        table: &dyn Table,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        default: QueryEntry,
        out_var: Variable,
    );
}

/// An extra layer of indirection over a [`WrappedTable`] that does not require that the caller
/// actually own the table. This is useful when a table implementation needs to construct a
/// WrappedTable on its own.
#[derive(Clone, Copy)]
pub struct WrappedTableRef<'a> {
    inner: &'a dyn Table,
    wrapper: &'a dyn TableWrapper,
}

impl WrappedTableRef<'_> {
    pub(crate) fn with_wrapper<T: Table, R>(
        inner: &T,
        f: impl for<'a> FnOnce(WrappedTableRef<'a>) -> R,
    ) -> R {
        let wrapper = WrapperImpl::<T>(PhantomData);
        f(WrappedTableRef {
            inner,
            wrapper: &wrapper,
        })
    }

    /// Starting at the given [`Offset`] into `subset`, scan up to `n` rows and
    /// write them to `out`. Return the next starting offset. If no offset is
    /// returned then the subset has been scanned completely.
    pub fn scan_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        out: &mut TaggedRowBuffer,
    ) -> Option<Offset> {
        self.wrapper.scan_bounded(self.inner, subset, start, n, out)
    }

    /// Group the contents of the given subset by the given column.
    pub(crate) fn group_by_col(&self, subset: SubsetRef, col: ColumnId) -> ColumnIndex {
        self.wrapper.group_by_col(self.inner, subset, col)
    }

    /// A multi-column vairant of [`WrappedTable::group_by_col`].
    pub(crate) fn group_by_key(&self, subset: SubsetRef, cols: &[ColumnId]) -> TupleIndex {
        self.wrapper.group_by_key(self.inner, subset, cols)
    }

    /// Scan each row in `subset` and call `f(row_id, col_value)` for each.
    /// This is a zero-copy alternative to `scan_project` for single-column
    /// scans over small subsets where an intermediate buffer is wasteful.
    pub(crate) fn for_each_col(
        &self,
        subset: SubsetRef,
        col: ColumnId,
        f: &mut dyn FnMut(RowId, Value),
    ) {
        self.wrapper.for_each_col(self.inner, subset, col, f);
    }

    /// A variant fo [`WrappedTable::scan_bounded`] that projects a subset of
    /// columns and only appends rows that match the given constraints.
    pub fn scan_project(
        &self,
        subset: SubsetRef,
        cols: &[ColumnId],
        start: Offset,
        n: usize,
        cs: &[Constraint],
        out: &mut dyn RowSink,
    ) -> Option<Offset> {
        self.wrapper
            .scan_project(self.inner, subset, cols, start, n, cs, out)
    }

    /// Return the contents of the subset as a [`TaggedRowBuffer`].
    pub fn scan(&self, subset: SubsetRef) -> TaggedRowBuffer {
        self.wrapper.scan(self.inner, subset)
    }

    /// Return the number of rows currently stored in the table.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub(crate) fn lookup_row_vectorized(
        &self,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        out_var: Variable,
    ) {
        self.wrapper
            .lookup_row_vectorized(self.inner, mask, bindings, args, col, out_var);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn lookup_with_default_vectorized(
        &self,
        mask: &mut Mask,
        bindings: &mut Bindings,
        args: &[QueryEntry],
        col: ColumnId,
        default: QueryEntry,
        out_var: Variable,
    ) {
        self.wrapper.lookup_with_default_vectorized(
            self.inner, mask, bindings, args, col, default, out_var,
        );
    }
}

impl Deref for WrappedTableRef<'_> {
    type Target = dyn Table;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}
