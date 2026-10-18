//! A sparse union-find with immutable, explained root links.
//!
//! Writes `(a, b, reason, timestamp)` assert `a = b`. Reads enumerate successful
//! root links `(loser, winner_at_merge, link_reason, timestamp)`, not current
//! representatives. Use [`ExplainedUfTable::find`] for canonicalization. Keeping
//! the relational projection immutable lets ordinary indexes remain valid.

use std::{
    any::Any,
    sync::{
        Arc, Weak,
        atomic::{AtomicU64, AtomicUsize, Ordering},
    },
};

use crossbeam_queue::SegQueue;
use smallvec::SmallVec;

use crate::{
    ColumnId, Constraint, ExecutionState, MergeOrigin, MutationBuffer, Offset, OffsetRange, Row,
    RowId, Subset, SubsetRef, Table, TableChange, TableSchema, TableSpec, TableVersion, Value,
    numeric_id::NumericId, pool::with_pool_set, table_spec::Generation,
};

// Identities are allocated only for table creation and successful unions. They
// let cursors detect rollback followed by a different history of the same length.
static NEXT_IDENTITY: AtomicUsize = AtomicUsize::new(1);
fn fresh_identity() -> usize {
    NEXT_IDENTITY.fetch_add(1, Ordering::Relaxed)
}

/// One oriented equality in a composable explanation path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReasonStep {
    pub reason: Value,
    pub reversed: bool,
}

/// The embedding's equality algebra. The table knows no proof constructors.
///
/// This prepares a root-link witness during merge, before publishing the link.
/// It may stage writes to declared proof dependencies, but must not query or
/// mutate this UF through `ExecutionState` while that table is being merged.
pub trait ReasonComposer: Send + Sync {
    fn compose(&self, steps: &[ReasonStep], state: &mut ExecutionState) -> Value;
}

/// An accepted union and its immutable explanation. Rejected/redundant
/// assertions do not allocate records or advance subscription cursors.
#[derive(Clone, Debug)]
pub struct EqualityMerged {
    identity: usize,
    pub origin: Option<MergeOrigin>,
    pub lhs: Value,
    pub rhs: Value,
    pub lhs_root: Value,
    pub rhs_root: Value,
    pub loser: Value,
    pub winner: Value,
    pub asserted_reason: Value,
    pub link_reason: Value,
    pub timestamp: Value,
}

/// A subscription position scoped to one UF table. `clear` invalidates it.
/// Obtain a new cursor only after successfully consuming a batch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EqualityCursor {
    source: usize,
    last_event: Option<usize>,
    generation: Generation,
    offset: usize,
}

mod node_index;
use node_index::NodeIndex;

/// A native table for an encoded equality sort. Node storage is dense in the
/// values actually seen, rather than in globally allocated egglog IDs.
pub struct ExplainedUfTable {
    identity: usize,
    nodes: NodeIndex,
    canonical: Vec<AtomicU64>,
    max_value: Value,
    values: Vec<Value>,
    parents: Vec<AtomicUsize>,
    links: Vec<Option<RowId>>,
    events: Vec<EqualityMerged>,
    generation: Generation,
    composer: Option<Arc<dyn ReasonComposer>>,
    pending: Arc<SegQueue<AssertionBatch>>,
}

impl Clone for ExplainedUfTable {
    fn clone(&self) -> Self {
        Self {
            identity: self.identity,
            nodes: self.nodes.clone(),
            canonical: self
                .canonical
                .iter()
                .map(|entry| AtomicU64::new(entry.load(Ordering::Relaxed)))
                .collect(),
            max_value: self.max_value,
            values: self.values.clone(),
            parents: self
                .parents
                .iter()
                .map(|parent| AtomicUsize::new(parent.load(Ordering::Relaxed)))
                .collect(),
            links: self.links.clone(),
            events: self.events.clone(),
            generation: self.generation,
            composer: self.composer.clone(),
            pending: Arc::default(),
        }
    }
}

impl ExplainedUfTable {
    pub fn new(composer: Option<Arc<dyn ReasonComposer>>) -> Self {
        Self {
            identity: fresh_identity(),
            nodes: NodeIndex::default(),
            canonical: Vec::new(),
            max_value: Value::new(0),
            values: Vec::new(),
            parents: Vec::new(),
            links: Vec::new(),
            events: Vec::new(),
            generation: Generation::new(0),
            composer,
            pending: Arc::default(),
        }
    }

    #[inline]
    pub fn find(&self, value: Value) -> Value {
        // Fresh IDs are usually larger than any endpoint ever unioned in this
        // sort. They are roots without even probing the sparse node map.
        if value > self.max_value {
            return value;
        }
        let Some(node) = self.nodes.get(value) else {
            return value;
        };
        // Fewer than 2^32 successful unions are possible in the u32 Value
        // domain. Union requires exclusive access, so this epoch is frozen
        // throughout parallel reads; any new union invalidates all old memos.
        let epoch = self.events.len() as u64;
        let cached = self.canonical[node].load(Ordering::Relaxed);
        if cached >> 32 == epoch {
            return Value::new(cached as u32);
        }
        let root = self.values[self.root(node)];
        self.canonical[node].store((epoch << 32) | u64::from(root.rep()), Ordering::Relaxed);
        root
    }

    pub fn has_reasons(&self) -> bool {
        self.composer.is_some()
    }

    pub fn cursor(&self) -> EqualityCursor {
        EqualityCursor {
            source: self.identity,
            last_event: self.events.last().map(|event| event.identity),
            generation: self.generation,
            offset: self.events.len(),
        }
    }

    pub fn start_cursor(&self) -> EqualityCursor {
        EqualityCursor {
            source: self.identity,
            last_event: None,
            generation: self.generation,
            offset: 0,
        }
    }

    /// Read a committed batch. `None` means this cursor was invalidated by a
    /// clear, or is ahead of this snapshot. Reading does not acknowledge it.
    pub fn events_since(&self, cursor: EqualityCursor) -> Option<&[EqualityMerged]> {
        (cursor.source == self.identity
            && cursor.generation == self.generation
            && cursor.last_event
                == cursor
                    .offset
                    .checked_sub(1)
                    .and_then(|i| self.events.get(i))
                    .map(|event| event.identity))
        .then(|| self.events.get(cursor.offset..))
        .flatten()
    }

    /// Explain an immutable ancestor path, including paths to former roots.
    /// Compression changes `parents`, never these historical links.
    pub fn explain_to(&self, value: Value, ancestor: Value) -> Option<Vec<ReasonStep>> {
        self.explanation_path(value, ancestor)
            .map(SmallVec::into_vec)
    }

    // Most paths are a single accepted root link. Keep short paths on the
    // stack in the hot canonicalization/union paths, preserving the public Vec
    // API for callers that retain a historical explanation.
    fn explanation_path(
        &self,
        mut value: Value,
        ancestor: Value,
    ) -> Option<SmallVec<[ReasonStep; 4]>> {
        let mut path = SmallVec::new();
        while value != ancestor {
            let node = self.nodes.get(value)?;
            let event = &self.events[self.links[node]?.index()];
            path.push(ReasonStep {
                reason: event.link_reason,
                reversed: false,
            });
            value = event.winner;
        }
        Some(path)
    }

    /// Compose a non-reflexive path to the current representative. No proof
    /// writes occur for roots, or in a table without a reason algebra.
    pub fn canonical_reason(&self, value: Value, state: &mut ExecutionState) -> Option<Value> {
        self.find_with_reason(value, state).1
    }

    /// Canonicalize and obtain its witness with a single representative lookup.
    /// The witness is absent for roots and when proof generation is disabled.
    pub fn find_with_reason(
        &self,
        value: Value,
        state: &mut ExecutionState,
    ) -> (Value, Option<Value>) {
        let root = self.find(value);
        if root == value {
            return (root, None);
        }
        let Some(composer) = self.composer.as_ref() else {
            return (root, None);
        };
        let path = self
            .explanation_path(value, root)
            .expect("UF explanation path missing");
        let reason = if path.len() == 1 {
            path[0].reason
        } else {
            composer.compose(&path, state)
        };
        (root, Some(reason))
    }

    fn node(&mut self, value: Value) -> usize {
        if let Some(node) = self.nodes.get(value) {
            return node;
        }
        let node = self.values.len();
        self.max_value = self.max_value.max(value);
        self.nodes.insert(value, node);
        self.canonical.push(AtomicU64::new(u64::MAX));
        self.values.push(value);
        self.parents.push(AtomicUsize::new(node));
        self.links.push(None);
        node
    }

    fn root(&self, node: usize) -> usize {
        let mut root = node;
        loop {
            let parent = self.parents[root].load(Ordering::Relaxed);
            if parent == root {
                break;
            }
            root = parent;
        }
        self.compress(node, root);
        root
    }

    fn compress(&self, mut node: usize, root: usize) {
        // Reads only overlap other reads: union/clear require exclusive table
        // access. Relaxed stores therefore shorten paths within one frozen
        // forest, with no payload publication or concurrent root changes.
        // Historical explanation links are never touched.
        loop {
            let parent = self.parents[node].load(Ordering::Relaxed);
            if parent == node || parent == root {
                break;
            }
            self.parents[node].store(root, Ordering::Relaxed);
            node = parent;
        }
    }

    fn insert(&mut self, row: [Value; 4], origin: Option<MergeOrigin>, state: &mut ExecutionState) {
        let [lhs, rhs, asserted_reason, timestamp] = row;
        if lhs == rhs {
            return;
        }
        let a = self.node(lhs);
        let b = self.node(rhs);
        let ra = self.root(a);
        let rb = self.root(b);
        if ra == rb {
            return;
        }
        let lhs_root = self.values[ra];
        let rhs_root = self.values[rb];
        let (winner_node, loser_node) = if lhs_root < rhs_root {
            (ra, rb)
        } else {
            (rb, ra)
        };
        let winner = self.values[winner_node];
        let loser = self.values[loser_node];
        let link_reason = if let Some(composer) = &self.composer {
            let mut path = self.explanation_path(lhs, lhs_root).unwrap();
            reverse(&mut path);
            path.push(ReasonStep {
                reason: asserted_reason,
                reversed: false,
            });
            path.extend(self.explanation_path(rhs, rhs_root).unwrap());
            if loser != lhs_root {
                reverse(&mut path);
            }
            composer.compose(&path, state)
        } else {
            asserted_reason
        };
        // Publish only after the explanation has been prepared from old paths.
        let row_id = RowId::from_usize(self.events.len());
        self.events.push(EqualityMerged {
            identity: fresh_identity(),
            origin,
            lhs,
            rhs,
            lhs_root,
            rhs_root,
            loser,
            winner,
            asserted_reason,
            link_reason,
            timestamp,
        });
        self.links[loser_node] = Some(row_id);
        self.parents[loser_node].store(winner_node, Ordering::Relaxed);
        self.compress(a, winner_node);
        self.compress(b, winner_node);
    }

    fn row(&self, id: RowId) -> [Value; 4] {
        let event = &self.events[id.index()];
        [
            event.loser,
            event.winner,
            event.link_reason,
            event.timestamp,
        ]
    }
}

fn reverse(path: &mut [ReasonStep]) {
    path.reverse();
    for step in path {
        step.reversed = !step.reversed;
    }
}

impl Table for ExplainedUfTable {
    fn dyn_clone(&self) -> Box<dyn Table> {
        Box::new(self.clone())
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn spec(&self) -> TableSpec {
        TableSpec {
            schema: TableSchema::Fd {
                n_keys: 1,
                n_vals: 3,
            },
            uncacheable_columns: Default::default(),
            allows_delete: false,
        }
    }
    fn clear(&mut self) {
        let generation = Generation::from_usize(self.generation.index() + 1);
        *self = Self::new(self.composer.clone());
        self.generation = generation;
    }
    fn all(&self) -> Subset {
        Subset::Dense(OffsetRange::new(
            RowId::new(0),
            RowId::from_usize(self.events.len()),
        ))
    }
    fn len(&self) -> usize {
        self.events.len()
    }
    fn has_stale_rows(&self) -> bool {
        false
    }
    fn version(&self) -> TableVersion {
        TableVersion {
            major: self.generation,
            minor: Offset::from_usize(self.events.len()),
        }
    }
    fn updates_since(&self, offset: Offset) -> Subset {
        Subset::Dense(OffsetRange::new(
            RowId::from_usize(offset.index()),
            RowId::from_usize(self.events.len()),
        ))
    }
    fn scan_generic_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        cs: &[Constraint],
        mut f: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset> {
        subset
            .iter_bounded(start.index(), start.index().saturating_add(n), |id| {
                let row = self.row(id);
                if cs.iter().all(|c| crate::uf::eval_constraint(&row, c)) {
                    f(id, &row);
                }
            })
            .map(Offset::from_usize)
    }
    fn refine_one(&self, mut subset: Subset, c: &Constraint) -> Subset {
        subset.retain(|id| crate::uf::eval_constraint(&self.row(id), c));
        subset
    }
    fn fast_subset(&self, c: &Constraint) -> Option<Subset> {
        let range = |start: usize, end: usize| {
            Subset::Dense(OffsetRange::new(
                RowId::from_usize(start),
                RowId::from_usize(end),
            ))
        };
        let timestamp_bounds = |value| {
            (
                self.events.partition_point(|e| e.timestamp < value),
                self.events.partition_point(|e| e.timestamp <= value),
            )
        };
        let ts = ColumnId::new(3);
        match c {
            Constraint::EqConst { col, val } if *col == ts => {
                let (lo, hi) = timestamp_bounds(*val);
                return Some(range(lo, hi));
            }
            Constraint::LtConst { col, val } if *col == ts => {
                return Some(range(0, timestamp_bounds(*val).0));
            }
            Constraint::LeConst { col, val } if *col == ts => {
                return Some(range(0, timestamp_bounds(*val).1));
            }
            Constraint::GtConst { col, val } if *col == ts => {
                return Some(range(timestamp_bounds(*val).1, self.len()));
            }
            Constraint::GeConst { col, val } if *col == ts => {
                return Some(range(timestamp_bounds(*val).0, self.len()));
            }
            _ => {}
        }
        if let Constraint::EqConst { col, val } = c
            && *col == ColumnId::new(0)
        {
            let id = self.nodes.get(*val).and_then(|node| self.links[node]);
            return Some(id.map_or_else(Subset::empty, |id| {
                Subset::Dense(OffsetRange::new(id, RowId::from_usize(id.index() + 1)))
            }));
        }
        None
    }
    fn get_row(&self, key: &[Value]) -> Option<Row> {
        assert_eq!(key.len(), 1);
        let id = self.links[self.nodes.get(key[0])?]?;
        let mut vals = with_pool_set(|ps| ps.get::<Vec<Value>>());
        vals.extend(self.row(id));
        Some(Row { id, vals })
    }
    fn new_buffer(&self) -> Box<dyn MutationBuffer> {
        Box::new(UfBuffer {
            origin: None,
            rows: Vec::new(),
            pending: Arc::downgrade(&self.pending),
        })
    }
    fn merge(&mut self, state: &mut ExecutionState) -> TableChange {
        let before = self.events.len();
        let mut rows = Vec::new();
        while let Some(batch) = self.pending.pop() {
            rows.extend(batch.rows.into_iter().map(|row| (row, batch.origin)));
        }
        if !rows.is_sorted_by_key(|(row, _)| row[3]) {
            rows.sort_by_key(|(row, _)| row[3]);
        }
        for (row, origin) in rows {
            assert!(
                self.events.last().is_none_or(|e| e.timestamp <= row[3]),
                "UF timestamps must increase"
            );
            self.insert(row, origin, state);
        }
        TableChange {
            added: self.events.len() != before,
            removed: false,
        }
    }
}

struct AssertionBatch {
    rows: Vec<[Value; 4]>,
    origin: Option<MergeOrigin>,
}

struct UfBuffer {
    origin: Option<MergeOrigin>,
    rows: Vec<[Value; 4]>,
    pending: Weak<SegQueue<AssertionBatch>>,
}

impl MutationBuffer for UfBuffer {
    fn set_merge_origin(&mut self, origin: MergeOrigin) {
        assert!(self.rows.is_empty(), "origin must be set before writing");
        self.origin = Some(origin);
    }
    fn stage_insert(&mut self, row: &[Value]) {
        self.rows
            .push(row.try_into().expect("UF assertions have four columns"));
    }
    fn stage_remove(&mut self, _: &[Value]) {
        panic!("UF assertions cannot be removed");
    }
    fn fresh_handle(&self) -> Box<dyn MutationBuffer> {
        Box::new(Self {
            origin: self.origin,
            rows: Vec::new(),
            pending: self.pending.clone(),
        })
    }
}

impl Drop for UfBuffer {
    fn drop(&mut self) {
        if !self.rows.is_empty()
            && let Some(pending) = self.pending.upgrade()
        {
            pending.push(AssertionBatch {
                rows: std::mem::take(&mut self.rows),
                origin: self.origin,
            });
        }
    }
}

#[cfg(test)]
mod tests;
