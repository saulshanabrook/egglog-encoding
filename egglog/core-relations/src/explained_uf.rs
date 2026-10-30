//! A sparse union-find with immutable, explained root links.
//!
//! Writes `(a, b, reason, timestamp)` assert `a = b`. Reads enumerate successful
//! root links `(loser, winner_at_merge, link_reason, timestamp)`, not current
//! representatives. Use [`ExplainedUfTable::find`] for canonicalization. Keeping
//! the relational projection immutable lets ordinary indexes remain valid.

use std::{
    any::Any,
    sync::{Arc, Weak},
};

use crossbeam_queue::SegQueue;

use crate::{
    ColumnId, Constraint, ExecutionState, MutationBuffer, Offset, OffsetRange, Row, RowId, Subset,
    SubsetRef, Table, TableChange, TableSchema, TableSpec, TableVersion, Value, common::HashMap,
    numeric_id::NumericId, pool::with_pool_set, table_spec::Generation,
};

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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EqualityCursor {
    generation: Generation,
    offset: usize,
}

/// A native table for an encoded equality sort. Node storage is dense in the
/// values actually seen, rather than in globally allocated egglog IDs.
pub struct ExplainedUfTable {
    nodes: HashMap<Value, usize>,
    values: Vec<Value>,
    parents: Vec<usize>,
    links: Vec<Option<RowId>>,
    events: Vec<EqualityMerged>,
    generation: Generation,
    composer: Option<Arc<dyn ReasonComposer>>,
    pending: Arc<SegQueue<Vec<[Value; 4]>>>,
}

impl Clone for ExplainedUfTable {
    fn clone(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            values: self.values.clone(),
            parents: self.parents.clone(),
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
            nodes: HashMap::default(),
            values: Vec::new(),
            parents: Vec::new(),
            links: Vec::new(),
            events: Vec::new(),
            generation: Generation::new(0),
            composer,
            pending: Arc::default(),
        }
    }

    pub fn find(&self, value: Value) -> Value {
        let Some(&node) = self.nodes.get(&value) else {
            return value;
        };
        self.values[self.root(node)]
    }

    pub fn has_reasons(&self) -> bool {
        self.composer.is_some()
    }

    pub fn cursor(&self) -> EqualityCursor {
        EqualityCursor {
            generation: self.generation,
            offset: self.events.len(),
        }
    }

    pub fn start_cursor(&self) -> EqualityCursor {
        EqualityCursor {
            generation: self.generation,
            offset: 0,
        }
    }

    /// Read a committed batch. `None` means this cursor was invalidated by a
    /// clear, or is ahead of this snapshot. Reading does not acknowledge it.
    pub fn events_since(&self, cursor: EqualityCursor) -> Option<&[EqualityMerged]> {
        (cursor.generation == self.generation)
            .then(|| self.events.get(cursor.offset..))
            .flatten()
    }

    /// Explain an immutable ancestor path, including paths to former roots.
    /// Compression changes `parents`, never these historical links.
    pub fn explain_to(&self, mut value: Value, ancestor: Value) -> Option<Vec<ReasonStep>> {
        let mut path = Vec::new();
        while value != ancestor {
            let node = *self.nodes.get(&value)?;
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
        let composer = self.composer.as_ref()?;
        let root = self.find(value);
        if root == value {
            return None;
        }
        let path = self
            .explain_to(value, root)
            .expect("UF explanation path missing");
        Some(composer.compose(&path, state))
    }

    fn node(&mut self, value: Value) -> usize {
        if let Some(&node) = self.nodes.get(&value) {
            return node;
        }
        let node = self.values.len();
        self.nodes.insert(value, node);
        self.values.push(value);
        self.parents.push(node);
        self.links.push(None);
        node
    }

    fn root(&self, mut node: usize) -> usize {
        while self.parents[node] != node {
            node = self.parents[node];
        }
        node
    }

    fn compress(&mut self, mut node: usize, root: usize) {
        while self.parents[node] != node {
            let parent = self.parents[node];
            self.parents[node] = root;
            node = parent;
        }
    }

    fn insert(&mut self, row: [Value; 4], state: &mut ExecutionState) {
        let [lhs, rhs, asserted_reason, timestamp] = row;
        let a = self.node(lhs);
        let b = self.node(rhs);
        let ra = self.root(a);
        let rb = self.root(b);
        self.compress(a, ra);
        self.compress(b, rb);
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
            let mut path = self.explain_to(lhs, lhs_root).unwrap();
            reverse(&mut path);
            path.push(ReasonStep {
                reason: asserted_reason,
                reversed: false,
            });
            path.extend(self.explain_to(rhs, rhs_root).unwrap());
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
        self.parents[loser_node] = winner_node;
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
            let id = self.nodes.get(val).and_then(|&node| self.links[node]);
            return Some(id.map_or_else(Subset::empty, |id| {
                Subset::Dense(OffsetRange::new(id, RowId::from_usize(id.index() + 1)))
            }));
        }
        None
    }
    fn get_row(&self, key: &[Value]) -> Option<Row> {
        assert_eq!(key.len(), 1);
        let id = self.links[*self.nodes.get(&key[0])?]?;
        let mut vals = with_pool_set(|ps| ps.get::<Vec<Value>>());
        vals.extend(self.row(id));
        Some(Row { id, vals })
    }
    fn new_buffer(&self) -> Box<dyn MutationBuffer> {
        Box::new(UfBuffer {
            rows: Vec::new(),
            pending: Arc::downgrade(&self.pending),
        })
    }
    fn merge(&mut self, state: &mut ExecutionState) -> TableChange {
        let before = self.events.len();
        let mut rows = Vec::new();
        while let Some(batch) = self.pending.pop() {
            rows.extend(batch);
        }
        if !rows.is_sorted_by_key(|row| row[3]) {
            rows.sort_by_key(|row| row[3]);
        }
        for row in rows {
            assert!(
                self.events.last().is_none_or(|e| e.timestamp <= row[3]),
                "UF timestamps must increase"
            );
            self.insert(row, state);
        }
        TableChange {
            added: self.events.len() != before,
            removed: false,
        }
    }
}

struct UfBuffer {
    rows: Vec<[Value; 4]>,
    pending: Weak<SegQueue<Vec<[Value; 4]>>>,
}

impl MutationBuffer for UfBuffer {
    fn stage_insert(&mut self, row: &[Value]) {
        self.rows
            .push(row.try_into().expect("UF assertions have four columns"));
    }
    fn stage_remove(&mut self, _: &[Value]) {
        panic!("UF assertions cannot be removed");
    }
    fn fresh_handle(&self) -> Box<dyn MutationBuffer> {
        Box::new(Self {
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
            pending.push(std::mem::take(&mut self.rows));
        }
    }
}

#[cfg(test)]
mod tests;
