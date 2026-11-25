//! Function storage owned by the replacement runtime.

use std::{
    any::Any,
    collections::BTreeMap,
    sync::{Arc, Mutex, Weak},
};

use crate::columns::{GpuOps, Matrix};
use egglog_core_relations::{
    BackendTable, Constraint, ExecutionState, Generation, MergeFn, MutationBuffer, Offset,
    OffsetRange, Pooled, Row, RowId, Subset, SubsetRef, Table, TableChange, TableSchema, TableSpec,
    TableVersion, Value,
};
use egglog_numeric_id::NumericId;

pub(crate) fn matches(row: &[Value], c: &Constraint) -> bool {
    match *c {
        Constraint::Eq { l_col, r_col } => row[l_col.index()] == row[r_col.index()],
        Constraint::EqConst { col, val } => row[col.index()] == val,
        Constraint::LtConst { col, val } => row[col.index()] < val,
        Constraint::LeConst { col, val } => row[col.index()] <= val,
        Constraint::GtConst { col, val } => row[col.index()] > val,
        Constraint::GeConst { col, val } => row[col.index()] >= val,
    }
}

enum Mutation {
    Insert(Vec<Value>),
    Remove(Vec<Value>),
    Device(Matrix, bool),
}
type Pending = Mutex<Vec<Mutation>>;

pub(crate) struct Buffer {
    pending: Weak<Pending>,
    changes: Vec<Mutation>,
    arity: usize,
    keys: Option<usize>,
    read_only: bool,
}

impl Buffer {
    pub(crate) fn stage_device(&mut self, rows: Matrix, remove: bool) {
        assert!(
            !self.read_only,
            "native unions are unavailable; use term encoding"
        );
        assert_eq!(
            rows.cols,
            if remove {
                self.keys.unwrap()
            } else {
                self.arity
            }
        );
        if rows.rows > 0 {
            self.changes.push(Mutation::Device(rows, remove));
        }
    }
}

impl MutationBuffer for Buffer {
    fn stage_insert(&mut self, row: &[Value]) {
        assert!(
            !self.read_only,
            "native unions are unavailable; use term encoding"
        );
        assert_eq!(row.len(), self.arity);
        assert!(row.iter().all(|v| v.rep() != u32::MAX));
        self.changes.push(Mutation::Insert(row.to_vec()));
    }
    fn stage_remove(&mut self, key: &[Value]) {
        assert!(
            !self.read_only,
            "native unions are unavailable; use term encoding"
        );
        assert_eq!(Some(key.len()), self.keys);
        self.changes.push(Mutation::Remove(key.to_vec()));
    }
    fn fresh_handle(&self) -> Box<dyn MutationBuffer> {
        Box::new(Self {
            pending: self.pending.clone(),
            changes: Vec::new(),
            arity: self.arity,
            keys: self.keys,
            read_only: self.read_only,
        })
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        if let Some(pending) = self.pending.upgrade() {
            pending.lock().unwrap().append(&mut self.changes);
        }
    }
}

/// Rows keep their ids within a generation. Compaction advances the generation
/// to invalidate host ABI indexes; source term ids and timestamps never change.
pub(crate) struct Store {
    pub(crate) error: Option<String>,
    device: Option<Arc<GpuOps>>,
    pub(crate) resident: Option<(Matrix, wgpu::Buffer)>,
    read_only: bool,
    schema: TableSchema,
    merge: Option<Arc<MergeFn>>,
    generation: Generation,
    pub(crate) rows: Vec<Vec<Value>>,
    pub(crate) live: Vec<bool>,
    index: BTreeMap<Vec<Value>, usize>,
    pending: Arc<Pending>,
}

impl Store {
    pub(crate) fn new(def: BackendTable, device: Option<Arc<GpuOps>>) -> Self {
        let mut store = Self {
            error: None,
            device,
            resident: None,
            read_only: def.read_only,
            schema: def.schema,
            merge: def.merge.map(Arc::from),
            generation: Generation::new(0),
            rows: Vec::new(),
            live: Vec::new(),
            index: BTreeMap::new(),
            pending: Arc::new(Mutex::new(Vec::new())),
        };
        store.sync_device();
        store
    }
    fn sync_device(&mut self) {
        if self.error.is_none()
            && let Some(device) = &self.device
        {
            match device
                .upload(&self.rows, self.schema.arity())
                .and_then(|matrix| Ok((matrix, device.live(&self.live)?)))
            {
                Ok(resident) => self.resident = Some(resident),
                Err(error) => {
                    self.resident = None;
                    self.error = Some(error);
                }
            }
        }
    }
    fn compact(&mut self) {
        if self.live.iter().all(|&live| live) {
            return;
        }
        let mut live = self.live.iter();
        self.rows.retain(|_| *live.next().unwrap());
        self.live = vec![true; self.rows.len()];
        self.index.clear();
        if let Some(keys) = self.keys() {
            self.index.extend(
                self.rows
                    .iter()
                    .enumerate()
                    .map(|(id, row)| (row[..keys].to_vec(), id)),
            );
        }
        self.generation = self.generation.inc();
    }
    pub(crate) fn current(&self) -> Matrix {
        // Commit compacts retired rows before uploading. Filtering and sorting
        // this already-live snapshot again adds work and loses cached indexes.
        self.resident.as_ref().expect("resident storage").0.clone()
    }
    pub(crate) fn keys(&self) -> Option<usize> {
        match self.schema {
            TableSchema::Fd { n_keys, .. } => Some(n_keys),
            TableSchema::Flat { .. } => None,
        }
    }
}

impl Clone for Store {
    fn clone(&self) -> Self {
        Self {
            error: self.error.clone(),
            device: self.device.clone(),
            resident: self.resident.clone(),
            read_only: self.read_only,
            schema: self.schema,
            merge: self.merge.clone(),
            generation: self.generation,
            rows: self.rows.clone(),
            live: self.live.clone(),
            index: self.index.clone(),
            pending: Arc::new(Mutex::new(Vec::new())),
        }
    }
}

impl Table for Store {
    fn dyn_clone(&self) -> Box<dyn Table> {
        Box::new(self.clone())
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn spec(&self) -> TableSpec {
        TableSpec {
            schema: self.schema,
            uncacheable_columns: Default::default(),
        }
    }
    fn clear(&mut self) {
        self.pending = Arc::new(Mutex::new(Vec::new()));
        self.rows.clear();
        self.live.clear();
        self.index.clear();
        self.generation = self.generation.inc();
        self.sync_device();
    }
    fn all(&self) -> Subset {
        Subset::Dense(OffsetRange::new(
            RowId::new(0),
            RowId::from_usize(self.rows.len()),
        ))
    }
    fn len(&self) -> usize {
        self.live.iter().filter(|&&x| x).count()
    }
    fn version(&self) -> TableVersion {
        TableVersion {
            major: self.generation,
            minor: Offset::from_usize(self.rows.len()),
        }
    }
    fn updates_since(&self, offset: Offset) -> Subset {
        Subset::Dense(OffsetRange::new(
            RowId::from_usize(offset.index()),
            RowId::from_usize(self.rows.len()),
        ))
    }
    fn has_stale_rows(&self) -> bool {
        self.live.iter().any(|&x| !x)
    }
    fn refine_live(&self, mut subset: Subset) -> Subset {
        subset.retain(|id| self.live[id.index()]);
        subset
    }
    fn scan_generic_bounded(
        &self,
        subset: SubsetRef,
        start: Offset,
        n: usize,
        constraints: &[Constraint],
        mut emit: impl FnMut(RowId, &[Value]),
    ) -> Option<Offset> {
        subset
            .iter_bounded(start.index(), start.index().saturating_add(n), |id| {
                if self.live[id.index()]
                    && constraints
                        .iter()
                        .all(|c| matches(&self.rows[id.index()], c))
                {
                    emit(id, &self.rows[id.index()]);
                }
            })
            .map(Offset::from_usize)
    }
    fn refine_one(&self, mut subset: Subset, c: &Constraint) -> Subset {
        subset.retain(|id| self.live[id.index()] && matches(&self.rows[id.index()], c));
        subset
    }
    fn get_row(&self, key: &[Value]) -> Option<Row> {
        assert_eq!(Some(key.len()), self.keys());
        let &id = self.index.get(key)?;
        let mut vals: Pooled<Vec<Value>> = Pooled::default();
        vals.extend_from_slice(&self.rows[id]);
        Some(Row {
            id: RowId::from_usize(id),
            vals,
        })
    }
    fn new_buffer(&self) -> Box<dyn MutationBuffer> {
        Box::new(Buffer {
            pending: Arc::downgrade(&self.pending),
            changes: Vec::new(),
            arity: self.schema.arity(),
            keys: self.keys(),
            read_only: self.read_only,
        })
    }
    fn merge(&mut self, state: &mut ExecutionState) -> TableChange {
        let changes = std::mem::take(&mut *self.pending.lock().unwrap());
        if changes.is_empty() {
            return TableChange { added: false };
        }
        let mut materialized = Vec::new();
        for change in changes {
            match change {
                Mutation::Device(rows, remove) => {
                    match self.device.as_ref().unwrap().download(&rows) {
                        Ok(rows) => materialized.extend(rows.into_iter().map(|row| {
                            if remove {
                                Mutation::Remove(row)
                            } else {
                                Mutation::Insert(row)
                            }
                        })),
                        Err(error) => {
                            self.error = Some(error);
                            return TableChange { added: false };
                        }
                    }
                }
                change => materialized.push(change),
            }
        }
        let changes = materialized;
        // A run reads a committed snapshot: removals precede its staged writes.
        let mut changed = false;
        for change in &changes {
            if let Mutation::Remove(key) = change
                && let Some(id) = self.index.remove(key)
            {
                self.live[id] = false;
                changed = true;
            }
        }
        let mut added = false;
        for change in changes {
            let Mutation::Insert(mut row) = change else {
                continue;
            };
            let key = self.keys().map(|n| row[..n].to_vec());
            if let Some(key) = &key
                && let Some(&id) = self.index.get(key)
            {
                let mut merged = Vec::new();
                if !(self.merge.as_ref().expect("FD merge"))(
                    state,
                    &self.rows[id],
                    &row,
                    &mut merged,
                ) {
                    continue;
                }
                assert_eq!(merged.len(), self.schema.arity());
                assert_eq!(&merged[..key.len()], key);
                self.live[id] = false;
                row = merged;
            }
            if let Some(key) = key {
                self.index.insert(key, self.rows.len());
            }
            self.rows.push(row);
            self.live.push(true);
            added = true;
            changed = true;
        }
        if changed {
            self.compact();
            self.sync_device();
        }
        TableChange { added }
    }
}
