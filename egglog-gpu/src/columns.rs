//! Device-resident relational operators. Only cardinalities cross the host
//! boundary between operators; payload readback is explicit for host extensions.

use crate::DeviceJoin;
#[cfg(test)]
mod tests;
use egglog_core_relations::{Constraint, Value};
use egglog_numeric_id::NumericId;
use std::{
    collections::BTreeMap,
    sync::{
        Arc, Mutex,
        atomic::{AtomicUsize, Ordering},
    },
};

#[derive(Clone)]
pub(crate) struct Matrix {
    pub data: wgpu::Buffer,
    pub rows: usize,
    pub cols: usize,
    // A matrix is immutable after its producing commands. Clones share indexes,
    // while every new table version or operator result starts with none.
    orders: Arc<Mutex<BTreeMap<Vec<usize>, wgpu::Buffer>>>,
}

/// Counted join whose payload has not been allocated. Candidate plans can be
/// compared even when a discarded intermediate would exceed the row limit.
pub(crate) struct JoinPlan {
    left: Matrix,
    right: Matrix,
    config: wgpu::Buffer,
    prefix: wgpu::Buffer,
    extra: usize,
    pub rows: usize,
}

#[derive(Default)]
struct Commands {
    encoder: Option<wgpu::CommandEncoder>,
    operations: usize,
}

/// The action shader's (kind, payload) operand encoding.
pub(crate) type DeviceEntry = (u32, u32);
type Rows = Vec<Vec<Value>>;

pub(crate) struct GpuOps {
    dev: Arc<DeviceJoin>,
    layout: wgpu::BindGroupLayout,
    pipelines: Mutex<BTreeMap<&'static str, wgpu::ComputePipeline>>,
    shader: wgpu::ShaderModule,
    pipeline_layout: wgpu::PipelineLayout,
    max_rows: usize,
    commands: Mutex<Commands>,
    dummy: [wgpu::Buffer; 3],
    scalar_staging: Mutex<wgpu::Buffer>,
    pub dispatches: AtomicUsize,
    pub submissions: AtomicUsize,
    pub readbacks: AtomicUsize,
    pub sorts: AtomicUsize,
    pub sort_cache_hits: AtomicUsize,
}

const STORAGE: wgpu::BufferUsages = wgpu::BufferUsages::STORAGE
    .union(wgpu::BufferUsages::COPY_SRC)
    .union(wgpu::BufferUsages::COPY_DST);

impl GpuOps {
    pub fn new(dev: Arc<DeviceJoin>, max_rows: usize) -> Self {
        let shader = dev
            .device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("egglog relational operators"),
                source: wgpu::ShaderSource::Wgsl(include_str!("relational.wgsl").into()),
            });
        let entries: Vec<_> = (0..6)
            .map(|binding| wgpu::BindGroupLayoutEntry {
                binding,
                visibility: wgpu::ShaderStages::COMPUTE,
                ty: wgpu::BindingType::Buffer {
                    ty: if binding == 5 {
                        wgpu::BufferBindingType::Uniform
                    } else {
                        wgpu::BufferBindingType::Storage {
                            read_only: binding < 3,
                        }
                    },
                    has_dynamic_offset: false,
                    min_binding_size: None,
                },
                count: None,
            })
            .collect();
        let layout = dev
            .device
            .create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: None,
                entries: &entries,
            });
        let pipeline_layout = dev
            .device
            .create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: None,
                bind_group_layouts: &[&layout],
                push_constant_ranges: &[],
            });
        let dummy = std::array::from_fn(|_| {
            dev.device.create_buffer(&wgpu::BufferDescriptor {
                label: Some("unused relational binding"),
                size: 4,
                usage: STORAGE,
                mapped_at_creation: false,
            })
        });
        let scalar_staging = Mutex::new(dev.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("reusable cardinality readback"),
            size: 4,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        }));
        Self {
            dev,
            layout,
            pipelines: Mutex::new(BTreeMap::new()),
            shader,
            pipeline_layout,
            max_rows,
            commands: Mutex::new(Commands::default()),
            dummy,
            scalar_staging,
            dispatches: AtomicUsize::new(0),
            submissions: AtomicUsize::new(0),
            readbacks: AtomicUsize::new(0),
            sorts: AtomicUsize::new(0),
            sort_cache_hits: AtomicUsize::new(0),
        }
    }
    // Keep dependent GPU passes together until the host needs a result. The cap
    // bounds retained command resources during long stretches without readback.
    fn encode(&self, record: impl FnOnce(&mut wgpu::CommandEncoder)) {
        let mut commands = self.commands.lock().unwrap();
        let encoder = commands
            .encoder
            .get_or_insert_with(|| self.dev.device.create_command_encoder(&Default::default()));
        record(encoder);
        commands.operations += 1;
        if commands.operations >= 256 {
            self.submit(&mut commands);
        }
    }
    fn submit(&self, commands: &mut Commands) {
        if let Some(encoder) = commands.encoder.take() {
            self.dev.queue.submit([encoder.finish()]);
            self.submissions.fetch_add(1, Ordering::Relaxed);
        }
        commands.operations = 0;
    }
    pub fn flush(&self) {
        self.submit(&mut self.commands.lock().unwrap());
    }
    fn allocate(&self, words: usize) -> Result<wgpu::Buffer, String> {
        let bytes = words.max(1).checked_mul(4).ok_or("buffer size overflow")? as u64;
        let limits = self.dev.device.limits();
        if bytes > limits.max_buffer_size || bytes > limits.max_storage_buffer_binding_size as u64 {
            return Err(format!(
                "relational buffer needs {bytes} bytes, exceeding device limits (buffer {}, storage binding {})",
                limits.max_buffer_size, limits.max_storage_buffer_binding_size
            ));
        }
        Ok(self.dev.device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size: bytes,
            usage: STORAGE,
            mapped_at_creation: false,
        }))
    }
    fn words(&self, words: &[u32]) -> Result<wgpu::Buffer, String> {
        self.dev.buffer(words, STORAGE)
    }
    fn matrix(&self, rows: usize, cols: usize) -> Result<Matrix, String> {
        if rows > self.max_rows {
            return Err(format!(
                "relation has {rows} rows, exceeding --max-join-rows={}",
                self.max_rows
            ));
        }
        Ok(Matrix {
            data: self
                .allocate(
                    rows.checked_mul(cols.max(1))
                        .ok_or("matrix size overflow")?,
                )
                .map_err(|error| format!("{error}; {rows} rows x {cols} columns"))?,
            rows,
            cols,
            orders: Arc::new(Mutex::new(BTreeMap::new())),
        })
    }
    pub fn upload(&self, rows: &[Vec<Value>], cols: usize) -> Result<Matrix, String> {
        let matrix = self.matrix(rows.len(), cols)?;
        let data: Vec<u32> = if cols == 0 {
            vec![0; rows.len()]
        } else {
            rows.iter()
                .flat_map(|row| {
                    assert_eq!(row.len(), cols);
                    row.iter().map(|v| v.rep())
                })
                .collect()
        };
        if !data.is_empty() {
            self.dev
                .queue
                .write_buffer(&matrix.data, 0, bytemuck::cast_slice(&data));
        }
        Ok(matrix)
    }
    pub fn concat(&self, left: &Matrix, right: &Matrix) -> Result<Matrix, String> {
        assert_eq!(left.cols, right.cols);
        let result = self.matrix(
            left.rows
                .checked_add(right.rows)
                .ok_or("row count overflow")?,
            left.cols,
        )?;
        self.encode(|encoder| {
            let mut offset = 0;
            for source in [left, right] {
                let bytes = (source.rows * source.cols.max(1) * 4) as u64;
                if bytes > 0 {
                    encoder.copy_buffer_to_buffer(&source.data, 0, &result.data, offset, bytes);
                }
                offset += bytes;
            }
        });
        Ok(result)
    }
    /// Bound action working buffers by the device's storage-binding limit.
    /// Row order and multiplicity are preserved across contiguous pieces.
    pub fn split_for_width(
        &self,
        matrix: Matrix,
        max_columns: usize,
    ) -> Result<Vec<Matrix>, String> {
        let limits = self.dev.device.limits();
        let bytes = limits
            .max_buffer_size
            .min(u64::from(limits.max_storage_buffer_binding_size));
        let row_bytes = max_columns
            .max(1)
            .checked_mul(4)
            .ok_or("action row size overflow")?;
        let rows_per_batch = (bytes / row_bytes as u64) as usize;
        if rows_per_batch == 0 {
            return Err("one action row exceeds device limits".into());
        }
        if matrix.rows <= rows_per_batch {
            return Ok(vec![matrix]);
        }
        let mut batches = Vec::new();
        for start in (0..matrix.rows).step_by(rows_per_batch) {
            let rows = rows_per_batch.min(matrix.rows - start);
            let batch = self.matrix(rows, matrix.cols)?;
            self.encode(|encoder| {
                encoder.copy_buffer_to_buffer(
                    &matrix.data,
                    (start * matrix.cols.max(1) * 4) as u64,
                    &batch.data,
                    0,
                    (rows * matrix.cols.max(1) * 4) as u64,
                );
            });
            batches.push(batch);
        }
        Ok(batches)
    }
    fn run(
        &self,
        name: &'static str,
        buffers: [&wgpu::Buffer; 5],
        params: [u32; 4],
        lanes: usize,
    ) -> Result<(), String> {
        if lanes == 0 {
            return Ok(());
        }
        let groups = lanes.div_ceil(64);
        let x = groups.min(65535);
        let y = groups.div_ceil(x);
        if y > self
            .dev
            .device
            .limits()
            .max_compute_workgroups_per_dimension as usize
        {
            return Err("relational dispatch exceeds device limits".into());
        }
        let mut buffers = buffers;
        if !matches!(
            name,
            "scan_blocks"
                | "sort_tile_init"
                | "sort_tile_merge"
                | "sort_step"
                | "select_project"
                | "join_emit"
        ) {
            buffers[3] = &self.dummy[1];
        }
        if matches!(name, "sort_tile_init" | "sort_tile_merge" | "sort_step") {
            buffers[4] = &self.dummy[2];
        }
        let uniform = self.dev.buffer(&params, wgpu::BufferUsages::UNIFORM)?;
        let mut entries: Vec<_> = buffers
            .iter()
            .enumerate()
            .map(|(i, b)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: b.as_entire_binding(),
            })
            .collect();
        entries.push(wgpu::BindGroupEntry {
            binding: 5,
            resource: uniform.as_entire_binding(),
        });
        let bind = self
            .dev
            .device
            .create_bind_group(&wgpu::BindGroupDescriptor {
                label: None,
                layout: &self.layout,
                entries: &entries,
            });
        let pipeline = self
            .pipelines
            .lock()
            .unwrap()
            .entry(name)
            .or_insert_with(|| {
                self.dev
                    .device
                    .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                        label: Some(name),
                        layout: Some(&self.pipeline_layout),
                        module: &self.shader,
                        entry_point: Some(name),
                        compilation_options: Default::default(),
                        cache: None,
                    })
            })
            .clone();
        self.encode(|encoder| {
            let mut pass = encoder.begin_compute_pass(&Default::default());
            pass.set_pipeline(&pipeline);
            pass.set_bind_group(0, &bind, &[]);
            pass.dispatch_workgroups(x as u32, y as u32, 1);
        });
        self.dispatches.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }
    fn read(&self, buffer: &wgpu::Buffer, offset: usize, words: usize) -> Result<Vec<u32>, String> {
        self.read_slices(&[(buffer, offset, words)])
    }
    fn read_slices(&self, slices: &[(&wgpu::Buffer, usize, usize)]) -> Result<Vec<u32>, String> {
        let words = slices
            .iter()
            .try_fold(0usize, |sum, (_, _, words)| sum.checked_add(*words))
            .ok_or("readback size overflow")?;
        if words == 0 {
            return Ok(Vec::new());
        }
        let bytes = words.checked_mul(4).ok_or("readback size overflow")? as u64;
        if bytes > self.dev.device.limits().max_buffer_size {
            return Err("readback exceeds device limits".into());
        }
        let scalar_guard = (words == 1).then(|| self.scalar_staging.lock().unwrap());
        let staging = scalar_guard
            .as_ref()
            .map(|buffer| (*buffer).clone())
            .unwrap_or_else(|| {
                self.dev.device.create_buffer(&wgpu::BufferDescriptor {
                    label: None,
                    size: bytes,
                    usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
                    mapped_at_creation: false,
                })
            });
        self.encode(|encoder| {
            let mut dst = 0;
            for &(buffer, offset, words) in slices {
                let bytes = (words * 4) as u64;
                if bytes > 0 {
                    encoder.copy_buffer_to_buffer(
                        buffer,
                        (offset * 4) as u64,
                        &staging,
                        dst,
                        bytes,
                    );
                    dst += bytes;
                }
            }
        });
        self.flush();
        self.readbacks.fetch_add(1, Ordering::Relaxed);
        let (tx, rx) = std::sync::mpsc::sync_channel(1);
        staging.slice(..).map_async(wgpu::MapMode::Read, move |r| {
            let _ = tx.send(r);
        });
        self.dev
            .device
            .poll(wgpu::PollType::Wait)
            .map_err(|e| e.to_string())?;
        rx.recv()
            .map_err(|e| e.to_string())?
            .map_err(|e| e.to_string())?;
        let result =
            bytemuck::cast_slice::<u8, u32>(&staging.slice(..).get_mapped_range()).to_vec();
        staging.unmap();
        Ok(result)
    }
    pub fn download(&self, matrix: &Matrix) -> Result<Rows, String> {
        if matrix.cols == 0 {
            return Ok(vec![Vec::new(); matrix.rows]);
        }
        Ok(self
            .read(&matrix.data, 0, matrix.rows * matrix.cols)?
            .chunks_exact(matrix.cols)
            .map(|r| r.iter().copied().map(Value::new).collect())
            .collect())
    }
    pub fn download_pair(&self, left: &Matrix, right: &Matrix) -> Result<(Rows, Rows), String> {
        let left_words = left.rows * left.cols;
        let values = self.read_slices(&[
            (&left.data, 0, left_words),
            (&right.data, 0, right.rows * right.cols),
        ])?;
        let decode = |words: &[u32], matrix: &Matrix| {
            if matrix.cols == 0 {
                vec![Vec::new(); matrix.rows]
            } else {
                words
                    .chunks_exact(matrix.cols)
                    .map(|row| row.iter().copied().map(Value::new).collect())
                    .collect()
            }
        };
        Ok((
            decode(&values[..left_words], left),
            decode(&values[left_words..], right),
        ))
    }
    fn scan(&self, counts: wgpu::Buffer, n: usize) -> Result<wgpu::Buffer, String> {
        if n < 2 {
            return Ok(counts);
        }
        let blocks = n.div_ceil(64);
        let sums = self.allocate(blocks)?;
        let local = self.allocate(n)?;
        let dummy = &self.dummy[0];
        self.run(
            "scan_blocks",
            [&counts, dummy, dummy, &sums, &local],
            [n as u32, 0, 0, 0],
            n,
        )?;
        if blocks == 1 {
            return Ok(local);
        }
        let sums = self.scan(sums, blocks)?;
        let result = self.allocate(n)?;
        self.run(
            "scan_add",
            [&local, &sums, dummy, dummy, &result],
            [n as u32, 0, 0, 0],
            n,
        )?;
        Ok(result)
    }
    fn prefix_total(
        &self,
        counts: wgpu::Buffer,
        n: usize,
    ) -> Result<(wgpu::Buffer, usize), String> {
        if n == 0 {
            return Ok((counts, 0));
        }
        let current = self.scan(counts, n)?;
        let total = self.read(&current, n - 1, 1)?[0] as usize;
        Ok((current, total))
    }
    fn prefix(&self, counts: wgpu::Buffer, n: usize) -> Result<(wgpu::Buffer, usize), String> {
        let (current, total) = self.prefix_total(counts, n)?;
        if total > self.max_rows {
            return Err(format!(
                "join exceeds --max-join-rows={} ({total} rows)",
                self.max_rows
            ));
        }
        Ok((current, total))
    }
    fn sort(&self, matrix: &Matrix, keys: &[usize]) -> Result<wgpu::Buffer, String> {
        let mut orders = matrix.orders.lock().unwrap();
        if let Some(order) = orders.get(keys) {
            self.sort_cache_hits.fetch_add(1, Ordering::Relaxed);
            return Ok(order.clone());
        }
        let padded = matrix
            .rows
            .max(1)
            .checked_next_power_of_two()
            .ok_or("sort size overflow")?;
        let order = self.allocate(padded)?;
        let dummy = &self.dummy[0];
        let config = self.words(
            &[0, 64, keys.len() as u32]
                .into_iter()
                .chain(keys.iter().map(|&k| k as u32))
                .collect::<Vec<_>>(),
        )?;
        let params = [matrix.rows as u32, padded as u32, matrix.cols as u32, 0];
        self.run(
            "sort_tile_init",
            [&matrix.data, dummy, &config, &order, dummy],
            params,
            padded,
        )?;
        let mut k = 128;
        while k <= padded {
            let mut j = k / 2;
            while j >= 64 {
                let config: Vec<_> = [j as u32, k as u32, keys.len() as u32]
                    .into_iter()
                    .chain(keys.iter().map(|&k| k as u32))
                    .collect();
                let config = self.words(&config)?;
                self.run(
                    "sort_step",
                    [&matrix.data, dummy, &config, &order, dummy],
                    params,
                    padded,
                )?;
                j /= 2;
            }
            let config = self.words(
                &[0, k as u32, keys.len() as u32]
                    .into_iter()
                    .chain(keys.iter().map(|&key| key as u32))
                    .collect::<Vec<_>>(),
            )?;
            self.run(
                "sort_tile_merge",
                [&matrix.data, dummy, &config, &order, dummy],
                params,
                padded,
            )?;
            k *= 2;
        }
        orders.insert(keys.to_vec(), order.clone());
        self.sorts.fetch_add(1, Ordering::Relaxed);
        Ok(order)
    }
    pub fn unique(&self, matrix: Matrix) -> Result<Matrix, String> {
        let keys: Vec<_> = (0..matrix.cols).collect();
        self.unique_by(matrix, &keys)
    }
    pub fn unique_by(&self, matrix: Matrix, keys: &[usize]) -> Result<Matrix, String> {
        if matrix.rows < 2 {
            return Ok(matrix);
        }
        if keys.is_empty() {
            let result = self.matrix(1, matrix.cols)?;
            if matrix.cols > 0 {
                self.encode(|encoder| {
                    encoder.copy_buffer_to_buffer(
                        &matrix.data,
                        0,
                        &result.data,
                        0,
                        (matrix.cols * 4) as u64,
                    );
                });
            }
            return Ok(result);
        }
        let order = self.sort(&matrix, keys)?;
        let flags = self.allocate(matrix.rows)?;
        let dummy = self.dummy[0].clone();
        let config = self.words(
            &std::iter::once(keys.len() as u32)
                .chain(keys.iter().map(|&k| k as u32))
                .collect::<Vec<_>>(),
        )?;
        let params = [matrix.rows as u32, 0, matrix.cols as u32, 0];
        self.run(
            "unique_flags",
            [&matrix.data, &order, &config, &dummy, &flags],
            params,
            matrix.rows,
        )?;
        let (prefix, total) = self.prefix(flags, matrix.rows)?;
        let result = self.matrix(total, matrix.cols)?;
        self.run(
            "gather_unique",
            [&matrix.data, &order, &prefix, &dummy, &result.data],
            params,
            matrix.rows,
        )?;
        Ok(result)
    }
    fn compact(&self, matrix: Matrix, flags: wgpu::Buffer) -> Result<Matrix, String> {
        let (prefix, total) = self.prefix(flags, matrix.rows)?;
        let result = self.matrix(total, matrix.cols)?;
        let dummy = self.dummy[0].clone();
        self.run(
            "compact",
            [&matrix.data, &prefix, &dummy, &dummy, &result.data],
            [matrix.rows as u32, 0, matrix.cols as u32, 0],
            matrix.rows,
        )?;
        Ok(result)
    }
    pub fn select(
        &self,
        matrix: &Matrix,
        live: &wgpu::Buffer,
        constraints: &[Constraint],
        projection: &[u32],
        occurrence: (u32, u32, &[u32]),
        preserves_key: bool,
    ) -> Result<Matrix, String> {
        let (mode, key, occurrence_cols) = occurrence;
        let candidates = matrix
            .rows
            .checked_mul(if mode == 2 { occurrence_cols.len() } else { 1 })
            .ok_or("occurrence cardinality overflow")?;
        let result = self.matrix(candidates, projection.len())?;
        let mut config = vec![
            constraints.len() as u32,
            projection.len() as u32,
            mode,
            key,
            occurrence_cols.len() as u32,
        ];
        config.extend_from_slice(occurrence_cols);
        for c in constraints {
            config.extend(match *c {
                Constraint::Eq { l_col, r_col } => [0, l_col.rep(), r_col.rep()],
                Constraint::EqConst { col, val } => [1, col.rep(), val.rep()],
                Constraint::LtConst { col, val } => [2, col.rep(), val.rep()],
                Constraint::LeConst { col, val } => [3, col.rep(), val.rep()],
                Constraint::GtConst { col, val } => [4, col.rep(), val.rep()],
                Constraint::GeConst { col, val } => [5, col.rep(), val.rep()],
            });
        }
        config.extend_from_slice(projection);
        let config = self.words(&config)?;
        let flags = self.allocate(candidates)?;
        self.run(
            "select_project",
            [&matrix.data, live, &config, &flags, &result.data],
            [matrix.rows as u32, candidates as u32, matrix.cols as u32, 0],
            candidates,
        )?;
        let result = self.compact(result, flags)?;
        if preserves_key {
            Ok(result)
        } else {
            self.unique(result)
        }
    }
    pub fn live(&self, live: &[bool]) -> Result<wgpu::Buffer, String> {
        self.words(&live.iter().map(|&x| u32::from(x)).collect::<Vec<_>>())
    }
    pub fn plan_join(
        &self,
        left: &Matrix,
        right: &Matrix,
        keys: &[(usize, usize)],
        extra: &[usize],
    ) -> Result<JoinPlan, String> {
        if left.rows == 0 || right.rows == 0 {
            return Ok(JoinPlan {
                left: left.clone(),
                right: right.clone(),
                config: self.dummy[0].clone(),
                prefix: self.dummy[0].clone(),
                extra: extra.len(),
                rows: 0,
            });
        }
        let order = self.sort(right, &keys.iter().map(|&(_, r)| r).collect::<Vec<_>>())?;
        let mut header = vec![keys.len() as u32, extra.len() as u32];
        for &(l, r) in keys {
            header.extend([l as u32, r as u32]);
        }
        header.extend(extra.iter().map(|&c| c as u32));
        let config = self.allocate(header.len() + right.rows)?;
        self.dev
            .queue
            .write_buffer(&config, 0, bytemuck::cast_slice(&header));
        self.encode(|encoder| {
            encoder.copy_buffer_to_buffer(
                &order,
                0,
                &config,
                (header.len() * 4) as u64,
                (right.rows * 4) as u64,
            );
        });
        let counts = self.allocate(left.rows)?;
        let dummy = self.dummy[0].clone();
        let params = [
            left.rows as u32,
            right.rows as u32,
            left.cols as u32,
            right.cols as u32,
        ];
        self.run(
            "join_count",
            [&left.data, &right.data, &config, &dummy, &counts],
            params,
            left.rows,
        )?;
        let (prefix, total) = self.prefix_total(counts, left.rows)?;
        Ok(JoinPlan {
            left: left.clone(),
            right: right.clone(),
            config,
            prefix,
            extra: extra.len(),
            rows: total,
        })
    }
    pub fn join(&self, plan: JoinPlan) -> Result<Matrix, String> {
        let JoinPlan {
            left,
            right,
            config,
            prefix,
            extra,
            rows,
        } = plan;
        let result = self.matrix(rows, left.cols + extra)?;
        let params = [
            left.rows as u32,
            right.rows as u32,
            left.cols as u32,
            right.cols as u32,
        ];
        self.run(
            "join_emit",
            [&left.data, &right.data, &config, &prefix, &result.data],
            params,
            rows,
        )?;
        // Inputs are sets and the planner retains the union of their variables:
        // the emitted tuple uniquely determines both contributing input rows.
        // A natural join therefore needs no additional duplicate elimination.
        Ok(result)
    }
    pub fn project(&self, source: &Matrix, columns: &[(u32, u32)]) -> Result<Matrix, String> {
        if columns.len() == source.cols
            && columns
                .iter()
                .enumerate()
                .all(|(i, &entry)| entry == (1, i as u32))
        {
            return Ok(source.clone());
        }
        let result = self.matrix(source.rows, columns.len())?;
        if columns.is_empty() {
            return Ok(result);
        }
        let config = self.words(
            &columns
                .iter()
                .flat_map(|&(k, v)| [k, v])
                .collect::<Vec<_>>(),
        )?;
        let dummy = self.dummy[0].clone();
        self.run(
            "action_project",
            [&source.data, &dummy, &config, &dummy, &result.data],
            [
                source.rows as u32,
                columns.len() as u32,
                source.cols as u32,
                0,
            ],
            source.rows,
        )?;
        Ok(result)
    }
    pub fn bind(
        &self,
        source: &Matrix,
        values: &Matrix,
        value_col: usize,
        dst: usize,
    ) -> Result<Matrix, String> {
        assert_eq!(source.rows, values.rows);
        assert!(dst <= source.cols);
        let result = self.matrix(source.rows, source.cols.max(dst + 1))?;
        let config = self.words(&[value_col as u32, dst as u32])?;
        let dummy = self.dummy[0].clone();
        self.run(
            "bind_column",
            [&source.data, &values.data, &config, &dummy, &result.data],
            [
                source.rows as u32,
                result.cols as u32,
                source.cols as u32,
                values.cols as u32,
            ],
            source.rows,
        )?;
        Ok(result)
    }
    pub fn bind_constant(&self, source: &Matrix, value: u32, dst: usize) -> Result<Matrix, String> {
        assert!(dst <= source.cols);
        self.project(
            source,
            &(0..source.cols.max(dst + 1))
                .map(|c| if c == dst { (0, value) } else { (1, c as u32) })
                .collect::<Vec<_>>(),
        )
    }
    pub fn resolve_lookup(
        &self,
        source: &Matrix,
        found: &Matrix,
        default: (u32, u32),
    ) -> Result<Matrix, String> {
        assert_eq!(source.rows, found.rows);
        let result = self.matrix(source.rows, 1)?;
        let config = self.words(&[default.0, default.1])?;
        let dummy = self.dummy[0].clone();
        self.run(
            "resolve_lookup",
            [&source.data, &found.data, &config, &dummy, &result.data],
            [source.rows as u32, 0, source.cols as u32, 0],
            source.rows,
        )?;
        Ok(result)
    }
    pub fn filter(
        &self,
        source: Matrix,
        equal: bool,
        pairs: &[(DeviceEntry, DeviceEntry)],
    ) -> Result<Matrix, String> {
        let mut config = vec![u32::from(!equal), pairs.len() as u32];
        for &((ak, av), (bk, bv)) in pairs {
            config.extend([ak, av, bk, bv]);
        }
        let config = self.words(&config)?;
        let dummy = self.dummy[0].clone();
        let flags = self.allocate(source.rows)?;
        self.run(
            "assert_flags",
            [&source.data, &dummy, &config, &dummy, &flags],
            [source.rows as u32, 0, source.cols as u32, 0],
            source.rows,
        )?;
        self.compact(source, flags)
    }
    pub fn lookup(&self, keys: &Matrix, table: &Matrix, col: usize) -> Result<Matrix, String> {
        let result = self.matrix(keys.rows, 2)?;
        if keys.rows == 0 || table.rows == 0 {
            return Ok(result);
        }
        if keys.rows <= 8 {
            // A few probes do not justify sorting an entire changing table.
            // Each workgroup scans one key in parallel and selects its first hit.
            let config = self.words(&[col as u32])?;
            self.run(
                "lookup_small",
                [
                    &keys.data,
                    &table.data,
                    &config,
                    &self.dummy[0],
                    &result.data,
                ],
                [
                    keys.rows as u32,
                    table.rows as u32,
                    keys.cols as u32,
                    table.cols as u32,
                ],
                keys.rows * 64,
            )?;
            return Ok(result);
        }
        let order = self.sort(table, &(0..keys.cols).collect::<Vec<_>>())?;
        let mut header = vec![keys.cols as u32, 1];
        for key in 0..keys.cols {
            header.extend([key as u32, key as u32]);
        }
        header.push(col as u32);
        let config = self.allocate(header.len() + table.rows)?;
        self.dev
            .queue
            .write_buffer(&config, 0, bytemuck::cast_slice(&header));
        self.encode(|encoder| {
            encoder.copy_buffer_to_buffer(
                &order,
                0,
                &config,
                (header.len() * 4) as u64,
                (table.rows * 4) as u64,
            );
        });
        let dummy = self.dummy[0].clone();
        self.run(
            "lookup_values",
            [&keys.data, &table.data, &config, &dummy, &result.data],
            [
                keys.rows as u32,
                table.rows as u32,
                keys.cols as u32,
                table.cols as u32,
            ],
            keys.rows,
        )?;
        Ok(result)
    }
}
