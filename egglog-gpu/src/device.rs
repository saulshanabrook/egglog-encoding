//! Vulkan implementation of a two-pass sorted-range equality join.

use egglog_core_relations::MatchRelation;
use egglog_numeric_id::NumericId;
use wgpu::util::DeviceExt;

/// `Hardware` fails if only a CPU driver is available. `Software` explicitly
/// requests a fallback adapter, such as Mesa lavapipe. Neither silently switches
/// to the Rust simulator.
#[derive(Debug, Clone, Copy)]
pub enum AdapterMode {
    Hardware,
    Software,
}

pub struct DeviceJoin {
    pub(crate) device: wgpu::Device,
    pub(crate) queue: wgpu::Queue,
    count: wgpu::ComputePipeline,
    emit: wgpu::ComputePipeline,
    layout: wgpu::BindGroupLayout,
    name: String,
}

impl DeviceJoin {
    pub fn new(mode: AdapterMode) -> anyhow::Result<Self> {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor {
            backends: wgpu::Backends::VULKAN,
            ..Default::default()
        });
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            force_fallback_adapter: matches!(mode, AdapterMode::Software),
            ..Default::default()
        }))?;
        let info = adapter.get_info();
        anyhow::ensure!(
            !matches!(mode, AdapterMode::Hardware) || info.device_type != wgpu::DeviceType::Cpu,
            "only a CPU Vulkan adapter is available; select --backend software or simulate"
        );
        // The portable defaults cap a storage binding at 128 MiB even when the
        // adapter supports larger tables. Negotiate the actual buffer limits;
        // every allocation still checks the limits of the resulting device.
        let available = adapter.limits();
        let (device, queue) =
            pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
                label: Some("egglog GPU matcher"),
                required_limits: wgpu::Limits {
                    max_buffer_size: available.max_buffer_size,
                    max_storage_buffer_binding_size: available.max_storage_buffer_binding_size,
                    ..Default::default()
                },
                ..Default::default()
            }))?;
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("sorted range join"),
            source: wgpu::ShaderSource::Wgsl(include_str!("join.wgsl").into()),
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
        let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: None,
            entries: &entries,
        });
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: None,
            bind_group_layouts: &[&layout],
            push_constant_ranges: &[],
        });
        let pipeline = |entry| {
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some(entry),
                compilation_options: Default::default(),
                cache: None,
            })
        };
        let count = pipeline("count");
        let emit = pipeline("emit");
        Ok(Self {
            device,
            queue,
            count,
            emit,
            layout,
            name: format!("{} ({:?}, Vulkan)", info.name, info.device_type),
        })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn buffer(
        &self,
        words: &[u32],
        usage: wgpu::BufferUsages,
    ) -> Result<wgpu::Buffer, String> {
        let words = if words.is_empty() { &[0][..] } else { words };
        let bytes = std::mem::size_of_val(words) as u64;
        let limits = self.device.limits();
        if bytes > limits.max_buffer_size
            || (usage.contains(wgpu::BufferUsages::STORAGE)
                && bytes > u64::from(limits.max_storage_buffer_binding_size))
        {
            return Err(format!(
                "join buffer needs {bytes} bytes, exceeding device limits (buffer {}, storage binding {})",
                limits.max_buffer_size, limits.max_storage_buffer_binding_size
            ));
        }
        Ok(self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: None,
                contents: bytemuck::cast_slice(words),
                usage,
            }))
    }

    fn dispatch(
        &self,
        pipeline: &wgpu::ComputePipeline,
        buffers: &[&wgpu::Buffer; 6],
        n: u32,
        read: &wgpu::Buffer,
        words: usize,
    ) -> Result<Vec<u32>, String> {
        let groups = n.div_ceil(64);
        if groups > self.device.limits().max_compute_workgroups_per_dimension {
            return Err("join dispatch exceeds device limits".into());
        }
        let entries: Vec<_> = buffers
            .iter()
            .enumerate()
            .map(|(i, b)| wgpu::BindGroupEntry {
                binding: i as u32,
                resource: b.as_entire_binding(),
            })
            .collect();
        let bindings = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &self.layout,
            entries: &entries,
        });
        let size = (words * 4) as u64;
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        let mut encoder = self.device.create_command_encoder(&Default::default());
        {
            let mut pass = encoder.begin_compute_pass(&Default::default());
            pass.set_pipeline(pipeline);
            pass.set_bind_group(0, &bindings, &[]);
            pass.dispatch_workgroups(groups, 1, 1);
        }
        encoder.copy_buffer_to_buffer(read, 0, &staging, 0, size);
        self.queue.submit([encoder.finish()]);
        let (tx, rx) = std::sync::mpsc::sync_channel(1);
        staging.slice(..).map_async(wgpu::MapMode::Read, move |r| {
            let _ = tx.send(r);
        });
        self.device
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

    /// `right` must be sorted lexicographically by the shared key columns.
    pub(crate) fn join(
        &self,
        left: &MatchRelation,
        right: &MatchRelation,
        keys: &[(usize, usize)],
        max_rows: usize,
    ) -> Result<Vec<[u32; 2]>, String> {
        if left.rows.is_empty() || right.rows.is_empty() {
            return Ok(vec![]);
        }
        let storage = wgpu::BufferUsages::STORAGE;
        let transfer = storage | wgpu::BufferUsages::COPY_SRC | wgpu::BufferUsages::COPY_DST;
        let columnar = |rel: &MatchRelation| -> Vec<u32> {
            (0..rel.variables.len())
                .flat_map(|c| rel.rows.iter().map(move |r| r[c].rep()))
                .collect()
        };
        let l = self.buffer(&columnar(left), storage)?;
        let r = self.buffer(&columnar(right), storage)?;
        let key_words: Vec<_> = keys
            .iter()
            .flat_map(|&(l, r)| [l as u32, r as u32])
            .collect();
        let key = self.buffer(
            if key_words.is_empty() {
                &[0, 0]
            } else {
                &key_words
            },
            storage,
        )?;
        let mut params = [
            u32::try_from(left.rows.len()).map_err(|e| e.to_string())?,
            u32::try_from(right.rows.len()).map_err(|e| e.to_string())?,
            keys.len() as u32,
            0,
        ];
        let uniform = self.buffer(
            &params,
            wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
        )?;
        let offsets = self.buffer(&vec![0; left.rows.len() + 1], transfer)?;
        let dummy = self.buffer(&[0, 0], transfer)?;
        let counts = self.dispatch(
            &self.count,
            &[&l, &r, &key, &offsets, &dummy, &uniform],
            params[0],
            &offsets,
            left.rows.len(),
        )?;
        let mut prefix = Vec::with_capacity(counts.len() + 1);
        let mut total = 0u32;
        for count in counts {
            prefix.push(total);
            total = total
                .checked_add(count)
                .ok_or("join cardinality exceeds u32")?;
            if total as usize > max_rows {
                return Err("join exceeds the experimental bulk row limit".into());
            }
        }
        prefix.push(total);
        if total == 0 {
            return Ok(vec![]);
        }
        params[3] = total;
        self.queue
            .write_buffer(&uniform, 0, bytemuck::cast_slice(&params));
        self.queue
            .write_buffer(&offsets, 0, bytemuck::cast_slice(&prefix));
        let output = self.buffer(&vec![0; total as usize * 2], transfer)?;
        let pairs = self.dispatch(
            &self.emit,
            &[&l, &r, &key, &offsets, &output, &uniform],
            total,
            &output,
            total as usize * 2,
        )?;
        Ok(pairs.chunks_exact(2).map(|p| [p[0], p[1]]).collect())
    }
}
