use std::{path::PathBuf, sync::Arc};

use clap::{Parser, ValueEnum};
use egglog_gpu::{AdapterMode, Backend as Runtime};

#[derive(Clone, Copy, ValueEnum)]
enum Backend {
    Simulate,
    Software,
    Gpu,
}

#[derive(Parser)]
#[command(about = "Relational backend replacement for term-encoded egglog")]
struct Args {
    /// simulate: Rust reference; software: CPU Vulkan; gpu: hardware Vulkan.
    #[arg(long, value_enum, default_value = "simulate")]
    backend: Backend,
    /// Optional row guard; device buffer and 32-bit indexing limits always apply.
    #[arg(long)]
    max_join_rows: Option<usize>,
    /// Files run in order in a single term-encoded e-graph.
    #[arg(required = true)]
    files: Vec<PathBuf>,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let max_rows = args.max_join_rows.unwrap_or(egglog_gpu::MAX_ROW_COUNT);
    anyhow::ensure!(max_rows > 0, "--max-join-rows must be positive");
    anyhow::ensure!(
        max_rows < u32::MAX as usize,
        "--max-join-rows must fit the device row index space"
    );
    let backend = Arc::new(match args.backend {
        Backend::Simulate => Runtime::simulated(max_rows),
        Backend::Software => Runtime::vulkan(AdapterMode::Software, max_rows)?,
        Backend::Gpu => Runtime::vulkan(AdapterMode::Hardware, max_rows)?,
    });
    eprintln!("Backend: {}", backend.adapter());
    let mut graph = backend.egraph();
    let run = (|| -> anyhow::Result<()> {
        for path in args.files {
            let source = std::fs::read_to_string(&path)?;
            let outputs = graph.parse_and_run_program(Some(path.display().to_string()), &source)?;
            for output in outputs {
                let rendered = output.to_string();
                if !rendered.is_empty() {
                    println!("{rendered}");
                }
            }
        }
        Ok(())
    })();
    eprintln!("Backend statistics: {:?}", backend.statistics());
    run
}
