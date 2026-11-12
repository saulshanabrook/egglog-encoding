use anyhow::{Context, Result, ensure};
use clap::Parser;
use egg_math_benchmark::{
    CHECK_LEFT, CHECK_RIGHT, ITERATIONS, MATH12_CHECK_LEFT, MATH12_CHECK_RIGHT, ProofMode, run_math,
};
use egglog_reports::TimingSummary;
use std::{
    fs::File,
    io::BufWriter,
    path::{Path, PathBuf},
};
#[global_allocator]
static ALLOCATOR: benchmark_memory::LimitedAllocator = benchmark_memory::LimitedAllocator;

#[derive(Debug, Parser)]
#[command(
    about = "Run the fixed PLDI 2023 Math workload with current egg",
    after_help = "Native memory option: --memory-limit-bytes <N>"
)]
struct Args {
    #[arg(long, value_enum, default_value_t)]
    proof_mode: ProofMode,
    #[arg(long)]
    timing_summary: Option<PathBuf>,
    #[arg(long)]
    proof_summary: Option<PathBuf>,
    #[arg(long)]
    math12: bool,
}

fn main() -> Result<()> {
    let args = Args::parse_from(benchmark_memory::configure(std::env::args_os()));
    let (iterations, check_left, check_right) = if args.math12 {
        (12, MATH12_CHECK_LEFT, MATH12_CHECK_RIGHT)
    } else {
        (ITERATIONS, CHECK_LEFT, CHECK_RIGHT)
    };
    let (timing, _, check_passed) = run_math(args.proof_mode, iterations, check_left, check_right)?;
    if let Some(path) = args.proof_summary {
        let produced =
            check_passed && matches!(args.proof_mode, ProofMode::Extract | ProofMode::Check);
        let summary = serde_json::json!({
            "schema_version": 1,
            "success": check_passed,
            "check_requests": 1,
            "extraction_requests": 0,
            "produced_certificates": usize::from(produced),
            "verified_certificates": usize::from(produced && args.proof_mode == ProofMode::Check),
        });
        serde_json::to_writer(File::create(path)?, &summary)?;
    }
    ensure!(
        check_passed,
        "terminal equality is not established after iteration {}",
        iterations
    );
    if let Some(path) = args.timing_summary {
        write_timing_summary(&path, &timing)?;
    }
    Ok(())
}

fn write_timing_summary(path: &Path, timing: &TimingSummary) -> Result<()> {
    let file = File::create(path)
        .with_context(|| format!("failed to create timing summary {}", path.display()))?;
    serde_json::to_writer(BufWriter::new(file), timing)
        .with_context(|| format!("failed to write timing summary {}", path.display()))
}
