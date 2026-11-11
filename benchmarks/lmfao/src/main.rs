use anyhow::{Result, bail, ensure};
use egglog_experimental::slotted;
use std::{fs, path::Path, time::Instant};

#[global_allocator]
static ALLOCATOR: benchmark_memory::LimitedAllocator = benchmark_memory::LimitedAllocator;

fn run() -> Result<()> {
    let args: Vec<_> = benchmark_memory::configure(std::env::args_os())
        .into_iter()
        .collect();
    let [_, mode, input, destination, timeout] = args.as_slice() else {
        bail!("usage: lmfao-extract <slotted|off> INPUT PLAN.json DAG_TIMEOUT_SECONDS");
    };
    let timeout: f64 = timeout
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("invalid timeout"))?
        .parse()?;
    ensure!(
        timeout.is_finite() && timeout > 0.0,
        "DAG timeout must be finite and positive"
    );
    let source = fs::read_to_string(input)?;
    let start = Instant::now();
    let (mut result, rewriting) = if mode == "slotted" || mode == "off" {
        let mut graph = if mode == "slotted" {
            slotted::new_egraph()
        } else {
            egglog_experimental::new_experimental_egraph_with_options(true)
        };
        graph.set_num_threads(1);
        let encoded = if mode == "slotted" {
            slotted::Compiler::default()
                .compile(None, &source)
                .map_err(anyhow::Error::msg)?
        } else {
            source.clone()
        };
        graph.parse_and_run_program(None, &encoded)?;
        let rewriting = start.elapsed().as_secs_f64();
        let result = if mode == "slotted" {
            lmfao_extract::extract_live(&graph, timeout)?
        } else {
            lmfao_extract::extract_plain(&graph, timeout)?
        };
        (result, rewriting)
    } else {
        bail!("unknown input mode")
    };
    let total = start.elapsed().as_secs_f64();
    result.report["phases_seconds"] =
        serde_json::json!({"rewriting": rewriting, "extraction": total - rewriting});
    result.report["views"] = result.plan["views"].as_array().unwrap().len().into();
    result.report["aggregates"] = result.plan["views"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v["aggregates"].as_array().unwrap().len())
        .sum::<usize>()
        .into();
    fs::write(destination, serde_json::to_vec_pretty(&result.plan)?)?;
    fs::write(
        Path::new(destination).with_file_name("extraction.json"),
        serde_json::to_vec_pretty(&result.report)?,
    )?;
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("LMFAO extraction: {error:#}");
        std::process::exit(1);
    }
}
