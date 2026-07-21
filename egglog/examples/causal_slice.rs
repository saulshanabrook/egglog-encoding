use std::{
    env, fmt, fs,
    io::{self, Write},
    process::ExitCode,
};

use egglog::causal_slice::causal_slice_program_with_fact_directory;

fn main() -> ExitCode {
    let mut args = env::args_os();
    let executable = args
        .next()
        .and_then(|arg| arg.into_string().ok())
        .unwrap_or_else(|| "causal_slice".to_owned());
    let usage = || {
        report(format_args!(
            "usage: {executable} [--full] [--fact-directory <dir>] <program.egg>"
        ));
        ExitCode::from(2)
    };
    let mut full = false;
    let mut fact_directory = None;
    let mut path = None;
    while let Some(arg) = args.next() {
        if arg == "--full" {
            if full {
                return usage();
            }
            full = true;
        } else if arg == "--fact-directory" {
            if fact_directory.is_some() {
                return usage();
            }
            let Some(directory) = args.next() else {
                return usage();
            };
            fact_directory = Some(std::path::PathBuf::from(directory));
        } else if path.replace(arg).is_some() {
            return usage();
        }
    }
    let Some(path) = path else {
        return usage();
    };

    let input = match fs::read_to_string(&path) {
        Ok(input) => input,
        Err(error) => {
            report(format_args!(
                "failed to read {}: {error}",
                path.to_string_lossy()
            ));
            return ExitCode::FAILURE;
        }
    };
    let slice = match causal_slice_program_with_fact_directory(
        Some(path.to_string_lossy().into_owned()),
        &input,
        fact_directory.as_deref(),
    ) {
        Ok(slice) => slice,
        Err(error) => {
            report(format_args!("{error}"));
            return ExitCode::FAILURE;
        }
    };

    let output = if full {
        &slice.full_transcript_source
    } else {
        &slice.source
    };
    if let Err(error) = io::stdout().lock().write_all(output.as_bytes()) {
        report(format_args!("failed to write generated source: {error}"));
        return ExitCode::FAILURE;
    }
    report(format_args!(
        "causal slice: {} waves, {} pending, {} promoted, {} no-op, {} retained; bytes {} -> {} (full {}); total {:?}",
        slice.stats.waves,
        slice.stats.pending_firings,
        slice.stats.promoted_events,
        slice.stats.no_op_applications,
        slice.stats.retained_applications,
        slice.stats.original_bytes,
        slice.stats.sliced_bytes,
        slice.stats.full_transcript_bytes,
        slice.stats.total_time,
    ));
    report(format_args!(
        "generator phases: prepare {:?}; trace {:?}; elaborate {:?}; slice {:?}; emit {:?}; validate {:?}",
        slice.stats.preparation_time,
        slice.stats.traced_run_time,
        slice.stats.elaboration_time,
        slice.stats.slicing_time,
        slice.stats.emission_time,
        slice.stats.emitted_validation_time,
    ));
    report(format_args!(
        "trace volume: {} application source bindings; {} observation matches / {} source bindings; {} raw bindings; max batch {}; >= {} bytes; arenas: {} source events, {} deps, {} witnesses, {} equality edges, {} prefixes",
        slice.stats.captured_bindings,
        slice.stats.observation_matches,
        slice.stats.observation_bindings,
        slice.stats.raw_trace_bindings,
        slice.stats.max_batch_matches,
        slice.stats.raw_trace_lower_bound_bytes,
        slice.stats.source_events,
        slice.stats.dependency_nodes,
        slice.stats.witness_nodes,
        slice.stats.equality_edges,
        slice.stats.prefix_fallbacks,
    ));
    ExitCode::SUCCESS
}

fn report(message: fmt::Arguments<'_>) {
    let _ = writeln!(io::stderr().lock(), "{message}");
}
