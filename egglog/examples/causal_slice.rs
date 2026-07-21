use std::{
    env, fmt, fs,
    io::{self, Write},
    process::ExitCode,
};

use egglog::causal_slice::{
    causal_slice_program_with_fact_directory,
    causal_slice_proof_replay_program_with_fact_directory,
    causal_slice_replay_program_with_fact_directory,
};

fn main() -> ExitCode {
    let mut args = env::args_os();
    let executable = args
        .next()
        .and_then(|arg| arg.into_string().ok())
        .unwrap_or_else(|| "causal_slice".to_owned());
    let usage = || {
        report(format_args!(
            "usage: {executable} [--full | --proof-projection] [--fact-directory <dir>] <program.egg>"
        ));
        ExitCode::from(2)
    };
    let mut full = false;
    let mut proof_projection = false;
    let mut fact_directory = None;
    let mut path = None;
    while let Some(arg) = args.next() {
        if arg == "--full" {
            if full || proof_projection {
                return usage();
            }
            full = true;
        } else if arg == "--proof-projection" {
            if full || proof_projection {
                return usage();
            }
            proof_projection = true;
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
    let filename = Some(path.to_string_lossy().into_owned());
    let generated = if full {
        causal_slice_program_with_fact_directory(filename, &input, fact_directory.as_deref())
            .map(|slice| (slice.full_transcript_source, slice.stats))
    } else if proof_projection {
        causal_slice_proof_replay_program_with_fact_directory(
            filename,
            &input,
            fact_directory.as_deref(),
        )
        .map(|replay| (replay.source, replay.stats))
    } else {
        causal_slice_replay_program_with_fact_directory(filename, &input, fact_directory.as_deref())
            .map(|replay| (replay.source, replay.stats))
    };
    let (output, stats) = match generated {
        Ok(generated) => generated,
        Err(error) => {
            report(format_args!("{error}"));
            return ExitCode::FAILURE;
        }
    };

    if let Err(error) = io::stdout().lock().write_all(output.as_bytes()) {
        report(format_args!("failed to write generated source: {error}"));
        return ExitCode::FAILURE;
    }
    report(format_args!(
        "causal slice: {} waves, {} pending, {} promoted, {} no-op, {} retained; bytes {} -> {} (full {}); total {:?}",
        stats.waves,
        stats.pending_firings,
        stats.promoted_events,
        stats.no_op_applications,
        stats.retained_applications,
        stats.original_bytes,
        stats.sliced_bytes,
        stats.full_transcript_bytes,
        stats.total_time,
    ));
    report(format_args!(
        "generator phases: prepare {:?}; trace {:?}; elaborate {:?}; slice {:?}; emit {:?}; validate {:?}",
        stats.preparation_time,
        stats.traced_run_time,
        stats.elaboration_time,
        stats.slicing_time,
        stats.emission_time,
        stats.emitted_validation_time,
    ));
    report(format_args!(
        "trace volume: {} application source bindings; {} observation matches / {} source bindings; {} raw bindings; max batch {}; >= {} bytes; arenas: {} source events, {} deps, {} witnesses ({} shared in replay), {} equality edges, {} prefixes",
        stats.captured_bindings,
        stats.observation_matches,
        stats.observation_bindings,
        stats.raw_trace_bindings,
        stats.max_batch_matches,
        stats.raw_trace_lower_bound_bytes,
        stats.source_events,
        stats.dependency_nodes,
        stats.witness_nodes,
        stats.shared_replay_witnesses,
        stats.equality_edges,
        stats.prefix_fallbacks,
    ));
    ExitCode::SUCCESS
}

fn report(message: fmt::Arguments<'_>) {
    let _ = writeln!(io::stderr().lock(), "{message}");
}
