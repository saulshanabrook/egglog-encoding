use std::{env, fs, process::ExitCode};

use egglog::causal_slice::causal_slice_proof_replay_program_with_egraph;

fn main() -> ExitCode {
    let mut args = env::args_os().skip(1);
    let Some(input_path) = args.next() else {
        eprintln!("usage: causal_slice_proof <input.egg> <output.egg>");
        return ExitCode::from(2);
    };
    let Some(output_path) = args.next() else {
        eprintln!("usage: causal_slice_proof <input.egg> <output.egg>");
        return ExitCode::from(2);
    };
    if args.next().is_some() {
        eprintln!("usage: causal_slice_proof <input.egg> <output.egg>");
        return ExitCode::from(2);
    }
    let input = match fs::read_to_string(&input_path) {
        Ok(input) => input,
        Err(error) => {
            eprintln!("failed to read {}: {error}", input_path.to_string_lossy());
            return ExitCode::FAILURE;
        }
    };
    let replay = match causal_slice_proof_replay_program_with_egraph(
        Some(input_path.to_string_lossy().into_owned()),
        &input,
        egglog_experimental::new_experimental_egraph_for_proofs(),
    ) {
        Ok(replay) => replay,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::FAILURE;
        }
    };
    if let Err(error) = fs::write(&output_path, &replay.source) {
        eprintln!("failed to write {}: {error}", output_path.to_string_lossy());
        return ExitCode::FAILURE;
    }
    eprintln!(
        "causal proof projection: {} pending, {} promoted, {} retained, {} prefix fallbacks; bytes {} -> {}; arenas: {} source events, {} dependencies, {} witnesses; trace {:?}; elaborate {:?}; slice {:?}; emit {:?}; validate {:?}; total {:?}",
        replay.stats.pending_firings,
        replay.stats.promoted_events,
        replay.stats.retained_applications,
        replay.stats.prefix_fallbacks,
        replay.stats.original_bytes,
        replay.stats.sliced_bytes,
        replay.stats.source_events,
        replay.stats.dependency_nodes,
        replay.stats.witness_nodes,
        replay.stats.traced_run_time,
        replay.stats.elaboration_time,
        replay.stats.slicing_time,
        replay.stats.emission_time,
        replay.stats.emitted_validation_time,
        replay.stats.total_time,
    );
    ExitCode::SUCCESS
}
