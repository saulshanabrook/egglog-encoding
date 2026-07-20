use std::{
    env, fmt, fs,
    io::{self, Write},
    process::ExitCode,
};

use egglog::causal_slice::causal_slice_program;

fn main() -> ExitCode {
    let mut args = env::args_os();
    let executable = args
        .next()
        .and_then(|arg| arg.into_string().ok())
        .unwrap_or_else(|| "causal_slice".to_owned());
    let Some(first) = args.next() else {
        report(format_args!("usage: {executable} [--full] <program.egg>"));
        return ExitCode::from(2);
    };
    let (full, path) = if first == "--full" {
        let Some(path) = args.next() else {
            report(format_args!("usage: {executable} [--full] <program.egg>"));
            return ExitCode::from(2);
        };
        (true, path)
    } else {
        (false, first)
    };
    if args.next().is_some() {
        report(format_args!("usage: {executable} [--full] <program.egg>"));
        return ExitCode::from(2);
    }

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
    let slice = match causal_slice_program(Some(path.to_string_lossy().into_owned()), &input) {
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
        "causal slice: {} waves, {} matched, {} effective, {} no-op, {} retained; bytes {} -> {} (full {}); traced run {:?}",
        slice.stats.waves,
        slice.stats.matched_applications,
        slice.stats.effective_applications,
        slice.stats.no_op_applications,
        slice.stats.retained_applications,
        slice.stats.original_bytes,
        slice.stats.sliced_bytes,
        slice.stats.full_transcript_bytes,
        slice.stats.traced_run_time,
    ));
    report(format_args!(
        "trace volume: {} application source bindings; {} observation matches / {} source bindings; {} raw bindings; max batch {}; >= {} bytes",
        slice.stats.captured_bindings,
        slice.stats.observation_matches,
        slice.stats.observation_bindings,
        slice.stats.raw_trace_bindings,
        slice.stats.max_batch_matches,
        slice.stats.raw_trace_lower_bound_bytes,
    ));
    ExitCode::SUCCESS
}

fn report(message: fmt::Arguments<'_>) {
    let _ = writeln!(io::stderr().lock(), "{message}");
}
