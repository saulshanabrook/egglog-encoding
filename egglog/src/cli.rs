use crate::*;
use std::ffi::OsString;
use std::io::{self, BufRead, BufReader, IsTerminal, Read, Write};
use std::str::FromStr;

use clap::Parser;
use egglog_reports::TimingSummaryV2;
use env_logger::Env;
use std::path::{Path, PathBuf};

#[derive(Debug, Parser)]
#[command(version = env!("FULL_VERSION"), about = env!("CARGO_PKG_DESCRIPTION"))]
struct Args {
    /// Directory for files when using `input` and `output` commands
    #[clap(short = 'F', long)]
    fact_directory: Option<PathBuf>,
    /// Turns off the seminaive optimization
    #[clap(long)]
    naive: bool,
    /// Skips tree-decomposition during query planning. Tree decomposition
    /// tries to decompose complex queries into smaller independent subqueries,
    /// and evaluate them separately. It has a better theoretical guarantee,
    /// but sometimes the decomposed subqueries (called "bags") can be much larger
    /// than the final output, which leads to worse performance sometimes.
    ///
    /// Setting this flag forces the query planner to skip tree decomposition and
    /// evaluate the query as a single bag.
    ///
    /// You can also disable tree decomposition on a per-rule basis with the `:no-decomp` label
    /// on rules.
    #[clap(long)]
    no_decomp: bool,
    /// Prints extra information, which can be useful for debugging
    #[clap(long, default_value_t = RunMode::Normal)]
    mode: RunMode,
    /// The file names for the egglog files to run
    inputs: Vec<PathBuf>,
    /// Serializes the egraph for each egglog file as JSON
    #[clap(long)]
    to_json: bool,
    /// Serializes the egraph for each egglog file as a dot file
    #[clap(long)]
    to_dot: bool,
    /// Serializes the egraph for each egglog file as an SVG
    #[clap(long)]
    to_svg: bool,
    /// Splits the serialized egraph into primitives and non-primitives
    #[clap(long)]
    serialize_split_primitive_outputs: bool,
    /// Maximum number of function nodes to render in dot/svg output
    #[clap(long, default_value = "40")]
    max_functions: usize,
    /// Maximum number of calls per function to render in dot/svg output
    #[clap(long, default_value = "40")]
    max_calls_per_function: usize,
    /// Number of times to inline leaves
    #[clap(long, default_value = "0")]
    serialize_n_inline_leaves: usize,
    #[clap(short = 'j', long, default_value = "1")]
    /// Number of threads to use for parallel execution. Passing `0` will use the maximum
    /// inferred parallelism available on the current system.
    threads: usize,
    #[arg(value_enum)]
    #[clap(long, default_value_t = ReportLevel::TimeOnly)]
    report_level: ReportLevel,
    #[clap(long)]
    save_report: Option<PathBuf>,
    /// Writes compact per-ruleset timing JSON after all inputs succeed.
    ///
    /// This requires `--threads 1` because parallel search and apply overlap
    /// and therefore cannot be reported as additive wall-clock phases.
    #[clap(long)]
    timing_summary: Option<PathBuf>,
    /// Treat missing `$` prefixes on globals as errors instead of warnings
    #[clap(long = "strict-mode")]
    strict_mode: bool,
    /// Run the terms encoding of equality saturation
    #[clap(long)]
    term_encoding: bool,
    /// Run with proof generation enabled
    #[clap(long)]
    proofs: bool,
    /// Enable proof testing, turning all `check` statements into `prove` statements
    #[clap(long)]
    proof_testing: bool,
    /// Record an ordinary run and validate a replay of the successful checks
    #[clap(long)]
    slice: bool,
    /// Write the validated replay program. This implies `--slice`.
    #[clap(long)]
    slice_output: Option<PathBuf>,
}

fn path_identity(path: &Path) -> Result<PathBuf, String> {
    if path.exists() {
        return path
            .canonicalize()
            .map_err(|error| format!("cannot resolve `{}`: {error}", path.display()));
    }

    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let name = path
        .file_name()
        .ok_or_else(|| format!("path `{}` has no file name", path.display()))?;
    parent
        .canonicalize()
        .map(|parent| parent.join(name))
        .map_err(|error| format!("cannot resolve parent of `{}`: {error}", path.display()))
}

fn validate_slice_paths(args: &Args) -> Result<(), String> {
    let Some(output) = args.slice_output.as_ref() else {
        return Ok(());
    };
    let output_identity = path_identity(output)?;
    let conflicts = [
        ("input file", args.inputs.first()),
        ("--save-report", args.save_report.as_ref()),
        ("--timing-summary", args.timing_summary.as_ref()),
    ];
    for (label, candidate) in conflicts {
        if let Some(candidate) = candidate
            && path_identity(candidate)? == output_identity
        {
            return Err(format!(
                "--slice-output `{}` conflicts with {label} `{}`",
                output.display(),
                candidate.display()
            ));
        }
    }
    Ok(())
}

fn publish_slice_output(path: &Path, rendered: &str) -> io::Result<()> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    temporary.write_all(rendered.as_bytes())?;
    temporary.as_file().sync_all()?;
    if std::fs::read(temporary.path())? != rendered.as_bytes() {
        return Err(io::Error::other(
            "temporary artifact differs from the validated replay program",
        ));
    }
    temporary.persist(path).map_err(|error| error.error)?;
    Ok(())
}

/// Start a command-line interface for the E-graph.
///
/// This is what vanilla egglog uses, and custom egglog builds (i.e., "egglog batteries included")
/// should also call this function.
#[allow(clippy::disallowed_macros)]
pub fn cli(egraph: EGraph) {
    cli_with_args_inner(egraph, std::env::args_os(), None);
}

/// Start a command-line interface with an explicit argv.
///
/// Custom binaries can pre-parse their own flags and pass the remaining
/// arguments here while still using egglog's standard CLI behavior.
#[allow(clippy::disallowed_macros)]
pub fn cli_with_args<I, T>(egraph: EGraph, args: I)
where
    I: IntoIterator<Item = T>,
    T: Into<OsString> + Clone,
{
    cli_with_args_inner(egraph, args, None);
}

/// Start a command-line interface with a factory for the fresh validation graph
/// used by `--slice`.
///
/// Custom binaries which install sorts, primitives, or command extensions
/// must use this entrypoint so replay receives the same extensions as capture.
#[allow(clippy::disallowed_macros)]
pub fn cli_with_args_and_factory<I, T, F>(egraph: EGraph, args: I, replay_factory: F)
where
    I: IntoIterator<Item = T>,
    T: Into<OsString> + Clone,
    F: FnOnce() -> EGraph + 'static,
{
    cli_with_args_inner(egraph, args, Some(Box::new(replay_factory)));
}

#[allow(clippy::disallowed_macros)]
fn cli_with_args_inner<I, T>(
    mut egraph: EGraph,
    args: I,
    replay_factory: Option<Box<dyn FnOnce() -> EGraph>>,
) where
    I: IntoIterator<Item = T>,
    T: Into<OsString> + Clone,
{
    env_logger::Builder::from_env(Env::default().default_filter_or("warn"))
        .format_timestamp(None)
        .format_target(false)
        .parse_default_env()
        .init();

    let args = Args::parse_from(args);

    if args.timing_summary.is_some() && args.threads != 1 {
        log::error!("--timing-summary requires --threads 1 for accurate phase timing");
        std::process::exit(2);
    }
    let slice_requested = args.slice || args.slice_output.is_some();
    if slice_requested {
        let invalid = if args.threads != 1 {
            Some("--slice requires --threads 1")
        } else if args.inputs.len() != 1 {
            Some("--slice requires exactly one input file")
        } else if args.proof_testing {
            Some("--slice conflicts with --proof-testing")
        } else if args.term_encoding {
            Some("--slice conflicts with --term-encoding")
        } else if args.naive {
            Some("--slice does not support --naive")
        } else if args.to_json || args.to_dot || args.to_svg {
            Some("--slice conflicts with --to-json, --to-dot, and --to-svg")
        } else if replay_factory.is_none() {
            Some(
                "--slice requires a fresh-graph factory; custom binaries must call cli_with_args_and_factory",
            )
        } else if matches!(
            args.mode,
            RunMode::Interactive | RunMode::ShowDesugaredEgglog
        ) {
            Some("--slice supports only normal and no-messages modes")
        } else {
            None
        };
        if let Some(message) = invalid {
            log::error!("{message}");
            std::process::exit(2);
        }
        if let Err(message) = validate_slice_paths(&args) {
            log::error!("{message}");
            std::process::exit(2);
        }
    }

    EGraph::set_num_threads(args.threads);

    egraph.fact_directory.clone_from(&args.fact_directory);
    egraph.seminaive = !args.naive;
    egraph.no_decomp = args.no_decomp;
    egraph.set_report_level(args.report_level);
    if args.strict_mode {
        egraph.set_strict_mode(true);
    }

    if args.term_encoding {
        egraph = egraph.with_term_encoding_enabled();
    }

    if args.proofs && !slice_requested {
        egraph = egraph.with_proofs_enabled();
    }

    if args.proof_testing {
        egraph = egraph.with_proofs_enabled();
        egraph = egraph.with_proof_testing();
    }

    if slice_requested && let Err(error) = egraph.enable_trace() {
        log::error!("{error}");
        std::process::exit(2);
    }

    if slice_requested {
        let input = &args.inputs[0];
        let program = std::fs::read_to_string(input).unwrap_or_else(|_| {
            let arg = input.to_string_lossy();
            panic!("Failed to read file {arg}")
        });
        let filename = Some(input.to_str().unwrap().to_owned());
        let capture_start = std::time::Instant::now();
        let parsed = egraph
            .parse_program(filename, &program)
            .unwrap_or_else(|error| {
                log::error!("{error}");
                std::process::exit(1);
            });
        if let Err(error) = egraph.run_program(parsed) {
            log::error!("{error}");
            std::process::exit(1);
        }
        let capture_time = capture_start.elapsed();

        let slice_start = std::time::Instant::now();
        let slice = crate::slicing::backward::slice_all_checks(&egraph).unwrap_or_else(|error| {
            log::error!("{error}");
            std::process::exit(1);
        });
        let replay =
            crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap_or_else(|error| {
                log::error!("{error}");
                std::process::exit(1);
            });
        let replay_stats = replay.stats;
        let commands = replay.to_commands().unwrap_or_else(|error| {
            log::error!("{error}");
            std::process::exit(1);
        });
        let rendered = crate::slicing::replay::ReplayProgram::render_commands(&commands)
            .unwrap_or_else(|error| {
                log::error!("{error}");
                std::process::exit(1);
            });
        let slice_time = slice_start.elapsed();

        // Drop every runtime value and trace allocation before constructing
        // fresh replay graphs. The rendered program is the phase boundary.
        drop(egraph);
        let mut replay_seed = replay_factory.expect("slice factory was validated")();
        replay_seed.fact_directory.clone_from(&args.fact_directory);
        replay_seed.seminaive = true;
        replay_seed.no_decomp = args.no_decomp;
        replay_seed.set_report_level(args.report_level);
        if args.strict_mode {
            replay_seed.set_strict_mode(true);
        }
        let user_seed = args.proofs.then(|| replay_seed.clone());
        let mut strict_graph = replay_seed.with_proofs_enabled().with_proof_testing();
        let replay_start = std::time::Instant::now();
        strict_graph
            .parse_and_run_program(Some("generated slice replay".into()), &rendered)
            .unwrap_or_else(|error| {
                log::error!("slice replay validation failed: {error}");
                std::process::exit(1);
            });
        let (final_graph, outputs) = if let Some(user_seed) = user_seed {
            let mut user_graph = user_seed.with_proofs_enabled();
            let outputs = user_graph
                .parse_and_run_program(Some("generated slice replay".into()), &rendered)
                .unwrap_or_else(|error| {
                    if matches!(&error, crate::Error::CheckError(..)) {
                        log::error!("slice replay check failed: {error}");
                    } else {
                        log::error!("slice replay execution failed: {error}");
                    }
                    std::process::exit(1);
                });
            (user_graph, outputs)
        } else {
            (strict_graph, Vec::new())
        };
        let replay_time = replay_start.elapsed();
        if let Some(path) = &args.slice_output {
            publish_slice_output(path, &rendered).unwrap_or_else(|error| {
                log::error!(
                    "cannot publish slice replay artifact `{}`: {error}",
                    path.display()
                );
                std::process::exit(1);
            });
        }
        if args.mode != RunMode::NoMessages {
            let mut output = io::stdout();
            for message in outputs {
                write!(output, "{message}").unwrap();
            }
        }
        log::info!(
            "slice: capture={capture_time:?} slice={slice_time:?} replay={replay_time:?} facts={} firings={} equalities={} removals={} waves={} aliases={} replayed_firings={}",
            slice.facts.len(),
            slice.firings.len(),
            slice.equalities.len(),
            slice.replay_removals.len(),
            replay_stats.waves,
            replay_stats.aliases,
            replay_stats.firings,
        );
        egraph = final_graph;
    } else if args.inputs.is_empty() {
        match egraph.repl(args.mode) {
            Ok(()) => {}
            Err(err) => {
                log::error!("{err}");
                std::process::exit(1)
            }
        }
    } else {
        for input in &args.inputs {
            let program = std::fs::read_to_string(input).unwrap_or_else(|_| {
                let arg = input.to_string_lossy();
                panic!("Failed to read file {arg}")
            });

            match run_commands(
                &mut egraph,
                Some(input.to_str().unwrap().into()),
                &program,
                io::stdout(),
                args.mode,
            ) {
                Ok(None) => {}
                _ => std::process::exit(1),
            }

            if args.to_json || args.to_dot || args.to_svg {
                let serialized_output = egraph.serialize(SerializeConfig {
                    max_functions: Some(args.max_functions),
                    max_calls_per_function: Some(args.max_calls_per_function),
                    ..SerializeConfig::default()
                });
                if !serialized_output.is_complete() {
                    log::warn!("{}", serialized_output.omitted_description());
                }
                let mut serialized = serialized_output.egraph;
                if args.serialize_split_primitive_outputs {
                    serialized.split_classes(|id, _| egraph.from_node_id(id).is_primitive())
                }
                for _ in 0..args.serialize_n_inline_leaves {
                    serialized.inline_leaves();
                }

                // if we are splitting primitive outputs, add `-split` to the end of the file name
                let serialize_filename = if args.serialize_split_primitive_outputs {
                    input.with_file_name(format!(
                        "{}-split",
                        input.file_stem().unwrap().to_str().unwrap()
                    ))
                } else {
                    input.clone()
                };
                if args.to_dot {
                    let dot_path = serialize_filename.with_extension("dot");
                    serialized
                        .to_dot_file(dot_path.clone())
                        .unwrap_or_else(|_| panic!("Failed to write dot file to {dot_path:?}"));
                }
                if args.to_svg {
                    let svg_path = serialize_filename.with_extension("svg");
                    serialized.to_svg_file(svg_path.clone()).unwrap_or_else( |_|
                        panic!("Failed to write svg file to {svg_path:?}. Make sure you have the `dot` executable installed")
                    );
                }
                if args.to_json {
                    let json_path = serialize_filename.with_extension("json");
                    serialized
                        .to_json_file(json_path.clone())
                        .unwrap_or_else(|_| panic!("Failed to write json file to {json_path:?}"));
                }
            }
        }
    }

    if let Some(report_path) = args.save_report {
        let report = egraph.get_overall_run_report();
        serde_json::to_writer(
            std::fs::File::create(&report_path)
                .unwrap_or_else(|_| panic!("Failed to create report file at {report_path:?}")),
            &report,
        )
        .expect("Failed to serialize report");
        log::info!("Saved report to {report_path:?}");
    }

    if let Some(summary_path) = args.timing_summary {
        let summary = TimingSummaryV2::from_run_report(egraph.get_overall_run_report())
            .unwrap_or_else(|error| {
                log::error!("failed to create timing summary: {error}");
                std::process::exit(1);
            });
        let mut file = std::fs::File::create(&summary_path)
            .unwrap_or_else(|_| panic!("Failed to create timing summary file at {summary_path:?}"));
        serde_json::to_writer(&mut file, &summary).expect("Failed to serialize timing summary");
        file.write_all(b"\n")
            .expect("Failed to finish writing timing summary");
        log::info!("Saved timing summary to {summary_path:?}");
    }

    // no need to drop the egraph if we are going to exit
    std::mem::forget(egraph)
}

impl EGraph {
    /// Start a Read-Eval-Print Loop with standard I/O.
    pub fn repl(&mut self, mode: RunMode) -> io::Result<()> {
        self.repl_with(io::stdin(), io::stdout(), mode, io::stdin().is_terminal())
    }

    /// Start a Read-Eval-Print Loop with the given input and output channel.
    pub fn repl_with<R, W>(
        &mut self,
        input: R,
        mut output: W,
        mode: RunMode,
        is_terminal: bool,
    ) -> io::Result<()>
    where
        R: Read,
        W: Write,
    {
        // https://doc.rust-lang.org/beta/std/io/trait.IsTerminal.html#examples
        if is_terminal {
            output.write_all(welcome_prompt().as_bytes())?;
            output.write_all(b"\n> ")?;
            output.flush()?;
        }
        let mut cmd_buffer = String::new();

        for line in BufReader::new(input).lines() {
            let line_str = line?;
            cmd_buffer.push_str(&line_str);
            cmd_buffer.push('\n');
            // handles multi-line commands
            if should_eval(&cmd_buffer) {
                run_commands(self, None, &cmd_buffer, &mut output, mode)?;
                cmd_buffer = String::new();
                if is_terminal {
                    output.write_all(b"> ")?;
                    output.flush()?;
                }
            }
        }

        if !cmd_buffer.is_empty() {
            run_commands(self, None, &cmd_buffer, &mut output, mode)?;
        }

        Ok(())
    }
}

fn welcome_prompt() -> String {
    format!("Welcome to Egglog REPL! (build: {})", env!("FULL_VERSION"))
}

fn should_eval(curr_cmd: &str) -> bool {
    all_sexps(SexpParser::new(None, curr_cmd)).is_ok()
}

fn run_commands<W>(
    egraph: &mut EGraph,
    filename: Option<String>,
    command: &str,
    mut output: W,
    mode: RunMode,
) -> io::Result<Option<Error>>
where
    W: Write,
{
    if mode == RunMode::ShowDesugaredEgglog {
        return Ok(match egraph.resolve_program(filename, command) {
            Ok(resolved) => {
                let sanitized = sanitize_internal_names(&resolved);

                for line in sanitized {
                    writeln!(output, "{line}")?;
                }
                None
            }
            Err(err) => {
                log::error!("{err}");
                Some(err)
            }
        });
    };

    Ok(match egraph.parse_and_run_program(filename, command) {
        Ok(msgs) => {
            if mode != RunMode::NoMessages {
                for msg in msgs {
                    write!(output, "{msg}")?;
                }
            }
            if mode == RunMode::Interactive {
                writeln!(output, "(done)")?;
            }
            None
        }
        Err(err) => {
            log::error!("{err}");
            if mode == RunMode::Interactive {
                writeln!(output, "(error)")?;
            }
            Some(err)
        }
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum RunMode {
    Normal,
    ShowDesugaredEgglog,
    Interactive,
    NoMessages,
}

impl Display for RunMode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            RunMode::Normal => write!(f, "normal"),
            RunMode::ShowDesugaredEgglog => write!(f, "desugar"),
            RunMode::Interactive => write!(f, "interactive"),
            RunMode::NoMessages => write!(f, "no-messages"),
        }
    }
}

impl FromStr for RunMode {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "normal" => Ok(RunMode::Normal),
            "desugar" => Ok(RunMode::ShowDesugaredEgglog),
            "interactive" => Ok(RunMode::Interactive),
            "no-messages" => Ok(RunMode::NoMessages),
            _ => Err(format!("Unknown run mode: {s}")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_should_eval() {
        #[rustfmt::skip]
        let test_cases = vec![
            vec![
                "(extract",
                "\"1",
                ")",
                "(",
                ")))",
                "\"",
                ";; )",
                ")"
            ],
            vec![
                "(extract 1) (extract",
                "2) (",
                "extract 3) (extract 4) ;;;; ("
            ],
            vec![
                "(extract \"\\\")\")"
            ]];
        for test in test_cases {
            let mut cmd_buffer = String::new();
            for (i, line) in test.iter().enumerate() {
                cmd_buffer.push_str(line);
                cmd_buffer.push('\n');
                assert_eq!(should_eval(&cmd_buffer), i == test.len() - 1);
            }
        }
    }

    #[test]
    fn test_repl() {
        let mut egraph = EGraph::default();

        let input = "(extract 1)";
        let mut output = Vec::new();
        egraph
            .repl_with(input.as_bytes(), &mut output, RunMode::Normal, false)
            .unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), "1\n");

        let input = "\n\n\n";
        let mut output = Vec::new();
        egraph
            .repl_with(input.as_bytes(), &mut output, RunMode::Normal, false)
            .unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), "");

        let input = "(extract 1)";
        let mut output = Vec::new();
        egraph
            .repl_with(input.as_bytes(), &mut output, RunMode::Interactive, false)
            .unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), "1\n(done)\n");

        let input = "xyz";
        let mut output: Vec<u8> = Vec::new();
        egraph
            .repl_with(input.as_bytes(), &mut output, RunMode::Interactive, false)
            .unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), "(error)\n");

        let missing_include = std::env::temp_dir().join(format!(
            "egglog_missing_include_{}_{}.egg",
            std::process::id(),
            "repl_test"
        ));
        let input = format!(
            "(include \"{}\")",
            missing_include.to_string_lossy().replace('\\', "/")
        );
        let mut output = Vec::new();
        egraph
            .repl_with(input.as_bytes(), &mut output, RunMode::Interactive, false)
            .unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), "(error)\n");

        let input = "(extract 1)";
        let mut output = Vec::new();
        egraph
            .repl_with(
                input.as_bytes(),
                &mut output,
                RunMode::ShowDesugaredEgglog,
                false,
            )
            .unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), "(extract 1 0)\n");

        let input = "(extract 1)";
        let mut output = Vec::new();
        egraph
            .repl_with(input.as_bytes(), &mut output, RunMode::NoMessages, false)
            .unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), "");

        let input = "(extract 1)";
        let mut output = Vec::new();
        egraph
            .repl_with(input.as_bytes(), &mut output, RunMode::Normal, true)
            .unwrap();
        assert_eq!(
            String::from_utf8(output).unwrap(),
            format!("{}\n> 1\n> ", welcome_prompt())
        );
    }
}
