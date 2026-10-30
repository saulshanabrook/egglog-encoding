use crate::*;
use std::io::{self, BufRead, BufReader, IsTerminal, Read, Write};
use std::str::FromStr;

use clap::Parser;
use env_logger::Env;
use std::ffi::OsString;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(version = env!("FULL_VERSION"), about = env!("CARGO_PKG_DESCRIPTION"))]
struct Args {
    /// Directory for files when using `input` and `output` commands
    #[clap(short = 'F', long)]
    fact_directory: Option<PathBuf>,
    /// Turns off the seminaive optimization
    #[clap(long)]
    naive: bool,
    /// Uses tree decomposition during query planning, which is off by default.
    /// Tree decomposition splits a complex query into smaller independent
    /// subqueries and evaluates them separately. It has a better theoretical
    /// guarantee, but a bag's materialized boundary is routinely wider than the
    /// split saves, so without this flag the planner evaluates each query as a
    /// single bag.
    ///
    /// The `:no-decomp` label on a rule keeps decomposition off for that rule
    /// even when this flag is set.
    #[clap(long, conflicts_with = "no_decomp")]
    decomp: bool,
    /// Accepted and ignored: tree decomposition is already off by default. Kept
    /// so one command line can drive this build and an older one that still
    /// decomposes unless told not to.
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
    /// Prove every `check` and certify every `extract` outside `fail`.
    /// Commands inside `fail` retain their ordinary behavior.
    #[clap(long)]
    proof_testing: bool,
    /// Extract proofs for every `check` and `extract` outside `fail` without verifying them.
    /// Commands inside `fail` retain their ordinary behavior.
    #[clap(long, conflicts_with_all = ["proofs", "proof_testing"])]
    proof_extraction: bool,
}

/// Start a command-line interface for the E-graph.
///
/// This is what vanilla egglog uses, and custom egglog builds (i.e., "egglog batteries included")
/// should also call this function.
#[allow(clippy::disallowed_macros)]
pub fn cli(egraph: EGraph) {
    cli_from(egraph, std::env::args_os())
}

/// Run the standard CLI after an extension consumes its own arguments.
#[allow(clippy::disallowed_macros)]
pub fn cli_from<I, T>(egraph: EGraph, args: I)
where
    I: IntoIterator<Item = T>,
    T: Into<OsString> + Clone,
{
    cli_with_preprocessor_impl(egraph, args, |_, source| Ok(source.to_owned()), false);
}

/// Use the standard CLI with a source-to-source pass before parsing each input.
/// File names, serialization, reports, and evaluation retain normal CLI behavior.
/// The pass also receives each complete REPL input, with no file name.
/// Failed REPL inputs restore both the e-graph and the cloned pass state, including
/// when evaluation executed part of the input before failing. File inputs exit on
/// failure.
#[allow(clippy::disallowed_macros)]
pub fn cli_with_preprocessor<I, T>(
    egraph: EGraph,
    args: I,
    preprocess: impl FnMut(Option<String>, &str) -> Result<String, Error> + Clone,
) where
    I: IntoIterator<Item = T>,
    T: Into<OsString> + Clone,
{
    cli_with_preprocessor_impl(egraph, args, preprocess, true);
}

#[allow(clippy::disallowed_macros)]
fn cli_with_preprocessor_impl<I, T>(
    mut egraph: EGraph,
    args: I,
    mut preprocess: impl FnMut(Option<String>, &str) -> Result<String, Error> + Clone,
    transactional_repl: bool,
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

    if args.term_encoding {
        egraph = egraph.with_term_encoding_enabled();
    }

    if args.proofs {
        egraph = egraph.with_proofs_enabled();
    }

    if args.proof_testing {
        egraph = egraph.with_proofs_enabled();
        egraph = egraph.with_proof_testing();
    }

    if args.proof_extraction {
        egraph = egraph.with_proof_extraction();
    }

    egraph.set_num_threads(args.threads);
    egraph.fact_directory.clone_from(&args.fact_directory);
    egraph.seminaive = !args.naive;
    egraph.no_decomp = !args.decomp;
    egraph.set_report_level(args.report_level);
    if args.strict_mode {
        egraph.set_strict_mode(true);
    }
    if args.inputs.is_empty() {
        match egraph.repl_preprocessed(
            io::stdin(),
            io::stdout(),
            args.mode,
            io::stdin().is_terminal(),
            &mut preprocess,
            transactional_repl,
        ) {
            Ok(()) => {}
            Err(err) => {
                log::error!("{err}");
                std::process::exit(1)
            }
        }
    } else {
        for input in &args.inputs {
            let program = match std::fs::read_to_string(input) {
                Ok(program) => program,
                Err(e) => {
                    let arg = input.to_string_lossy();
                    log::error!("Failed to read file {arg}: {e}");
                    std::process::exit(1)
                }
            };

            match run_commands(
                &mut egraph,
                Some(input.to_string_lossy().into_owned()),
                &program,
                io::stdout(),
                args.mode,
                &mut preprocess,
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
                        input
                            .file_stem()
                            .map(|s| s.to_string_lossy())
                            .unwrap_or_default()
                    ))
                } else {
                    input.clone()
                };
                if args.to_dot {
                    let dot_path = serialize_filename.with_extension("dot");
                    if let Err(e) = serialized.to_dot_file(dot_path.clone()) {
                        log::error!("Failed to write dot file to {dot_path:?}: {e}");
                        std::process::exit(1)
                    }
                }
                if args.to_svg {
                    let svg_path = serialize_filename.with_extension("svg");
                    if let Err(e) = serialized.to_svg_file(svg_path.clone()) {
                        log::error!(
                            "Failed to write svg file to {svg_path:?}: {e}. Make sure you have the `dot` executable installed"
                        );
                        std::process::exit(1)
                    }
                }
                if args.to_json {
                    let json_path = serialize_filename.with_extension("json");
                    if let Err(e) = serialized.to_json_file(json_path.clone()) {
                        log::error!("Failed to write json file to {json_path:?}: {e}");
                        std::process::exit(1)
                    }
                }
            }
        }
    }

    if let Some(report_path) = args.save_report {
        let report = egraph.get_overall_run_report();
        let file = match std::fs::File::create(&report_path) {
            Ok(file) => file,
            Err(e) => {
                log::error!("Failed to create report file at {report_path:?}: {e}");
                std::process::exit(1)
            }
        };
        if let Err(e) = serde_json::to_writer(file, &report) {
            log::error!("Failed to serialize report: {e}");
            std::process::exit(1)
        }
        log::info!("Saved report to {report_path:?}");
    }

    if let Some(summary_path) = args.timing_summary {
        let summary = egraph.timing_summary().unwrap_or_else(|error| {
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
        output: W,
        mode: RunMode,
        is_terminal: bool,
    ) -> io::Result<()>
    where
        R: Read,
        W: Write,
    {
        self.repl_preprocessed(
            input,
            output,
            mode,
            is_terminal,
            &mut |_, source| Ok(source.to_owned()),
            false,
        )
    }

    fn repl_preprocessed<R: Read, W: Write>(
        &mut self,
        input: R,
        mut output: W,
        mode: RunMode,
        is_terminal: bool,
        preprocess: &mut (impl FnMut(Option<String>, &str) -> Result<String, Error> + Clone),
        transactional: bool,
    ) -> io::Result<()> {
        let mut run = |egraph: &mut Self, source: &str, output: &mut W| {
            let checkpoint = transactional.then(|| (egraph.clone(), preprocess.clone()));
            let result = run_commands(egraph, None, source, output, mode, preprocess);
            if !matches!(result, Ok(None))
                && let Some((previous_graph, previous_pass)) = checkpoint
            {
                *egraph = previous_graph;
                *preprocess = previous_pass;
            }
            result.map(|_| ())
        };
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
                run(self, &cmd_buffer, &mut output)?;
                cmd_buffer = String::new();
                if is_terminal {
                    output.write_all(b"> ")?;
                    output.flush()?;
                }
            }
        }

        if !cmd_buffer.is_empty() {
            run(self, &cmd_buffer, &mut output)?;
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
    preprocess: &mut impl FnMut(Option<String>, &str) -> Result<String, Error>,
) -> io::Result<Option<Error>>
where
    W: Write,
{
    let command = match preprocess(filename.clone(), command) {
        Ok(source) => source,
        Err(err) => {
            log::error!("{err}");
            if mode == RunMode::Interactive {
                writeln!(output, "(error)")?;
            }
            return Ok(Some(err));
        }
    };
    if mode == RunMode::ShowDesugaredEgglog {
        return Ok(match egraph.resolve_program(filename, &command) {
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

    Ok(match egraph.parse_and_run_program(filename, &command) {
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
    fn tree_decomposition_is_opt_in_on_the_cli() {
        let args = Args::try_parse_from(["egglog"]).unwrap();
        assert!(!args.decomp);
        let args = Args::try_parse_from(["egglog", "--decomp"]).unwrap();
        assert!(args.decomp);
        let args = Args::try_parse_from(["egglog", "--no-decomp"]).unwrap();
        assert!(!args.decomp);

        let error = Args::try_parse_from(["egglog", "--decomp", "--no-decomp"])
            .expect_err("decomposition flags should conflict");
        assert_eq!(error.kind(), clap::error::ErrorKind::ArgumentConflict);
    }

    #[test]
    fn proof_extraction_is_a_distinct_cli_mode() {
        let args = Args::try_parse_from(["egglog", "--proof-extraction"]).unwrap();
        assert!(args.proof_extraction);

        for conflicting in ["--proofs", "--proof-testing"] {
            let error = Args::try_parse_from(["egglog", "--proof-extraction", conflicting])
                .expect_err("proof extraction should conflict with other proof modes");
            assert_eq!(error.kind(), clap::error::ErrorKind::ArgumentConflict);
        }
    }

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
