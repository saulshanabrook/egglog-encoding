use anyhow::{Context, Result, ensure};
use clap::{Parser, ValueEnum};
use egg::{RecExpr, Runner, SimpleScheduler, StopReason};
use egglog_reports::{RulesetTimingRecord, RulesetTimingRole, TimingSummary};
use std::{
    collections::BTreeMap,
    fs::File,
    io::BufWriter,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

mod math;

use math::Math;

const ITERATIONS: usize = 11;
const CHECK_LEFT: &str = "(+ (cos x) (cos x))";
const CHECK_RIGHT: &str = "(d x (+ (sin x) (sin x)))";

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
enum ProofMode {
    #[default]
    Off,
    Enabled,
    Extract,
    Check,
}

#[derive(Debug, Parser)]
#[command(about = "Run the PLDI 2023 Math rules and seeds with current egg")]
struct Args {
    #[arg(long, value_enum, default_value_t)]
    proof_mode: ProofMode,
    #[arg(long)]
    timing_summary: Option<PathBuf>,
    /// Number of complete simple-scheduler iterations (zero inspects the seeds).
    #[arg(long, default_value_t = ITERATIONS)]
    iterations: usize,
    #[arg(long, default_value = CHECK_LEFT)]
    check_left: String,
    #[arg(long, default_value = CHECK_RIGHT)]
    check_right: String,
    /// Untimed validation only: write logical graph sizes around the check/proof.
    #[arg(long)]
    diagnostic_output: Option<PathBuf>,
    /// Untimed validation only: require the equality to be absent at this cutoff.
    #[arg(long, requires = "diagnostic_output")]
    expect_check_failure: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let (timing, _) = run_math(&args)?;
    if let Some(path) = args.timing_summary {
        write_timing_summary(&path, &timing)?;
    }
    Ok(())
}

fn run_math(args: &Args) -> Result<(TimingSummary, egg::EGraph<Math, ()>)> {
    let left: RecExpr<Math> = args
        .check_left
        .parse()
        .context("invalid left check expression")?;
    let right: RecExpr<Math> = args
        .check_right
        .parse()
        .context("invalid right check expression")?;
    let iterations = args.iterations;
    let proof_mode = args.proof_mode;
    let rules = math::rules();
    let mut runner = Runner::default()
        .with_scheduler(SimpleScheduler)
        .with_iter_limit(iterations)
        .with_node_limit(usize::MAX)
        .with_time_limit(Duration::MAX);
    if proof_mode != ProofMode::Off {
        runner = runner
            .with_explanations_enabled()
            .without_explanation_length_optimization();
    }
    for start in math::START_EXPRESSIONS {
        let expression = start.parse().expect("fixed Math seed must parse");
        runner = runner.with_expr(&expression);
    }
    if iterations == 0 {
        // Runner::run records a stopped iteration even for a zero limit. Rebuild
        // just the seeds so checkpoint zero really performs no rule iterations.
        runner.egraph.rebuild();
        runner.stop_reason = Some(StopReason::IterationLimit(0));
    } else {
        runner = runner.run(&rules);
    }

    let report = runner.report();
    ensure!(
        report.iterations == iterations,
        "egg stopped after {} of {iterations} required iterations: {:?}",
        report.iterations,
        report.stop_reason
    );
    ensure!(
        matches!(report.stop_reason, StopReason::IterationLimit(limit) if limit == iterations),
        "egg did not stop at the requested iteration limit: {:?}",
        report.stop_reason
    );

    let before = args
        .diagnostic_output
        .as_ref()
        .map(|_| graph_size(&runner.egraph));
    // Lookup must precede explain_equivalence: explaining arbitrary expressions
    // can otherwise insert them, making an absent checkpoint witness look valid.
    let left_id = runner.egraph.lookup_expr(&left);
    let right_id = runner.egraph.lookup_expr(&right);
    let check_passed = matches!((left_id, right_id), (Some(left), Some(right))
        if runner.egraph.find(left) == runner.egraph.find(right));

    let proof_postprocessing_started = Instant::now();
    let proof_postprocessing = if check_passed
        && !args.expect_check_failure
        && matches!(proof_mode, ProofMode::Extract | ProofMode::Check)
    {
        let mut explanation = runner.explain_equivalence(&left, &right);
        explanation.make_flat_explanation();
        if proof_mode == ProofMode::Check {
            explanation.check_proof(&rules);
        }
        proof_postprocessing_started.elapsed()
    } else {
        Duration::ZERO
    };

    if let Some(path) = &args.diagnostic_output {
        let (nodes_before, classes_before) = before.unwrap();
        let (nodes_after, classes_after) = graph_size(&runner.egraph);
        let diagnostic = serde_json::json!({
            "iterations": report.iterations,
            "stop_reason": format!("{:?}", report.stop_reason),
            "check_passed": check_passed,
            "left_present": left_id.is_some(),
            "right_present": right_id.is_some(),
            "before": {"constructors": nodes_before, "classes": classes_before},
            "after": {"constructors": nodes_after, "classes": classes_after},
        });
        serde_json::to_writer_pretty(BufWriter::new(File::create(path)?), &diagnostic)?;
        ensure!(
            nodes_before == nodes_after && classes_before == classes_after,
            "checking or extracting the witness changed the logical graph"
        );
    }
    ensure!(
        check_passed != args.expect_check_failure,
        "witness equality {} after iteration {iterations} (left present: {}, right present: {})",
        if check_passed {
            "unexpectedly established"
        } else {
            "not established"
        },
        left_id.is_some(),
        right_id.is_some()
    );

    let timing = TimingSummary {
        schema_version: TimingSummary::SCHEMA_VERSION,
        typecheck_ns: 0,
        frontend_parse_ns: 0,
        frontend_other_ns: 0,
        frontend_install_ns: 0,
        commands_actions_ns: 0,
        commands_check_ns: 0,
        commands_other_ns: proof_postprocessing.as_nanos().min(u64::MAX as u128) as u64,
        native_rebuild_ns: seconds_to_ns(report.rebuild_time),
        rulesets: vec![RulesetTimingRecord {
            name: String::new(),
            role: RulesetTimingRole::Program,
            assembly_ns: 0,
            search_ns: seconds_to_ns(report.search_time),
            apply_ns: seconds_to_ns(report.apply_time),
            execution_ns: seconds_to_ns(
                (report.total_time - report.search_time - report.apply_time - report.rebuild_time)
                    .max(0.0),
            ),
            merge_ns: 0,
        }],
    };
    Ok((timing, runner.egraph))
}

fn write_timing_summary(path: &Path, timing: &TimingSummary) -> Result<()> {
    let file = File::create(path)
        .with_context(|| format!("failed to create timing summary {}", path.display()))?;
    serde_json::to_writer(BufWriter::new(file), timing)
        .with_context(|| format!("failed to write timing summary {}", path.display()))
}

fn seconds_to_ns(seconds: f64) -> u64 {
    if !seconds.is_finite() || seconds <= 0.0 {
        return 0;
    }
    (seconds * 1_000_000_000.0).min(u64::MAX as f64) as u64
}

fn graph_size(egraph: &egg::EGraph<Math, ()>) -> (BTreeMap<&'static str, usize>, usize) {
    let mut egg_nodes: BTreeMap<&'static str, usize> = [
        "Diff", "Integral", "Add", "Sub", "Mul", "Div", "Pow", "Ln", "Sqrt", "Sin", "Cos", "Const",
        "Var",
    ]
    .into_iter()
    .map(|name| (name, 0))
    .collect();
    for node in egraph.classes().flat_map(|class| &class.nodes) {
        let name = match node {
            Math::Diff(_) => "Diff",
            Math::Integral(_) => "Integral",
            Math::Add(_) => "Add",
            Math::Sub(_) => "Sub",
            Math::Mul(_) => "Mul",
            Math::Div(_) => "Div",
            Math::Pow(_) => "Pow",
            Math::Ln(_) => "Ln",
            Math::Sqrt(_) => "Sqrt",
            Math::Sin(_) => "Sin",
            Math::Cos(_) => "Cos",
            Math::Constant(_) => "Const",
            Math::Symbol(_) => "Var",
        };
        *egg_nodes.get_mut(name).unwrap() += 1;
    }
    (egg_nodes, egraph.number_of_classes())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_iterations_does_not_apply_the_first_rewrite() {
        for mode in ["off", "extract", "check"] {
            let mut args = Args::parse_from([
                "egg-math-benchmark",
                "--iterations",
                "0",
                "--proof-mode",
                mode,
                "--check-left",
                "(i (+ x (cos x)) x)",
                "--check-right",
                "(+ (i x x) (i (cos x) x))",
            ]);
            let error = run_math(&args).unwrap_err().to_string();
            assert!(error.contains("witness equality not established after iteration 0"));
            args.iterations = 1;
            run_math(&args).unwrap();
        }
    }

    #[test]
    fn fixed_math_workload_matches_egglog_after_iteration_eleven() {
        let fixture =
            include_str!("../../egglog-experimental/tests/math-microbenchmark-rational.egg");
        for proof_mode in [ProofMode::Off, ProofMode::Extract, ProofMode::Check] {
            let mut args = Args::parse_from(["egg-math-benchmark"]);
            args.proof_mode = proof_mode;
            let (_, egraph) = run_math(&args).unwrap();
            assert_matches_egglog(&egraph, proof_mode, fixture);
        }
    }

    fn assert_matches_egglog(egraph: &egg::EGraph<Math, ()>, proof_mode: ProofMode, fixture: &str) {
        let (egg_nodes, classes) = graph_size(egraph);
        let egg_nodes = egg_nodes
            .into_iter()
            .map(|(name, count)| (name.to_owned(), count))
            .collect::<BTreeMap<_, _>>();
        let total = egg_nodes.values().sum::<usize>();
        assert_eq!(total, egraph.total_number_of_nodes());
        let mut egglog = if proof_mode == ProofMode::Off {
            egglog_experimental::new_experimental_egraph()
        } else {
            // The CLI's extraction-only configuration is crate-private. Strict proof
            // testing performs the same extraction and also validates its proof;
            // the plotted --proof-extraction mode is checked separately via the CLI.
            egglog_experimental::new_experimental_egraph_with_proof_testing()
        };
        egglog.parse_and_run_program(None, fixture).unwrap();
        let egglog_experimental::CommandOutput::PrintAllFunctionsSize(table_sizes) =
            egglog.print_size(None).unwrap()
        else {
            unreachable!("print-size without a table always returns all table sizes");
        };
        // print_size selects canonical views in proof mode, excluding the permanent
        // term rows and auxiliary proof tables. Declared zero-size tables stay present.
        let egglog_nodes = table_sizes.into_iter().collect::<BTreeMap<_, _>>();

        assert_eq!(
            egg_nodes, egglog_nodes,
            "egg {proof_mode:?} enodes and egglog visible constructor rows differ"
        );
        eprintln!(
            "Math parity {proof_mode:?}: {egg_nodes:?}; total={total}; classes={}",
            classes
        );
    }
}
