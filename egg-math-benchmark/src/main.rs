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
#[command(about = "Run the fixed PLDI 2023 Math workload with current egg")]
struct Args {
    #[arg(long, value_enum, default_value_t)]
    proof_mode: ProofMode,
    #[arg(long)]
    timing_summary: Option<PathBuf>,
    /// Untimed validation only: inspect the fixed witness at iteration 10 or 11.
    #[arg(long, requires = "diagnostic_output", value_parser = clap::value_parser!(u8).range(10..=11))]
    iterations: Option<u8>,
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
    let left: RecExpr<Math> = CHECK_LEFT.parse().expect("fixed left check must parse");
    let right: RecExpr<Math> = CHECK_RIGHT.parse().expect("fixed right check must parse");
    let iterations = args.iterations.map_or(ITERATIONS, usize::from);
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
    runner = runner.run(&rules);

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

    let before =
        (cfg!(test) || args.diagnostic_output.is_some()).then(|| graph_size(&runner.egraph));
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

    if let Some((nodes_before, classes_before)) = before {
        let (nodes_after, classes_after) = graph_size(&runner.egraph);
        if let Some(path) = &args.diagnostic_output {
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
        }
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
    use egglog_experimental::{CommandOutput, EGraph, Error, Read};
    use std::collections::HashSet;

    #[test]
    fn fixed_math_witness_has_iteration_boundary_and_graph_parity() {
        let fixture =
            include_str!("../../egglog-experimental/tests/math-microbenchmark-rational.egg");
        let (setup, check) = fixture.split_once("(run 11)").unwrap();
        // One test keeps these memory-intensive comparisons sequential.
        for proof_mode in [
            ProofMode::Off,
            ProofMode::Enabled,
            ProofMode::Extract,
            ProofMode::Check,
        ] {
            for iterations in [10, 11] {
                let mut args = Args::parse_from(["egg-math-benchmark"]);
                args.proof_mode = proof_mode;
                args.iterations = Some(iterations);
                args.expect_check_failure = iterations == 10;
                let (_, native) = run_math(&args).unwrap();
                let (nodes, classes) = graph_size(&native);
                assert_eq!(
                    nodes.values().sum::<usize>(),
                    native.total_number_of_nodes()
                );
                let expected = (
                    nodes
                        .into_iter()
                        .map(|(name, count)| (name.to_owned(), count))
                        .collect::<BTreeMap<_, _>>(),
                    classes,
                );
                drop(native);

                let mut egglog = match proof_mode {
                    ProofMode::Off => egglog_experimental::new_experimental_egraph(),
                    ProofMode::Enabled => {
                        egglog_experimental::new_experimental_egraph_with_proofs()
                    }
                    // The extraction-only builder is crate-private. Strict mode
                    // exercises the same extraction and additionally checks it;
                    // the exact --proof-extraction mode is covered by CLI smoke.
                    ProofMode::Extract | ProofMode::Check => {
                        egglog_experimental::new_experimental_egraph_with_proof_testing()
                    }
                };
                egglog
                    .parse_and_run_program(None, &format!("{setup}(run {iterations})"))
                    .unwrap();
                let before = egglog_graph_size(&egglog);
                let result = egglog.parse_and_run_program(None, check);
                if iterations == 10 {
                    match result.unwrap_err() {
                        Error::CheckError(..) => {
                            assert!(matches!(proof_mode, ProofMode::Off | ProofMode::Enabled));
                        }
                        Error::ProofError { error, .. } => {
                            assert!(matches!(proof_mode, ProofMode::Extract | ProofMode::Check));
                            assert!(
                                error.to_string().starts_with(
                                    "Could not find a proof due to query not matching "
                                )
                            );
                        }
                        error => panic!("expected an unestablished equality: {error}"),
                    }
                } else {
                    let outputs = result.unwrap();
                    assert_eq!(
                        outputs
                            .iter()
                            .any(|output| matches!(output, CommandOutput::ProveExists { .. })),
                        matches!(proof_mode, ProofMode::Extract | ProofMode::Check),
                    );
                }
                assert_eq!(
                    before,
                    egglog_graph_size(&egglog),
                    "Egglog {proof_mode:?} check/proof changed the logical graph at {iterations}",
                );
                assert_eq!(
                    expected, before,
                    "Egg/Egglog {proof_mode:?} constructor or class counts differ at {iterations}",
                );
            }
        }
    }

    fn egglog_graph_size(egraph: &EGraph) -> (BTreeMap<String, usize>, usize) {
        let CommandOutput::PrintAllFunctionsSize(table_sizes) = egraph.print_size(None).unwrap()
        else {
            unreachable!("print-size without a table always returns all table sizes");
        };
        let constructors = table_sizes.into_iter().collect::<BTreeMap<_, _>>();
        let mut classes = HashSet::new();
        egraph.read(|state| {
            for (name, count) in &constructors {
                let mut rows = 0;
                state
                    .constructor_enodes(name, |node| {
                        rows += 1;
                        // Rebuilt visible views contain canonical Math outputs,
                        // excluding historical term rows and auxiliary proofs.
                        classes.insert(node.eclass);
                    })
                    .unwrap();
                assert_eq!(rows, *count);
            }
        });
        (constructors, classes.len())
    }
}
