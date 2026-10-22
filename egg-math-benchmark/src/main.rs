use anyhow::{Context, Result, ensure};
use clap::{Parser, ValueEnum};
use egg::{RecExpr, Runner, SimpleScheduler, StopReason};
use egglog_reports::{RulesetTimingRecord, RulesetTimingRole, TimingSummary};
use std::{
    fs::File,
    io::BufWriter,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

mod math;

use math::Math;

#[global_allocator]
static ALLOCATOR: benchmark_memory::LimitedAllocator = benchmark_memory::LimitedAllocator;

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
#[command(
    about = "Run the fixed PLDI 2023 Math workload with current egg",
    after_help = "Native memory option: --memory-limit-bytes <N>"
)]
struct Args {
    #[arg(long, value_enum, default_value_t)]
    proof_mode: ProofMode,
    #[arg(long)]
    timing_summary: Option<PathBuf>,
}

fn main() -> Result<()> {
    let args = Args::parse_from(benchmark_memory::configure(std::env::args_os()));
    let (timing, _, check_passed) = run_math(args.proof_mode, ITERATIONS)?;
    ensure!(
        check_passed,
        "terminal equality is not established after iteration 11"
    );
    if let Some(path) = args.timing_summary {
        write_timing_summary(&path, &timing)?;
    }
    Ok(())
}

// The executable always passes ITERATIONS; the private cutoff also supports
// the test immediately before the fixed witness becomes established.
fn run_math(
    proof_mode: ProofMode,
    iterations: usize,
) -> Result<(TimingSummary, egg::EGraph<Math, ()>, bool)> {
    let left: RecExpr<Math> = CHECK_LEFT.parse().expect("fixed left check must parse");
    let right: RecExpr<Math> = CHECK_RIGHT.parse().expect("fixed right check must parse");
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

    #[cfg(test)]
    let before = tests::native_graph_size(&runner.egraph);
    // Queries must not insert an absent witness before attempting explanation.
    let left_id = runner.egraph.lookup_expr(&left);
    let right_id = runner.egraph.lookup_expr(&right);
    let check_passed = matches!((left_id, right_id), (Some(left), Some(right))
        if runner.egraph.find(left) == runner.egraph.find(right));

    let proof_postprocessing_started = Instant::now();
    let proof_postprocessing =
        if check_passed && matches!(proof_mode, ProofMode::Extract | ProofMode::Check) {
            let mut explanation = runner.explain_equivalence(&left, &right);
            explanation.make_flat_explanation();
            if proof_mode == ProofMode::Check {
                explanation.check_proof(&rules);
            }
            proof_postprocessing_started.elapsed()
        } else {
            Duration::ZERO
        };

    #[cfg(test)]
    assert_eq!(
        before,
        tests::native_graph_size(&runner.egraph),
        "native {proof_mode:?} query/explanation changed the logical graph at {iterations}",
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
    Ok((timing, runner.egraph, check_passed))
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

#[cfg(test)]
mod tests {
    use super::*;
    use egglog_experimental::{CommandOutput, EGraph, Error, Read};
    use std::collections::{BTreeMap, HashSet};

    #[test]
    fn fixed_math_witness_has_iteration_boundary_and_graph_parity() {
        let fixture =
            include_str!("../../egglog-experimental/tests/math-microbenchmark-rational.egg");
        let (setup, check) = fixture.split_once("(run 11)").unwrap();
        // Keep these memory-intensive comparisons sequential and drop each
        // native graph before constructing the corresponding Egglog graph.
        for proof_mode in [ProofMode::Off, ProofMode::Check] {
            for iterations in [10, 11] {
                let (timing, native, check_passed) = run_math(proof_mode, iterations).unwrap();
                assert_eq!(check_passed, iterations == 11);
                let expected = native_graph_size(&native);
                assert_eq!(
                    expected.0.values().sum::<usize>(),
                    native.total_number_of_nodes()
                );
                assert_eq!(
                    timing.commands_other_ns > 0,
                    proof_mode == ProofMode::Check && check_passed,
                    "native checked mode must extract and check the established witness",
                );
                drop(native);

                let mut egglog = match proof_mode {
                    ProofMode::Off => egglog_experimental::new_experimental_egraph(),
                    ProofMode::Check => {
                        egglog_experimental::new_experimental_egraph_with_proof_testing()
                    }
                    _ => unreachable!("this comparison exercises off and fully checked modes"),
                };
                egglog
                    .parse_and_run_program(None, &format!("{setup}(run {iterations})"))
                    .unwrap();
                let before = egglog_graph_size(&egglog);
                let result = egglog.parse_and_run_program(None, check);
                if iterations == 10 {
                    match result.unwrap_err() {
                        Error::CheckError(..) => assert_eq!(proof_mode, ProofMode::Off),
                        Error::ProofError { error, .. } => {
                            assert_eq!(proof_mode, ProofMode::Check);
                            assert!(
                                error.to_string().starts_with(
                                    "Could not find a proof due to query not matching "
                                )
                            );
                        }
                        error => panic!("expected an unestablished equality: {error}"),
                    }
                } else {
                    let proofs = result
                        .unwrap()
                        .iter()
                        .filter(|output| matches!(output, CommandOutput::ProveExists { .. }))
                        .count();
                    assert_eq!(proofs, usize::from(proof_mode == ProofMode::Check));
                }
                assert_eq!(
                    before,
                    egglog_graph_size(&egglog),
                    "Egglog {proof_mode:?} query/proof changed the logical graph at {iterations}",
                );
                assert_eq!(
                    expected, before,
                    "Egg/Egglog {proof_mode:?} constructor or class counts differ at {iterations}",
                );
                eprintln!(
                    "{proof_mode:?}/{iterations}: witness={check_passed}, {} constructors, {} classes; per-constructor parity and query/proof non-insertion verified",
                    before.0.values().sum::<usize>(),
                    before.1,
                );
            }
        }
    }

    pub(super) fn native_graph_size(
        egraph: &egg::EGraph<Math, ()>,
    ) -> (BTreeMap<String, usize>, usize) {
        let mut constructors: BTreeMap<_, _> = [
            "Diff", "Integral", "Add", "Sub", "Mul", "Div", "Pow", "Ln", "Sqrt", "Sin", "Cos",
            "Const", "Var",
        ]
        .into_iter()
        .map(|name| (name.to_owned(), 0))
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
            *constructors.get_mut(name).unwrap() += 1;
        }
        (constructors, egraph.number_of_classes())
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
                        // Visible rebuilt rows expose canonical Math classes,
                        // excluding historical encoding rows and proof helpers.
                        classes.insert(node.eclass);
                    })
                    .unwrap();
                assert_eq!(rows, *count);
            }
        });
        (constructors, classes.len())
    }
}
