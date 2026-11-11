//! Paper coverage is driven by the figure catalog and the shared ignore file.
//! Trials run in isolated processes. Native Math references run uncapped;
//! source executions retain the configured local allocator cap.
use egglog::{CommandOutput, Read};
use egglog_experimental::{EGraph, new_experimental_egraph_with_options};
use libtest_mimic::Trial;
use serde::Deserialize;
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    io::{Read as _, Seek},
    path::{Path, PathBuf},
    process::Command as Process,
    time::{Duration, Instant},
};

#[path = "../../../egglog-experimental/tests/support/extraction.rs"]
mod extraction;
#[path = "../../../egglog-experimental/tests/support/extraction_comparison.rs"]
mod extraction_comparison;
#[path = "support/paper_oracles.rs"]
mod paper_oracles;
#[path = "support/table_comparison.rs"]
mod table_comparison;

#[global_allocator]
static ALLOCATOR: benchmark_memory::LimitedAllocator = benchmark_memory::LimitedAllocator;
// Correctness adds extraction clones, proof checks, and native reference oracles.
const CORRECTNESS_TIMEOUT_FACTOR: u32 = 3;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Ignore {
    file: String,
    #[serde(default)]
    treatments: Vec<String>,
    kind: String,
    reason: String,
    evidence: String,
    memory_limit_bytes: Option<u64>,
    expected_table_sizes: Option<BTreeMap<String, (usize, usize)>>,
    #[serde(skip)]
    matched: BTreeSet<PathBuf>,
}

#[derive(Debug, PartialEq, Eq)]
struct Observations {
    /// Final row counts of source-visible tables, excluding encoding/proof internals.
    tables: BTreeMap<String, usize>,
    /// Distinct logical e-classes among constructor rows, populated only for
    /// the native Math12 comparison.
    math_eclass_count: Option<usize>,
    /// Outputs comparable across ordinary, term and strict proof modes: omit
    /// timings, print-function, proof certificates and extraction variants;
    /// render best extractions as costs. Actual extracted terms are checked below.
    stable_outputs: String,
    /// Terms and variant order are compared in addition to best-term costs.
    extractions: Vec<extraction_comparison::Extraction>,
    /// Per extraction, whether the other mode's best term was checked equal to
    /// this run's requested root. None means no alternative needed checking.
    comparison_in_root_class: Vec<Option<bool>>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofSummary {
    schema_version: usize,
    success: bool,
    check_requests: usize,
    extraction_requests: usize,
    produced_certificates: usize,
    verified_certificates: usize,
}

fn checked_summary(path: &Path) -> ProofSummary {
    let summary: ProofSummary =
        serde_json::from_reader(std::fs::File::open(path).unwrap()).unwrap();
    assert_eq!(summary.schema_version, 1);
    assert!(summary.success, "proof validation did not succeed");
    assert!(summary.check_requests + summary.extraction_requests > 0);
    assert_eq!(summary.produced_certificates, summary.verified_certificates);
    summary
}

/// The full author input and both canaries use the same CSV/certificate contract.
fn check_author_input(
    root: &Path,
    mode: &str,
    input: &Path,
    base: usize,
    diseq_num: usize,
    contradiction: &str,
    sizes: Option<(usize, usize)>,
) {
    let proofs = mode == "egg-nee-proof-testing";
    let binary = root
        .join("benchmarks/local/parameter-native/target/release")
        .join(if proofs { "egg-nee-proofs" } else { mode });
    let method = match mode {
        "egg-de" => "de",
        "egg-ee" => "ee",
        "egg-nee" => "nee-no-saturation",
        "egg-oee" => "nee-with-saturation",
        "egg-nee-proof-testing" => "nee-proofs",
        _ => panic!("unmapped author driver {mode}"),
    };
    let directory = tempfile::tempdir().unwrap();
    let proof_path = directory.path().join("proof-summary.json");
    let mut command = Process::new(&binary);
    command
        .arg(input)
        .arg(base.to_string())
        .arg(diseq_num.to_string());
    if proofs {
        command
            .args(["--proof-mode", "check", "--proof-summary"])
            .arg(&proof_path);
    }
    let output = command.output().unwrap_or_else(|error| {
        panic!(
            "{}: {error}; run make check to prepare author drivers",
            binary.display()
        )
    });
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    let mut rows = text.lines();
    let headers: Vec<_> = rows.next().unwrap().split(',').collect();
    let values: Vec<_> = rows.next().unwrap().split(',').collect();
    assert_eq!(headers.len(), values.len());
    for (column, expected) in [("method", method), ("contradiction", contradiction)] {
        let index = headers.iter().position(|&name| name == column).unwrap();
        assert_eq!(
            values[index],
            expected,
            "{mode}: {} / {column}",
            input.display()
        );
    }
    let mut counts = vec![("base", base), ("diseq_num", diseq_num)];
    if let Some((nodes, classes)) = sizes {
        counts.extend([("number_nodes", nodes), ("number_classes", classes)]);
    }
    for (column, expected) in counts {
        let index = headers.iter().position(|&name| name == column).unwrap();
        assert_eq!(
            values[index].parse::<usize>().unwrap(),
            expected,
            "{mode}: {} / {column}",
            input.display()
        );
    }
    assert!(rows.next().is_none());
    if proofs {
        let summary = checked_summary(&proof_path);
        assert_eq!(
            (summary.check_requests, summary.extraction_requests),
            (1, 0)
        );
        assert_eq!(
            summary.produced_certificates,
            usize::from(contradiction == "Y")
        );
    }
}

fn observe(
    file: &Path,
    mode: &str,
    expected: Option<&Observations>,
    egraph_threads: usize,
) -> Observations {
    let mut graph = new_experimental_egraph_with_options(mode == "off");
    graph.set_num_threads(egraph_threads);
    graph = match mode {
        "off" => graph,
        "term" => graph.with_term_encoding_enabled(),
        "proof-testing" => graph.with_proofs_enabled().with_proof_testing(),
        _ => panic!("unsupported egglog correctness mode {mode}"),
    };
    let source = std::fs::read_to_string(file).unwrap();
    let commands = graph
        .parse_program(Some(file.display().to_string()), &source)
        .unwrap();
    let baseline_terms: Vec<_> = expected
        .into_iter()
        .flat_map(|expected| &expected.extractions)
        .map(|(cost, terms)| (cost.is_some() && terms.len() == 1).then(|| terms[0].as_str()))
        .collect();
    let checked =
        extraction::run_program_with_extract_checks(&mut graph, commands, &baseline_terms)
            .unwrap_or_else(|error| panic!("{} / {mode}: {error}", file.display()));
    let outputs = checked.outputs;
    let CommandOutput::PrintAllFunctionsSize(sizes) = graph.print_size(None).unwrap() else {
        unreachable!()
    };
    let extractions = extraction_comparison::observe(&outputs);
    Observations {
        math_eclass_count: file
            .ends_with("math-iteration-12.egg")
            .then(|| math_counts(&graph).1),
        tables: sizes.into_iter().collect(),
        stable_outputs: CommandOutput::snapshot_non_proof_stable_under_proof_encoding(&outputs),
        extractions,
        comparison_in_root_class: checked.comparison_in_root_class,
    }
}

fn math_counts(graph: &EGraph) -> (BTreeMap<String, usize>, usize) {
    let CommandOutput::PrintAllFunctionsSize(sizes) = graph.print_size(None).unwrap() else {
        unreachable!()
    };
    let constructors: BTreeMap<_, _> = sizes.into_iter().collect();
    let mut classes = HashSet::new();
    graph.read(|state| {
        for (name, count) in &constructors {
            let mut rows = 0;
            state
                .constructor_enodes(name, |node| {
                    rows += 1;
                    classes.insert(node.eclass);
                })
                .unwrap();
            assert_eq!(rows, *count);
        }
    });
    (constructors, classes.len())
}

fn check_case(root: &Path, file: &Path, requested: &BTreeSet<String>, egraph_threads: usize) {
    use slotted_reference::{Matcher, Substitution};
    let requested = paper_oracles::correctness_modes(requested.iter().map(String::as_str));
    paper_oracles::validate(root, file, &requested).unwrap();
    if requested.iter().any(|mode| mode.starts_with("slotted")) {
        let source = std::fs::read_to_string(file).unwrap();
        let frozen = std::fs::read_to_string(file.with_extension("ref")).unwrap();
        // The generator's standalone fixtures contain exactly one positive run.
        // Parse its source forms rather than matching text in comments or strings.
        let forms = egglog::ast::parse_sexps(Some(file.display().to_string()), &source).unwrap();
        let runs: Vec<_> = forms
            .iter()
            .enumerate()
            .filter_map(|(i, form)| {
                let (name, args, _) = form.expect_call("workload command").unwrap();
                if name != "run" {
                    return None;
                }
                assert_eq!(args.len(), 1);
                let n = args[0].expect_uint::<usize>("run budget").unwrap();
                (n > 0).then_some((i, n))
            })
            .collect();
        assert_eq!(
            runs.len(),
            1,
            "frozen workload must have exactly one positive run"
        );
        let (boundary, budget) = runs[0];
        let rendered: Vec<_> = forms
            .iter()
            .map(|form| form.span().string().to_owned())
            .collect();
        let before = rendered[..=boundary].join("\n");
        let tail = rendered[boundary + 1..].join("\n");
        for (name, no_aliasing) in [
            ("slotted-proof-testing", false),
            ("slotted-proof-testing-no-aliasing", true),
        ] {
            if !requested.contains(name) {
                continue;
            }
            use egglog_experimental::slotted::{
                Compiler, Options, ProofMode, new_egraph_with_proofs,
            };
            let mut compiler = Compiler::new(Options {
                no_aliasing,
                proof_mode: ProofMode::Prove,
            });
            let mut graph = new_egraph_with_proofs();
            graph.set_num_threads(egraph_threads);
            let summary = graph
                .extension_state_or_default::<egglog::proof_summary::ProofSummary>()
                .clone();
            let program = compiler.compile_program(None, &source).unwrap();
            let outputs = program.run(&mut graph).unwrap();
            let directory = tempfile::tempdir().unwrap();
            let path = directory.path().join("proof-summary.json");
            summary.write(&path, true).unwrap();
            let summary = checked_summary(&path);
            assert!(
                summary.produced_certificates
                    >= summary.check_requests + summary.extraction_requests,
                "{name}: every executed source request needs a certificate"
            );
            assert_eq!(
                outputs
                    .iter()
                    .filter(|o| matches!(o, CommandOutput::UserDefined(_)))
                    .count(),
                summary.check_requests + summary.extraction_requests,
                "{name}: every executed source request must produce checked proofs"
            );
        }
        let mut counts = BTreeMap::new();
        for (name, nested) in [("slotted", false), ("slotted-no-aliasing", true)] {
            if !requested.contains(name) {
                continue;
            }
            eprintln!("Validating {name}");
            let mut compiler = egglog_experimental::slotted::Compiler::new(
                egglog_experimental::slotted::Options {
                    no_aliasing: nested,
                    ..Default::default()
                },
            );
            let mut graph = egglog_experimental::slotted::new_egraph();
            graph.set_num_threads(egraph_threads);
            let lowered = compiler.compile(None, &before).unwrap();
            graph.parse_and_run_program(None, &lowered).unwrap();
            let size = egglog_experimental::slotted::export::counts(&graph).unwrap();
            counts.insert(nested, (size.classes, size.nodes));
            let lowered = compiler.compile(None, &tail).unwrap();
            graph.parse_and_run_program(None, &lowered).unwrap();
        }
        for (name, matcher, policy, proofs) in [
            (
                "slotted-ref-multi",
                Matcher::Multi,
                Substitution::Snapshot,
                false,
            ),
            (
                "slotted-ref-nested-snapshot",
                Matcher::Nested,
                Substitution::Snapshot,
                false,
            ),
            (
                "slotted-ref-nested",
                Matcher::Nested,
                Substitution::Syntactic,
                false,
            ),
            (
                "slotted-ref-multi-proof-testing",
                Matcher::Multi,
                Substitution::Snapshot,
                true,
            ),
            (
                "slotted-ref-nested-proof-testing",
                Matcher::Nested,
                Substitution::Syntactic,
                true,
            ),
        ] {
            if !requested.contains(name) {
                continue;
            }
            eprintln!("Validating {name}");
            let spec = slotted_reference::select_frozen_spec(&frozen, matcher).unwrap();
            let budgets: Vec<_> = spec
                .lines()
                .filter_map(|line| line.strip_prefix("rounds "))
                .collect();
            assert_eq!(
                budgets,
                [budget.to_string()],
                "source/reference schedule mismatch"
            );
            let native =
                slotted_reference::run_spec(&spec, policy, slotted_reference::ProofMode::Off)
                    .unwrap();
            assert!(
                !native.goals.is_empty(),
                "paper workloads must prescribe a goal"
            );
            assert!(
                native.goals.iter().all(|&goal| goal),
                "{name} did not establish the prescribed target"
            );
            if proofs {
                // Keep explanation tracking out of the large proof-off oracles in
                // this package. The separate native binary owns its proof feature.
                let executable = std::env::current_exe().unwrap();
                let binary = executable.parent().unwrap().parent().unwrap().join(format!(
                    "slotted-reference-proofs{}",
                    std::env::consts::EXE_SUFFIX
                ));
                let directory = tempfile::tempdir().unwrap();
                let proof_path = directory.path().join("proof-summary.json");
                let output = Process::new(&binary)
                    .args([
                        "--matcher",
                        if matcher == Matcher::Multi { "multi" } else { "nested" },
                        "--substitution",
                        if policy == Substitution::Snapshot { "snapshot" } else { "syntactic" },
                        "--proof-mode",
                        "check",
                        "--proof-summary",
                    ])
                    .arg(&proof_path)
                    .arg(file.with_extension("ref"))
                    .output()
                    .unwrap_or_else(|error| panic!("{}: {error}; build slotted-reference-proofs separately before paper tests", binary.display()));
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let text = String::from_utf8(output.stdout).unwrap();
                let goals: Vec<_> = text
                    .lines()
                    .filter(|line| line.starts_with("GOAL "))
                    .collect();
                assert_eq!(goals, vec!["GOAL yes"; native.goals.len()]);
                let sizes: Vec<_> = text
                    .lines()
                    .filter_map(|line| line.strip_prefix("SIZES "))
                    .collect();
                assert_eq!(sizes, [format!("{} {}", native.classes, native.nodes)]);
                let summary = checked_summary(&proof_path);
                assert_eq!(summary.check_requests, native.goals.len());
                assert_eq!(summary.extraction_requests, 0);
                assert_eq!(summary.produced_certificates, native.goals.len());
            }
            if policy == Substitution::Snapshot {
                let nested = matcher == Matcher::Nested;
                let expected = counts.get(&nested).expect(
                    "native snapshot comparison requires an enabled encoded count oracle; exclude dependent modes when the oracle is excluded",
                );
                assert_eq!(
                    *expected,
                    (native.classes, native.nodes),
                    "{name}: policy-matched logical counts differ"
                );
            }
        }
        return;
    }
    let policy: Vec<Ignore> = serde_json::from_str(
        &std::fs::read_to_string(root.join("benchmarks/ignore.json")).unwrap(),
    )
    .unwrap();
    let file_identity = file.canonicalize().unwrap();
    let mut observations = BTreeMap::new();
    let mut modes = BTreeSet::new();
    for mode in &requested {
        match mode.as_str() {
            "off" | "term" => {
                modes.insert(mode.as_str());
            }
            "proofs" | "proof-extraction" | "proof-testing" => {
                modes.insert("proof-testing");
            }
            _ => {}
        }
    }
    // Native comparisons require this same source execution as their oracle.
    if requested.iter().any(|mode| mode.starts_with("egg")) {
        assert!(
            requested.contains("off"),
            "native comparison requires an enabled off oracle; exclude dependent modes when the oracle is excluded"
        );
        modes.insert("off");
    }
    // Off checks the actual term-mode alternatives on ordinary pre-command
    // clones; equality only in the encoded candidate graph is insufficient.
    // Strict mode instead supplies independently checked source proofs.
    for mode in ["term", "off", "proof-testing"] {
        if !modes.contains(mode) {
            continue;
        }
        eprintln!("Validating {mode}");
        let reference = if mode == "off" { "term" } else { "off" };
        let observed = observe(file, mode, observations.get(reference), egraph_threads);
        observations.insert(mode, observed);
    }
    for mode in ["term", "proof-testing"] {
        if let Some(mut observed) = observations.remove(mode) {
            let expected = observations
                .get("off")
                .expect("comparisons require enabled off mode");
            let (equality, evidence) = if mode == "term" {
                (&expected.comparison_in_root_class, "ordinary root check")
            } else {
                (&observed.comparison_in_root_class, "checked source proof")
            };
            let context = format!("{} / {mode}, {evidence}", file.display());
            let ties = extraction_comparison::compare(
                &mut observed.extractions,
                &expected.extractions,
                equality,
                &context,
            )
            .unwrap_or_else(|error| panic!("{error}"));
            if ties > 0 {
                eprintln!(
                    "Extraction tie summary: {context}: {ties} verified equal-cost best-term alternatives"
                );
            }
            let expected_failure = policy.iter().find(|rule| {
                rule.kind == "expected-failure"
                    && rule.treatments.iter().any(|treatment| treatment == mode)
                    && root
                        .join("benchmarks")
                        .join(&rule.file)
                        .canonicalize()
                        .unwrap()
                        == file_identity
            });
            let xfailed = table_comparison::compare(
                &observed.tables,
                &expected.tables,
                expected_failure.map(|rule| rule.expected_table_sizes.as_ref().unwrap()),
            )
            .unwrap_or_else(|error| panic!("{} / {mode}: {error}", file.display()));
            if xfailed {
                let rule = expected_failure.unwrap();
                eprintln!(
                    "XFAIL {} / {mode}: {:?}; {} [{}]",
                    file.display(),
                    rule.expected_table_sizes.as_ref().unwrap(),
                    rule.reason,
                    rule.evidence
                );
            }
            assert_eq!(
                observed.math_eclass_count, expected.math_eclass_count,
                "{mode}: classes"
            );
            assert_eq!(
                observed.stable_outputs, expected.stable_outputs,
                "{mode}: stable outputs"
            );
            assert!(
                observed.extractions == expected.extractions,
                "{mode}: extracted terms/costs differ"
            );
        }
    }
    for mode in &requested {
        if matches!(
            mode.as_str(),
            "egg" | "egg-proofs" | "egg-proof-extraction" | "egg-proof-testing"
        ) {
            use egg_math_benchmark::{MATH12_CHECK_LEFT, MATH12_CHECK_RIGHT, ProofMode};
            assert!(
                file.ends_with("math-iteration-12.egg"),
                "unregistered native Math workload"
            );
            let policy = if mode == "egg" {
                ProofMode::Off
            } else {
                ProofMode::Check
            };
            eprintln!("Validating {mode}: actual Math12 witness and iteration boundary");
            let (_, native, established) =
                egg_math_benchmark::run_math(policy, 11, MATH12_CHECK_LEFT, MATH12_CHECK_RIGHT)
                    .unwrap();
            assert!(
                !established,
                "Math12 witness must be absent at eleven rounds"
            );
            drop(native);
            let (_, native, established) =
                egg_math_benchmark::run_math(policy, 12, MATH12_CHECK_LEFT, MATH12_CHECK_RIGHT)
                    .unwrap();
            assert!(established);
            let counts = egg_math_benchmark::native_graph_size(&native);
            drop(native);
            let expected = &observations["off"];
            assert_eq!(
                (&expected.tables, expected.math_eclass_count),
                (&counts.0, Some(counts.1)),
                "native Math constructor/class counts differ"
            );
            let mut graph = new_experimental_egraph_with_options(policy == ProofMode::Off);
            graph.set_num_threads(egraph_threads);
            if policy == ProofMode::Check {
                graph = graph.with_proofs_enabled().with_proof_testing();
            }
            let source = std::fs::read_to_string(file)
                .unwrap()
                .replacen("(run 12)", "(run 11)", 1);
            let error = graph.parse_and_run_program(None, &source).unwrap_err();
            match error {
                egglog::Error::CheckError(..) if policy == ProofMode::Off => {}
                egglog::Error::ProofError { error, .. } if policy == ProofMode::Check => {
                    assert!(
                        error
                            .to_string()
                            .starts_with("Could not find a proof due to query not matching ")
                    );
                }
                error => panic!("expected unestablished Math12 equality at eleven: {error}"),
            }
        } else if mode.starts_with("egg-") {
            assert!(
                file.ends_with("parameter-analysis.egg"),
                "unregistered author-driver input"
            );
            eprintln!("Validating {mode}");
            let (nodes, classes) = match mode.as_str() {
                "egg-de" => (1_462_208, 1_362_208),
                "egg-ee" => (1_499_310, 1_362_209),
                "egg-nee" | "egg-nee-proof-testing" => (1_472_210, 1_372_210),
                "egg-oee" => (1_482_201, 1_362_210),
                _ => unreachable!(),
            };
            let canaries = root.join("benchmarks/disequality/correctness");
            for (input, base, diseq_num, contradiction, sizes) in [
                (canaries.join("contradiction.in"), 1, 0, "Y", None),
                (canaries.join("consistent.in"), 1, 0, "N", None),
                (
                    file.with_extension("in"),
                    100000,
                    10000,
                    "Y",
                    Some((nodes, classes)),
                ),
            ] {
                check_author_input(root, mode, &input, base, diseq_num, contradiction, sizes);
            }
        }
    }
}

/// Bound a correctness trial's runtime and retain its full diagnostics. This is
/// test orchestration, independent of the shared performance measurement path.
fn run_child(
    file: &Path,
    modes: &BTreeSet<String>,
    deadline: Duration,
    memory_limit_bytes: Option<u64>,
) -> Result<(), libtest_mimic::Failed> {
    let mut stdout = tempfile::tempfile()?;
    let mut stderr = tempfile::tempfile()?;
    let mut command = Process::new(std::env::current_exe()?);
    command.envs(benchmark_memory::ALLOCATOR_ENV);
    if let Some(limit) = memory_limit_bytes {
        command.arg(format!("--memory-limit-bytes={limit}"));
    }
    command
        .args([
            "--paper-child",
            file.to_str().unwrap(),
            &modes.iter().cloned().collect::<Vec<_>>().join(","),
        ])
        .stdout(stdout.try_clone()?)
        .stderr(stderr.try_clone()?);
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    let mut child = command.spawn()?;
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait()? {
            break status;
        }
        if started.elapsed() > deadline {
            #[cfg(unix)]
            unsafe {
                libc::kill(-(child.id() as i32), libc::SIGKILL);
            }
            #[cfg(not(unix))]
            child.kill()?;
            child.wait()?;
            return Err(format!(
                "test deadline exceeded after {} seconds",
                deadline.as_secs()
            )
            .into());
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    if !status.success() {
        let mut output = String::new();
        stdout.rewind()?;
        stdout.read_to_string(&mut output)?;
        stderr.rewind()?;
        stderr.read_to_string(&mut output)?;
        let category = if status.code() == Some(86) {
            "resource: allocator cap exceeded"
        } else {
            "correctness failure"
        };
        return Err(format!("{category}\n{output}\nchild status: {status}").into());
    }
    stderr.rewind()?;
    let mut diagnostics = String::new();
    stderr.read_to_string(&mut diagnostics)?;
    for line in diagnostics
        .lines()
        .filter(|line| line.starts_with("Extraction tie") || line.starts_with("XFAIL "))
    {
        eprintln!("{line}");
    }
    Ok(())
}

fn main() {
    let raw = benchmark_memory::configure(std::env::args_os());
    let raw: Vec<String> = raw
        .into_iter()
        .map(|arg| arg.into_string().unwrap())
        .collect();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .canonicalize()
        .unwrap();
    let egraph_threads =
        paper_oracles::egraph_threads(std::env::var_os("PAPER_EGRAPH_THREADS").as_deref()).unwrap();
    if raw.get(1).is_some_and(|arg| arg == "--paper-child") {
        std::env::set_current_dir(&root).unwrap();
        check_case(
            &root,
            Path::new(&raw[2]),
            &raw[3].split(',').map(str::to_owned).collect(),
            egraph_threads,
        );
        return;
    }
    let catalog_path = root.join("figures/catalog.json");
    eprintln!("Paper egraph workers: {egraph_threads}; native reference drivers remain serial");
    eprintln!(
        "Paper native reference internal checks: {}",
        slotted_reference::CHECKS_ENABLED
    );
    let catalog: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&catalog_path).unwrap()).unwrap();
    let mut ignores: Vec<Ignore> = serde_json::from_str(
        &std::fs::read_to_string(root.join("benchmarks/ignore.json")).unwrap(),
    )
    .unwrap();
    let mut cells: BTreeMap<PathBuf, BTreeSet<String>> = BTreeMap::new();
    for figure in catalog["figures"].as_object().unwrap().values() {
        let modes = paper_oracles::correctness_modes(
            figure["treatments"]
                .as_array()
                .unwrap()
                .iter()
                .chain(
                    figure
                        .get("checks")
                        .and_then(|v| v.as_array())
                        .into_iter()
                        .flatten(),
                )
                .map(|mode| mode.as_str().unwrap()),
        );
        for file in paper_oracles::figure_files(
            catalog_path.parent().unwrap(),
            figure["files"]
                .as_array()
                .unwrap()
                .iter()
                .map(|pattern| pattern.as_str().unwrap()),
        ) {
            cells.entry(file).or_default().extend(modes.iter().cloned());
        }
    }
    for file in glob::glob(
        root.join("benchmarks/slotted/inputs/**/*.egg")
            .to_str()
            .unwrap(),
    )
    .unwrap()
    {
        cells
            .entry(file.unwrap().canonicalize().unwrap())
            .or_default()
            .extend(
                [
                    "slotted",
                    "slotted-no-aliasing",
                    "slotted-ref-multi",
                    "slotted-ref-nested-snapshot",
                    "slotted-ref-nested",
                ]
                .map(str::to_owned),
            );
    }
    // This is the Rust execution dispatch contract, checked against Python's treatment table.
    let supported = [
        "off",
        "term",
        "proofs",
        "proof-extraction",
        "proof-testing",
        "egg",
        "egg-proofs",
        "egg-proof-extraction",
        "egg-proof-testing",
        "egg-de",
        "egg-ee",
        "egg-nee",
        "egg-oee",
        "egg-nee-proof-extraction",
        "egg-nee-proof-testing",
        "slotted",
        "slotted-proof-testing",
        "slotted-proof-testing-no-aliasing",
        "slotted-proof-extraction",
        "slotted-proof-extraction-no-aliasing",
        "slotted-no-aliasing",
        "slotted-ref-multi",
        "slotted-ref-nested",
        "slotted-ref-nested-snapshot",
        "slotted-ref-multi-proofs",
        "slotted-ref-nested-proofs",
        "slotted-ref-multi-proof-testing",
        "slotted-ref-nested-proof-testing",
    ];
    for rule in &mut ignores {
        assert!(matches!(
            rule.kind.as_str(),
            "resource" | "unsupported" | "expected-failure"
        ));
        if rule.kind == "expected-failure" {
            assert!(
                rule.expected_table_sizes
                    .as_ref()
                    .is_some_and(|sizes| !sizes.is_empty()
                        && sizes.keys().all(|name| !name.is_empty())
                        && sizes.values().all(|(off, candidate)| off != candidate))
            );
            assert!(
                matches!(rule.treatments.as_slice(), [mode] if matches!(mode.as_str(), "term" | "proof-testing"))
            );
            assert!(
                !rule.file.contains(['*', '?', '[']),
                "expected failures name one exact file"
            );
        } else {
            assert!(rule.expected_table_sizes.is_none());
        }
        assert!(!rule.reason.trim().is_empty() && !rule.evidence.trim().is_empty());
        assert!(
            rule.treatments
                .iter()
                .all(|mode| supported.contains(&mode.as_str())),
            "unknown ignored treatment"
        );
        assert!(
            rule.memory_limit_bytes
                .is_none_or(|limit| limit > 0 && rule.kind == "resource")
        );
        assert!(
            !Path::new(&rule.file).is_absolute()
                && !Path::new(&rule.file)
                    .components()
                    .any(|c| c == std::path::Component::ParentDir)
        );
        rule.matched = glob::glob(root.join("benchmarks").join(&rule.file).to_str().unwrap())
            .unwrap()
            .map(|path| path.unwrap().canonicalize().unwrap())
            .collect();
        assert!(!rule.matched.is_empty(), "stale ignore pattern");
    }
    // Read the Python defaults once in the parent; all trials and workers stay Rust.
    let defaults = Process::new("python3")
        .args(["-I", "-c", "import sys; sys.path.insert(0, sys.argv[1]); from benchmarking.config import DEFAULT_TIMEOUT_SEC, DEFAULT_MEMORY_LIMIT_BYTES; print(DEFAULT_TIMEOUT_SEC, DEFAULT_MEMORY_LIMIT_BYTES)"])
        .arg(&root)
        .output()
        .expect("paper-tests needs python3 to read benchmarking/config.py");
    assert!(
        defaults.status.success(),
        "cannot read resource defaults: {}",
        String::from_utf8_lossy(&defaults.stderr)
    );
    let defaults: Vec<u64> = String::from_utf8(defaults.stdout)
        .unwrap()
        .split_whitespace()
        .map(|value| value.parse().unwrap())
        .collect();
    let [timeout_sec, default_memory] = defaults[..] else {
        panic!("invalid benchmarking/config.py resource defaults")
    };
    assert!(timeout_sec > 0 && default_memory > 0);
    let memory_limit_bytes = match std::env::var("PAPER_TEST_MEMORY_LIMIT_BYTES").as_deref() {
        Err(_) => Some(default_memory),
        Ok("none") => None,
        Ok(value) => Some(
            value
                .parse::<u64>()
                .ok()
                .filter(|&limit| limit > 0)
                .expect("PAPER_TEST_MEMORY_LIMIT_BYTES must be positive or none"),
        ),
    };
    let mut trials = Vec::new();
    trials.push(Trial::test("paper/proof-dispatch/slotted", move || {
        let directory = tempfile::tempdir()?;
        let file = directory.path().join("benchmarks/slotted/inputs/smoke.egg");
        std::fs::create_dir_all(file.parent().unwrap())?;
        std::fs::write(&file, r#"
            (sort E)
            (constructor V (Var) E)
            (constructor Lam (Var E) E :binder 0)
            (constructor App (E E) E)
            (rewrite (App (Lam $x body) arg) (subst body $x arg) :name "beta")
            (let input0 (App (Lam $0 (V $0)) (V $1)))
            (run 1)
            (check (= input0 (V $1)))
            (extract input0)
        "#)?;
        let head = "rounds 1\nctor var V\nctor lam Lam\nctor app App\nterm (app (lam $0 (var $0)) (var $1))\nrule\n";
        let tail = "rhs root ?body[(var $x) := ?arg]\ngoal (var $1)\n";
        std::fs::write(file.with_extension("ref"), serde_json::to_vec(&serde_json::json!({
            "multi": format!("{head}atom root app lam arg\natom lam lam $x body\n{tail}"),
            "nested": format!("{head}nested (app (lam $x ?body) ?arg)\n{tail}"),
        }))?)?;
        check_case(directory.path(), &file, &[
            "slotted",
            "slotted-no-aliasing",
            "slotted-proof-extraction",
            "slotted-proof-extraction-no-aliasing",
            "slotted-ref-multi-proofs",
            "slotted-ref-nested-proofs",
        ].map(str::to_owned).into_iter().collect(), egraph_threads);
        Ok(())
    }));
    let native_root = root.clone();
    trials.push(Trial::test(
        "paper/proof-dispatch/nee-canaries",
        move || {
            let directory = native_root.join("benchmarks/disequality/correctness");
            for (file, contradiction) in [("contradiction.in", "Y"), ("consistent.in", "N")] {
                check_author_input(
                    &native_root,
                    "egg-nee-proof-testing",
                    &directory.join(file),
                    1,
                    0,
                    contradiction,
                    None,
                );
            }
            Ok(())
        },
    ));
    let mut excluded = 0;
    let mut enabled = 0;
    let mut expected_failures = 0;
    let mut applied_expected_failures = BTreeSet::new();
    let deadline = Duration::from_secs(timeout_sec).saturating_mul(CORRECTNESS_TIMEOUT_FACTOR);
    for (file, mut modes) in cells {
        let name = format!("paper/{}", file.strip_prefix(&root).unwrap().display());
        let native_math = file == root.join("benchmarks/corpus/math/math-iteration-12.egg");
        assert!(
            modes.iter().all(|mode| supported.contains(&mode.as_str())),
            "unknown paper treatment"
        );
        paper_oracles::validate(&root, &file, &modes).unwrap();
        let mut xfail_modes = Vec::new();
        modes.retain(|mode| {
            let mut matching = ignores.iter().enumerate().filter(|(_, rule)| {
                rule.matched.contains(&file)
                    && paper_oracles::exclusion_applies(&rule.treatments, mode)
                    && rule.memory_limit_bytes.is_none_or(|bound| {
                        // These modes run in a separate uncapped child below.
                        !(native_math && mode.starts_with("egg"))
                            && memory_limit_bytes.is_some_and(|limit| limit <= bound)
                    })
            });
            let matched = matching.next();
            assert!(
                matching.next().is_none(),
                "overlapping benchmark exclusions for {name}/{mode}"
            );
            if let Some((index, rule)) = matched {
                if rule.kind == "expected-failure" {
                    applied_expected_failures.insert(index);
                    expected_failures += 1;
                    xfail_modes.push(mode.clone());
                    return true;
                }
                excluded += 1;
                eprintln!(
                    "Excluded {name}/{mode}: {}: {} [{}]",
                    rule.kind, rule.reason, rule.evidence
                );
                false
            } else {
                true
            }
        });
        enabled += modes.len();
        if native_math {
            let mut native_modes = BTreeSet::new();
            modes.retain(|mode| {
                if mode.starts_with("egg") {
                    native_modes.insert(mode.clone());
                    false
                } else {
                    true
                }
            });
            if !native_modes.is_empty() {
                assert!(
                    modes.contains("off"),
                    "native Math requires an enabled off oracle"
                );
                // A capped child cannot raise its inherited hard VM limit.
                // Start this comparison from the uncapped parent instead,
                // repeating off as the native constructor/class-count oracle.
                native_modes.insert("off".to_owned());
                let file = file.clone();
                let kind = native_modes.iter().cloned().collect::<Vec<_>>().join(",");
                trials.push(
                    Trial::test(format!("{name}/native-egg"), move || {
                        run_child(
                            &file,
                            &native_modes,
                            deadline.saturating_mul(native_modes.len() as u32),
                            None,
                        )
                    })
                    .with_kind(format!("{kind}; no memory guard")),
                );
            }
        }
        let skipped = modes.is_empty();
        let mut kind = if skipped {
            "excluded".to_owned()
        } else {
            modes.iter().cloned().collect::<Vec<_>>().join(",")
        };
        if !xfail_modes.is_empty() {
            kind += &format!("; XFAIL {}", xfail_modes.join(","));
        }
        trials.push(
            Trial::test(name, move || {
                if modes.is_empty() {
                    return Err("remove the shared ignore entry to execute this trial".into());
                }
                run_child(
                    &file,
                    &modes,
                    deadline.saturating_mul(modes.len() as u32),
                    memory_limit_bytes,
                )
            })
            .with_kind(kind)
            .with_ignored_flag(skipped),
        );
    }
    for (index, rule) in ignores.iter().enumerate() {
        if rule.kind == "expected-failure" {
            assert!(
                applied_expected_failures.contains(&index),
                "expected failure is not registered by the paper catalog: {}/{}",
                rule.file,
                rule.treatments[0]
            );
        }
    }
    eprintln!(
        "Paper coverage: {enabled} runnable configurations; expected failures: {expected_failures}; excluded: {excluded}; benchmarks/ignore.json"
    );
    let mut args = libtest_mimic::Arguments::from_iter(raw);
    if args.test_threads.is_none() {
        args.test_threads = std::env::var("RUST_TEST_THREADS").ok().map(|value| {
            value
                .parse::<usize>()
                .ok()
                .filter(|&threads| threads > 0)
                .expect("RUST_TEST_THREADS must be a positive integer")
        });
    }
    libtest_mimic::run(&args, trials).exit();
}
