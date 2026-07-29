//! Workspace-level trace/slice/replay corpus.
//!
//! The corpus spans both package test suites and root benchmark fixtures, so
//! it belongs to the integrating workspace rather than either publishable
//! package. Keeping it here also lets each package archive compile its own
//! tests without reaching above its package root.

use std::{
    collections::HashSet,
    path::{Path, PathBuf},
};

use egglog::{EGraph, ast::Command, file_supports_proofs};
use egglog_experimental::{
    file_supports_proofs_with_egraph, new_experimental_egraph, new_experimental_egraph_for_proofs,
};
use libtest_mimic::Trial;

#[path = "../causal_corpus.rs"]
mod causal_corpus;
#[path = "../../egglog/tests/support/manual_proof_support.rs"]
mod manual_proof_support;

fn resolved_core_replay_roots(
    path: &Path,
    working_directory: &Path,
) -> Result<causal_corpus::ReplayRoots, String> {
    resolved_replay_roots(EGraph::default(), path, working_directory)
}

fn resolved_experimental_replay_roots(
    path: &Path,
    working_directory: &Path,
) -> Result<causal_corpus::ReplayRoots, String> {
    resolved_replay_roots(new_experimental_egraph(), path, working_directory)
}

fn resolved_replay_roots(
    mut egraph: EGraph,
    path: &Path,
    working_directory: &Path,
) -> Result<causal_corpus::ReplayRoots, String> {
    let mut roots = causal_corpus::ReplayRoots {
        checks: Vec::new(),
        extracts: 0,
    };
    collect_replay_roots(&mut egraph, path, working_directory, &mut roots)?;
    Ok(roots)
}

fn collect_replay_roots(
    egraph: &mut EGraph,
    path: &Path,
    working_directory: &Path,
    roots: &mut causal_corpus::ReplayRoots,
) -> Result<(), String> {
    let program = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    let commands = egraph
        .parse_program(path.to_str().map(String::from), &program)
        .map_err(|error| error.to_string())?;
    for command in commands {
        match command {
            Command::Include(_, file) => collect_replay_roots(
                egraph,
                &working_directory.join(file),
                working_directory,
                roots,
            )?,
            Command::Check(..) => roots.checks.push(command.to_string()),
            Command::Extract(..) => roots.extracts += 1,
            Command::UserDefined(_, name, _) if name == "extract" || name == "multi-extract" => {
                roots.extracts += 1;
            }
            _ => {}
        }
    }
    Ok(())
}

fn relative_name(path: &Path, root: &Path) -> String {
    path.strip_prefix(root)
        .expect("corpus path must be below its test root")
        .components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

fn generate_package_causal_tests(
    prefix: &'static str,
    package_root: &Path,
    capture_binary: &Path,
    replay_binary: &Path,
    proof_supported: fn(&Path) -> bool,
    resolve_roots: causal_corpus::RootResolver,
) -> Vec<Trial> {
    let tests_root = package_root.join("tests");
    let pattern = tests_root.join("**/*.egg").to_string_lossy().into_owned();
    let paths = glob::glob(&pattern)
        .unwrap()
        .map(|entry| entry.unwrap())
        .filter(|path| !path.to_string_lossy().contains("fail-typecheck"))
        .collect::<Vec<_>>();
    let names = paths
        .iter()
        .map(|path| format!("{prefix}{}", relative_name(path, &tests_root)))
        .collect::<Vec<_>>();
    causal_corpus::validate_allowlist(prefix, &names, causal_corpus::ALLOWLIST);

    paths
        .into_iter()
        .map(|path| {
            let name = format!("{prefix}{}", relative_name(&path, &tests_root));
            let proof_supported = proof_supported(&path);
            causal_corpus::CausalCase {
                allowlisted: causal_corpus::disposition_for(&name, causal_corpus::ALLOWLIST),
                name,
                path,
                working_directory: package_root.to_owned(),
                asset_directories: vec![(tests_root.clone(), PathBuf::from("tests"))],
                capture_binary: capture_binary.to_owned(),
                replay_binary: replay_binary.to_owned(),
                proof_supported,
            }
            .into_trial(resolve_roots)
        })
        .collect()
}

fn core_proof_supported(path: &Path) -> bool {
    file_supports_proofs(path) && manual_proof_support::manual_proof_disable_reason(path).is_none()
}

fn experimental_proof_supported(path: &Path) -> bool {
    file_supports_proofs_with_egraph(path, new_experimental_egraph_for_proofs())
}

fn generate_workload_causal_tests(
    workspace_root: &Path,
    capture_binary: &Path,
    replay_binary: &Path,
) -> Vec<Trial> {
    let workloads = [
        ("math", "egglog/tests/math-microbenchmark.egg", None),
        (
            "pointer",
            "benchmarks/pointer-analysis-small.egg",
            Some("benchmarks/data/pointer-analysis-small"),
        ),
        ("hardboiled", "egglog/tests/hardboiled_conv1d_32.egg", None),
        ("luminal", "benchmarks/luminal-llama.egg", None),
    ];
    let names = workloads
        .iter()
        .map(|(name, _, _)| format!("workload/{name}"))
        .collect::<Vec<_>>();
    causal_corpus::validate_allowlist("workload/", &names, causal_corpus::ALLOWLIST);

    workloads
        .into_iter()
        .map(|(name, path, assets)| {
            let name = format!("workload/{name}");
            causal_corpus::CausalCase {
                allowlisted: causal_corpus::disposition_for(&name, causal_corpus::ALLOWLIST),
                name,
                path: workspace_root.join(path),
                working_directory: workspace_root.to_owned(),
                asset_directories: assets
                    .map(|assets| vec![(workspace_root.join(assets), PathBuf::new())])
                    .unwrap_or_default(),
                capture_binary: capture_binary.to_owned(),
                replay_binary: replay_binary.to_owned(),
                proof_supported: true,
            }
            .into_trial(resolved_experimental_replay_roots)
        })
        .collect()
}

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let package_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = package_root
        .parent()
        .expect("test package must be in the workspace root");
    let core_root = workspace_root.join("egglog");
    let experimental_root = workspace_root.join("egglog-experimental");
    let core_binary = PathBuf::from(env!("CARGO_BIN_EXE_causal-egglog"));
    let experimental_capture_binary =
        PathBuf::from(env!("CARGO_BIN_EXE_causal-egglog-experimental-capture"));
    let experimental_replay_binary =
        PathBuf::from(env!("CARGO_BIN_EXE_causal-egglog-experimental-proof"));

    let mut tests = generate_package_causal_tests(
        "core/",
        &core_root,
        &core_binary,
        &core_binary,
        core_proof_supported,
        resolved_core_replay_roots,
    );
    tests.extend(generate_package_causal_tests(
        "experimental/",
        &experimental_root,
        &experimental_capture_binary,
        &experimental_replay_binary,
        experimental_proof_supported,
        resolved_experimental_replay_roots,
    ));
    tests.extend(generate_workload_causal_tests(
        workspace_root,
        &experimental_capture_binary,
        &experimental_replay_binary,
    ));

    let mut names = HashSet::new();
    for test in &tests {
        let name = test.name().to_string();
        assert!(names.insert(name.clone()), "duplicate test name: {name}");
    }
    libtest_mimic::run(&args, tests).exit();
}
