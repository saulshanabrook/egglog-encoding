use std::{collections::HashSet, path::PathBuf};

use egglog::{
    ast::{Command, sanitize_internal_names},
    file_supports_proofs_with_egraph,
};
use egglog_experimental::*;
use libtest_mimic::Trial;

#[path = "../../test-support/causal_corpus.rs"]
mod causal_corpus;

#[derive(Clone)]
struct Run {
    path: PathBuf,
    desugar: bool,
    proof_testing: bool,
}

impl Run {
    fn requires_proofs(&self) -> bool {
        self.path.parent().unwrap().ends_with("proofs")
    }

    fn run(&self) {
        let program = std::fs::read_to_string(&self.path)
            .unwrap_or_else(|err| panic!("Couldn't read {:?}: {:?}", self.path, err));

        let result = if !self.desugar {
            self.test_program(
                self.path.to_str().map(String::from),
                &program,
                "Top level error",
            )
        } else {
            let mut egraph = new_experimental_egraph();
            let resolved = egraph
                .resolve_program(self.path.to_str().map(String::from), &program)
                .unwrap();
            let desugared_str = sanitize_internal_names(&resolved)
                .iter()
                .map(|cmd| cmd.to_string())
                .collect::<Vec<_>>()
                .join("\n");

            self.test_program(
                None,
                &desugared_str,
                "ERROR after parse, to_string, and parse again.",
            )
        };

        if self.proof_testing {
            match result {
                Ok(outputs) => {
                    let snapshot = CommandOutput::snapshot_proofs_only(&outputs);
                    if !snapshot.is_empty() {
                        insta::assert_snapshot!(self.snapshot_name(), snapshot);
                    }
                }
                Err(err_msg) => {
                    panic!("proof fixture failed: {err_msg}");
                }
            }
        }
    }

    fn egraph(&self) -> EGraph {
        if self.proof_testing {
            new_experimental_egraph_with_proof_testing()
        } else {
            new_experimental_egraph()
        }
    }

    fn test_program(
        &self,
        filename: Option<String>,
        program: &str,
        message: &str,
    ) -> Result<Vec<CommandOutput>, String> {
        let mut egraph = self.egraph();
        match egraph.parse_and_run_program(filename, program) {
            Ok(outputs) => {
                if self.should_fail() {
                    panic!(
                        "Program should have failed! Instead, logged:\n {}",
                        outputs
                            .iter()
                            .map(|output| output.to_string())
                            .collect::<Vec<_>>()
                            .join("\n")
                    );
                } else {
                    if !self.proof_testing {
                        for output in &outputs {
                            print!("  {output}");
                        }
                    }
                    // Test graphviz dot generation
                    let mut serialized = egraph
                        .serialize(SerializeConfig {
                            max_functions: Some(40),
                            max_calls_per_function: Some(40),
                            ..Default::default()
                        })
                        .egraph;
                    serialized.to_dot();
                    // Also try splitting and inlining
                    serialized.split_classes(|id, _| egraph.from_node_id(id).is_primitive());
                    serialized.inline_leaves();
                    serialized.to_dot();

                    Ok(outputs)
                }
            }
            Err(err) => {
                if !self.should_fail() {
                    panic!("{}: {err}", message)
                }
                Err(err.to_string())
            }
        }
    }

    fn into_trial(self) -> Trial {
        let name = self.name().to_string();
        Trial::test(name, move || {
            self.run();
            Ok(())
        })
    }

    fn name(&self) -> impl std::fmt::Display + '_ {
        struct Wrapper<'a>(&'a Run);
        impl std::fmt::Display for Wrapper<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                if self.0.proof_testing {
                    write!(f, "proofs/")?;
                }
                let stem = self.0.path.file_stem().unwrap();
                let stem_str = stem.to_string_lossy().replace(['.', '-', ' '], "_");
                write!(f, "{stem_str}")?;
                if self.0.desugar {
                    write!(f, "_resugar")?;
                }
                if self.0.proof_testing {
                    write!(f, "_proof_testing")?;
                }
                Ok(())
            }
        }
        Wrapper(self)
    }

    fn snapshot_name(&self) -> String {
        self.name().to_string()
    }

    fn should_fail(&self) -> bool {
        self.path.to_string_lossy().contains("fail-typecheck")
    }
}

fn generate_tests(glob: &str) -> Vec<Trial> {
    let mut trials = vec![];
    let mut push_trial = |run: Run| trials.push(run.into_trial());
    let skipped_files = ["math-backoff.egg"];

    for entry in glob::glob(glob).unwrap() {
        let path = entry.unwrap();
        let is_fixture = path
            .components()
            .any(|component| component.as_os_str() == "fixtures");

        let run = Run {
            path: path.clone(),
            desugar: false,
            proof_testing: false,
        };
        if skipped_files.iter().any(|file| run.path.ends_with(file)) {
            continue;
        }
        let should_fail = run.should_fail();
        let supports_proofs = !should_fail
            && file_supports_proofs_with_egraph(&run.path, new_experimental_egraph_for_proofs());

        if !run.requires_proofs() && !is_fixture {
            push_trial(run.clone());
        }

        if supports_proofs {
            push_trial(Run {
                proof_testing: true,
                ..run.clone()
            });
        }

        // Temporarily removed due to egglog changes. TODO: uncomment once egglog desugar is fixed
        // if !should_fail {
        //     push_trial(Run {
        //         desugar: true,
        //         ..run.clone()
        //     });
        // }
    }

    trials
}

fn resolved_replay_roots(
    path: &std::path::Path,
    working_directory: &std::path::Path,
) -> Result<causal_corpus::ReplayRoots, String> {
    let mut egraph = new_experimental_egraph();
    let mut roots = causal_corpus::ReplayRoots {
        checks: Vec::new(),
        extracts: 0,
    };
    collect_replay_roots(&mut egraph, path, working_directory, &mut roots)?;
    Ok(roots)
}

fn collect_replay_roots(
    egraph: &mut EGraph,
    path: &std::path::Path,
    working_directory: &std::path::Path,
    roots: &mut causal_corpus::ReplayRoots,
) -> Result<(), String> {
    let program = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    let commands = egraph
        .parse_program(path.to_str().map(String::from), &program)
        .map_err(|error| error.to_string())?;
    for command in commands {
        match command {
            Command::Include(_, file) => {
                collect_replay_roots(
                    egraph,
                    &working_directory.join(file),
                    working_directory,
                    roots,
                )?;
            }
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

fn generate_causal_tests(glob: &str) -> Vec<Trial> {
    let package_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let binary = PathBuf::from(env!("CARGO_BIN_EXE_egglog-experimental"));
    let paths = glob::glob(glob)
        .unwrap()
        .map(|entry| entry.unwrap())
        .filter(|path| !path.to_string_lossy().contains("fail-typecheck"))
        .collect::<Vec<_>>();
    let names = paths
        .iter()
        .map(|path| {
            format!(
                "experimental/{}",
                path.strip_prefix("tests").unwrap().to_string_lossy()
            )
        })
        .collect::<Vec<_>>();
    causal_corpus::validate_allowlist("experimental/", &names, causal_corpus::ALLOWLIST);
    paths
        .into_iter()
        .map(|path| {
            let relative = path.strip_prefix("tests").unwrap().to_string_lossy();
            let name = format!("experimental/{relative}");
            let proof_supported =
                file_supports_proofs_with_egraph(&path, new_experimental_egraph_for_proofs());
            causal_corpus::CausalCase {
                allowlisted: causal_corpus::disposition_for(&name, causal_corpus::ALLOWLIST),
                name,
                path,
                working_directory: package_root.clone(),
                asset_directories: vec![(package_root.join("tests"), PathBuf::from("tests"))],
                binary: binary.clone(),
                proof_supported,
            }
            .into_trial(resolved_replay_roots)
        })
        .collect()
}

fn generate_workload_causal_tests() -> Vec<Trial> {
    let package_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = package_root.parent().unwrap().to_path_buf();
    let binary = PathBuf::from(env!("CARGO_BIN_EXE_egglog-experimental"));
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
                working_directory: workspace_root.clone(),
                asset_directories: assets
                    .map(|assets| vec![(workspace_root.join(assets), PathBuf::new())])
                    .unwrap_or_default(),
                binary: binary.clone(),
                proof_supported: true,
            }
            .into_trial(resolved_replay_roots)
        })
        .collect()
}

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let tests = generate_tests("tests/**/*.egg");
    let mut tests = tests;
    tests.extend(generate_causal_tests("tests/**/*.egg"));
    tests.extend(generate_workload_causal_tests());
    let mut names = HashSet::new();
    for test in &tests {
        let name = test.name().to_string();
        if !names.insert(name.clone()) {
            panic!("Duplicate test name: {name}");
        }
    }
    libtest_mimic::run(&args, tests).exit();
}
