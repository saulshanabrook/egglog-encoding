use std::{collections::HashSet, path::PathBuf};

use egglog::{ast::sanitize_internal_names, file_supports_proofs_with_egraph};
use egglog_experimental::*;
use libtest_mimic::Trial;

#[derive(Clone)]
struct Run {
    path: PathBuf,
    desugar: bool,
    proof_testing: bool,
    /// Compare stable command output, including the appended table sizes,
    /// between the ordinary and proof-testing runs.
    snapshot_across_treatments: bool,
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

        match result {
            Ok(outputs) => {
                if self.proof_testing {
                    let snapshot = CommandOutput::snapshot_proofs_only(&outputs);
                    if !snapshot.is_empty() {
                        insta::assert_snapshot!(self.snapshot_name(), snapshot);
                    }
                }

                if self.snapshot_across_treatments {
                    let snapshot = if self.proof_testing {
                        CommandOutput::snapshot_non_proof_stable_under_proof_encoding(&outputs)
                    } else {
                        CommandOutput::snapshot_stable_under_proof_encoding(&outputs)
                    };
                    if !snapshot.is_empty() {
                        insta::assert_snapshot!(self.snapshot_name_across_treatments(), snapshot);
                    }
                }
            }
            Err(err_msg) if self.proof_testing => {
                panic!("proof fixture failed: {err_msg}");
            }
            Err(_) => {}
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
        // Match the main file harness: table sizes are part of the output that
        // must remain stable under proof encoding.
        let program = if self.snapshot_across_treatments {
            format!("{program}\n(print-size)")
        } else {
            program.to_owned()
        };
        match egraph.parse_and_run_program(filename, &program) {
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

    fn snapshot_name_across_treatments(&self) -> String {
        let stem = self.path.file_stem().unwrap();
        let stem = stem.to_string_lossy().replace(['.', '-', ' '], "_");
        format!("shared_snapshot_{stem}")
    }

    fn should_fail(&self) -> bool {
        self.path.to_string_lossy().contains("fail-typecheck")
    }
}

fn generate_tests(glob: &str) -> Vec<Trial> {
    let mut trials = vec![];
    let mut push_trial = |run: Run| trials.push(run.into_trial());
    let skipped_files = [
        "math-backoff.egg",
        // The bounded paper test checks the iteration witness and full proof.
        "math-microbenchmark-rational.egg",
    ];

    for entry in glob::glob(glob).unwrap() {
        let path = entry.unwrap();
        if path
            .components()
            .any(|component| component.as_os_str() == "snapshots")
        {
            continue;
        }
        let is_fixture = path
            .components()
            .any(|component| component.as_os_str() == "fixtures");

        let run = Run {
            path: path.clone(),
            desugar: false,
            proof_testing: false,
            snapshot_across_treatments: false,
        };
        // The dedicated disequality regression supplies deterministic TSV facts.
        let requires_fact_directory = run.path.ends_with("disequality/parameter-analysis.egg");
        if requires_fact_directory || skipped_files.iter().any(|file| run.path.ends_with(file)) {
            continue;
        }
        let should_fail = run.should_fail();
        let supports_proofs = !should_fail
            && file_supports_proofs_with_egraph(&run.path, new_experimental_egraph_for_proofs());
        let run = Run {
            // A shared snapshot needs both an ordinary and proof-testing trial.
            snapshot_across_treatments: supports_proofs && !run.requires_proofs() && !is_fixture,
            ..run
        };

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

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let tests = generate_tests("tests/**/*.egg");
    let mut names = HashSet::new();
    for test in &tests {
        let name = test.name().to_string();
        if !names.insert(name.clone()) {
            panic!("Duplicate test name: {name}");
        }
    }
    libtest_mimic::run(&args, tests).exit();
}
