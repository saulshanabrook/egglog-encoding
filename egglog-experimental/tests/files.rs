use std::{collections::HashSet, path::PathBuf};

use egglog::{ast::sanitize_internal_names, file_supports_proofs_with_egraph};
use egglog_experimental::*;
use libtest_mimic::Trial;

#[derive(Clone)]
struct Run {
    path: PathBuf,
    desugar: bool,
    proofs: bool,
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

        if self.proofs || self.proof_testing {
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
        } else if self.proofs {
            new_experimental_egraph_with_proofs()
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
                    if !(self.proofs || self.proof_testing) {
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
                if self.0.proof_testing || self.0.proofs {
                    write!(f, "proofs/")?;
                }
                let stem = self.0.path.file_stem().unwrap();
                let stem_str = stem.to_string_lossy().replace(['.', '-', ' '], "_");
                write!(f, "{stem_str}")?;
                if self.0.desugar {
                    write!(f, "_resugar")?;
                }
                if self.0.proofs {
                    write!(f, "_proofs")?;
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
            proofs: false,
            proof_testing: false,
        };
        if skipped_files.iter().any(|file| run.path.ends_with(file)) {
            continue;
        }
        let should_fail = run.should_fail();
        let supports_proofs = !should_fail
            && file_supports_proofs_with_egraph(&run.path, new_experimental_egraph_for_proofs());

        if run.requires_proofs() {
            push_trial(Run {
                proofs: true,
                ..run.clone()
            });
        } else if !is_fixture {
            push_trial(run.clone());
        }

        if supports_proofs && !run.requires_proofs() {
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
