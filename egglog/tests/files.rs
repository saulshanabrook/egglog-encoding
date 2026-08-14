use std::path::{Path, PathBuf};

use egglog::{file_supports_proofs, *};
use hashbrown::HashSet;
use libtest_mimic::Trial;

struct ManualDisable {
    file: &'static str,
    reason: &'static str,
}

const MANUAL_DESUGAR_DISABLED_FILES: &[ManualDisable] = &[ManualDisable {
    file: "looking_up_global.egg",
    reason: "the expected-failure body binds a global name; static desugaring cannot determine whether that binding survives without executing the command",
}];

const MANUAL_PROOF_DISABLED_FILES: &[ManualDisable] = &[
    ManualDisable {
        file: "eggcc-2mm.egg",
        reason: "the full benchmark exceeds the routine proof harness resource budget; the bounded eggcc-2mm-pass1 fixture covers this workload in proof benchmarks",
    },
    ManualDisable {
        file: "subsume.egg",
        reason: "proof-testing rewrites a check on a subsumed expression into a prove query that no longer matches",
    },
    ManualDisable {
        file: "subsume-relation.egg",
        reason: "proof-testing rewrites a check on a subsumed relation row into a prove query that no longer matches",
    },
    ManualDisable {
        file: "llama.egg",
        reason: "luminal transformer benchmark: too large to run in proof modes as part of the routine test suite",
    },
    ManualDisable {
        file: "paged_llama.egg",
        reason: "luminal transformer benchmark: too large to run in proof modes as part of the routine test suite",
    },
    ManualDisable {
        file: "qwen.egg",
        reason: "luminal transformer benchmark: too large to run in proof modes as part of the routine test suite",
    },
    ManualDisable {
        file: "qwen3_moe.egg",
        reason: "luminal transformer benchmark: too large to run in proof modes as part of the routine test suite",
    },
    ManualDisable {
        file: "whisper.egg",
        reason: "luminal transformer benchmark: too large to run in proof modes as part of the routine test suite",
    },
];

// These proof-testing runs are still executed, but their proof snapshots are
// too large for default checked-in fixtures.
const PROOF_TESTING_SNAPSHOT_DISABLED_FILES: &[&str] = &[
    "eqsolve.egg",
    "hardboiled_conv1d_32.egg",
    "herbie.egg",
    "bdd.egg",
    "math.egg",
    "typeinfer.egg",
    "bool.egg",
    "container-fail.egg",
    "delete.egg",
    "fibonacci.egg",
    "knapsack.egg",
    "lambda.egg",
    "list.egg",
    "luminal-llama.egg",
    "pointer-analysis-initdb.egg",
    "repro-desugar-143.egg",
    "string_quotes.egg",
];

#[derive(Clone)]
struct Run {
    path: PathBuf,
    desugar: bool,
    term_encoding: bool,
    /// proof_testing mode adds automatic prove-exists commands, which produce
    /// proof output that differs from normal mode. This should use separate snapshots.
    proof_testing: bool,
    threads: usize,
}

impl Run {
    /// Tests in the proofs directory require proof testing to run successfully.
    fn requires_proofs(&self) -> bool {
        self.path.parent().unwrap().ends_with("proofs")
    }

    fn filename_for_test_run(&self) -> Option<String> {
        if self.should_fail() {
            // Fail-typecheck errors are snapshot-tested. Pass a stable display
            // name so Span can render the caller-provided path verbatim without
            // making snapshots depend on the local checkout path.
            self.path
                .file_name()
                .map(|name| name.to_string_lossy().into())
        } else {
            self.path.to_str().map(String::from)
        }
    }

    fn run(&self) {
        let _ = env_logger::builder().is_test(true).try_init();
        let program = std::fs::read_to_string(&self.path)
            .unwrap_or_else(|err| panic!("Couldn't read {:?}: {:?}", self.path, err));

        let result = if !self.desugar {
            self.test_program(
                self.filename_for_test_run(),
                &program,
                "",
                "Top level error",
            )
        } else {
            let resolved_str = self.resolve_prog(&program);
            // after desugaring run the program without term encoding or proofs
            let normal_run = Run {
                path: self.path.clone(),
                desugar: false,
                term_encoding: false,
                proof_testing: false,
                threads: self.threads,
            };
            let proof_check_prog = if self.proof_testing {
                program.clone()
            } else {
                "".to_string()
            };

            normal_run.test_program(
                None,
                &resolved_str,
                &proof_check_prog,
                "ERROR after parse, to_string, and parse again.",
            )
        };

        if !self.should_skip_snapshot() {
            match &result {
                Ok(outputs) => {
                    if self.proof_testing {
                        self.assert_proof_testing_snapshots(outputs);
                    } else {
                        // Use base snapshot name (without desugar/term_encoding suffixes)
                        // so all variants compare against the same expected output.
                        let snapshot_name_across_treatments =
                            self.snapshot_name_across_treatments();
                        let snapshot_content_across_treatments =
                            CommandOutput::snapshot_stable_under_proof_encoding(outputs);

                        if self.should_assert_snapshot_across_treatments(
                            &snapshot_content_across_treatments,
                        ) {
                            insta::assert_snapshot!(
                                snapshot_name_across_treatments,
                                snapshot_content_across_treatments
                            );
                        }
                    }
                }
                Err(err_msg) => {
                    if self.proof_testing {
                        panic!("proof fixture failed: {err_msg}");
                    } else {
                        // Snapshot the error message for fail-typecheck tests
                        let name = self.name().to_string();
                        insta::assert_snapshot!(name, err_msg);
                    }
                }
            }
        }
    }

    fn egraph(&self) -> EGraph {
        let mut egraph = if self.proof_testing {
            EGraph::new_with_proofs().with_proof_testing()
        } else if self.term_encoding {
            EGraph::new_with_term_encoding()
        } else {
            EGraph::default()
        };
        // A same-stem directory holds external inputs for file-harness fixtures.
        let fact_directory = self.path.with_extension("");
        if fact_directory.is_dir() {
            egraph.fact_directory = Some(fact_directory);
        }
        egraph.with_num_threads(self.threads)
    }

    // Returns a string of the desugared program and a string for the desugared program without proofs
    fn resolve_prog(&self, program: &str) -> String {
        let mut egraph = self.egraph();

        let resolved = egraph
            .resolve_program(self.path.to_str().map(String::from), program)
            .unwrap();
        resolved
            .iter()
            .map(|cmd| cmd.to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn test_program(
        &self,
        filename: Option<String>,
        program: &str,
        proof_check_prog: &str,
        message: &str,
    ) -> Result<Vec<CommandOutput>, String> {
        let mut egraph = self.egraph();
        let parsed_proof_check_prog = egraph
            .parse_program(None, proof_check_prog)
            .unwrap_or_else(|_| panic!("Failed to parse proof check program"));
        // hard code proof testing to true, we only use proof checking program in proof testing mode
        egraph
            .set_proof_checking_program(parsed_proof_check_prog, true)
            .expect("Failed to set proof checking program");

        egraph.ensure_no_reserved_symbols(false);

        // Append print-size to every test file to ensure it works
        let program = format!("{program}\n(print-size)");

        match egraph.parse_and_run_program(filename, &program) {
            Ok(msgs) => {
                if self.should_fail() {
                    panic!(
                        "Program should have failed! Instead, logged:\n {}",
                        msgs.iter()
                            .map(|s| s.to_string())
                            .collect::<Vec<_>>()
                            .join("\n")
                    );
                } else {
                    for msg in &msgs {
                        log::info!("  {msg}");
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

                    Ok(msgs)
                }
            }
            Err(err) => {
                if !self.should_fail() {
                    panic!("{message}: {err}")
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

    /// Base snapshot name without mode suffixes - all variants share the same snapshot
    /// except for proof_testing, which has different output due to using `prove` everywhere.
    fn snapshot_name_across_treatments(&self) -> String {
        let mut name = "shared_snapshot_".to_string();

        let stem = self.path.file_stem().unwrap();
        let stem_str = stem.to_string_lossy().replace(['.', '-', ' '], "_");
        name.push_str(&stem_str);

        if self.path.parent().unwrap().ends_with("fail-typecheck") {
            name.push_str("_fail_typecheck");
        }
        name
    }

    fn proof_testing_snapshot_name(&self) -> Option<String> {
        if self.proof_testing && !self.desugar && !proof_testing_snapshot_disabled(&self.path) {
            Some(self.name().to_string())
        } else {
            None
        }
    }

    fn assert_proof_testing_snapshots(&self, outputs: &[CommandOutput]) {
        if let Some(snapshot_name) = self.proof_testing_snapshot_name() {
            let proof_snapshot = CommandOutput::snapshot_proofs_only(outputs);
            if !proof_snapshot.is_empty() {
                insta::assert_snapshot!(snapshot_name, proof_snapshot);
            }

            if !self.requires_proofs() {
                let shared_snapshot =
                    CommandOutput::snapshot_non_proof_stable_under_proof_encoding(outputs);
                if !shared_snapshot.is_empty() {
                    insta::assert_snapshot!(
                        self.snapshot_name_across_treatments(),
                        shared_snapshot
                    );
                }
            }
        }
    }

    /// Full test name with mode suffixes for test identification
    fn name(&self) -> impl std::fmt::Display + '_ {
        struct Wrapper<'a>(&'a Run);
        impl std::fmt::Display for Wrapper<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                if self.0.proof_testing {
                    write!(f, "proofs/")?;
                } else if self.0.path.parent().unwrap().ends_with("fail-typecheck") {
                    write!(f, "fail-typecheck/")?;
                }
                let stem = self.0.path.file_stem().unwrap();
                let stem_str = stem.to_string_lossy().replace(['.', '-', ' '], "_");
                write!(f, "{stem_str}")?;
                if self.0.desugar {
                    write!(f, "_desugar")?;
                }
                if self.0.term_encoding {
                    write!(f, "_term_encoding")?;
                }
                if self.0.proof_testing {
                    write!(f, "_proof_testing")?;
                }

                if self.0.threads > 1 {
                    write!(f, "_{}threads", self.0.threads)?;
                }

                Ok(())
            }
        }
        Wrapper(self)
    }

    fn should_fail(&self) -> bool {
        self.path.to_string_lossy().contains("fail-typecheck")
    }

    fn should_skip_snapshot(&self) -> bool {
        if self.proof_testing {
            // Proof-testing snapshots have their own filtering below.
            false
        } else if self.threads > 1 {
            // Skip snapshots for parallel tests due to non-deterministic output ordering
            true
        } else {
            // Skip tests with known non-deterministic output
            let filename = self.path.file_stem().unwrap().to_string_lossy();
            const SKIP_PATTERNS: [&str; 6] = [
                "extract-vec-bench",
                "python_array_optimize",
                "stresstest_large_expr",
                "towers-of-hanoi",
                "taylor51",
                "factoring-multisets",
            ];
            SKIP_PATTERNS.iter().any(|pat| filename.contains(pat))
        }
    }

    /// Only assert the shared snapshot if the snapshot is non-empty.
    /// proof_testing snapshots are handled separately.
    fn should_assert_snapshot_across_treatments(
        &self,
        snapshot_content_across_treatments: &str,
    ) -> bool {
        !snapshot_content_across_treatments.is_empty() && !self.proof_testing
    }
}

fn manual_proof_disable_reason(path: &Path) -> Option<&'static str> {
    MANUAL_PROOF_DISABLED_FILES
        .iter()
        .find(|disabled| path.ends_with(disabled.file))
        .map(|disabled| disabled.reason)
}

fn proof_testing_snapshot_disabled(path: &Path) -> bool {
    PROOF_TESTING_SNAPSHOT_DISABLED_FILES
        .iter()
        .any(|file| path.ends_with(file))
}

fn generate_tests(glob: &str) -> Vec<Trial> {
    let mut trials = vec![];
    let mut push_trial = |run: Run| trials.push(run.into_trial());

    for entry in glob::glob(glob).unwrap() {
        let path = entry.unwrap().clone();

        // Files under tests/header/ are shared fragments pulled in via
        // `(include ...)`, not standalone test programs.
        if path.parent().is_some_and(|p| p.ends_with("header")) {
            continue;
        }

        // Test bypass: files too slow/large to run as part of the normal test
        // suite. They remain available as benchmarks (see scripts/bench.py).
        let test_bypass_file_list = ["gemma.egg", "gemma4_moe.egg"];
        if test_bypass_file_list.iter().any(|f| path.ends_with(f)) {
            continue;
        }

        let run = Run {
            path,
            desugar: false,
            term_encoding: false,
            proof_testing: false,
            threads: 1,
        };
        let should_fail = run.should_fail();
        let requires_proofs = run.requires_proofs();
        let proof_manually_disabled = manual_proof_disable_reason(&run.path).is_some();
        let supports_proofs = file_supports_proofs(&run.path) && !proof_manually_disabled;
        let supports_desugaring = !MANUAL_DESUGAR_DISABLED_FILES
            .iter()
            .any(|disabled| run.path.ends_with(disabled.file));

        if !requires_proofs {
            push_trial(run.clone());

            push_trial(Run {
                threads: 32,
                ..run.clone()
            });
        }
        if !requires_proofs && !should_fail && supports_desugaring {
            push_trial(Run {
                desugar: true,
                ..run.clone()
            });
        }
        if !should_fail && !requires_proofs && supports_proofs {
            push_trial(Run {
                term_encoding: true,
                ..run.clone()
            });
        }

        if !should_fail && supports_proofs {
            // proof_testing mode adds automatic prove-exists, which has different output
            push_trial(Run {
                proof_testing: true,
                ..run.clone()
            });

            // Desugar under proof-testing, then replay the desugared program
            // while checking proofs against the original source program.
            if supports_desugaring {
                push_trial(Run {
                    proof_testing: true,
                    desugar: true,
                    ..run.clone()
                });
            }
        }
    }

    trials
}

fn generate_manual_proof_disable_snapshot_test() -> Trial {
    Trial::test("proof_manual_disabled_files", || {
        let mut snapshot = MANUAL_PROOF_DISABLED_FILES
            .iter()
            .map(|disabled| format!("{}: {}", disabled.file, disabled.reason))
            .collect::<Vec<_>>();
        snapshot.sort();
        insta::assert_snapshot!("proof_manual_disabled_files", snapshot.join("\n"));

        Ok(())
    })
}

fn generate_manual_desugar_disable_snapshot_test() -> Trial {
    Trial::test("desugar_manual_disabled_files", || {
        let mut snapshot = MANUAL_DESUGAR_DISABLED_FILES
            .iter()
            .map(|disabled| format!("{}: {}", disabled.file, disabled.reason))
            .collect::<Vec<_>>();
        snapshot.sort();
        insta::assert_snapshot!("desugar_manual_disabled_files", snapshot.join("\n"));

        Ok(())
    })
}

fn generate_proof_support_snapshot_test() -> Trial {
    Trial::test("proof_support_snapshot", || {
        let mut supported_files = Vec::new();

        for entry in glob::glob("tests/**/*.egg").unwrap() {
            let path = entry.unwrap();
            // Skip shared header fragments (see generate_tests).
            if path.parent().is_some_and(|p| p.ends_with("header")) {
                continue;
            }
            if !file_supports_proofs(&path) && !path.parent().unwrap().ends_with("fail-typecheck") {
                // Use just the filename for cross-platform consistency
                let filename = path.file_name().unwrap().to_string_lossy().to_string();
                supported_files.push(filename);
            }
        }

        // Sort for deterministic output
        supported_files.sort();

        // Create snapshot
        let snapshot = supported_files.join("\n");
        insta::assert_snapshot!("proof_unsupported_files", snapshot);

        Ok(())
    })
}

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let mut tests = generate_tests("tests/**/*.egg");

    // Add the proof support snapshot test
    tests.push(generate_proof_support_snapshot_test());
    tests.push(generate_manual_proof_disable_snapshot_test());
    tests.push(generate_manual_desugar_disable_snapshot_test());

    // ensure all the tests have unique names
    let mut names = HashSet::new();
    for test in &tests {
        let name = test.name().to_string();
        if !names.insert(name.clone()) {
            panic!("Duplicate test name: {name}");
        }
    }
    libtest_mimic::run(&args, tests).exit();
}
