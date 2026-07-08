use std::path::PathBuf;

use egglog::{file_supports_proofs, *};
use hashbrown::HashSet;
use libtest_mimic::Trial;

struct ManualProofDisable {
    file: &'static str,
    reason: &'static str,
}

const MANUAL_PROOF_DISABLED_FILES: &[ManualProofDisable] = &[
    ManualProofDisable {
        file: "eggcc-2mm.egg",
        reason: "uses :no-merge declarations such as DUMMYCTX; proof encoding requires a merge function",
    },
    ManualProofDisable {
        file: "subsume.egg",
        reason: "proof-testing rewrites a check on a subsumed expression into a prove query that no longer matches",
    },
    ManualProofDisable {
        file: "subsume-relation.egg",
        reason: "proof-testing rewrites a check on a subsumed relation row into a prove query that no longer matches",
    },
];

const PROOF_INTEGRATION_FILES: &[&str] = &[
    "tests/integer_math.egg",
    "tests/web-demo/math.egg",
    "tests/math-microbenchmark.egg",
    "tests/web-demo/resolution.egg",
    "tests/web-demo/rw-analysis.egg",
    "tests/web-demo/eqsolve.egg",
];

#[derive(Clone)]
struct Run {
    path: PathBuf,
    desugar: bool,
    term_encoding: bool,
    proofs: bool,
    /// proof_testing mode adds automatic prove-exists commands, which produce
    /// proof output that differs from normal mode. This should use separate snapshots.
    proof_testing: bool,
    threads: usize,
}

impl Run {
    /// Tests in the proofs directory require proofs to run successfully.
    fn requires_proofs(&self) -> bool {
        self.path.parent().unwrap().ends_with("proofs")
    }

    fn is_proof_mode_trial(&self) -> bool {
        self.term_encoding || self.proofs || self.proof_testing
    }

    fn is_curated_proof_integration(&self) -> bool {
        PROOF_INTEGRATION_FILES
            .iter()
            .any(|file| self.path.ends_with(file))
    }

    fn proof_filter_prefix(&self) -> Option<&'static str> {
        if self.requires_proofs() && self.is_proof_mode_trial() {
            Some("proof_unit")
        } else if self.is_curated_proof_integration() && self.proof_testing {
            Some("proof_integration")
        } else {
            None
        }
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
                proofs: false,
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

        // Debug mode enables parallelism which can lead to non-deterministic output ordering
        if let Some(snapshot_name) = self.proof_testing_snapshot_name() {
            match &result {
                Ok(outputs) => {
                    let proof_snapshot = CommandOutput::snapshot_proofs_only(outputs);
                    if !proof_snapshot.is_empty() {
                        insta::assert_snapshot!(snapshot_name, proof_snapshot);
                    }

                    let shared_snapshot =
                        CommandOutput::snapshot_non_proof_stable_under_proof_encoding(outputs);
                    if !shared_snapshot.is_empty() {
                        insta::assert_snapshot!(
                            self.snapshot_name_across_treatments(),
                            shared_snapshot
                        );
                    }
                }
                Err(err_msg) => {
                    panic!("proof fixture failed: {err_msg}");
                }
            }
            return;
        }

        if !self.should_skip_snapshot() {
            match &result {
                Ok(outputs) => {
                    // Use base snapshot name (without desugar/term_encoding/proofs suffixes)
                    // so all variants compare against the same expected output
                    let snapshot_name_across_treatments = self.snapshot_name_across_treatments();
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
                Err(err_msg) => {
                    // Snapshot the error message for fail-typecheck tests
                    let name = self.name().to_string();
                    insta::assert_snapshot!(name, err_msg);
                }
            }
        }
    }

    fn egraph(&self) -> EGraph {
        if self.proof_testing {
            EGraph::new_with_proofs().with_proof_testing()
        } else if self.proofs {
            EGraph::new_with_proofs()
        } else if self.term_encoding {
            EGraph::new_with_term_encoding()
        } else {
            EGraph::default()
        }
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
            // We use a local rayon pool here because `build_global()` can only
            // be called once per process, but libtest-mimic runs many trials
            // (with different thread counts) in the same process.
            // The threads == 1 case also goes through pool.install so the trial
            // doesn't fall through to the default global rayon pool (which uses
            // num_cpus threads and would make "single-threaded" tests
            // nondeterministic).
            // TODO: when we move to per-EGraph local thread pools, replace this
            // with `egraph.with_num_threads()` and remove the explicit pool.
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(self.threads)
                .build()
                .expect("failed to build rayon thread pool");
            pool.install(|| self.run());
            Ok(())
        })
    }

    /// Base snapshot name without mode suffixes - all variants share the same `outputs_to_snapshot_preserved_across_treatments` snapshot
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
        if self.is_curated_proof_integration() && self.proof_testing {
            Some(self.name().to_string())
        } else {
            None
        }
    }

    /// Full test name with mode suffixes for test identification
    fn name(&self) -> impl std::fmt::Display + '_ {
        struct Wrapper<'a>(&'a Run);
        impl std::fmt::Display for Wrapper<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                if let Some(prefix) = self.0.proof_filter_prefix() {
                    write!(f, "{prefix}/")?;
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
                if self.0.proofs {
                    write!(f, "_proofs")?;
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
        if self.threads > 1 {
            // Skip snapshots for parallel tests due to non-deterministic output ordering
            return true;
        }

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

    /// only assert snapshot if the snapshot is non-empty
    /// proof_testing has different output due to automatic prove-exists, so no snapshot for that
    fn should_assert_snapshot_across_treatments(
        &self,
        snapshot_content_across_treatments: &str,
    ) -> bool {
        !snapshot_content_across_treatments.is_empty() && !self.proof_testing
    }
}

fn manual_proof_disable_reason(path: &std::path::Path) -> Option<&'static str> {
    MANUAL_PROOF_DISABLED_FILES
        .iter()
        .find(|disabled| path.ends_with(disabled.file))
        .map(|disabled| disabled.reason)
}

fn generate_tests(glob: &str) -> Vec<Trial> {
    let mut trials = vec![];
    let mut push_trial = |run: Run| trials.push(run.into_trial());

    for entry in glob::glob(glob).unwrap() {
        let run = Run {
            path: entry.unwrap().clone(),
            desugar: false,
            term_encoding: false,
            proofs: false,
            proof_testing: false,
            threads: 1,
        };
        let should_fail = run.should_fail();
        let requires_proofs = run.requires_proofs();
        let proof_manually_disabled = manual_proof_disable_reason(&run.path).is_some();
        let supports_proofs = file_supports_proofs(&run.path) && !proof_manually_disabled;

        if !requires_proofs {
            push_trial(run.clone());

            push_trial(Run {
                threads: 32,
                ..run.clone()
            });
        }
        if !requires_proofs && !should_fail {
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

        // proofs mode (without proof_testing) should produce the same output as normal mode
        if !should_fail && supports_proofs {
            push_trial(Run {
                proofs: true,
                ..run.clone()
            });
        }

        if !should_fail
            && !proof_manually_disabled
            && (supports_proofs || run.is_curated_proof_integration())
        {
            // proof_testing mode adds automatic prove-exists, which has different output
            push_trial(Run {
                proof_testing: true,
                ..run.clone()
            });

            if supports_proofs {
                // Complex mode: desugar using proof encoding, then run normally.
                // Yes this mode is important! It has found multiple bugs.
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

fn generate_proof_support_snapshot_test() -> Trial {
    Trial::test("proof_support_snapshot", || {
        let mut supported_files = Vec::new();

        for entry in glob::glob("tests/**/*.egg").unwrap() {
            let path = entry.unwrap();
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
