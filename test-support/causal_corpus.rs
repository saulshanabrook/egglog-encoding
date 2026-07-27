use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use libtest_mimic::Trial;

pub type RootResolver = fn(&Path, &Path) -> Result<ReplayRoots, String>;

pub struct ReplayRoots {
    pub checks: Vec<String>,
    pub extracts: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArtifactExpectation {
    Absent,
    Present,
}

#[derive(Clone, Copy, Debug)]
pub enum Disposition {
    StaticUnsupported {
        reason: &'static str,
    },
    Unsupported {
        diagnostic: &'static str,
        artifact: ArtifactExpectation,
    },
    KnownReplayFailure {
        diagnostic: &'static str,
        artifact: ArtifactExpectation,
    },
    NoReplayRoot,
    ExtractRootsUnsupported,
    ChecksOnly,
}

#[derive(Clone, Copy, Debug)]
pub struct AllowlistGroup {
    pub paths: &'static [&'static str],
    pub disposition: Disposition,
}

pub const ALLOWLIST: &[AllowlistGroup] = &[
    AllowlistGroup {
        paths: &[
            "core/eggcc-2mm.egg",
            "core/eggcc-extraction.egg",
            "core/hardboiled_conv1d_128.egg",
            "core/hidden_print_size.egg",
            "core/internal_let.egg",
            "core/looking_up_global.egg",
            "core/looking_up_nonconstructor_in_rewrite_good.egg",
            "core/luminal-llama.egg",
            "core/math-microbenchmark-mini.egg",
            "core/merge-saturates.egg",
            "core/merge_read.egg",
            "core/name-resolution.egg",
            "core/pass-typecheck/shadow-local-before-global.egg",
            "core/print-function.egg",
            "core/proofs/bare-container-side-condition.egg",
            "core/proofs/bind-prim-result.egg",
            "core/proofs/commute-collapse.egg",
            "core/proofs/container-set-collapse.egg",
            "core/proofs/eqsat-basic-proof.egg",
            "core/proofs/global-prove-query.egg",
            "core/proofs/primitive-args.egg",
            "core/proofs/rule-head-fast-path.egg",
            "core/proofs/simple_proof_check.egg",
            "core/rectangle.egg",
            "core/repro-665-set-union.egg",
            "core/repro-herbie-vanilla.egg",
            "core/repro-new-backend-delete.egg",
            "core/repro-new-backend-python-vec.egg",
            "core/repro-primitive-query.egg",
            "core/repro-querybug.egg",
            "core/repro-querybug3.egg",
            "core/repro-should-saturate.egg",
            "core/repro-silly-panic.egg",
            "core/repro-typechecking-schedule.egg",
            "core/repro-unsound-htutorial.egg",
            "core/repro-vec-unequal.egg",
            "core/set_sort_function.egg",
            "core/term-encoding-subsume-rebuild-bug.egg",
            "core/type-constraints-tests.egg",
            "core/web-demo/datatypes.egg",
            "core/web-demo/prims.egg",
            "experimental/math-microbenchmark-rational.egg",
            "experimental/proofs/unstable-fresh-proof.egg",
            "experimental/repro-scheduler-scopes.egg",
            "experimental/repro-unsound-htutorial-rational.egg",
        ],
        disposition: Disposition::NoReplayRoot,
    },
    AllowlistGroup {
        paths: &[
            "core/extract-vec-bench.egg",
            "core/proof-extract-cost.egg",
            "core/taylor51.egg",
            "core/use-at-in-string.egg",
        ],
        disposition: Disposition::ExtractRootsUnsupported,
    },
    AllowlistGroup {
        paths: &[
            "core/fibonacci-demand.egg",
            "core/intersection.egg",
            "core/repro-typecheck-term-encoding.egg",
            "core/web-demo/antiunify.egg",
            "core/web-demo/combinators.egg",
            "core/web-demo/typecheck.egg",
            "core/web-demo/unification-points-to.egg",
        ],
        disposition: Disposition::ChecksOnly,
    },
    AllowlistGroup {
        paths: &[
            "core/before-proofs.egg",
            "core/container-rebuild.egg",
            "core/cykjson.egg",
            "core/interval.egg",
            "core/naive-action-lookup.egg",
            "core/pair.egg",
            "core/rat-pow-eval.egg",
            "core/tricky-type-checking.egg",
            "core/tuple-output.egg",
            "core/typed_primitive_unstable_app.egg",
            "core/unsafe-seminaive.egg",
            "core/vec.egg",
            "core/web-demo/array.egg",
            "core/web-demo/bdd.egg",
            "core/web-demo/bignum.egg",
            "core/web-demo/cyk.egg",
            "core/web-demo/herbie-tutorial.egg",
            "core/web-demo/herbie.egg",
            "core/web-demo/math.egg",
            "core/web-demo/multiset.egg",
            "core/web-demo/set.egg",
            "core/web-demo/towers-of-hanoi.egg",
            "core/web-demo/typeinfer.egg",
            "experimental/herbie-rational.egg",
            "experimental/herbie-tutorial-rational.egg",
            "experimental/interval-rational.egg",
            "experimental/primitive-constructor-body.egg",
            "experimental/primitive-function-container.egg",
            "experimental/primitive-global-body.egg",
            "experimental/primitive-map-empty-output-context.egg",
            "experimental/primitive-overload-output-context.egg",
            "experimental/primitive-read-body.egg",
            "experimental/primitive-table-backed-body.egg",
            "experimental/primitive.egg",
            "experimental/web-demo/get-size.egg",
            "experimental/web-demo/math-backoff.egg",
            "experimental/web-demo/node-limit.egg",
        ],
        disposition: Disposition::StaticUnsupported {
            reason: "the ordinary proof-support predicate rejects this file before causal replay",
        },
    },
    AllowlistGroup {
        paths: &["core/causal-checked-alias-collision.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "collides with a user symbol",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["core/causal-late-input.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "input command executed after a run command",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["core/causal-late-source.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "source action executed after a run command",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &[
            "experimental/python_array_optimize_old.egg",
            "experimental/stresstest_large_expr_old.egg",
        ],
        disposition: Disposition::Unsupported {
            diagnostic: "causal replay does not support push/pop state",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["experimental/web-demo/multi-extract.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "causal replay does not support user-defined command `multi-extract`",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &[
            "core/bitwise.egg",
            "core/delete.egg",
            "core/fail_wrong_assertion.egg",
            "core/merge-during-rebuild.egg",
            "core/repro-desugar-143.egg",
            "core/repro-empty-query.egg",
            "core/repro-equal-constant2.egg",
            "core/repro-new-backend-prims.egg",
            "core/string_quotes.egg",
            "core/web-demo/fibonacci.egg",
            "core/web-demo/list.egg",
            "core/web-demo/push-pop.egg",
        ],
        disposition: Disposition::Unsupported {
            diagnostic: "causal equality checks currently require constructor/function-call endpoints",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &[
            "core/bool.egg",
            "core/f64.egg",
            "core/filter-or-bool-neq.egg",
            "core/i64.egg",
            "core/primitives.egg",
            "core/string.egg",
        ],
        disposition: Disposition::Unsupported {
            diagnostic: "causal equality checks do not support primitive or tuple endpoints",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &[
            "core/calc.egg",
            "core/container-fail.egg",
            "core/python_array_optimize.egg",
            "core/stresstest_large_expr.egg",
            "core/web-demo/lambda.egg",
        ],
        disposition: Disposition::Unsupported {
            diagnostic: "causal replay does not support push/pop state",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &[
            "core/combined-nested.egg",
            "core/container-proofs.egg",
            "core/include.egg",
            "core/relation-query-allowed.egg",
            "core/repro-noteqbug.egg",
            "core/test-combined-steps.egg",
            "core/web-demo/matrix.egg",
            "core/web-demo/naturals.egg",
            "core/web-demo/path.egg",
            "core/web-demo/schedule-demo.egg",
            "experimental/web-demo/for.egg",
            "experimental/web-demo/with-ruleset.egg",
        ],
        disposition: Disposition::Unsupported {
            diagnostic: "causal replay does not support nested fail commands",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["core/proofs/run-rule-selected.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "causal receipt recording does not support source run-rule schedules",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["core/run-rule.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "checked aliases are replay-only and cannot be recorded as causal sources",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["core/subsume-relation.egg", "core/web-demo/subsume.egg"],
        disposition: Disposition::StaticUnsupported {
            reason: "the ordinary proof suite manually excludes checks over subsumed values",
        },
    },
    AllowlistGroup {
        paths: &[
            "core/complex-merge-func.egg",
            "core/web-demo/rw-analysis.egg",
        ],
        disposition: Disposition::Unsupported {
            diagnostic: "merge reached an unsupported structural result expression",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["core/factoring-multisets.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "typed equality endpoint has no structural producer",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["core/repro-738-fn-sort.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "receipt-enabled action requires exact match witnesses",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &["core/uf-extraction.egg"],
        disposition: Disposition::Unsupported {
            diagnostic: "sort has a :internal-uf annotation",
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &[
            "core/repro-unsound.egg",
            "core/web-demo/levenshtein-distance.egg",
            "experimental/before-proofs-rational.egg",
            "experimental/math-rational.egg",
            "experimental/repro-unsound-rational.egg",
            "experimental/web-demo/rational.egg",
        ],
        disposition: Disposition::StaticUnsupported {
            reason: "the ordinary proof-support predicate rejects this historical proof shape",
        },
    },
    AllowlistGroup {
        paths: &["core/web-demo/eqsolve.egg"],
        disposition: Disposition::KnownReplayFailure {
            diagnostic: r#"tests/web-demo/eqsolve.egg: (check (= (Var "y") (Add (Add (Num 12) (Neg (Var "y"))) (Neg (Var "y")))))"#,
            artifact: ArtifactExpectation::Absent,
        },
    },
    AllowlistGroup {
        paths: &[
            "core/complex-merge-prim.egg",
            "core/merge-action-block.egg",
            "core/web-demo/fusion.egg",
        ],
        disposition: Disposition::StaticUnsupported {
            reason: "the ordinary proof-support predicate rejects this merge expression",
        },
    },
    AllowlistGroup {
        paths: &[
            "core/map.egg",
            "core/unsafe-seminaive-read-prim.egg",
            "core/web-demo/eqsat-basic-multiset.egg",
            "core/web-demo/unstable-fn.egg",
        ],
        disposition: Disposition::StaticUnsupported {
            reason: "the ordinary proof-support predicate rejects this primitive or container shape",
        },
    },
];

#[derive(Clone)]
pub struct CausalCase {
    pub name: String,
    pub path: PathBuf,
    pub working_directory: PathBuf,
    pub asset_directories: Vec<(PathBuf, PathBuf)>,
    pub binary: PathBuf,
    pub proof_supported: bool,
    pub allowlisted: Option<Disposition>,
}

impl CausalCase {
    pub fn into_trial(self, resolve_roots: RootResolver) -> Trial {
        Trial::test(format!("proofs/causal/{}", self.name), move || {
            run_case(&self, resolve_roots);
            Ok(())
        })
    }
}

pub fn disposition_for(path: &str, allowlist: &[AllowlistGroup]) -> Option<Disposition> {
    let mut found = None;
    let mut all_paths = std::collections::BTreeSet::new();
    for group in allowlist {
        match group.disposition {
            Disposition::StaticUnsupported { reason } => {
                assert!(!reason.is_empty(), "static causal exclusion has no reason");
            }
            Disposition::Unsupported { diagnostic, .. }
            | Disposition::KnownReplayFailure { diagnostic, .. } => {
                assert!(
                    !diagnostic.is_empty(),
                    "runtime causal exclusion has no diagnostic"
                );
            }
            Disposition::NoReplayRoot
            | Disposition::ExtractRootsUnsupported
            | Disposition::ChecksOnly => {}
        }
        for pair in group.paths.windows(2) {
            assert!(
                pair[0] < pair[1],
                "causal allowlist group must be sorted and duplicate-free: {:?} then {:?}",
                pair[0],
                pair[1]
            );
        }
        for entry in group.paths {
            assert!(
                entry.starts_with("core/")
                    || entry.starts_with("experimental/")
                    || entry.starts_with("workload/"),
                "causal allowlist entry has an unknown corpus prefix: {entry}"
            );
            assert!(
                all_paths.insert(*entry),
                "duplicate causal allowlist entry: {entry}"
            );
            if *entry == path {
                found = Some(group.disposition);
            }
        }
    }
    found
}

pub fn validate_allowlist(prefix: &str, discovered: &[String], allowlist: &[AllowlistGroup]) {
    let discovered: std::collections::BTreeSet<_> = discovered.iter().map(String::as_str).collect();
    for entry in allowlist.iter().flat_map(|group| group.paths) {
        if entry.starts_with(prefix) {
            assert!(
                discovered.contains(entry),
                "stale causal allowlist entry names a missing file: {entry}"
            );
        }
    }
}

fn run_case(case: &CausalCase, resolve_roots: RootResolver) {
    let source_roots = resolve_roots(&case.path, &case.working_directory)
        .unwrap_or_else(|error| panic!("failed to resolve {}: {error}", case.path.display()));
    let extract_roots_unsupported =
        matches!(case.allowlisted, Some(Disposition::ExtractRootsUnsupported));
    let classified_runtime_failure = matches!(
        case.allowlisted,
        Some(Disposition::Unsupported { .. } | Disposition::KnownReplayFailure { .. })
    );
    match case.allowlisted {
        Some(Disposition::NoReplayRoot) => {
            assert!(
                source_roots.checks.is_empty() && source_roots.extracts == 0,
                "{} is stale: it now has a check or extract replay root",
                case.name
            );
            return;
        }
        Some(Disposition::ExtractRootsUnsupported) => {
            assert!(
                source_roots.checks.is_empty() && source_roots.extracts > 0,
                "{} is stale: it is no longer extract-only",
                case.name
            );
        }
        Some(Disposition::ChecksOnly) => {
            assert!(
                !source_roots.checks.is_empty() && source_roots.extracts > 0,
                "{} is stale: it no longer combines check and unsupported extract roots",
                case.name
            );
        }
        _ => {}
    }
    if !extract_roots_unsupported && !classified_runtime_failure {
        assert!(
            !source_roots.checks.is_empty(),
            "{} has no positive check; classify it explicitly",
            case.name
        );
    }
    if let Some(Disposition::StaticUnsupported { reason }) = case.allowlisted {
        assert!(
            !case.proof_supported,
            "{} has stale static causal exclusion ({reason}): proof mode now supports it",
            case.name
        );
        return;
    }
    if !classified_runtime_failure && !extract_roots_unsupported {
        assert!(
            case.proof_supported,
            "{} is not proof-compatible; classify it as statically unsupported",
            case.name
        );
    }
    if case.allowlisted.is_none() {
        assert_eq!(
            source_roots.extracts, 0,
            "{} also has extract roots; classify its check-only coverage explicitly",
            case.name
        );
    }

    let sandbox = Sandbox::new(&case.name);
    for (assets, relative_destination) in &case.asset_directories {
        copy_assets(assets, &sandbox.path().join(relative_destination));
    }
    let artifact = sandbox.path().join("causal-replay.egg");
    let capture = Command::new(&case.binary)
        .current_dir(&case.working_directory)
        .args(["--proofs", "--causal-slice", "--causal-slice-output"])
        .arg(&artifact)
        .args(["--fact-directory"])
        .arg(sandbox.path())
        .arg(&case.path)
        .output()
        .unwrap_or_else(|error| panic!("failed to launch {}: {error}", case.binary.display()));

    match case.allowlisted {
        None | Some(Disposition::ChecksOnly) | Some(Disposition::ExtractRootsUnsupported) => {
            assert_success("causal capture", &case.name, &capture)
        }
        Some(Disposition::StaticUnsupported { .. }) => unreachable!(),
        Some(Disposition::Unsupported {
            diagnostic,
            artifact: expected,
        })
        | Some(Disposition::KnownReplayFailure {
            diagnostic,
            artifact: expected,
        }) => {
            assert_expected_failure(&case.name, &capture, diagnostic);
            assert_artifact(&case.name, &artifact, expected);
            return;
        }
        Some(Disposition::NoReplayRoot) => unreachable!(),
    }

    let artifact_roots = resolve_roots(&artifact, &case.working_directory)
        .unwrap_or_else(|error| panic!("failed to resolve {}: {error}", artifact.display()));
    if extract_roots_unsupported {
        assert!(
            artifact_roots.checks.is_empty(),
            "{} unexpectedly emitted checks while omitting extract roots",
            case.name
        );
    } else {
        assert_eq!(
            artifact_roots.checks, source_roots.checks,
            "{} did not preserve its ordered positive checks",
            case.name
        );
    }
    assert_eq!(artifact_roots.extracts, 0);

    let replay = run_strict_replay(case, &sandbox, &artifact);
    assert_success("strict replay", &case.name, &replay);
}

fn run_strict_replay(case: &CausalCase, sandbox: &Sandbox, artifact: &Path) -> Output {
    Command::new(&case.binary)
        .current_dir(&case.working_directory)
        .arg("--proof-testing")
        .args(["--fact-directory"])
        .arg(sandbox.path())
        .arg(artifact)
        .output()
        .unwrap_or_else(|error| panic!("failed to launch strict replay: {error}"))
}

fn assert_expected_failure(name: &str, output: &Output, diagnostic: &str) {
    assert!(
        !output.status.success(),
        "{name} is stale: causal replay now succeeds"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(diagnostic),
        "{name} changed failure signature; expected {diagnostic:?}, stderr:\n{stderr}"
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "{name} is classified unsupported but did not take the controlled CLI failure path:\n{stderr}"
    );
    assert!(
        !stderr.contains("panicked at"),
        "{name} is classified unsupported but panicked:\n{stderr}"
    );
}

fn assert_artifact(name: &str, artifact: &Path, expected: ArtifactExpectation) {
    assert_eq!(
        artifact.exists(),
        expected == ArtifactExpectation::Present,
        "{name} changed whether failure leaves an artifact"
    );
}

fn assert_success(stage: &str, name: &str, output: &Output) {
    if !output.status.success() {
        panic!(
            "{stage} failed for {name}:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn copy_assets(source: &Path, destination: &Path) {
    fn recurse(root: &Path, current: &Path, destination: &Path) {
        for entry in fs::read_dir(current)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", current.display()))
        {
            let entry = entry.expect("cannot read asset entry");
            let path = entry.path();
            let relative = path.strip_prefix(root).expect("asset path escaped root");
            let target = destination.join(relative);
            if path.is_dir() {
                fs::create_dir_all(&target).expect("cannot create asset directory");
                recurse(root, &path, destination);
            } else if path.extension() != Some(OsStr::new("egg")) {
                if let Some(parent) = target.parent() {
                    fs::create_dir_all(parent).expect("cannot create asset parent");
                }
                fs::copy(&path, &target).unwrap_or_else(|error| {
                    panic!(
                        "cannot copy {} to {}: {error}",
                        path.display(),
                        target.display()
                    )
                });
            }
        }
    }

    recurse(source, source, destination);
}

struct Sandbox(PathBuf);

impl Sandbox {
    fn new(name: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let id = NEXT.fetch_add(1, Ordering::Relaxed);
        let safe_name: String = name
            .chars()
            .map(|character| {
                if character.is_ascii_alphanumeric() {
                    character
                } else {
                    '_'
                }
            })
            .collect();
        let path = std::env::temp_dir().join(format!(
            "egglog-causal-corpus-{}-{id}-{safe_name}",
            std::process::id()
        ));
        fs::create_dir(&path)
            .unwrap_or_else(|error| panic!("cannot create {}: {error}", path.display()));
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for Sandbox {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0)
            .unwrap_or_else(|error| panic!("cannot remove {}: {error}", self.0.display()));
    }
}
