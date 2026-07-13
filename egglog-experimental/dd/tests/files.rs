//! Runs egglog's `.egg` corpus through the DD backend and checks each
//! result against egglog's OWN golden snapshot.
//!
//! egglog's `tests/files.rs` appends `(print-size)` to every corpus file and, for
//! each file, stores ONE snapshot (`egglog/tests/snapshots/
//! files__shared_snapshot_<stem>.snap`) whose content is normalized to be
//! identical across the native / term-encoding / proofs treatments
//! (`CommandOutput::snapshot_stable_under_proof_encoding`). DD is
//! term-encoded, so its normalized output must equal that shared snapshot. This
//! test reuses those files directly — egglog is the single source of truth, and
//! DD keeps no snapshots of its own.
//!
//! egglog's snapshot is only meaningful for DD when it is term-encoding
//! output: egglog runs the term-encoding treatment (and so the shared snapshot is
//! stable across native + term encoding) exactly when `file_supports_proofs`. For
//! files that don't support proofs the snapshot is native-only, which a
//! term-encoded backend needn't reproduce, so those are skipped.
//!
//! Per (proof-supporting) corpus file:
//! - DD can't run it (an unsupported FEATURE — see [`KNOWN_UNSUPPORTED`]) →
//!   passes only if listed; a new failure (or a listed file that starts working)
//!   fails the harness so the list stays honest;
//! - DD runs it and its normalized output equals egglog's snapshot → pass;
//! - otherwise the normal insta assertion reports the mismatch.
//!
//! Run with `--release`: differential-dataflow is impractically slow in debug
//! builds. Under `cargo test` (debug) this harness covers only a fast
//! [`DEBUG_SUBSET`]; `cargo test --release` runs the whole corpus.

use egglog::{file_supports_proofs, CommandOutput, EGraph};
use libtest_mimic::{Arguments, Failed, Trial};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;

/// Files that saturate too slowly on the differential-dataflow path to belong in
/// a test suite. Skipped entirely (not run on DD).
const HANG: &[&str] = &[
    "eggcc-2mm.egg",
    "eqsolve.egg",
    "math-microbenchmark.egg",
    "rectangle.egg",
    "repro-herbie-vanilla.egg",
    "resolution.egg",
    "until.egg",
];

/// A fast, representative slice of the corpus run under debug builds (where
/// differential-dataflow is too slow for the full set). `--release` runs
/// everything. All of these match egglog's snapshot (including `eqsat-basic`,
/// which exercises multi-step congruence closure).
const DEBUG_SUBSET: &[&str] = &[
    "i64.egg",
    "bitwise.egg",
    "string.egg",
    "path.egg",
    "birewrite.egg",
    "eqsat-basic.egg",
];

/// Files egglog snapshots but DD cannot run, because they use a FEATURE this
/// simplified backend does not implement (as opposed to a wrong answer, of which
/// there are none). Listed explicitly so the harness fails if the set changes in
/// either direction. Reasons:
///
/// - push/pop (needs backend snapshotting / `clone_boxed`, which a live
///   differential-dataflow dataflow cannot provide):
///   `array`, `bdd`, `calc`, `container-fail`, `lambda`, `math`, `push-pop`.
/// - container rebuild read primitives (registered through egglog's
///   `ActionRegistry`; DD has direct container storage but no registry
///   execution state for read primitives over its term-encoded mirror):
///   `container-proofs`, `datatypes`, `nested-container-dirty-propagation`,
///   `repro-querybug3`.
const KNOWN_UNSUPPORTED: &[&str] = &[
    "array.egg",
    "bdd.egg",
    "calc.egg",
    "container-fail.egg",
    "container-proofs.egg",
    "datatypes.egg",
    "lambda.egg",
    "math.egg",
    "nested-container-dirty-propagation.egg",
    "push-pop.egg",
    "repro-querybug3.egg",
];

/// Run `program` on DD and render its outputs with the SAME normalization
/// egglog's snapshot used, so the two are directly comparable.
fn run_dd(file: &str, program: &str) -> Result<String, String> {
    let mut eg =
        EGraph::with_backend(Box::new(egglog_experimental_dd::EGraph::new())).with_term_encoding();
    match eg.parse_and_run_program(Some(file.to_string()), program) {
        Ok(outs) => Ok(CommandOutput::snapshot_stable_under_proof_encoding(&outs)
            .trim_end()
            .to_string()),
        Err(e) => Err(e.to_string()),
    }
}

fn check(path: &PathBuf) -> Result<(), Failed> {
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    let stem = path
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .replace(['.', '-', ' '], "_");

    // egglog only produces a term-encoding-valid shared snapshot for files that
    // support proofs (it runs the term-encoding treatment then). Otherwise the
    // snapshot is native-only, which a term-encoded backend needn't reproduce.
    if !file_supports_proofs(path) {
        return Ok(());
    }
    let src = std::fs::read_to_string(path).map_err(|e| format!("read {name}: {e}"))?;
    let program = format!("{src}\n(print-size)");
    let file = path.display().to_string();
    let dd = catch_unwind(AssertUnwindSafe(|| run_dd(&file, &program)));

    let unsupported = KNOWN_UNSUPPORTED.contains(&name.as_str());
    match dd {
        // DD couldn't run it (unsupported feature or a panic). Fine only if
        // documented; a new failure means the list is stale.
        Ok(Err(err)) => {
            if unsupported {
                Ok(())
            } else {
                Err(format!(
                    "{name}: DD failed but is not in KNOWN_UNSUPPORTED — \
                     add it (with the reason) or investigate the regression\n\
                     error: {err}"
                )
                .into())
            }
        }
        Err(panic) => {
            if unsupported {
                Ok(())
            } else {
                let panic = panic
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| panic.downcast_ref::<&str>().copied())
                    .unwrap_or("<non-string panic payload>");
                Err(format!(
                    "{name}: DD panicked but is not in KNOWN_UNSUPPORTED — \
                     add it (with the reason) or investigate the regression\n\
                     panic: {panic}"
                )
                .into())
            }
        }
        Ok(Ok(_)) if unsupported => Err(format!(
            "{name} is listed in KNOWN_UNSUPPORTED but now runs — remove it from that list"
        )
        .into()),
        Ok(Ok(out)) => {
            let mut settings = insta::Settings::clone_current();
            settings.set_snapshot_path("../../../egglog/tests/snapshots");
            settings.bind(|| {
                insta::assert_snapshot!(format!("shared_snapshot_{stem}"), out);
            });
            Ok(())
        }
    }
}

fn corpus() -> Vec<PathBuf> {
    let mut v = vec![];
    for dir in ["../../egglog/tests", "../../egglog/tests/web-demo"] {
        if let Ok(rd) = std::fs::read_dir(dir) {
            for e in rd.flatten() {
                let p = e.path();
                if p.extension().and_then(|s| s.to_str()) == Some("egg") {
                    let name = p.file_name().unwrap().to_string_lossy().to_string();
                    let debug_ok = !cfg!(debug_assertions) || DEBUG_SUBSET.contains(&name.as_str());
                    if !HANG.contains(&name.as_str()) && debug_ok {
                        v.push(p);
                    }
                }
            }
        }
    }
    v.sort();
    v
}

fn main() {
    let args = Arguments::from_args();
    let trials = corpus()
        .into_iter()
        .map(|path| {
            let name = path
                .file_stem()
                .unwrap()
                .to_string_lossy()
                .replace(['-', '.'], "_");
            Trial::test(name, move || check(&path))
        })
        .collect();
    libtest_mimic::run(&args, trials).exit();
}
