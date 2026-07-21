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
//!   passes only if the returned error contains that file's expected diagnostic;
//!   panics, new failures, and listed files that start working all fail the
//!   harness so the list stays honest;
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
/// - container rebuild read primitives (registered through egglog's
///   `ActionRegistry`; DD has direct container storage but no registry
///   execution state for read primitives over its term-encoded mirror):
///   `container-proofs`, `container-fail`, `container-reorder-proofs`,
///   `custom-container-output-rebuild`, `datatypes`,
///   `nested-container-dirty-propagation`, `hardboiled_conv1d_32`,
///   `repro-querybug3`.
/// - `input` from an external CSV whose path is relative to the corpus dir; the
///   DD harness runs from the `dd` crate root, so the file cannot be found:
///   `string_quotes`.
const KNOWN_UNSUPPORTED: &[(&str, &str)] = &[
    ("container-proofs.egg", "requires a backend action registry"),
    ("container-fail.egg", "requires a backend action registry"),
    (
        "container-reorder-proofs.egg",
        "requires a backend action registry",
    ),
    (
        "custom-container-output-rebuild.egg",
        "requires a backend action registry",
    ),
    ("repro-querybug3.egg", "requires a backend action registry"),
    ("datatypes.egg", "requires a backend action registry"),
    (
        "nested-container-dirty-propagation.egg",
        "requires a backend action registry",
    ),
    (
        "hardboiled_conv1d_32.egg",
        "requires a backend action registry",
    ),
    ("string_quotes.egg", "string_quotes.csv"),
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
    let name = path
        .file_name()
        .ok_or_else(|| format!("corpus path has no file name: {}", path.display()))?
        .to_string_lossy()
        .to_string();
    let stem = path
        .file_stem()
        .ok_or_else(|| format!("corpus path has no file stem: {}", path.display()))?
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

    let expected_unsupported = KNOWN_UNSUPPORTED
        .iter()
        .find_map(|&(file, expected)| (file == name).then_some(expected));
    match dd {
        Ok(Err(err)) => match expected_unsupported {
            Some(expected) if err.contains(expected) => Ok(()),
            Some(expected) => Err(format!(
                "{name}: DD returned the wrong controlled error for a known unsupported feature\n\
                 expected diagnostic containing: {expected}\n\
                 actual error: {err}"
            )
            .into()),
            None => Err(format!(
                "{name}: DD failed but is not in KNOWN_UNSUPPORTED — \
                     add it with an expected controlled diagnostic or investigate the regression\n\
                     error: {err}"
            )
            .into()),
        },
        Err(panic) => {
            let panic = panic
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| panic.downcast_ref::<&str>().copied())
                .unwrap_or("<non-string panic payload>");
            Err(format!(
                "{name}: DD panicked; unsupported cases must return their documented controlled error\n\
                 panic: {panic}"
            )
            .into())
        }
        Ok(Ok(_)) if expected_unsupported.is_some() => Err(format!(
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

fn corpus_from_dirs(dirs: &[&str]) -> Result<Vec<PathBuf>, String> {
    let mut v = vec![];
    for dir in dirs {
        let rd =
            std::fs::read_dir(dir).map_err(|error| format!("read corpus dir {dir}: {error}"))?;
        for entry in rd {
            let entry =
                entry.map_err(|error| format!("read entry in corpus dir {dir}: {error}"))?;
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) == Some("egg") {
                let name = p
                    .file_name()
                    .ok_or_else(|| format!("corpus path has no file name: {}", p.display()))?
                    .to_string_lossy()
                    .to_string();
                let debug_ok = !cfg!(debug_assertions) || DEBUG_SUBSET.contains(&name.as_str());
                if !HANG.contains(&name.as_str()) && debug_ok {
                    v.push(p);
                }
            }
        }
    }
    v.sort();
    if v.is_empty() {
        return Err("DD corpus selection is empty".to_string());
    }
    Ok(v)
}

fn corpus() -> Result<Vec<PathBuf>, String> {
    corpus_from_dirs(&["../../egglog/tests", "../../egglog/tests/web-demo"])
}

fn main() {
    let args = Arguments::from_args();
    let mut trials = vec![
        Trial::test("missing_corpus_directory_is_an_error", || {
            corpus_from_dirs(&["__egglog_dd_missing_corpus_directory__"])
                .expect_err("missing corpus directory must fail discovery");
            Ok(())
        }),
        Trial::test("empty_corpus_selection_is_an_error", || {
            corpus_from_dirs(&[]).expect_err("empty corpus selection must fail discovery");
            Ok(())
        }),
    ];
    match corpus() {
        Ok(paths) => trials.extend(paths.into_iter().map(|path| {
            let name = path
                .file_stem()
                .expect("validated corpus path must have a file stem")
                .to_string_lossy()
                .replace(['-', '.'], "_");
            Trial::test(name, move || check(&path))
        })),
        Err(error) => trials.push(Trial::test("corpus_discovery", move || Err(error.into()))),
    }
    libtest_mimic::run(&args, trials).exit();
}
