//! Runs egglog's `.egg` corpus through the FlowLog backend and checks each
//! result against egglog's OWN golden snapshot.
//!
//! egglog's `tests/files.rs` appends `(print-size)` to every corpus file and, for
//! each file, stores ONE snapshot (`egglog/tests/snapshots/
//! files__shared_snapshot_<stem>.snap`) whose content is normalized to be
//! identical across the native / term-encoding / proofs treatments
//! (`CommandOutput::snapshot_stable_under_proof_encoding`). FlowLog is
//! term-encoded, so its normalized output must equal that shared snapshot. This
//! test reuses those files directly — egglog is the single source of truth, and
//! FlowLog keeps no snapshots of its own.
//!
//! egglog's snapshot is only meaningful for FlowLog when it is term-encoding
//! output: egglog runs the term-encoding treatment (and so the shared snapshot is
//! stable across native + term encoding) exactly when `file_supports_proofs`. For
//! files that don't support proofs the snapshot is native-only, which a
//! term-encoded backend needn't reproduce, so those are skipped.
//!
//! Per (proof-supporting) corpus file:
//! - FlowLog can't run it (an unsupported FEATURE — see [`KNOWN_UNSUPPORTED`]) →
//!   passes only if listed; a new failure (or a listed file that starts working)
//!   fails the harness so the list stays honest;
//! - FlowLog runs it and its normalized output equals egglog's snapshot → pass;
//! - otherwise it DIFFERS from egglog → fail, unless in [`KNOWN_MISMATCH`].
//!
//! Run with `--release`: differential-dataflow is impractically slow in debug
//! builds. Under `cargo test` (debug) this harness covers only a fast
//! [`DEBUG_SUBSET`]; `cargo test --release` runs the whole corpus.

use egglog::{file_supports_proofs, CommandOutput, EGraph};
use libtest_mimic::{Arguments, Failed, Trial};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;

/// egglog's shared golden snapshots (one per corpus file, stable across
/// treatments), which this harness checks FlowLog against.
const EGGLOG_SNAPSHOTS: &str = "../../egglog/tests/snapshots";

/// Files that saturate too slowly on the differential-dataflow path to belong in
/// a test suite. Skipped entirely (not run on FlowLog).
const HANG: &[&str] = &[
    "eggcc-2mm.egg",
    "eggcc-2mm-pass1-merge-old.egg",
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

/// Files egglog snapshots but FlowLog cannot run, because they use a FEATURE this
/// simplified backend does not implement (as opposed to a wrong answer, of which
/// there are none). Listed explicitly so the harness fails if the set changes in
/// either direction. Reasons:
///
/// - push/pop (needs backend snapshotting / `clone_boxed`, which a live
///   differential-dataflow dataflow cannot provide):
///   `calc`, `array`, `bdd`, `lambda`, `math`, `push-pop`.
const KNOWN_UNSUPPORTED: &[&str] = &[
    "array.egg",
    "bdd.egg",
    "calc.egg",
    "lambda.egg",
    "math.egg",
    "push-pop.egg",
];

/// Files FlowLog runs but whose output DIVERGES from egglog's snapshot — real
/// bugs surfaced by comparing the full normalized output. Keep this list empty:
/// any matching failure should either be fixed or documented narrowly here.
const KNOWN_MISMATCH: &[&str] = &[];

/// The stable content of egglog's shared snapshot for `stem`, if egglog produced
/// one. Strips insta's `---`-delimited YAML header.
fn egglog_snapshot(stem: &str) -> Option<String> {
    let path = format!("{EGGLOG_SNAPSHOTS}/files__shared_snapshot_{stem}.snap");
    let raw = std::fs::read_to_string(path).ok()?;
    // insta format: `---\n<yaml header>\n---\n<content>`.
    let content = raw.splitn(3, "---\n").nth(2)?;
    Some(content.trim_end().to_string())
}

/// Run `program` on FlowLog and render its outputs with the SAME normalization
/// egglog's snapshot used, so the two are directly comparable.
fn run_flowlog(file: &str, program: &str) -> Result<String, String> {
    let mut eg = EGraph::with_backend(Box::new(
        egglog_experimental_flowlog::EGraph::new_interpret(),
    ))
    .with_term_encoding();
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
    // A proof-supporting file that egglog ran always has a snapshot; be defensive.
    let Some(expected) = egglog_snapshot(&stem) else {
        return Ok(());
    };

    let src = std::fs::read_to_string(path).map_err(|e| format!("read {name}: {e}"))?;
    let program = format!("{src}\n(print-size)");
    let file = path.display().to_string();
    let flowlog = catch_unwind(AssertUnwindSafe(|| run_flowlog(&file, &program)));

    let unsupported = KNOWN_UNSUPPORTED.contains(&name.as_str());
    let known_mismatch = KNOWN_MISMATCH.contains(&name.as_str());

    match flowlog {
        // FlowLog couldn't run it (unsupported feature or a panic). Fine only if
        // documented; a new failure means the list is stale.
        Ok(Err(err)) => {
            if unsupported {
                Ok(())
            } else {
                Err(format!(
                    "{name}: FlowLog failed but is not in KNOWN_UNSUPPORTED — \
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
                    "{name}: FlowLog panicked but is not in KNOWN_UNSUPPORTED — \
                     add it (with the reason) or investigate the regression\n\
                     panic: {panic}"
                )
                .into())
            }
        }
        Ok(Ok(out)) if out == expected => {
            if unsupported {
                Err(format!(
                    "{name} is listed in KNOWN_UNSUPPORTED but now matches egglog's \
                     snapshot — remove it from that list"
                )
                .into())
            } else if known_mismatch {
                Err(format!(
                    "{name} is listed in KNOWN_MISMATCH but now matches egglog's \
                     snapshot — remove it from that list"
                )
                .into())
            } else {
                Ok(())
            }
        }
        // Documented divergence: still differs (checked above), don't fail.
        Ok(Ok(_)) if known_mismatch => Ok(()),
        Ok(Ok(out)) => Err(format!(
            "{name}: FlowLog disagrees with egglog's snapshot\n\
             --- egglog ---\n{expected}\n--- flowlog ---\n{out}"
        )
        .into()),
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
    // FlowLog panics on features it can't lower; keep the output clean while
    // `catch_unwind` turns those into a KNOWN_UNSUPPORTED check.
    std::panic::set_hook(Box::new(|_| {}));
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
