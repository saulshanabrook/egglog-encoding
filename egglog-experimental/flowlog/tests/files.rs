//! Runs egglog's whole `.egg` test corpus through the FlowLog backend, mirroring
//! egglog's own `tests/files.rs` (a libtest-mimic harness, one trial per file)
//! but generalized to a backend that supports only a subset of egglog.
//!
//! Both backends run TERM-ENCODED. FlowLog has no native union-find, so it
//! requires term encoding (congruence and rebuild lower to rules over `@uf`
//! tables). The reference is therefore a term-encoded bridge e-graph too, so
//! `(print-size)` compares like-for-like — a native reference would show
//! different (un-encoded) functions and mismatch spuriously.
//!
//! For each corpus file, the trial runs the program (with `(print-size)`
//! appended) on BOTH backends and then:
//!
//! - if the reference can't run it (a term-encoding limitation — proofs,
//!   containers, function extraction, …), it isn't a FlowLog concern: skip;
//! - if FlowLog runs it and the final `(print-size)` matches the reference, the
//!   output is snapshotted (`insta`) — the cross-backend agreement + regression
//!   pin;
//! - if FlowLog runs it but the output DIFFERS, the trial FAILS (there are
//!   currently no such files);
//! - if FlowLog can't run it (an unsupported FEATURE — see [`KNOWN_UNSUPPORTED`]),
//!   the trial passes only if the file is in that list; a NEW failure fails the
//!   harness, and a listed file that starts working also fails it (so the list
//!   stays honest).
//!
//! Run with `--release`: differential-dataflow is impractically slow in debug
//! builds. Under `cargo test` (debug) this harness covers only a fast
//! [`DEBUG_SUBSET`]; `cargo test --release` runs the whole corpus.

use egglog::EGraph;
use libtest_mimic::{Arguments, Failed, Trial};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;

/// Files that saturate too slowly on the differential-dataflow path to belong in
/// a test suite. Skipped entirely (not run on FlowLog).
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
/// everything. All of these MATCH the reference (including `eqsat-basic`, which
/// exercises multi-step congruence closure).
const DEBUG_SUBSET: &[&str] = &[
    "i64.egg",
    "bitwise.egg",
    "string.egg",
    "path.egg",
    "birewrite.egg",
    "eqsat-basic.egg",
];

/// Files the reference runs but FlowLog cannot, because they use a FEATURE this
/// simplified backend does not implement (as opposed to a wrong answer, of which
/// there are none). Listed explicitly so the harness fails if the set changes in
/// either direction. Reasons:
///
/// - push/pop (needs backend snapshotting / `clone_boxed`, which a live
///   differential-dataflow dataflow cannot provide):
///   `calc`, `array`, `bdd`, `math`, `push-pop`.
const KNOWN_UNSUPPORTED: &[&str] = &[
    "array.egg",
    "bdd.egg",
    "calc.egg",
    "math.egg",
    "push-pop.egg",
];

fn run(reference: bool, file: &str, program: &str) -> Result<String, String> {
    let mut eg = if reference {
        EGraph::new_with_term_encoding()
    } else {
        // FlowLog requires term encoding (it has no native union-find);
        // congruence and rebuild lower to rules over `@uf` tables.
        EGraph::with_backend(Box::new(
            egglog_experimental_flowlog::EGraph::new_interpret(),
        ))
        .with_term_encoding()
    };
    match eg.parse_and_run_program(Some(file.to_string()), program) {
        // The trailing `(print-size)` is the last command; its output is a
        // per-function row-count summary of the final database.
        Ok(outs) => Ok(outs.last().map(|o| o.to_string()).unwrap_or_default()),
        Err(e) => Err(e.to_string()),
    }
}

fn check(path: &PathBuf) -> Result<(), Failed> {
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    let src = std::fs::read_to_string(path).map_err(|e| format!("read {name}: {e}"))?;
    let program = format!("{src}\n(print-size)");
    let file = path.display().to_string();

    // The reference backend is the oracle. If it can't run the program (a
    // term-encoding limitation or a fail-typecheck fixture), this isn't a FlowLog
    // concern — skip.
    let reference = match catch_unwind(AssertUnwindSafe(|| run(true, &file, &program))) {
        Ok(Ok(s)) => s,
        _ => return Ok(()),
    };

    let flowlog = catch_unwind(AssertUnwindSafe(|| run(false, &file, &program)));
    let unsupported = KNOWN_UNSUPPORTED.contains(&name.as_str());

    match flowlog {
        // FlowLog couldn't run it (unsupported feature or a panic). Fine only if
        // documented; a new failure means the list is stale.
        Ok(Err(_)) | Err(_) => {
            if unsupported {
                Ok(())
            } else {
                Err(format!(
                    "{name}: FlowLog failed but is not in KNOWN_UNSUPPORTED — \
                     add it (with the reason) or investigate the regression"
                )
                .into())
            }
        }
        Ok(Ok(out)) if out == reference => {
            if unsupported {
                return Err(format!(
                    "{name} is listed in KNOWN_UNSUPPORTED but now matches the \
                     reference — remove it from that list"
                )
                .into());
            }
            let stem = name.trim_end_matches(".egg").replace(['-', '.'], "_");
            insta::assert_snapshot!(stem, out);
            Ok(())
        }
        Ok(Ok(out)) => Err(format!(
            "{name}: FlowLog disagrees with the reference backend\n\
             --- reference ---\n{reference}\n--- flowlog ---\n{out}"
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
