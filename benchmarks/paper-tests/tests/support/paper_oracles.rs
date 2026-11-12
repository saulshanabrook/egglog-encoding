//! Reject conditions without an oracle before registering or executing a trial.
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

/// Correctness trials default to one egraph worker; native drivers stay serial.
pub fn egraph_threads(value: Option<&std::ffi::OsStr>) -> Result<usize, &'static str> {
    match value {
        None => Ok(1),
        Some(value) => value
            .to_str()
            .and_then(|value| value.parse::<usize>().ok())
            .filter(|&threads| threads > 0)
            .ok_or("PAPER_EGRAPH_THREADS must be a positive integer"),
    }
}

/// Apply ordered inclusion and `!` exclusion globs before registering trials.
pub fn figure_files<'a>(
    directory: &Path,
    patterns: impl IntoIterator<Item = &'a str>,
) -> Vec<PathBuf> {
    let mut files = Vec::new();
    for pattern in patterns {
        let (exclude, glob_pattern) = pattern
            .strip_prefix('!')
            .map_or((false, pattern), |pattern| (true, pattern));
        assert!(!glob_pattern.is_empty(), "empty catalog file pattern");
        let mut matches: Vec<_> = glob::glob(directory.join(glob_pattern).to_str().unwrap())
            .unwrap()
            .map(Result::unwrap)
            .collect();
        assert!(
            !matches.is_empty(),
            "catalog pattern matched nothing: {pattern}"
        );
        matches.sort();
        for file in matches {
            assert!(file.is_file(), "not a workload file: {}", file.display());
            let file = file.canonicalize().unwrap();
            if exclude {
                files.retain(|selected| selected != &file);
            } else if !files.contains(&file) {
                files.push(file);
            }
        }
    }
    assert!(!files.is_empty(), "catalog patterns selected no files");
    files
}

/// Timed recording/extraction modes inherit strict proof oracles and exclusions.
/// Normalize before registration so generation-only names cannot bypass a
/// strict expected failure, resource deferral, or unsupported configuration.
pub fn correctness_modes<'a>(modes: impl IntoIterator<Item = &'a str>) -> BTreeSet<String> {
    modes
        .into_iter()
        .map(|mode| match mode {
            "proofs" | "proof-extraction" => "proof-testing",
            "egg-proofs" | "egg-proof-extraction" => "egg-proof-testing",
            "egg-nee-proof-extraction" => "egg-nee-proof-testing",
            "slotted-proof-extraction" => "slotted-proof-testing",
            "slotted-proof-extraction-no-aliasing" => "slotted-proof-testing-no-aliasing",
            "slotted-ref-multi-proofs" => "slotted-ref-multi-proof-testing",
            "slotted-ref-nested-proofs" => "slotted-ref-nested-proof-testing",
            other => other,
        })
        .map(str::to_owned)
        .collect()
}

/// Enabling certificates cannot bypass a base policy's unsupported/resource deferral.
pub fn exclusion_applies(treatments: &[String], mode: &str) -> bool {
    let base = match mode {
        "slotted-proof-testing" => "slotted",
        "slotted-proof-testing-no-aliasing" => "slotted-no-aliasing",
        "slotted-ref-multi-proof-testing" => "slotted-ref-multi",
        "slotted-ref-nested-proof-testing" => "slotted-ref-nested",
        "egg-nee-proof-testing" => "egg-nee",
        other => other,
    };
    treatments.is_empty()
        || treatments
            .iter()
            .any(|excluded| excluded == mode || excluded == base)
}

pub fn validate(root: &Path, file: &Path, modes: &BTreeSet<String>) -> Result<(), String> {
    let relative = file
        .strip_prefix(root)
        .map_err(|_| format!("paper input is outside the repository: {}", file.display()))?;
    let ordinary = ["off", "term", "proof-testing"];
    let (allowed, companion): (&[&str], Option<&str>) =
        if relative.starts_with("benchmarks/slotted/inputs") {
            (
                &[
                    "slotted",
                    "slotted-proof-testing",
                    "slotted-proof-testing-no-aliasing",
                    "slotted-no-aliasing",
                    "slotted-ref-multi",
                    "slotted-ref-multi-proof-testing",
                    "slotted-ref-nested",
                    "slotted-ref-nested-proof-testing",
                    "slotted-ref-nested-snapshot",
                ],
                Some("ref"),
            )
        } else if relative == Path::new("benchmarks/corpus/math/math-iteration-12.egg") {
            (
                &["off", "term", "proof-testing", "egg", "egg-proof-testing"],
                None,
            )
        } else if relative == Path::new("benchmarks/disequality/parameter-analysis.egg") {
            (
                &[
                    "off",
                    "term",
                    "proof-testing",
                    "egg-de",
                    "egg-ee",
                    "egg-nee",
                    "egg-nee-proof-testing",
                    "egg-oee",
                ],
                Some("in"),
            )
        } else {
            (&ordinary, None)
        };
    for mode in modes {
        if !allowed.contains(&mode.as_str()) {
            return Err(format!(
                "unmapped paper oracle: {}/{mode}",
                relative.display()
            ));
        }
    }
    for input in std::iter::once(file.to_path_buf())
        .chain(companion.map(|extension| file.with_extension(extension)))
    {
        if !input.is_file() {
            return Err(format!("missing physical paper input: {}", input.display()));
        }
    }
    Ok(())
}
