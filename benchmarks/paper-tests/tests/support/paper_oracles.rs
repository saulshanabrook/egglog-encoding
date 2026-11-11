//! Reject conditions without an oracle before registering or executing a trial.
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

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
            other => other,
        })
        .map(str::to_owned)
        .collect()
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
                    "slotted-no-aliasing",
                    "slotted-ref-multi",
                    "slotted-ref-nested",
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
