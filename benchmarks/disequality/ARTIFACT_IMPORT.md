# Dis/Equality Graphs artifact baseline

This is Stage 1 of a two-PR review. It establishes the published artifact as a
reviewable baseline. The egglog compiler, host integrations, tests, captures,
and performance reports are intentionally deferred to Stage 2 in PR #63.

## Verbatim artifact files

Commit `1cc22b6c09dde6642435b14330751f0a2c91453c` imports 213 files byte-for-byte
from Zenodo record [13938878](https://doi.org/10.5281/zenodo.13938878):

- the artifact README and `disegg.patch`;
- the EUF solver source, manifest, documentation, and runner;
- the Propel source, build files, scripts, and documentation; and
- all 128 small Propel benchmark inputs.

[`IMPORT_MANIFEST.json`](IMPORT_MANIFEST.json) records the archive path,
SHA-256, and size of every imported file. It also gives an explicit disposition
for all 7,608 omitted archive members, including the large EUF corpus,
container image, precomputed outputs, and parameter-analysis payload.

No file from that import commit is modified by this Stage 1 branch.
The root Cargo and Python configuration only excludes the nested third-party
projects from workspace discovery and repository linting; `.gitignore` records
their build and downloaded-corpus outputs.

## Reconstructed dependency

The archive includes `disegg.patch` and refers to an absolute `/disegg`
checkout, but does not contain that checkout. [`disegg/`](disegg/) reconstructs
it from the published egg 0.9.5 crate plus the archived patch. This directory is
derived third-party source, not a claim that those files occurred verbatim in
the Zenodo archive. [`disegg/ARTIFACT_PROVENANCE.md`](disegg/ARTIFACT_PROVENANCE.md)
documents the reconstruction and the one normalized-manifest adjustment.

## Review procedure

Stage 1 review has two independent checks:

1. Verify that the 213-file import commit matches the selected Zenodo members
   and that every omitted member has a recorded category.
2. Verify that `disegg/` is egg 0.9.5 with the published `disegg.patch` applied,
   subject only to the documented normalized `Cargo.toml` adjustment.

With `die-graph.zip` downloaded from the Zenodo record, run:

```sh
uv run --locked python benchmarks/disequality/scripts/verify_import.py \
  --archive /path/to/die-graph.zip \
  --check
```

The command compares archive bytes against the dedicated import commit rather
than the working tree. Stage 2 can therefore adapt selected artifact files
without weakening the provenance check.

## Merge sequence

Merge this artifact-baseline PR first. PR #63 is based on this branch so its
GitHub diff contains only the egglog implementation and evidence. After this
baseline lands on `main`, PR #63 can be retargeted to `main` without changing
its implementation diff.
