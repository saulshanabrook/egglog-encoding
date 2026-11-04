# Cordic core row-order repair: ready for guarded native validation

Only four proposed files change; root remains untouched. Patch:
`review/core-row-order.patch`
SHA-256 `ad254b06c601df6a05518c7b79f9b51796be5809f058480412945710589cb244`.
Exact root baseline and final file hashes: `review/handoff.json`.
Read-only `git apply --check` passed against those unchanged root baselines.

The repair is the exact upstream commit 201579a mail patch, with five production
lines and its original regression. The original Eggcc/Experimental/core pins
remain; three URL-scoped core overrides and nine source-field removals in a
separate derived lock keep all other dependency entries unchanged. Full core
source hashes and repair provenance enter the new family identity. There is no
assertion removal, engine upgrade, extractor/schedule change, or proof claim.

The callable is unchanged except optional `continue_from: Path | None`:
`prepare_eggcc(output, engine, *, build_root=None, timeout_sec=600, continue_from=None)`.
It uses its caller's shared heavy slot; CLI owns the lock. Both native gates use
Preparation's existing 5 GiB ceiling, 2 GiB reserve, 10 GiB disk reserve, warning-allowed guard and one Cargo
job. Core regression uses the original core workspace lock and exact one-test
filter; Eggcc uses the separately derived original lock. All source/lock hashes
are checked again before publishing settings.

Suggested root invocation after integration and when the heavy slot is free:

```sh
.venv/bin/python -m scripts.reproduction_prepare_eggcc \
  --output benchmarks/local/reproduction/prerequisites/eggcc-pr914/attempt-0001 \
  --continue-from benchmarks/local/reproduction/stages/eggcc-prerequisites/prepare/d6cd45c8d4e581fad03a3ed83179a6b716c4348d437526a2c63d0ba9d74a54b5/attempt-0001/environment \
  --egglog target/release/egglog-experimental \
  --timeout-sec 600
```

Use a fresh output if that name already exists. The original archive is verified
and extracted anew; old prepared sources, Tiger, binary, receipts and lockfiles
are untouched. The old 1.0 GiB Cargo target is cloned into new copy-on-write files,
then the corrected compiler must differ from the old bytes. Cargo writes only
a new home seeded with locked archives/index entries and independent Git objects.
No global Cargo config or mutable checkout is imported. New physical allocation
is estimated 1–3 GiB, not measured; 28 GiB free was observed before root's remaining
native gates. The existing 10 GiB reserve remains mandatory.

Validation completed without native jobs/builds:

- 14 focused mock tests: acquisition/source pins, exact patch, narrow lock changes,
private cache/checksums, borrowed Git cache refusal, actual-source command flow,
regression-before-build, old continuation bytes preserved, missing Tiger blocked.
- Ruff format/check and Mypy passed.
- Exact upstream patch applies to small copies of the actual pinned ebba files.
- Actual original continuation receipt/source/products/archive verified.
- Actual 291-package Eggcc lock retains 291 packages; exactly 9 source fields change.
Derived lock SHA 3addb0ed6a83aba28be309ed62c180c213943847fb1043182da8257d49c6a799.
Evidence: `review/offline-evidence.json`.
- Cargo peer independently reviewed source graph, preparation logic, tests and
fixture with no blocker. Final minor additions after that review: post-build
Eggcc source hash verification, cached-root symlink rejection, exact regression
summary prefix, and completed docs. Root should review those final deltas.

Root still owns actual upstream regression, locked build, Cordic complete parent
and ordinary replay validation. Preparation success is not benchmark admission.
All prior successful family evidence remains bound to its original identity.
