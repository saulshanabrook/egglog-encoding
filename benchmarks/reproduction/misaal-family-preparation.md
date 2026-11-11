# Fresh MISAAL family preparation

The combined fresh-build recipe is implemented and tested. Separate real
native preparations now cover all 102 host generators (32 x86, 31 ARM,
39 HVX). Their requests and current source/tool hashes were reverified, then
copied unchanged into
`benchmarks/local/reproduction/prerequisites/misaal-all-targets-attempt-0001/requests`.
The merge receipt records each original preparation and settings hash.
The complete fresh-build recipe has not yet been run from an empty environment;
these native results used the preserved common preparation plus documented
continuations. Full optimizer and replay results remain separate.

`scripts/reproduction_preparation.py` now prepares the common pinned44ff
MISAAL environment, followed by original x86, ARM and Hexagon targets in that
order. It calls the existing in-process APIs and never takes a nested heavy-job
lock. Every selected inventory ID is initialized before source preparation.
Each target gets its exact inventory subset, source/configuration identities
are checked, and all target outcomes remain in immutable
`preparation-{x86,arm,hexagon}.json` receipts.

The source setup step clears inherited `PYTHONPATH`, `DYLD_LIBRARY_PATH`,
and `LD_LIBRARY_PATH` before sourcing the pinned setup script. Its resulting
paths are captured explicitly, so older artifact environments cannot leak into
a fresh preparation.

ARM/HVX reuse the actual CMake executable recorded by common Halide preparation,
even if CMake is absent from PATH, and the Boost tree under `seed.preparation`.
The ARM API's own default was corrected to the same stable location; a
relocated x86 plugin no longer changes the inferred Boost path.

After all safe preparation steps finish, ready request JSON files are copied
byte-for-byte into one `attempt/requests` directory. Case/source/configuration
and recorded request SHA must still match. Changed requests become explicit
case blockers. Published settings retain the native backend, Python, LLVM,
libraries and declared request/runtime identities. Original target settings and
request receipts are not rewritten. Partial ordinary compiler/dependency
failures can publish usable settings for the other cases, with exact per-case
configuration blockers and evidence. This status does not claim source
optimization has completed.

A nested guard status or saved guard receipt stops all later target launches
and prevents combined settings publication. The target's successful prefix and
all inventory rows remain evidence. Launch refusals fail closed as a resource
stop. Shared dependency failure reaches no target generator recipe.

ARM also now verifies original full-file source pins before selector generation:
actual frontend semantics, original selector generator, raw metadata dictionary,
metadata reader, intrinsic metadata and original wrapper LLVM. Their SHA-256
values were calculated from `git show <pin>:<path>` only after verifying both
Git repository roots; full revision/blob/SHA evidence is in
`MISAAL-ARM-SOURCE-PINS.json`. All six working files match those immutable blobs.
Actual read-only ARM inspection still finds1152 concrete targets and5026
required wrapper definitions, all present.

`scripts/suite_reproduction.py` includes ARM/HVX preparation and the HVX lowering
helper in preparation implementation identity. It also binds both catalog and
paper-population manifest hashes. Regression tests show each
changed module or manifest invalidates a cached fresh MISAAL preparation while preserving
old receipts; no source captures launch during preparation.

Changed implementation files (all have retained baseline bytes):

- `scripts/reproduction_preparation.py`
- `scripts/reproduction_prepare_misaal_arm.py`
- `scripts/suite_reproduction.py`
- Corresponding `tests/test_reproduction_preparation.py`,
  `tests/test_reproduction_prepare_misaal_arm.py`,
  `tests/test_suite_reproduction.py`

Validation:93 focused mocked orchestration/ARM/coordinator/x86/HVX tests pass;
Ruff and Mypy pass on the six changed source/test files. Tests cover partial
failure, every-target guard stops (including wrapped receipts), all-case shared
failure, no-ready-request failure, changed requests, explicit CMake/Boost reuse,
ARM source pin drift, relocated plugin paths and implementation invalidation.
Those tests did not execute native builds. The separate actual native evidence
is summarized above. No target-device execution or performance collection is
part of this reproduction work.


## First clean run and bounded recovery

The first combined clean attempt,
`stages/misaal-prerequisites/prepare/0f67aafd362b6103c78806cf8933ead463a12b2749807023e8f46862ece0281a/attempt-0001`,
rebuilt the pinned backend and Halide successfully. The guard stopped compilation
of the53,680-line x86 selector at5.01GiB after43.2seconds. This failure remains
intact; no requests from this attempt were published. Its source and normalized
compiler flags match the earlier successful near-limit build.

The revised recipe overrides **only the host x86 selector's Release flags** with
`-O1 -DNDEBUG`, retaining the5GiB cap and assertions configuration. It also fixes
the selector's no-match fallthrough with an explicit `return false`; the common
legalizer accumulates a Boolean indicating changed instructions, and every
existing successful match branch remains byte-identical. The exact patch context
must match once. These changes do not alter Egglog rules, schedules or costs.

Focused tests and full-source context inspection pass. A fresh native build,
actual lowering/output checks and full source canary remain required before the
new selector can support corpus admission.


The second clean attempt `e4a9741a.../attempt-0001` reached the same5GiB limit
with the verified `-O1` flags (45.9seconds). A separately retained build-only
diagnostic, `diagnostics/misaal-x86-o0-build-0001`, changed only those flags to
`-O0 -DNDEBUG` in a fresh build directory. It succeeded in11.32seconds at2.65GiB,
with prior sources/receipts unchanged. The repeatable recipe now uses these
unoptimized **host selector** flags. Halide, the original backend and ordinary
replay engine retain their separate build settings. This diagnostic establishes
build feasibility, not full source reproduction or target-code correctness.

## Clean combined preparation outcome

The third clean preparation completed successfully at `benchmarks/local/reproduction/stages/misaal-prerequisites/prepare/de24509065a91a0011099031af73b866aad56a8f4ccd70149684696c620846b1/attempt-0001`. Both stage status and generator preparation status are `success`: 32 x86, 31 ARM, and 39 HVX requests were prepared and verified, with no configuration blockers. The source environment, backend, Halide, selectors, and all generators were built afresh. The x86 selector build took 11.9 seconds and its LLVM load check passed. The 5-GiB process-group cap and host/disk reserves were unchanged. This establishes preparation only; fresh native source optimization and standalone replay remain separate gates. The complete six-family settings are preserved in `prerequisites/misaal-clean-attempt-0003/settings.json`.

## Optional optimized original backend

A backend-only preparation can build the same pinned original Egglog revision
`6b6938bc0088163f61240482cd34a1579715b804` with Rust 1.91.0 and its original
archive, source, dependency lock, and default features:

```sh
python -m scripts.reproduction_prepare_misaal --optimized-backend-only \
  --storage benchmarks/local/reproduction/prerequisites/misaal-optimized-backend
```

The fixed `optimized-dev-assertions-v1` recipe uses the dev profile with
optimization level 3, debug information disabled, assertions and overflow checks
enabled, incremental compilation disabled, and one job. Each attempt owns fresh
Cargo-home and target directories. Compiler/profile/target environment overrides
are cleared. Ancestor Cargo configuration is rejected except for empty files and
the exact existing `kache` wrapper configuration, whose wrapper is explicitly
disabled. No Halide, selector, generator, or Racket preparation runs in this mode.
It uses the shared heavy-job lock, 5-GiB process-group guard, 2-GiB host reserve,
10-GiB disk reserve, and the existing preparation pressure policy.

A successful `backend.json` binds the complete source inventory, actual Cargo
and Rust compiler paths and hashes, Rust version, profile, preparer and guard
implementation hashes, Cargo configuration, build request/result/logs, and actual
executable hash. The binary hash is an observed identity, not a deterministic
build promise: the original `build.rs` embeds the current date and any parent Git
revision. Failed or stopped builds cannot supply a verified receipt.

A separate full clean preparation can reuse this exact verified product with
`--backend-receipt /absolute/attempt/path/backend.json`. It verifies the receipt
before preparing other dependencies and again before publishing the request,
which retains the receipt hash and provenance identities. Default full preparation
still builds the original unoptimized backend; historical `--backend` reuse still
requires its existing fixed binary hash. The three backend modes are mutually
exclusive, and historical repair retains its fixed-hash backend requirement.

This opt-in path is intended for finite source workloads. It does not fix ARM
`blur7x7`'s missing 16-bit pattern or its repeated residual lowering.

The guarded build in `prerequisites/misaal-optimized-backend/attempt-20260925T200917Z-744b6266`
completed successfully. Its verified executable SHA-256 is
`7f132999da6c101bfe0e077a3b1a9af00e57cc9e575a0888904c532ca7fdc5e5`.
`diagnostics/misaal-optimized-backend-output-controls-0001/summary.json` records
byte-identical outputs from both binaries on unchanged captured ARM blur3x3,
x86 blur3x3 and extra HVX tensor-add inputs; each also matches its historical
source result. These are source-compatibility diagnostics, not benchmark samples.
Complete native parent and ordinary-replay canaries are recorded separately in
`diagnostics/misaal-optimized-backend-source-canaries-0001/` before adoption.
