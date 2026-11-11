# HardBoiled / MISAAL adapter handoff

The first section records the initial adapter-only slice. The later native
prerequisite slice below supersedes its statement that no builds/downloads ran.

Work is confined to this isolated mirror. No original source tree, live root,
catalog, cache or stored acquisition record was changed. No native build,
generator, download or container has run. `.baseline` retains the original four
owned files for review.

Implemented:

- `scripts/suite_capture_hardboiled_misaal.py`: optional complete HardBoiled AOT
  source-copy adaptation; actual sidecar selections/status receipts; native
  output verification; complete-only replay preparation; explicit case/revision
  inputs for future reviewed mappings.
- `scripts/hardboiled_replay.py`: all-root checks against actual selections,
  preserving extract commands and scope, without adding witness inputs.
- `scripts/misaal_reproduction.py`: callable request API; real generated-child
  interception; guarded backend/LLVM subprocesses; fresh feedback validation and
  continuation of the original Halide parent; exact replay/check contracts.
- Focused tests cover original behavior, all-root scope, failed-parent
  quarantine, source/output hashes, live child-to-parent feedback, duplicate
  calls, and failure propagation. Fake native tools are protocol tests only.
- `benchmarks/reproduction/misaal-hardboiled.md`: API, schema, inspected source
  paths, proposed first canaries, prerequisites and validation gates.

Validation: `pytest` on `test_misaal_reproduction.py`,
`test_hardboiled_replay.py` and `test_suite_capture_hardboiled_misaal.py` passed
**74 tests**. Ruff lint, Ruff formatting checks and Mypy passed on those three
tests and the three corresponding implementation modules. Only lightweight
Python protocol tests ran. Native success, ordinary replay compatibility and
strict proof validity remain untested for the new complete path. Existing
historical evidence does not satisfy them.

Next gated work: acquire/verify a full HardBoiled source/build and real sidecar,
then the single VNNI 1x1 AOT canary; separately prepare MISAAL candidate
`44ff893445d664cd87f52b08a138260ed2015ba8` with pinned dependencies, a fresh pattern
cache, matching LLVM/legalizers and a built HVX add generator. The source/type
mapping from five current AMX programs to seven supported paper cells is not
invented here. Root must grant the heavy slot before any of these operations.

## Native MISAAL prerequisite slice — completed 2026-09-25 UTC

New mirror files: `scripts/reproduction_prepare_misaal.py` and
`tests/test_reproduction_prepare_misaal.py`. Root's latest `benchmarking/pilot.py`,
`benchmarking/memory_guard.py`, `scripts/reproduction_process.py` and
`scripts/reproduction_stages.py` were copied into the mirror without changing
their implementation. Live root copies and all capture adapters were untouched.

The heavy job used the shared
`benchmarks/local/reproduction/stages/.heavy-job.lock`, one compiler job, required
host guard, warning-pressure diagnostic allowance, 5 GiB process-group limit,
10 GiB disk reserve and 600/1800-second step limits. **The lock is released.**

Actual attempt (all paths below are relative to it):
`/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc`.

- Acquired full MISAAL `44ff893445d664cd87f52b08a138260ed2015ba8` and required
  Hydride subtrees at `beb825327fc946d65032e96f7cde9acf3d24c13e`; exact Git steps
  and identities are retained. Reused the verified native Egglog6b6938 backend
  and Homebrew LLVM12.0.1.
- Built new Halide in 188.5s, sampled peak 572,964,864 bytes. Its SHA-256 is
  `1276349f99b13dd321cf65dea2a56df5fef2c6acab637fbd2a2a2a53a8e1451f`.
- Original x86 legalizer compilation failed on twelve C++ integer literals
  exceeding built-in integer types. `patches/legalizer-exact-wide-constants.patch`
  constructs those same decimal values using the already-declared Boost
  `int512_t` type. The first bounded repair built successfully in 75.1s and
  loaded/registers its pass in LLVM12. **Sampled peak 5,308,596,224 bytes (~4.94
  GiB), close to the 5 GiB cap.** Legalizer SHA-256:
  `2546d4239f78028ecfbd3a4c63916e83910b577de57f7c632ed108279824c48b`.
- Prepared the exact Python environment, including sympy/ply and the pinned
  vendored llvmlite IR package. Real Rose imports passed. The original x86
  blur3x3 generator compiled in 2.3s; SHA-256:
  `be66a3fdf2fcc884cd3dbb570648cdf6aa519ff9ffe8cd2bef4e0bf4685c4a2e`.
- Preserved original failure, repair summary, exact executing preparer snapshots
  and numbered command/results/logs. An earlier empty attempt
  `attempt-20260925T051709Z-4b75e089` records a local prefixed-versus-raw-hash
  validation mistake; no child or source acquisition ran there.

**Use `capture-request-isolated-cache.json`, not the initial `capture-request.json`.**
The reviewed request SHA-256 is
`a02855f71d1322f7edab380d2ef8e30f321877e212856333cfff9d94ceab2c03`.
It has the inventory's exact source directory/configuration, actual generator
source hash and all native tool hashes. `request-review.json` records successful
validation by the live root adapter's `verified_request` plus matching catalog
source/configuration. `environment_unset` is empty.

At root's request, four additional saved Python source patches redirect only
Halide/x86/ARM/HVX pickle filenames through optional `MISAAL_PATTERN_CACHE_DIR`.
Pattern generation/content and original default cache paths are unchanged. The
reviewed request hashes all four updated modules. Root's adapter must create a
fresh empty attempt-owned cache directory, set the variable before original
Python imports and retain resulting cache hashes. No pattern import, source
generator execution, complete capture, replay validation, proof validation or
performance-cache/catalog mutation was performed. Source `lib/patterns` has no
pickle files. This is readiness for the single canary, not a reproduction result.

Final lightweight checks: six focused tests passed; Ruff lint/format and Mypy
passed for the new preparer and test module. Tests cover mandatory guard options,
failure retention, exact-context/owned-source patching, immutable receipts, raw
capture hash format, unchanged wide decimal values and cache path fallback /
override behavior. No claims of native success rely on these mocks.

## 2026-09-25 HardBoiled preparation implementation (no heavy execution)

Added `scripts/reproduction_prepare_hardboiled.py`, five focused tests and
`HARDBOILED-PREPARATION.md`. The script acquires exact full artifact/sidecar/Egglog
pins, preflights LLVM18's native WebAssembly/X86/NVPTX development packages,
reuses the required guarded immutable step runner, builds with one job, and
publishes coordinator settings for one unchanged AMX and one unchanged GPU case
only after real build outputs exist. No source builds/downloads/generators ran
in this slice. Local LLVM package presence was inspected read-only. Twelve
combined preparer tests, Ruff lint/format and Mypy passed; mocks are not runtime
reproduction evidence. GPU adapter gaps and exact commands are in the handoff.

Also incorporated root's review of MISAAL preparation: fresh runs now apply the
reviewed 12-constant `int512_t` repair **before** the first legalizer build.
`patch_wide_literals` owns the exact context/count/range invariant and is reused
by the explicit retained-failure repair path. Original actual failure logs and
prior attempt receipts remain unchanged. Seven MISAAL preparer tests pass.

## 2026-09-25 Repeatable Eggcc Statewalk preparation (lightweight only)

Added `scripts/reproduction_prepare_eggcc.py`, five focused tests and
`EGGCC-PREPARATION.md`. The in-process API takes no lock; CLI owns the shared
lock. It downloads/hash-checks the exact source archive from the retained
successful build, applies the current shared observation instrumenter, preserves
Rust1.88/LLVM18/debug0/incremental0/jobs1 and requires both Eggcc and Tiger.
Sources/inputs/receipts/settings are durable; optional Cargo target is disposable.
Gurobi's exact native options remain explicitly blocked because the real CLI is
missing and the user has no licensed access. No extractor substitution.

Read-only evidence: actual prior build104.30s; latest inspected Statewalk fact
canary14ce072 reports completed native parent and six ordinary replay sessions.
No new build/capture/download ran. Five new tests and Ruff/Mypy passed. Copied
live `scripts/eggcc_churchroad_complete.py` into this mirror unchanged solely to
exercise the new module's import; do not integrate that copy as an adapter edit.

## 2026-09-25 Repeatable DialEgg preparation (lightweight only)

Added `scripts/reproduction_prepare_dialegg.py`, five focused tests and
`DIALEGG-PREPARATION.md`. Actual original backend repository resolved from
artifact docs and retained receipts: saulshanabrook/egg-smol b6e1c96 cost-action.
Acquires exact frontend4d0 and backend archive bee6dc..., preserves original
Cargo workspace (never appends), Rust1.88/debug0/incremental0/jobs1; records
source/tool/LLVM18/MLIR/dynamic-library identities and existing adapter settings.
API uses caller lock; CLI locks. Frontend compilation remains owned by existing
complete capture adapter. No shared adapter edits and no native job/download.

Successful old backend build44.743s/557,039,616B peak is cited separately from
new mocked preparation tests. Five tests, Ruff/Mypy and CLI help pass.

## 2026-09-25 MISAAL x86 per-case generator preparation (lightweight only)

Added `scripts/reproduction_prepare_misaal_cases.py`, eleven focused tests, and
`MISAAL-CASES-PREPARATION.md`. Reuses the verified inliner-repaired 44ff seed,
compiles original shared generator support once and all selected x86 generator
sources serially under the established guard, binds compiler-observed headers,
and publishes only verified requests. The immutable summary is indexed by every
selected case ID, including absent requests, compiler evidence and resource
stops. API takes no lock; CLI alone owns the heavy lock. No parent optimizer or
target execution is owned here. The default inventory is 32 x86 generators
(31 required plus tensor_shr extra), retaining runtime paper aliases.

Source review found a stateful cold→raw→abstract pickle lifecycle: the raw-cache
branch runs abstraction and can mutate raw patterns; later imports load abstract
patterns. Per parent, children naturally share the fresh adapter cache. The
original Makefile does not remove these pickles. No cache reuse implemented;
all requests preserve the fresh-cache contract. ARM/HVX remain explicit missing
prerequisites. No native compile/build/download/capture ran in this slice.
Eleven mocked tests, Ruff, Mypy and CLI help pass. Copied live
`scripts/reproduction_inventory.py` into the mirror unchanged solely as an
import dependency; do not integrate that copy as an adapter change.

## 2026-09-25 ARM recovery and shared SIMD lowering defect

Static full-checkout audit corrected earlier codegen-only missing ARM metadata:
all current frontend instructions have raw metadata and real wrappers. Added
new ARM preparer plus five mocked tests, and generalized the owned case builder
for original ARM target/defaults/fully_connected parameter while preserving
x86 defaults. The ARM driver uses actual MISAAL semantics, never the differing
Hydride dictionary; generated sources/library/requests remain hash-bound and
immutable, all cases indexed. No native build/generation ran.

Discovered common Legalizer's bitsimd=true default erased normal SIMD results:
actual retained 1b8cc canary has 198/198 required legalizer functions returning
undef. Root and recovery worker informed immediately; old run is intermediate
evidence pending repair. Added shared exact per-SIMD-pass mode repair and LLVM
loss check, eight tests; parent integrated helper/capture gate. ARM applies the
same repair to an isolated original-generator copy. BitSIMD behavior remains.

Handoff: MISAAL-ARM-HVX-RECOVERY.md, static MISAAL-ARM-HVX-EVIDENCE.json,
MISAAL-ARM-HVX-UPSTREAM.json, MISAAL-LOWERING-AUDIT.json. HVX proposals only:
regenerate missing ordinary shifts, implement two checked-in concat pseudo-ops,
make wrapperless intrinsic path explicit, preserve original config differences.
Latest Hydride inspected leaves match pinned files. 24 focused tests, Ruff/Mypy,
CLI help pass; actual read-only ARM input audit verifies157/1152/5026 counts.

### HVX selector preparation handoff (2026-09-25)

New HVX preparation + exact concat helper + focused tests/fixtures are ready in
this mirror. Released shared case builder now adds original Hexagon requests,
sealed selector receipt, optional-link contract and explicit fully_connected
EXPR_DEPTH=2 variance. Actual static source check:114groups/310targets,
308LLVM12intrinsics+2concat operations, max16significant matched-constantbits.
Native frontend requires libHVXLegalizer.so. Also repaired source binary-literal
parsing in private generator copy: base16 misread0b1as177. All actual builds,
selector generation, captures and target execution remain unexecuted here.
See MISAAL-HVX-PREPARATION.md and MISAAL-HVX-PREPARATION-INPUTS.json.

### Fresh all-target MISAAL orchestration handoff (2026-09-25)

Fresh preparation now serially prepares x86/ARM/HVX, retains every inventoried
case, merges only unchanged successful request bytes, and publishes per-case
blockers for ordinary failures. Nested/current saved guard stops halt later
recipes and prevent settings publication. No nested lock/native jobs here.
ARM Boost default is now seed.preparation; exact original ARM source blob pins
were verified independently with git-show. Catalog/population hashes are bound
in preparation identity.93 focused tests, Ruff and Mypy pass.
See MISAAL-FAMILY-PREPARATION.md and MISAAL-ARM-SOURCE-PINS.json. Baselines remain
for the six source/test files listed in the handoff.

## 2026-09-25: opt-in MISAAL exact deduplication repair

Ready for review in `MISAAL-PATTERN-DEDUP.patch`, with file hashes in
`MISAAL-PATTERN-DEDUP-MANIFEST.json`. Root adapter/test baselines are retained
under `.baseline/misaal-patterns`; both still matched live root when packaged,
and `git apply --check` passed against live root. Only the adapter wiring is an
existing-file change; new module, focused tests, two source-backed fixtures and
a short reproduction note are included. No source checkout was modified.

Enable only in a new immutable request with
`"pattern_deduplication": "exact-render-last-v1"`. The hook verifies four pinned
source files and loaded code, preserves last-object exact-render deduplication,
and records create/prune/dedup phase starts/ends/counts before generated imports.
Original cold/raw/abstract transitions and helper/backend observation remain.
No flag leaves the original capture behavior unchanged.

Validation: 70 focused unit/protocol tests passed in 30.83 seconds; Ruff check,
Ruff formatting, and Mypy passed for the new module/tests and adapter. Tests use
actual pinned equality/rendering declarations and eight recorded source
expression renderings, without importing complete pattern populations. Native
speed/completion is untested; root owns the next guarded flagged canary. The
unmodified 900-second timeout remains separate retained evidence.

## HVX semantic lowering repair, 2026-09-25

Baseline-checked nine-file patch: MISAAL-HVX-SEMANTIC-REPAIR.patch and manifest. Portable active-formal shifts/half extractions/four swizzle contexts; private common complete permutation/type checks; verifier inside pass before ADCE. No source checkout or active Egglog changes. 26 focused tests, Ruff, Mypy passed. Broader46-test run:45 passed, one unchanged case-prep error-message expectation mismatch (reported to root). Independent read-only review found no blocker. New LLVM constant-fold harness has19 success checks/eight rejection modes and remains uncompiled/unexecuted; root owns native gate. Native recipe and scope limitations are in benchmarks/reproduction/misaal-hvx-preparation.md.
