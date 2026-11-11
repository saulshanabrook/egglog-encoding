# Repeatable Eggcc Statewalk prerequisite build

The new `scripts/reproduction_prepare_eggcc.py` implements the real acquisition,
instrumentation and build recipe that already produced a successful Statewalk
canary. It does not copy the previous compiler binary. **This new entry point
has only lightweight tests so far; it has not itself run a native build.**

## Existing runtime evidence

The immutable successful build receipt is:

`benchmarks/local/reproduction/stages/eggcc-toolchain/prepare/17311470f90ae4abc3a290247612fc44d9e7d00eb6b3b009919173ac370553f7/attempt-0001/`

Its `build-0.json` records exit0, 104.30 seconds and sampled peak RSS
1,153,335,296 bytes. `complete-preparation.json` records original compiler hash
`0c6a40816f234c757db340a37e0c980a5d379a304238b32b26bf724ba2a8cf17`.
The original archive and lockfile are retained there. Archive source has no
`.git`; a parent repository's HEAD must not be used as its revision.

The latest inspected complete Statewalk fact canary is:

`benchmarks/local/reproduction/stages/eggcc-fact--statewalk/complete/14ce07208c94d789a149ab065c4e8fa968fe324398d39d6cf4bb317384ed9f63/attempt-0001/capture-result.json`

It reports `reproduced`, successful native parent completion and six replay
workloads: optimization and reconstruction for each of three passes. This is
actual native/ordinary-replay evidence for that case, not proof validation or
coverage of the entire paper population. An earlier `a87bf8...` attempt remains
blocked by its recorded root-accounting mismatch; it is not overwritten.

## API and CLI

The root coordinator may call this directly while it owns the shared job slot:

```python
prepare_eggcc(output, engine, build_root=optional_disposable_target, timeout_sec=600)
```

The API takes **no nested lock**. It returns a record with `status`, `reason`,
`settings`, source pin, build products and per-configuration blocker metadata.
A successful result means prerequisites are ready, not that any new benchmark
has run. The settings file has an `eggcc` family key compatible with the current
coordinator.

For a standalone, explicitly scheduled build, the CLI owns the shared lock:

```sh
.venv/bin/python -m scripts.reproduction_prepare_eggcc \
  --output benchmarks/local/reproduction/prerequisites/eggcc-16be/attempt-NEW \
  --egglog target/release/egglog-experimental \
  --build-root target/benchmark-acquisition/eggcc-prepared-NEW
```

`NEW` must be a fresh attempt name. The module refuses existing output/build
paths. Durable source, archive, patches, original and prepared file manifests,
settings, tool hashes and numbered guarded logs live below `benchmarks/local`.
The optional Cargo build directory may remain disposable. Deleting it removes
the compiler prerequisite; rerun preparation as a fresh attempt before capture.

The callable function reuses the existing `Preparation` guarded-step and
immutable-patch implementation. Each child requires the memory guard, permits
diagnostic warning pressure, caps process-group RSS at 5 GiB, keeps a 10 GiB
disk reserve and has a bounded timeout. Cargo has one job. No native generator,
benchmark, target code, performance observation or Gurobi solver is run here.

## Preserved build contract

Acquisition downloads the exact codeload archive for Eggcc
`16be0063133ef0b8ba21cd75ee377002dc3ecbed`, then verifies the successful attempt's
SHA-256 `ced650bba88d7c12ce8091281660a26117ba83c68ad23281289c289ef129558c`.
Extraction requires ordinary files within the pinned archive root and records
all 763 original file hashes. The checked-in Cargo.lock remains
`271911b11aa595cb22c9bb55915580a6afa7bec3dc8ccd0bf6e284381c916272`.
Archive or lock drift is an explicit failure, not an automatic dependency update.

The only patches are the existing isolated `[workspace]` declaration and
observation instrumentation returned by the actual
`scripts/eggcc_churchroad_complete.py:patched_eggcc_sources`. The preparer does
not duplicate or rewrite the instrumentation/extraction algorithm. It records
reversible diffs and hashes before and after applying them to acquired sources.

The original successful command is preserved, with only the fresh Cargo target
path changed:

```sh
env LLVM_SYS_180_PREFIX=/opt/homebrew/opt/llvm@18 \
  LIBRARY_PATH=/opt/homebrew/lib CARGO_TARGET_DIR=FRESH_BUILD \
  CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 RUSTC_WRAPPER= \
  cargo +1.88.0 build --locked -j1 --bin eggcc
```

This is explicitly the demonstrated native Apple Silicon/LLVM18.1.8 recipe.
Host tools, actual Rust compiler/Cargo executables, LLVM config/library and replay
engine are hashed. No Linux reproduction claim is made from this Mac evidence.
Upstream `dag_in_context/build.rs` invokes `g++` and emits Tiger at
`CHECKOUT/target/debug/tiger` independently of `CARGO_TARGET_DIR`; the native
lookup in `dag_in_context/src/lib.rs` supports that location. Both real Eggcc and
real Tiger outputs are required and hashed before publishing settings.

After reviewing a successful preparation, the first capture command is:

```sh
.venv/bin/python -m scripts.suite_reproduction --family eggcc \
  --case eggcc-fact--statewalk --stage capture --settings "$ATTEMPT/settings.json"
```

## Gurobi remains a distinct blocked configuration

Both the returned preparation record and its settings explicitly record this
blocked graph/extraction configuration:

```json
{"native_options": ["--tiger-ilp", "--ilp-solver", "gurobi"]}
```

The measured failure is missing `gurobi_cl`. The user states they have no
installation or usable license access. The successful Statewalk result does not
resolve that dependency. Metadata references the existing
`benchmarks/reproduction/eggcc-gurobi.md` access assessment. No license probe,
package installation, solver shim or extractor substitution is attempted.
Coordinator/report gating remains root's responsibility.

## Lightweight validation

Five new tests pass: archive hash refusal, traversal refusal, durable/fresh path
requirements, exact source-build command and no nested lock, explicit Gurobi
blocker, and failure to publish settings if Tiger is missing. The success and
missing-Tiger cases are parameterized. Ruff lint/format and Mypy pass. Native
children are mocked, so these tests establish the preparation contract only.
