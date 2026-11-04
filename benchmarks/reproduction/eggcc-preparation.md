# Repeatable Eggcc Statewalk prerequisite build

The new `scripts/reproduction_prepare_eggcc.py` implements the real acquisition,
instrumentation and build recipe that already produced a successful Statewalk
canary. Each preparation requires a guarded compiler build. **The original entry point
successfully acquired and built the compiler on 2026-09-25**, in 106.8 seconds:
`benchmarks/local/reproduction/stages/eggcc-prerequisites/prepare/d6cd45c8d4e581fad03a3ed83179a6b716c4348d437526a2c63d0ba9d74a54b5/attempt-0001/`.
The full Statewalk population is now running with this durable environment;
its first complete Ackermann source run and ordinary replay passed. This build
success alone is not a full-family reproduction claim.

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
prepare_eggcc(output, engine, build_root=optional_disposable_target, timeout_sec=600,
              continue_from=optional_original_preparation)
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
all 763 original file hashes. The original Cargo.lock is retained with SHA-256
`271911b11aa595cb22c9bb55915580a6afa7bec3dc8ccd0bf6e284381c916272`.
New preparations derive a separate lock for the correction described below.
Archive or lock drift is an explicit failure, not an automatic dependency update.

The Eggcc source patches retain the existing isolated `[workspace]` declaration and
observation instrumentation returned by the actual
`scripts/eggcc_churchroad_complete.py:patched_eggcc_sources`. The preparer does
not duplicate or rewrite the instrumentation/extraction algorithm. It records
reversible diffs and hashes before and after applying them to acquired sources.

The historical successful build command was:

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

Focused tests cover acquisition pins, traversal refusal, fresh paths, exact
source-build commands, no nested lock, Gurobi metadata, missing Tiger, private
cache copies, continuation immutability, narrow dependency identity changes,
and the exact upstream patch/regression. Native children are mocked; these
tests establish preparation contracts, not corrected native behavior.


## Pinned column-index correction

The retained Cordic diagnostic `benchmarks/local/reproduction/diagnostics/eggcc-cordic-backtrace-0002/`
failed in `SortedOffsetSlice::new_unchecked` through `SubsetBuffer::make_ref`
and `ColumnIndex::get_subset`, with offsets `[151, 38, 151, 478]`. This is a
source-engine failure, before the selected-output replay stage.

New preparations backport only the five production lines and original regression
from [upstream commit 201579a](https://github.com/egraphs-good/egglog/commit/201579afd2b8b646fa518d3065bd319d1a084eba),
part of [PR 914](https://github.com/egraphs-good/egglog/pull/914). Equal-value
multi-column groups are sorted by row before the existing duplicate removal.
Assertions, schedules, optimization rules, extractors and proof implementation
remain unchanged. The exact upstream mail patch is tracked at
`benchmarks/reproduction/fixtures/eggcc-core-row-order.patch`, SHA-256
`84e6de41c4d7e4741773f58ed271f80072fb5ead1ed0c3b26ad6b0a591e93495`.

Eggcc remains at `16be0063133ef0b8ba21cd75ee377002dc3ecbed`, its Experimental
dependency at `08771f9f69de51cc8cdc58e3760b7f00a03e40d8`, and core at
`ebba7bb902bdc1b0f377b6bb22c06ac305912674` plus that patch. The new core checkout
has independent Git metadata: its build script cannot accidentally identify
this repository's HEAD. Revision and exact before-file hashes are checked before
applying the patch. `core-repair.json` retains all original/prepared core file
hashes and upstream provenance and is included in the published family identity.

The fresh Eggcc workspace overrides the three core packages directly used by
Experimental (`egglog`, `egglog-ast`, `egglog-reports`) under the original Git URL
`https://github.com/saulshanabrook/egg-smol.git`. Their original workspace path
edges keep all nine core packages together. Only those nine packages' Git source
fields are removed in the derived Eggcc lock: names, versions, dependency lists,
checksums and all other packages remain unchanged. The original archive/lock and
reversible manifest/lock diffs are retained. No unrestricted Cargo update runs.

The upstream regression executes first, with its own original core workspace
lock (SHA-256 `466ad68262801a539f11e04a4537d9347c02019d25c480cefed62e67bc31b080`):

```sh
cargo +1.88.0 test --manifest-path FRESH_CORE/Cargo.toml --locked -j1 \
  -p egglog-core-relations --lib \
  hash_index::tests::multi_column_column_index_rebuild_orders_each_value_by_row \
  -- --exact
```

The preparer requires exactly one passing test before the separate locked Eggcc
build. Both steps retain commands, logs and guarded results; both use the fresh
`CARGO_HOME`, existing LLVM settings and disabled Rust wrapper. All original
locked core/Eggcc source files are checked again before settings are published.
These preparation gates do not establish Cordic source/replay success or proof
compatibility. Root must run the actual complete Cordic parent and ordinary
replays with the resulting new identity. Old successful family observations
remain associated with their original compiler identity.

## Immutable incremental continuation

To reuse the original successful preparation without changing it:

```sh
.venv/bin/python -m scripts.reproduction_prepare_eggcc \
  --output benchmarks/local/reproduction/prerequisites/eggcc-pr914/attempt-NEW \
  --continue-from ORIGINAL_PREPARATION_ENVIRONMENT \
  --egglog target/release/egglog-experimental
```

The original success receipt, prepared source allowlist, product hashes and
pinned archive/lock must still match. The new attempt re-extracts the retained
original archive and applies the current capture instrumentation. It never
builds inside the old source tree (Tiger also writes below that tree regardless
of `CARGO_TARGET_DIR`). A guarded macOS `cp -cR` clones the old target into a
fresh directory, using independent copy-on-write files and rejecting symlinks.
Cargo may reuse eligible compiled dependencies; changed paths/identities can
still require recompilation. A byte-identical old compiler cannot be published
as repaired. The old receipt/source/product pins are verified again at completion.

All Cargo work uses a fresh home. Cache seeding copies checksum-verified locked
registry archives, their sparse index entries and the four original Git object
stores; no mutable original cache path is given to Cargo. Git stores with
symlinks or borrowed object stores are refused. Missing cache data may be
acquired into the fresh home under the original locks. No cache configuration,
old source checkout or old Tiger executable is reused in place.

The original target measured about 1 GiB. Its clone initially shares physical
blocks; new build outputs and unpacked private dependencies require additional
space. Allow roughly 1–3 GiB of new allocation as a planning estimate, while the
existing guard maintains its 10 GiB free-disk reserve. The source/regression/build
steps retain the existing 5 GiB process-group ceiling, 2 GiB host reserve,
warning-pressure allowance, one Cargo job and per-step timeout. The coordinator
owns the shared lock; only the standalone CLI acquires it.
