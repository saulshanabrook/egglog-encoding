# Reproduce the EggCC encoding study

The report distinguishes semantic fixtures, engine-upgrade controls and
feature controls. Keep those contrasts separate. Raw evidence is retained at
`/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/`.
The paths below name the actual retained checkout and frozen binaries; rebuilding
or moving them requires a new manifest/result capture, not an update to old
measurements.

## Verify and regenerate retained measurements

From `/Users/saul/p/wt/egglog-encoding/eggcc-study`:

```sh
uv run --no-project --python 3.13 python scripts/eggcc_encoding_case_study.py verify \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/engine-control/study.json \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/engine-control/results.json

uv run --no-project --python 3.13 --with matplotlib==3.10.7 \
  python scripts/eggcc_encoding_case_study.py figures \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/engine-control/study.json \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/engine-control/results.json \
  /tmp/eggcc-engine-control-figures-NEW
```

Choose a fresh output directory. The retained `figures-regenerated/` and
`figure-qa/receipt.json` already demonstrate an independent identical export.
The collector documentation describes its schema and exact measurement scope:
[scripts/eggcc_encoding_case_study.md](/Users/saul/p/wt/egglog-encoding/eggcc-study/scripts/eggcc_encoding_case_study.md).

For a fresh engine-control collection, use `collect` with the retained study
and a fresh result path, then `verify`. This launches full compiler processes;
it never builds or silently reuses old observations. Keep compiler builds and
other study sampling stopped during collection. The default study requests one
warmup and ten observations per case/arm after checking interpreter agreement.

## Rebuild elsewhere

1. Create clean EggCC worktrees at
   `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b` and an encoding checkout at
   `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`. The encoding root Cargo workspace
   includes the matching core and experimental subtrees.
2. For A, retain EggCC's original root and standalone DAG manifests/lockfiles.
   For B, apply the retained `retarget/engine-only.patch`. Replace the recorded
   local encoding path in both manifests with the new encoding checkout's
   `egglog-experimental` path. Both dependency graphs must resolve that same
   checkout; do not substitute a package named `egglog` for the existing alias
   of package `egglog-experimental`.
3. Use the common Rust 1.91.0 toolchain. The captured Apple Silicon build used
   LLVM18 at `/opt/homebrew/opt/llvm@18`, `LIBRARY_PATH=/opt/homebrew/lib`, four
   Cargo build jobs and one Rayon thread. Supply the corresponding LLVM/native
   prerequisites on the new host. Root and standalone DAG dependency metadata
   and exact original build command receipts are retained in `retarget/`.
4. Build each endpoint with
   `cargo +1.91.0 build --release --locked --no-default-features --bin eggcc`.
   Preserve the normal native Tiger build; copy each finished `eggcc` and its
   matching `tiger` to a separate frozen sibling directory. Verify that the CLI
   actually resolves that sibling Tiger. A shared Cargo cache can suppress a
   previously completed build-script side effect, so a successful host build
   alone does not establish that the expected native executable exists.
5. Copy the case-specific collector and fixtures from the study checkpoint.
   Write a new study manifest naming the new paths, source revisions/patches,
   toolchain, native executable and compiler configuration. Hash each required
   source/configuration artifact individually. Run focused nonzero tests and
   full interpreted canaries before sampling; retain actual command logs.

The manifest fixes contexts, all passes, extraction, thread count and CLI flags.
An engine upgrade comparison cannot establish the benefit of the encoding.
Different hosts/toolchains produce a new experiment even with identical inputs.

## Semantic fixtures and validation

The fixture README explains which commands should succeed, which deliberately
seeded faults should fail, and the required diagnostics. Do not treat every
nonzero exit as a passing rejection test or include these single diagnostic
timings in performance plots. The original16 outcomes and fail-fast extension
have separate immutable receipts under `semantic/`.

The repository gates are:

```sh
# Encoding root; existing proof tests are regressions, not new proof support.
make check

# EggCC root; the Makefile covers root and standalone dag_in_context crates.
RUSTUP_TOOLCHAIN=1.91.0 make test
RUSTUP_TOOLCHAIN=1.91.0 make nits
```

The collector's focused protocol/export tests use an isolated pinned environment
so Matplotlib is not a new project dependency:

```sh
uv run --no-project --python 3.13 --with pytest==8.4.2 --with matplotlib==3.10.7 \
  python -m pytest -q tests/test_eggcc_encoding_case_study.py
```

## Feature comparison and fresh rerun

Apply `retarget/prototype/final/full.patch` to clean EggCC at `15ee7cba` for the full
prototype, instead of applying the engine-only patch. Its `feature.patch` is the
review delta after the engine-only checkpoint. Apply
`encoding-study/study.patch` to encoding at `392b6d6b` for the collector and all
semantic fixtures. Both checkpoints archive every changed/new file and its hash;
no commit or push was made.

The final frozen compiler is
`retarget/prototype/final/bin/eggcc` (SHA256 `d44a89c2f752aff60b2691d9e055f23e54215fc9dfa74a0db8e956afc713162e`).
Keep its matching sibling Tiger. The feature study fixes one binary and changes
only `--exact-local-addresses off|keys|query|manual`. Enabled modes require
`--with-context` and reject ablation. Keys/query/manual share the added
memory/type closure and query-based consistency audit, so off→keys is not a
pure annotation-cost contrast. Query/manual use the same inference domain.

From the encoding study checkout:

```sh
uv run --no-project --python 3.13 python scripts/eggcc_encoding_case_study.py verify \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/feature-control/study.json \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/feature-control/results.json

uv run --no-project --python 3.13 --with matplotlib==3.10.7 \
  python scripts/eggcc_encoding_case_study.py figures \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/feature-control/study.json \
  /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/feature-control/results.json \
  /tmp/eggcc-feature-control-figures-NEW
```

The feature capture contains 144 successful invocations: 12 correctness checks,
12 warmups and 120 observations (three inputs × four modes × ten). The fresh
representative capture under `reproduction/` selects only `fresh-allocations`,
keeps all four modes and ten observations, and was collected and verified from
`/tmp` using the absolute script path. Its 48 invocations use a fresh result and
receipt directory. Use that study/result pair with the same `verify`/`figures`
commands, or `collect` into another new result path. Measurement receipts retain
exact per-child commands, configuration, environment fingerprints and outputs.

## Full-gate setup and known limits

LLVM/Cranelift validation additionally needs the documented runtime outputs.
Run `make runtime` with `CARGO_TARGET_DIR` unset; its installer uses pinned
nightly-2024-05-01 and its own target directory. The installer failed its final
no_main executable link on this macOS host after producing valid bitcode.
The retained recovery used LLVM18 `opt -passes=verify` on that emitted `.bc`,
copied it to `runtime/rt.bc`, then ran `cc -c rt.c -o rt.o` from `runtime/`.
The exact generated filename, commands, validation and hashes are in
`retarget/prototype/final/runtime-bitcode-copy.json`, `runtime-artifacts.json`
and the `prototype-runtime-*` command receipts. Substitute your emitted
filename when rebuilding; no runtime source change is required by this study.
The ordinary greedy compiler measurements do not execute these LLVM backends.

Retained strict `make test` exits 2 for 13 changed snapshots, despite all root
test executions and 66 DAG tests passing after runtime setup. All 13 golden
bodies match engine-only B before the feature; no snapshot was accepted.
Strict `make nits` exits 2 for unchanged Rust 1.91 Clippy lints, with separate
baseline attribution and narrow diagnostic checks. These limits are part of
the evidence; reproducing them does not establish a new feature regression.
[final/summary.md](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/prototype/final/summary.md)
and `gates.json` retain exact official and supplementary commands/results.
