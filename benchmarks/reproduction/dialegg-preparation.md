# Repeatable DialEgg prerequisite preparation

`reproduction_prepare_dialegg.py` acquires the pinned original sources, builds
the real cost-action Egglog backend, and emits settings for the existing complete
capture adapter. **The fresh prerequisite recipe succeeded on 2026-09-25.** It acquired the
original pinned sources and built the original cost-action backend in45.1
seconds, with linked-library verification. Evidence is retained at
`benchmarks/local/reproduction/stages/dialegg-prerequisites/prepare/8f1522ef2c98a9626f33bd2fbd9791675ba47e3568cbabe981add5c20d46dea0/attempt-0001/environment/`.
All 24 required source parents and all 73 ordinary replay sessions now pass
against these durable prerequisites, yielding 51 corpus workloads. Helper-only
sessions remain captured and validated. The outcome snapshot is
`benchmarks/local/reproduction/dialegg-complete-current-20260925.json`.

## Existing evidence and exact sources

The actual successful backend build is retained at:

`benchmarks/local/reproduction/stages/dialegg-backend/prepare/bf1e171cd34d58bd91b9274798682f21728873d126181d90c9973e64676dda86/attempt-0001/preparation.json`

It records exit0, **44.743 seconds**, and sampled peak RSS **557,039,616 bytes**.
The original archive is retained in the preceding `57e2455.../attempt-0001`
directory. That preceding build failed because it appended a duplicate
`[workspace]` declaration. Both attempts remain intact; the new recipe preserves
the original valid workspace without any Cargo.toml patch.

| Component | Exact source |
|---|---|
| DialEgg frontend, rules and MLIR inputs | `AzizZayed/dialegg-cgo-artifact`, `4d0d522e98c15becdc5e7d711348cb0891ff0d44` |
| Original cost-action Egglog | `saulshanabrook/egg-smol`, `b6e1c96ed7335366e90056ea0a24ef425dfbb8fb` |
| Backend source archive SHA-256 | `bee6dc3afa05fcbedc4246cf71ef25c6693745f4013abbc4381aa3b909c9e070` |
| Original Cargo.toml SHA-256 | `285072ca24f3f7cc88c2a022b7451902e41ca80b3ab7cc2ca9131e16af16d2c3` |
| Original Cargo.lock SHA-256 | `d40ef351e9bc73acd0b525245acf5a285d084df8763309baf978d0bab8f7286c` |

The artifact's [build guide](https://github.com/AzizZayed/dialegg-cgo-artifact/blob/4d0d522e98c15becdc5e7d711348cb0891ff0d44/docs/README.md)
names the `cost-action` branch of that actual backend repository, and its
[build script](https://github.com/AzizZayed/dialegg-cgo-artifact/blob/4d0d522e98c15becdc5e7d711348cb0891ff0d44/build.sh)
pins the same backend revision. The new recipe builds that engine unchanged; it
does not substitute the current ordinary/proof engine for native optimization.

Frontend acquisition is an exact detached Git checkout, verified against its
pin and recorded with hashes for all non-Git source files. The backend archive
must match the retained hash before safe extraction. Its Cargo manifest and
lockfile hashes must match before and after building. No source patches are
applied by this preparer.

## API and CLI

The root coordinator can call, within its existing exclusive job slot:

```python
prepare_dialegg(output, engine, build_root=optional_disposable_target, timeout_sec=600)
```

The API takes no lock. It returns `status`, `reason`, and, only after successful
preparation, `settings` and artifact identities. The CLI alone acquires the shared
`benchmarks/local/reproduction/stages/.heavy-job.lock`:

```sh
.venv/bin/python -m scripts.reproduction_prepare_dialegg \
  --output benchmarks/local/reproduction/prerequisites/dialegg-4d0/attempt-NEW \
  --egglog target/release/egglog-experimental \
  --build-root target/benchmark-acquisition/dialegg-backend-NEW
```

Use a fresh name in place of `NEW`. Existing source/output/build paths are
refused. Source, archive, settings and receipts remain durable below
`benchmarks/local`; the optional backend Cargo target may be disposable.
Deletion of that target invalidates its backend prerequisite and requires a new
preparation attempt before capture.

The script reuses `Preparation` for guarded immutable steps and the existing
`acquire_source` exact-Git-pin helper. Every child has the required native guard,
diagnostic warning-pressure allowance, a 5 GiB process-group RSS cap, 10 GiB
free-disk floor and bounded timeout. Builds have one job. The backend command
preserves the actual successful build flags:

```sh
env CARGO_TARGET_DIR=FRESH_BUILD CARGO_PROFILE_DEV_DEBUG=0 \
  CARGO_INCREMENTAL=0 RUSTC_WRAPPER= \
  cargo +1.88.0 build --locked -j1 --bin egglog
```

This is the proven native Apple Silicon route, with existing LLVM18.1.8. It does
not install LLVM or build the all-purpose Docker/LLVM environment.

## Frontend and library boundaries

The preparer requires and hashes LLVM18 `clang++`, `llvm-config`, MLIR headers and
CMake config, `libMLIROptLib.a`, `libMLIR.dylib`, and `libLLVM.dylib`. The actual
Rust1.88 compiler/Cargo executables, host tools, current replay engine and support
scripts are also bound to hashes. After building, `otool -L` records the backend,
Clang and LLVM/MLIR dynamic dependency closure. Non-system dependencies must
resolve to real files and are hashed; system install names are retained explicitly
because macOS may serve them from the dyld shared cache.

The new settings file has a `dialegg` family key and the exact existing adapter
path keys: `dialegg_source`, `llvm18_prefix`, `native_egglog`, and `egglog`.
Additional identity paths bind the source/tool/library receipts and actual linked
libraries. The ordinary/proof engine stays a separately identified executable.

`prepare_complete_dialegg` in `scripts/dialegg_speq_complete.py` remains the owner
of frontend instrumentation and compilation. On each capture it copies original
`src`, applies the existing pass hook, compiles the three C++ objects, and links
against MLIROptLib/MLIR/LLVM. This preparer does not duplicate that patch, launch
the frontend, or claim a complete compiler parent from backend build success.

After reviewing a successful preparation, an example first complete capture is:

```sh
.venv/bin/python -m scripts.suite_reproduction --family dialegg \
  --case dialegg-runtime-2mm-eqsat --stage capture --settings "$ATTEMPT/settings.json"
```

Native optimization completion, reconstruction of every actual output, ordinary
replay and strict proof validation remain separate gates. No target-device
execution or performance campaign is part of preparation.

## Lightweight tests

Five tests pass: original workspace bytes preserved; unpinned archive rejected;
dynamic-library cycles/system cache handling and unresolved dependency refusal;
correct real-backend build/settings without a nested lock; and no settings if
the backend binary is missing. The final two are parameterized cases. Ruff,
Mypy and CLI help pass. Native commands are mocked, so these are implementation
checks, not another observed build or benchmark result.
