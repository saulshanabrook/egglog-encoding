# SpEQ prerequisite preparation (not executed)

New owned files are `scripts/reproduction_prepare_speq.py` and
`tests/test_reproduction_prepare_speq.py`. No shared adapter, recorder, source,
settings, catalog, cache or live implementation was edited. All native commands,
network artifact streams and package installs remain unrun in this slice.

`prepare_speq(output, engine, *, llvm_config, artifact_source=None,
artifact_receipt=None, lleq_source=None, acquire_archive=False,
timeout_sec=1800)` returns a durable preparation record and, only after every
gate succeeds, a coordinator-compatible `settings.json`. The CLI alone holds the
shared heavy-job lock; the function runs under a coordinator-owned slot. Each
child uses the ordinary native guard, warning-pressure policy and 10-GiB disk
reserve. LLVM compilation is a single compiler process; worker/build job limits
are one. Failed attempts are immutable and retain command intent/results/logs.

## Original inputs and exact pins

- Artifact: [Zenodo record 10963236](https://zenodo.org/records/10963236),
  `speq-artifact.tar.gz`, 6,259,975,347 compressed bytes, MD5
  `813c94e4c12a3466909849f38b6ac1fe`.
- REV source: [avery-laird/lleq at 00bd6254b3832d94558b7c38a394ea03d01a2763](https://github.com/avery-laird/lleq/tree/00bd6254b3832d94558b7c38a394ea03d01a2763).
  This is an exact sparse export of `REVPass.cpp`, `REVPass.h`, and `REVTest.cpp`,
  each independently SHA-256 checked by the existing recorder constants. It is
  not represented as a complete LLVM checkout. Existing verified local copies
  are copied; missing files can be acquired from those exact raw GitHub paths.
- Existing native LLVM 17.0.6 development installation is required. The module
  verifies `llvm-config`, clang/clang++/opt and library files and records their
  actual hashes. It does not build LLVM or assume an x86-only host. Native
  macOS uses `otool`; Linux uses `ldd` for additional linked-library evidence.
- Private Python 3.11.11, egglog-python 13.2.0, Lark 1.1.7 and
  z3-solver 4.12.2.0. The recorder already defines the explicit 13.2 API port;
  this preparation does not add a semantic port. Both egglog 13.2 and Z3's
  selected version publish macOS ARM wheels. [egglog release metadata](https://pypi.org/pypi/egglog/13.2.0/json),
  [Z3 release metadata](https://pypi.org/pypi/z3-solver/4.12.2.0/json).

The original artifact `requirements.txt` remains byte-for-byte retained, including
its historical egglog 1.0.0 requirement. It is not falsely reported as the
installed environment. The capture dependency closure is separately resolved to
an exact, hash-checked lock, downloaded as wheels only, installed offline from
those retained wheels, and frozen after installation. The lock and all wheels,
actual Python environment/runtime, original/adapted parser, native plugin, helper
source and LLVM binaries/libraries participate in preparation/capture identity.

The copy includes all eight available application C files and both headers,
the four original reference `.ll` files, `parseIR.py`, `run_benchmark.py`,
`driver.py`, the table script and paper-name mapping, requirements and Dockerfile.
Known member hashes are independently pinned. The new acquisition entry point
streams only the pinned archive into bounded buffers and extracts only these
small allowlisted regular files; duplicate members, unsafe names, wrong size,
wrong member hashes, incomplete streams and wrong full MD5 prevent an admission
receipt. It retains the complete member index without saving the multi-GB tarball.
The original root Dockerfile must be 1,893 bytes and is hashed after the full
archive verifies; no Dockerfile command is executed.

## Why a new acquisition is currently necessary

The existing `stream_speq_artifact` helper writes to a global shared storage path
and its complete-index mapping filter omits root `Dockerfile`. This module does
not alter that shared helper. The existing historical receipt/index proves the
root file exists, but its contents were not retained. The default source reuse
path therefore stops with an actionable missing-Dockerfile error, before any
Python environment or REV build is attempted. A fresh explicit `--acquire-archive`
run captures it without overwriting historical source or evidence.

The earlier full stream took roughly 1,501 seconds in its saved receipt. The new
single-stream path is not performance-tested; allow at least 1,800 seconds per
step or choose a reviewed longer timeout. A network/time/resource failure retains
the partial attempt but never publishes settings. No full stream ran now.

## Native gates and scope

1. Verify native LLVM 17.0.6 tools/libraries and all original member/source hashes.
2. Prepare and lock the Python environment; import the unchanged explicit
   `adapt_parse_ir` port and require egglog-python 13.2.0.
3. Invoke existing `record_speq.build_rev_plugin` inside a guarded child process.
   Its compiler descendants stay in that monitored process group. Pin both REV
   implementation files and `speq_rev_plugin.cpp`; do not rewrite REV semantics.
4. Invoke existing `reference_fir` in guarded children on all four reference IR
   inputs, retaining FIR bytes and requiring the recorder's exact expected hashes.
5. Freeze native/runtime evidence and publish settings. No original-C benchmark
   optimization or replay is run by preparation.

The emitted family settings intentionally use empty frontend flags. The separately
observed `_FORTIFY_SOURCE`/PolyBench options affect capture identity and must be
selected explicitly in case settings, not silently injected by dependency setup.
Known PolyBench/frontend and Parboil semantic concerns are not repaired or declared
resolved by preparation. Eight available application parents still need complete
native source optimization plus ordinary standalone validation. TPAL/TSVC2 remain
explicitly missing original inputs; no reference kernels are substituted for them.

## Commands after integration and a new heavy-slot grant

From the live root, for a fresh acquisition plus native preparation:

```sh
uv run --locked python -m scripts.reproduction_prepare_speq \
  --output benchmarks/local/reproduction/preparation/speq-attempt-0001 \
  --egglog target/release/egglog-experimental \
  --llvm-config /opt/homebrew/opt/llvm@17/bin/llvm-config \
  --acquire-archive --timeout-sec 1800
```

For later verified source reuse, choose a new output attempt and pass the earlier
`archive/artifact` and `archive/artifact-receipt.json` as `--artifact-source` and
`--artifact-receipt`. The exact source hashes are checked again. Never point output
at an old attempt and do not wrap this CLI in a second process-group guard.

After actual preparation success, the existing public coordinator can run a first
available paper parent, for example:

```sh
uv run --locked python -m scripts.suite_reproduction \
  --settings benchmarks/local/reproduction/preparation/speq-attempt-0001/settings.json \
  --family speq --case speq-taco_spmv_csc --stage all
```

That parent command is proposed, not run here. Preparation success is not corpus
admission, a whole-paper success, proof validation, or device execution.

## Lightweight validation

18 tests exercise complete stream/root Dockerfile retention, archive and source
mismatches, duplicate/symlink/unsafe members, absent inputs, native version and
reference FIR gates, resource-stop propagation, immutable output, exact settings
and guarded helper placement. Archive tests use tiny in-memory tarballs; native
commands are mocked. Ruff/mypy and CLI help pass. No runtime compatibility result
is inferred from these tests.

Independent read-only review found no concrete blocker in archive admission, guarded helper descendants, reference gates or runtime identity closure. Native compatibility is still untested.
