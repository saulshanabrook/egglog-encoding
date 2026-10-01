# SpEQ prerequisite preparation

`scripts/reproduction_prepare_speq.py` prepares a fresh native environment from
verified original inputs. The repaired fresh environment passed actual preparation on 2026-09-25 at
`benchmarks/local/reproduction/preparation/speq-attempt-0002`: verified original
source reuse, pinned Python and hashed wheels, parser imports, native REV plugin
build and unchanged reference FIR checks. Subsequent full source optimization and ordinary replay pass seven applications.
PolyBench fails its required GEMM translation; TPAL and TSVC2 remain missing-input
blockers. The current snapshot is
`benchmarks/local/reproduction/speq-complete-current-20260925.json`.
No archive re-download was needed.

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
  This is an exact sparse export of `REVPass.cpp`, `REVPass.h`, the custom
  `MemorySSA.h`, and `REVTest.cpp`, each independently SHA-256 checked by the existing recorder constants. It is
  not represented as a complete LLVM checkout. Existing verified local copies
  are copied; missing files can be acquired from those exact raw GitHub paths.
- Existing native LLVM 17.0.6 development installation is required. The module
  verifies `llvm-config`, clang/clang++/opt and library files and records their
  actual hashes. It does not build LLVM or assume an x86-only host. Native
  macOS uses `otool`; Linux uses `ldd` for additional linked-library evidence.
- Private Python 3.11.11, egglog-python 13.2.0, Lark 1.1.7,
  z3-solver 4.12.2.0 and setuptools 80.9.0. The recorder already defines the explicit 13.2 API port;
  this preparation does not add a semantic port. Both egglog 13.2 and Z3's
  selected version publish macOS ARM wheels. [egglog release metadata](https://pypi.org/pypi/egglog/13.2.0/json),
  [Z3 release metadata](https://pypi.org/pypi/z3-solver/4.12.2.0/json).

The first actual fresh preparation, retained at
`benchmarks/local/reproduction/preparation/speq-attempt-0001`, passed archive and
source verification, environment creation and locked wheel installation, then
failed at `python-import`: Z3 4.12.2.0 imports `pkg_resources`, which the seeded
setuptools 84.0.0 does not provide. Its failed receipt and logs remain unchanged.
The historical working environment used Z3 4.15.3.0, so it did not validate this
older Z3 dependency combination.

Setuptools 80.9.0 explicitly packages `pkg_resources` in its
[pinned package configuration](https://raw.githubusercontent.com/pypa/setuptools/v80.9.0/pyproject.toml)
and retains the [required resource API](https://raw.githubusercontent.com/pypa/setuptools/v80.9.0/pkg_resources/__init__.py).
Its [published universal wheel](https://pypi.org/pypi/setuptools/80.9.0/json)
supports Python 3.9 and later. This exact runtime dependency now enters the same
hashed requirements lock, wheel retention and offline installation as Z3; it is
not left to whichever setuptools `uv --seed` supplies. The guarded import probe
explicitly imports `pkg_resources`, requires setuptools 80.9.0, imports the
adapted parser, and records the provider version and module path. No Z3, parser,
rule or schedule changes are needed. The repaired environment subsequently passed the guarded preparation run;
the failed attempt remains intact.

The original artifact `requirements.txt` remains byte-for-byte retained, including
its historical egglog 1.0.0 requirement. It is not falsely reported as the
installed environment. The capture dependency closure is separately resolved to
an exact, hash-checked lock, downloaded as wheels only, installed offline from
those retained wheels, and frozen after installation. The lock and all wheels,
actual Python environment/runtime, original/adapted parser, native plugin, helper
source and LLVM binaries/libraries participate in preparation/capture identity.

The copy includes all eight available application C files and both headers,
the four original reference `.ll` files, `parseIR.py`, `run_benchmark.py`,
`driver.py`, the table script and paper-name mapping, and requirements. A retained
Dockerfile is copied only when its bytes match its full-archive receipt and original length;
it is never executed or used to build the native environment.
Known member hashes are independently pinned. The new acquisition entry point
streams only the pinned archive into bounded buffers and extracts only these
small allowlisted regular files; duplicate members, unsafe names, wrong size,
wrong member hashes, incomplete streams and wrong full MD5 prevent an admission
receipt. It retains the complete member index without saving the multi-GB tarball.
The original root Dockerfile must be 1,893 bytes and is hashed after the full
archive verifies; no Dockerfile command is executed.

## Reusing the verified historical archive inputs

The retained historical receipt at
`benchmarks/local/evidence/speq-artifact-index.json` records a complete
6,259,975,347-byte stream with the pinned MD5, 73,109 members, and member-index
SHA-256 `23acf74505c56b2e08479b8cfb82a52b4670ef5f95bd3fce36192649615ab136`.
All 20 required artifact inputs currently match both their independent source
pins and receipt entries; all four required REV source files also match their
independent pins. The original extraction omitted the root Dockerfile, whose
regular-file membership and 1,893-byte length remain in that complete index.

Preparation can reuse those inputs without another archive transfer. It requires
the recorded full-stream length, MD5 and completion flag; rehashes the actual
member index against its receipt; checks its member count and unique original
Dockerfile entry; and independently verifies every required artifact input.
When the receipt's old temporary index path is unavailable, the only relocation
fallback is the same index basename beside the receipt. Both the receipt and
verified index bytes are copied into the new attempt's evidence directory.
Required source files are copied from the exact bytes hashed, so the published
settings use the new durable copy rather than the historical mutable source cache.
This reuses previously recorded full-stream verification; it does not claim to
have recomputed the archive MD5 during preparation.

The Dockerfile is the only optional retained member. If neither the historical
receipt nor source directory contains it, `preparation.json` explicitly records
`artifact_provenance.dockerfile.status = "not-retained"`, its indexed size, a null
content hash and `used_by_native_preparation = false`. Its base image, commands
and any external fetches remain unknown. A receipt that claims Dockerfile bytes
must still have the file; a file without a matching receipt entry, changed bytes,
or an unexpected length blocks preparation. No replacement Dockerfile is created.
This exception does not make any C input, parser, rule, schedule, reference IR or
REV source optional, nor does it change complete-parent or standalone admission.

Fresh explicit `--acquire-archive` preparation still streams the full pinned
archive, captures Dockerfile, and requires its size and the complete archive
checksum before admitting it. This is optional provenance recovery, not a native
build dependency. The earlier full stream took roughly 1,501 seconds; the new
single-stream path remains untested. A network/time/resource failure preserves
the failed attempt and never publishes settings.

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

The emitted family settings select `-D_FORTIFY_SOURCE=0`,
`-DPOLYBENCH_USE_C99_PROTO`, and the existing PHI-polarity repair used by the seven
successful complete parents. Preparation still builds the original pinned plugin
and checks its four reference FIRs. The complete capture path records that this
prebuilt plugin is omitted, then builds a fresh PHI-repaired plugin from the pinned
source inside the guarded source child. Its materialization, plugin hash, frontend
flags and repair setting remain explicit in capture identity and evidence. The
C99 address-serialization candidate remains disabled. Preparation does not claim
GEMM translation or replace the required complete source and ordinary replay
checks. TPAL/TSVC2 remain explicitly missing original inputs; no reference kernels
are substituted for them.

## Commands after integration and a new heavy-slot grant

From the live root, reuse the verified existing inputs to build a new durable
environment (the output directory must not already exist):

```sh
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python -m scripts.reproduction_prepare_speq \
  --output benchmarks/local/reproduction/preparation/speq-attempt-0002 \
  --egglog target/release/egglog-experimental \
  --llvm-config /opt/homebrew/opt/llvm@17/bin/llvm-config \
  --artifact-source benchmarks/local/sources/speq/artifact \
  --artifact-receipt benchmarks/local/evidence/speq-artifact-index.json \
  --lleq-source benchmarks/local/sources/speq/lleq \
  --timeout-sec 1800
```

To recover Dockerfile provenance as well, choose another fresh output and replace
`--artifact-source` and `--artifact-receipt` with `--acquire-archive`; a reviewed
`--timeout-sec 3600` gives additional transfer margin. Later attempts can reuse its
`archive/artifact` and `archive/artifact-receipt.json` without downloading again.
Never point output at an old attempt or wrap this CLI in a second process-group
guard. The CLI owns the shared heavy-job lock; wait for the active native slot to
be released before launching it.

After actual preparation success, the existing public coordinator can run a first
available paper parent, for example:

```sh
uv run --locked python -m scripts.suite_reproduction \
  --settings benchmarks/local/reproduction/preparation/speq-attempt-0002/settings.json \
  --family speq --case speq-taco_spmv_csc --stage all
```

That parent command is proposed, not run here. Preparation success is not corpus
admission, a whole-paper success, proof validation, or device execution.

## Lightweight validation

38 focused tests cover the exact legacy resource dependency/import contract and
historical source reuse with an explicitly absent Dockerfile,
retained Dockerfile/hash/length consistency, full-stream evidence, member-index
integrity, independent source pins, immutable source copies, native version and
reference FIR gates, resource-stop propagation, settings and guarded helper
placement. Acquisition tests use tiny in-memory archives and still require
Dockerfile. Native commands are mocked; these tests establish no native runtime
compatibility or full-parent result. Ruff and mypy pass for the two changed Python
files. Native compatibility of the fresh preparation remains untested.

## Scoped original-C GEMM frontend repair

The public family recipe now requests `c99_frontend_repair: polybench-gemm-address-v1`.
It is published only after fresh, tracked source gates pass. Existing family
settings are not silently upgraded: `--stage all` reuses them; explicit
`--stage prepare` builds and gates the new preparation identity. Direct preparer
users can select `--c99-frontend-repair polybench-gemm-address-v1`; omitting it
preserves the original preparation behavior.

This mode applies only to the original `polybench_gemm` application, requires the
PHI repair and the recorded `-D_FORTIFY_SOURCE=0 -DPOLYBENCH_USE_C99_PROTO` flags,
and refuses arbitrary prebuilt plugins at the recorder boundary. Preparation
uses the tracked `speq_c99_diagnostic` materializer, exact C++ fragment and LLVM
fixtures. Every gate runs under the existing process guard with a 5-GiB cap and
10-GiB disk reserve. There is no dependency on ignored diagnostic output files.
The gate evidence, materialized source and built plugins enter the settings'
identity paths. Failed or resource-stopped gates do not publish enabled settings.

Each selected capture builds a fresh PHI-only/candidate pair, regenerates all
three application FIR regions from the unchanged C, and compares the selected
region to exact, narrowly permitted edits of that fresh baseline. The comparison
derives memory-state names from the baseline; it never renames the candidate or
substitutes historical FIR. Other regions must remain byte-identical, and LLVM
must remain identical except for its verified input-path comment. Only the GEMM
analysis subprocess receives the enable variable. All four reference analyses
run with the candidate disabled and still require their original FIR hashes.

The original parser, original parse-skip decisions, reference rules, 5/1/3
schedule, actual GEMM recognition, ordered extraction results and ordinary replay
admission remain in the existing recorder/validator. Preparation gates alone do
not admit any benchmark. The successful original-C diagnostic is recorded in
[speq-c99-diagnostic.md](speq-c99-diagnostic.md); fresh public preparation and
complete capture at the integrated identity remain separate execution gates.
