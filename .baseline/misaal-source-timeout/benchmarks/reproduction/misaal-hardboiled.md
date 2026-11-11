# Complete HardBoiled and MISAAL acquisition

These adapters capture source optimization through native compiler output. They
do not run generated target code or collect benchmark observations. Historical
partial capture modes remain available for diagnosis; they are not complete
source receipts.

## Coordinator boundary

Call the following Python APIs directly from the coordinator, without another
native process-group wrapper:

```python
from scripts.misaal_reproduction import capture_misaal
from scripts.suite_capture_hardboiled_misaal import (
    capture_hardboiled,
    prepare_hardboiled_capture,
)

misaal_case = capture_misaal(request_path, fresh_attempt)
hardboiled_cases = capture_hardboiled(
    checkout, build, fresh_capture, sidecar,
    {"hardboiled-matmul_vnni_1x1"},
    optimization_only=True, library=halide_library, compiler=compiler,
)
hardboiled_prepared = prepare_hardboiled_capture(
    fresh_capture / "cases.json", fresh_preparation,
)
```

Both complete paths use the shared native guard with a required host-memory
check and 10 GiB disk reserve. MISAAL has a 900-second, 5 GiB parent allowance;
individual backend and LLVM tools have 120-second limits. HardBoiled complete-mode compilation
and generation each have the configured family timeout (300 seconds by default
in the coordinator) and a 5 GiB allowance. The historical partial-capture CLI
keeps its 120-second, 2 GiB defaults. All descendants inherit
the guarded process group. Linux executables must use the coordinator's Linux
container runner rather than the native API on macOS. The coordinator owns
platform matching, source acquisition/builds, immutable attempt identity, and
resume policy. An interrupted/resource-stopped attempt is not a success.

`capture_misaal` returns a dictionary and saves `capture.json` and `process.json`.
HardBoiled returns/saves a case list in `cases.json`; preparation returns/saves
the corresponding case list in `preparation.json`. Prepared records contain:

- `status`, `reason`, and `workloads`: replay paths, exposed only when every
  required source/native boundary and every capture contract succeeded;
- `source_completion`: parent outcome plus actual output paths and SHA-256;
- `invocations`: every actual call, including byte-identical calls, with raw
  input, output, executable and replay hashes;
- each invocation's `root_count`, ordered `selections` (`root`, `selected`,
  `check`) and `ordinary_contract`.

`ordinary-validation-pending` is deliberately not admission. Run every replay
with the ordinary engine and compare its extract count/order with the recorded
contract; all added equality checks must pass. Equality establishes membership
of the source's actual choice, not identical cost-model optimality. Strict proof
validation is a separate result. No adapter inserts a selected term as an input,
unions it into a root, substitutes an invented backend response, or shortens a
schedule. Existing extracts remain in place; checks follow their extracts within
the original push/pop scope. Unchanged native selections are valid observations.

## HardBoiled boundary and first canary

`hardboiled_aot_source` creates an attempt-local C++ copy. It replaces exactly
`result.realize(out, target)` with `compile_to_llvm_assembly`, using inferred
arguments and the existing target. It keeps later compilation calls and scopes
`/tmp` diagnostic filenames to the attempt. An unrecognized realization shape
fails before compilation. This replacement is a proposed source adaptation;
the first real canary must establish its compatibility with the pinned Halide
API and the relevant pipeline bounds.

The sidecar wrapper forwards actual stdout to HardBoiled's native parser. It
independently records each raw input, sidecar identity/status, and every selected
root. Complete status requires parent success, all sidecar calls succeeding,
and fresh nonempty native output files. AMX requires each replacement LLVM file;
GPU generators require their emitted `.a`, `.stmt`, `.h`, `.ll`, and `.s` files.
The native parent still executes HardBoiled's post-selection lowering.

The first proposed canary is `hardboiled-matmul_vnni_1x1`:

```sh
python scripts/suite_capture_hardboiled_misaal.py hardboiled \
  --checkout "$PREPARED_HARDBOILED" --build "$PREPARED_HALIDE_BUILD" \
  --halide-library "$PREPARED_HALIDE_LIBRARY" --sidecar "$PREPARED_SIDECAR" \
  --case hardboiled-matmul_vnni_1x1 --optimization-only \
  --output "$FRESH_CAPTURE"
python scripts/suite_capture_hardboiled_misaal.py hardboiled-prepare \
  --capture "$FRESH_CAPTURE/cases.json" --output "$FRESH_PREPARATION"
```

These variables denote prepared prerequisites, not existing verified builds.
The actual inspected source is
`benchmarks/local/recovery-20260922/misaal-hardboiled/sources/HardBoiled/instrsel-benchmarks/matmul_vnni_1x1.cpp`.
The source revision is `b99cf0c6400e954a278f697bf3a0596ac3fa4f25` and the separately
acquired sidecar revision is `aa2beffdca1043e0468a03be8c316f934abdd7d9`.
The retained directory is selected source recovery, not a new complete build.

After the canary, verify all reached calls, replay contracts and actual output
files before expanding. `case_records` and `revision` may be supplied explicitly
to `capture_hardboiled`; cases have `id`, checkout-relative `source` and
`configuration` fields. This permits reviewed new source-to-paper mappings
without rewriting the current catalog. The default catalog still has only five
AMX programs. This adapter does not claim those cover all seven supported paper
cells; their exact source/type/tiling mapping remains an explicit prerequisite.

## MISAAL request and first canary

`capture_misaal` accepts a JSON request with the following fields. Paths must be
absolute in the execution environment. SHA-256 values must be computed from
actual prepared files; placeholders must not be submitted.

| Field | Required value |
|---|---|
| `case_id` | Stable source/configuration identity |
| `revision` | Full 40-hex MISAAL source revision |
| `checkout` | Prepared complete MISAAL checkout |
| `source_hashes` | Checkout-relative path to SHA-256 mapping; at least `lib/compiler/EggLogCompiler.py` and `lib/compiler/HydrideCompiler.py` |
| `python`, `python_sha256` | Actual dependency environment interpreter |
| `backend`, `backend_sha256` | Actual source-compatible Egglog backend |
| `llvm_as`, `llvm_as_sha256` | LLVM syntax verifier matching the source toolchain |
| `generator`, `generator_sha256` | Built original Halide generator |
| `generator_command` | Argument list, beginning with `generator`, using `{output}` for its fresh output directory |
| `expected_generator_outputs` | Nonempty relative output list, including final `.ll` |
| `environment` | Exact source flags plus Hydride/Python/LLVM paths |

Additional provenance fields, such as dependency revisions, patch hashes and the
generator build receipt, are preserved in the request receipt. The coordinator
should supply them. The adapter also records actual legalizer script, input,
library, intrinsic and LLVM-tool identities at the boundary.

For an HVX add canary, the actual inspected source recipe is
`benchmarks/local/artifact-audit-20260924/misaal/cases/misaal-hexagon-add/request.json`;
the source is
`benchmarks/local/artifact-audit-20260924/misaal/source/benchmarks/hexagon/halide/add/src/add_generator.cpp`.
Its command shape for this adapter is:

```json
{
  "case_id": "misaal-hexagon-add",
  "revision": "44ff893445d664cd87f52b08a138260ed2015ba8",
  "generator_command": [
    "ABSOLUTE_PREPARED_GENERATOR", "-t", "0", "-o", "{output}",
    "-g", "add", "-e", "static_library,stmt,h,llvm_assembly,assembly",
    "-f", "add_hvx128",
    "target=hexagon-32-noos-no_bounds_query-no_asserts-hvx_128-hvx_v66"
  ],
  "expected_generator_outputs": [
    "add_hvx128.a", "add_hvx128.stmt", "add_hvx128.h", "add_hvx128.ll", "add_hvx128.s"
  ],
  "environment": {
    "HYDRIDE_BENCHMARK": "add_hvx", "HL_FORCE_HEXAGON_OPT": "1",
    "HL_ENABLE_HYDRIDE": "1", "HL_ENABLE_MISAAL": "1",
    "HYDRIDE_TARGET": "hvx", "MISAAL_EQ_SAT_ITERS": "3"
  }
}
```

This fragment illustrates the inspected artifact recipe, not a complete runnable
request: fill all fields from the table, and include the prepared `PYTHONPATH`,
`PATH`, `HYDRIDE_DIR`, `HYDRIDE_ROOT`, `LEGALIZERS_DIR` and LLVM paths required by
the acquired checkout. Recheck the recipe against the pinned candidate checkout
before adopting it. Three iterations are the inspected artifact setting, not a
claim of agreement with the paper's five-iteration description. No current
44ff checkout or build receipt existed at the time this adapter was implemented.

Once prerequisites and the request have been reviewed, the proposed first call is:

```sh
python scripts/misaal_reproduction.py capture \
  --request "$PREPARED_HVX_ADD_REQUEST" --output "$FRESH_ATTEMPT"
```

The prepared checkout must have no existing `lib/patterns/*.pickle`. Generated
caches are hashed after the attempt; do not point the request at retained source
recovery containing old caches. Use a fresh prepared copy for another attempt.

The adapter observes the **actual generated Python child**, executes each actual
Egglog call, and returns the same last-line choice expected by the original API.
All stdout selections are retained for replay even when that API consumes only
the last. The genuine low-level LLVM script runs with checked native tool exits.
Fresh legalizer outputs must define every requested function and pass `llvm-as`.
The legalized `.ll` is copied to the frontend's expected feedback path, and the
original Halide generator must return successfully with all final outputs.

The source hardcodes `/tmp/<HYDRIDE_BENCHMARK>` for LLVM feedback. The adapter
appends an attempt-specific suffix to that output name and records both names;
it does not change rewrite flags or schedules. Feedback paths are rejected if
already present. Durable copies are kept under the attempt. Native fresh-run
validation must check that this output-name adaptation has no optimization
effect. A failed import, backend, legalization, missing function, or late parent
failure leaves `workloads` empty, with its raw calls retained as diagnostics.

Only the outer `capture` mode is a public native entrypoint. `frontend`, `child`
and `low-level` are internal hooks and must stay inside the native guard or the
coordinator's guarded container. The legacy SIGTERM frontend capture and
intentional legalizer-abort helpers are not used by this path.
