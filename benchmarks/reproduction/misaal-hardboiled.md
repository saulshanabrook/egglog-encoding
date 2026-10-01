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
check and 10 GiB disk reserve. MISAAL defaults to a 900-second, 5 GiB parent allowance;
individual backend and LLVM tools have 120-second limits. HardBoiled complete-mode compilation
and generation each have the configured family timeout (300 seconds by default
in the coordinator) and a 5 GiB allowance. The historical partial-capture CLI
keeps its 120-second, 2 GiB defaults. The current native guard accounts for the launch process group;
detached descendants require verified accounting and cleanup before increasing
a source allowance. Linux executables must use the coordinator's Linux
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

Optional `source_timeout_sec` sets the complete source-parent time budget in
seconds, independently of ordinary replay's timeout. It defaults to 900 and must
be a finite positive JSON number (booleans are rejected). The effective value is
recorded in the capture receipt; the request bytes participate in acquisition
identity. A changed budget needs a new derived request and fresh attempt. It does
not change the memory limit, disk/host guards, cache transitions or completion
requirements, and does not authorize a longer run before detached-descendant
accounting and cleanup have passed their safety gate.

Optional `source_memory_limit_bytes` sets the complete source-parent aggregate
RSS allowance, including the registered Racket groups. It defaults to 5 GiB and
must be a positive JSON integer no greater than the existing 10 GiB host-policy
cap; booleans and fractional values are rejected. The effective allowance is
recorded on successful and failed captures. Ordinary replay budgets, the source's
eight-worker pool, solver timeouts, fresh-cache transitions and output checks
are unchanged. The mandatory 2 GiB host reserve, critical-pressure stop and
10 GiB disk reserve still apply. This sampled guard neither reserves memory nor
guarantees a higher allowance is safe or sufficient; recheck host conditions
before any separately authorized run.

Use a new derived request and fresh attempt for a changed allowance, preserving
the old request and failed evidence. Request and adapter hashes participate in
acquisition identity. Introducing this adapter policy invalidates prior MISAAL
capture identities, which require explicit refresh before current admission;
it does not promote historical captures or change other families' adapters or
the performance cache.

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

### Acquisition output policy

Fresh family publication derives new requests with
`"acquisition_tail": "llvm-ir-only-v1"`. It retains the original requests and
their hashes, and records each changed field as `acquisition_tail_delta` in the
family receipt. This policy selects `-e stmt,h,llvm_assembly`, expects exactly
the named `.stmt`, `.h`, and `.ll` files, and explicitly sets
`HYDRIDE_DISABLE_LLVM_OPTS=1`. The original full-output request remains usable
without this policy. Existing source, generator, library, selector and runtime
bytes, rewrite flags, cold caches, timeout and guards are preserved.

At MISAAL `44ff893445d664cd87f52b08a138260ed2015ba8`, `Module.cpp` builds the
LLVM module before its separate object/archive/assembly output branches. The
remaining `.ll` output still reaches every `compile_func`, MISAAL call, and
`add_hydride_code`. That method links the actual legalized feedback and performs
wrapper inlining/deletion itself. `finish_codegen` verifies the module before
the source-supported environment switch skips its final LLVM optimizer. The
policy pins these source files, including the Hexagon code-generation path.
Unsupported flags, multiple targets, duplicate output selections, wrong output
filenames, environment conflicts and missing source pins are rejected.

All selected Egglog results still feed their real continuations. Legalization,
the required-function/SIMD audit, `llvm-as`, parent completion, standalone
materialization and ordinary replay retain their existing checks. This mode
omits final machine-code products; it does not report their generation as
successful, perform target-device execution, or constitute performance evidence.

Native fidelity gates are required before adopting these requests into the
corpus. Compare a complete reduced-tail `mul` run with its retained five-call
x86 control, then ARM `blur3x3` and HVX `tensor_add` controls at matching source,
tool and runtime identities. Account for every call, duplicate, helper result,
selected output and replay contract; compare actual legalized feedback using
only the receipt-declared capture-name normalization. Final LLVM bytes may
differ because the final optimizer is omitted. Require successful parent and
ordinary validation with unchanged LLVM checks; an unexplained comparison
difference is inconclusive and stops promotion. Unit/protocol tests alone do
not establish these native gates.

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

Complete MISAAL capture now requires `racket_group_containment` set to
`misaal-racket-lease-v1`, a pinned absolute `racket` executable and its
`racket_sha256`, and the exact pinned `lib/utils/DSLInstructionUtils.py` hash in
`source_hashes`. Old requests lacking these prerequisites fail before launch.
The source's detached Racket group reserves a launch before fork and waits for
an authenticated outer-guard lease before starting actual Racket work. RSS
accounting includes the root and registered groups once each. Source-local
`killpg` timeout/fallback remains, with confirmed group drain required; loss of
the guard lease kills the supervisor's own group. Root shutdown retains the
unreaped PID, stops root work first, then drains registered groups. This is a
sampled operational guard for the pinned launch sites, not a general process
sandbox or hard allocation limit. Receipts identify this accounting scope.

The prepared ignored known-launch diagnostic fixtures test this contract
with a Python-backed Racket stand-in, separately from package readiness. They
must pass as real guarded processes before any longer source canary. The actual
Racket prerequisite smoke at
`benchmarks/local/reproduction/diagnostics/misaal-racket-prerequisite-0001`
found Racket 9.2 but failed to load Rosette; Rosette/Hydride/MISAAL package
readiness remains unproved. A later isolated preparation step must use the
artifact's vendored packages, pin that environment, and prove the solver/source
package smoke before emitting fresh guarded requests. Neither existing requests
nor retained cache contents are rewritten by this change.

### Optional parameter-synthesis ABI restoration

The opt-in `parameter_abi: "c098-four-argument-v1"` contract restores the
executable parameter-synthesis ABI from paper revision
`c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4` inside the otherwise unchanged
`44ff893445d664cd87f52b08a138260ed2015ba8` source. The newer Python emitter
always sends five arguments, while both revisions' `synthesize-param-expression`
Racket definition accepts four. The adaptation removes the Python emitter's
`reg_only` parameter and fifth emitted argument, and removes the sole
`reg_only=True` call argument in `generate_param_expr_general`. Passing that
keyword to the restored emitter raises an error; it is never silently ignored.

This is explicitly a **mixed-revision restoration**, not evidence that the
undocumented register-only intention is preserved. The general source-parameter
legalization call still uses the paper's depth 1 and exclusions. Its grammar
permits arithmetic, including multiplying a destination parameter by two to
recover a source parameter. The paper's commented `reg-leq` assertion stays
commented. Newer bidirectional validation, simplification, example limits,
ordinary depth-2 queries, cache behavior and source-local timeouts remain as
written in 44ff. A successful synthesis fits the supplied examples; it does not
establish universal semantic correctness.

`restore_parameter_abi` in `scripts/reproduction_misaal_patterns.py` requires
both the request's `source_hashes` and actual checkout bytes to match:

| Source | SHA-256 |
|---|---|
| `lib/patterns/PatternUtils.py` | `e89b1a4c9dda901f2416100dbc6b5e47554264e00eb755c52c669f48b54eb8d5` |
| `misaal/synthesis/param_abstract.rkt` | `762f379a373b30c965d8bb3760b2908515f52945e58a76c820c11da2fa6c2b47` |

Before installing either method, the helper verifies the loaded class, every
method's full-module code identity, globals and defaults. It compiles the
two-site adaptation in memory, replaces only the emitter and general method,
and restores their original objects on every exit. It never edits the checkout
or imports pattern populations again. Its receipt records source, original and
adapted method, virtual-source and implementation hashes, plus the mixed-revision
semantics. An absent request flag has no effect; unsupported contracts and
changed identities fail closed.

This helper alone does not authorize a native capture or establish runtime
readiness. Public capture integration must include the request field and these
source pins in acquisition identity, enter the context around actual source
execution, and retain the existing containment and resource guards. Before a
source canary, run genuine emitted scripts for the ordinary depth-2 and general
depth-1 paths using the pinned Racket/Rosette packages. Focused offline tests
compare both complete generation paths with the original paper methods and
retain the arithmetic distinction. Native and proof admission remain separate.

The durable gate recipe is `scripts/reproduction_misaal_abi_gate.py`. After
isolated Racket preparation completes, run it from the repository root:

```sh
python -m scripts.reproduction_misaal_abi_gate \
  --runtime "$PREPARED_RUNTIME_JSON" --checkout "$PREPARED_MISAAL_CHECKOUT" \
  --output "$FRESH_ABI_GATE_DIRECTORY"
```

The fresh output must be beneath `benchmarks/local/reproduction`. The standalone
entrypoint owns the shared heavy-job lock. `run_gates(runtime_path, checkout,
output, lock_owned=True)` is reserved for the coordinator while it already owns
that lock. Each of the four generated-script gates and the captured-script gate
runs sequentially through the existing 60-second, 5 GiB process-group guard,
with 2 GiB host reserve and 10 GiB disk reserve. A failure stops the sequence and
retains partial receipts. No acquisition, LLVM/Cargo build, source workflow or
checkout edit occurs. `prepare_programs(checkout, output)` only reconstructs the
four scripts offline and requires a fresh output directory.

The generator instantiates the pinned source's full-module method code without
executing its imports or pattern populations. Both adapted programs must match
the tracked c098-generated oracle bytes exactly. Both original five-argument
controls must fail specifically with the four-versus-five arity error; unrelated
failures do not pass. The exact historical `ki4k2nlc.rkt` and the small paper
oracles live in `benchmarks/reproduction/fixtures/misaal-parameter/`, with source
identities and capture provenance. The captured fixture is an actual source
operation from a diagnostic attempt, **not an inferred program, benchmark input
or evidence of complete reproduction success**. Its original bytes remain
unchanged; only the documented single argument removal is applied to the
separate executed copy.

The returned `abi_gate` and `captured_gate` references identify the existing
result contracts accepted by `seal_runtime`; the recipe does not itself seal or
publish a runtime. Completed package/runtime identity checks, the runtime seal,
and a fresh complete source canary remain separate requirements.
