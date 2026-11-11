# Disabled C99 address-serialization candidate

This candidate has **not** compiled or run natively. It is not connected to the
recorder, preparation settings, or corpus admission. It targets the retained
`polybench_gemm` C99 frontend output, not the separate SCALAR_LB loop-summary
problems. Native gates decide whether its deliberately restricted domain covers
the actual application.

The original parser's `MkFold.castinst` discards `sext` and `zext`, and represents
both i32 and i64 as mathematical integers. Printing a missing zero extension is
therefore insufficient. The candidate requires LLVM 17 ScalarEvolution to prove
its source nonnegative at each serialized use. Original cast instructions remain
in the FIR evidence. Negative or unknown unsigned-to-signed interpretations,
truncations, unrepresented integer widths (such as i16), floating casts,
memory-derived external definitions and unsupported
arithmetic are rejected. Signed widening retains its signed value; an address
index additionally needs the nonnegative domain below.

Only one explicitly named function is eligible. The candidate plugin remains
disabled unless `SPEQ_REV_C99_DIAGNOSTIC=1` is set for the individual frontend
invocation. Any other value or a missing selected definition fails. LLVM's module
verification excludes duplicate function/global names. All other functions keep
their existing REV serialization, including setup regions the original parser
skips. No region, pass or existing skip boundary is removed.

The three changes are local to serialization:

- Emit a dependency-ordered closure of dominating, pure entry/preheader
  casts/adds/multiplies before their loop-body uses. Recheck domain conditions at
  every use, even when a definition was already emitted. Definitions in existing
  loops retain their original scope and serialization.
- Flatten only inbounds, address-space-zero, same-`double`, single-i64-index GEP
  chains rooted at an argument. Nonnegative interval bounds must prove every
  integer operation and new sum fits its signed width. This retains original
  inbounds/defined-execution preconditions; it is not a claim that arbitrary C
  pointer inputs are defined. No LLVM instruction or Egglog equality is inserted.
- Infer `ptr 1 double` for a memory root only when every reachable pointer use is
  a compatible GEP or nonvolatile/non-atomic double load/store. Escapes, conflicting
  element types and unsupported uses fail. No general tensor or product-state
  language is introduced.

The actual counterexample is retained at
`stages/speq-polybench_gemm/complete/11c4e63e0a9d5ff9b9cddf33bca39c56d2425f0b1af18f88562ea8787ca389cc/attempt-0001/capture/speq/speq-polybench_gemm/source/frontend/`
under `benchmarks/local/reproduction/`. Its `analysis.ll` hash is
`00d29c8af3f9c40ac2720bdd9c4003bb463eb2d9c2ae0c6eced479f59fb7f8bd`;
`application-002.fir` is
`88ea197d575dfd8cf55a189ff2e6d067f40b3f1369da4f95129605c716ee334f`.
The missing `%0/%1` are dimension widenings; `%arrayidx*` chains denote offsets,
not nested array objects; the single mutable C root currently has bare `ptr`.

## Root-run gate recipe (not executed)

Materialization is data-only and reuses the PHI materializer for original source,
REV/MemorySSA header pins, and the separately retained PHI baseline:

```sh
.venv/bin/python -m scripts.speq_c99_diagnostic \
  --source benchmarks/local/sources/speq/lleq \
  --function polybench_gemm \
  --output benchmarks/local/reproduction/diagnostics/speq-c99-native-0001/materialized
```

Root must hold the shared `benchmarks/local/reproduction/stages/.heavy-job.lock` through
`exclusive_job`, and run each native command sequentially with
`run_bounded_command(require_guard=True, memory_limit_bytes=5*1024**3,
disk_reserve_bytes=10*1024**3, allow_warning_pressure=True)`. Use a fresh receipt
directory, 120 seconds for compilation, 30 seconds per tiny fixture, and retain
every command, tool hash, guard result, stdout/stderr hash and generated-file
hash. Stop on timeout/resource failure; a negative fixture passes only on an
ordinary nonzero exit **and** its expected diagnostic text. Do not automatically
retry safety failures.

1. Record LLVM 17.0.6 `clang++`, `opt`, `llvm-config` hashes/version. Under the
   guard obtain `llvm-config --cxxflags --ldflags --libs core analysis irreader
   support --system-libs`; split those flags with `shlex.split`. Compile
   `materialized/c99-harness.cpp` using those exact flags. This harness contains
   the same fragment as the candidate plugin, verifies IR, creates real DT/LI/SE
   analyses, and asserts its LLVM module is unchanged after serialization.
2. Invoke `[harness, materialized/fixtures/<name>.ll, name]` for each ordered gate
   in `diagnostic.json`. The three positive fixtures cover guarded variable
   stride, nonzero offsets and a distinct stride. The thirteen rejection fixtures
   cover unsafe zero extension, negative index, truncation, overflow, external
   load/PHI, conflicting memory type, non-inbounds access, pointer escape, wrong
   index width/layout, an unrepresented integer type and reserved-name collision. Require positive output to
   contain the original `%n64`/`%row64` cast definitions, `memory-type: ptr 1
   double`, a flattened `%element` rooted at `%C`, and `LLVM module unchanged`.
   Check the emitted address's actual operand structure, including +3 or stride
   +7 where applicable; exit zero alone is insufficient. Zero/negative dimensions
   keep the original no-iteration guard; the harness never executes input IR.
3. Build the PHI baseline and candidate full plugins separately using the same
   existing `build_rev_plugin` compile command shape: `clang++ -fPIC -shared
   <tree>/llvm/lib/Analysis/REVPass.cpp scripts/paper_benchmarks/speq_rev_plugin.cpp
   -I<tree>/llvm/include <LLVM flags> -o <fresh-plugin>`. Use the existing core,
   analysis, passes, scalaropts, transformutils, ipo, support library list. Do not
   pass the candidate tree to `build_rev_plugin`'s original-source hash check or
   replace an existing plugin.
4. With the opt-in environment absent, run the four existing `reference_fir`
   gates against each plugin and require the unchanged pinned hashes. These
   helpers themselves call subprocesses: invoke their Python driver as a child
   of the guard, not directly in the controller.
5. Compare baseline versus enabled candidate on the exact retained GEMM LLVM
   above, using unchanged `-passes=print<revpass>`. Retain baseline's missing
   definitions/nested addresses/bare memory type as the original failure. Require
   selected candidate FIR scalar closure, correctly composed C/A/B addresses,
   and typed C fold state. Compare every other ordered region's FIR byte-for-byte
   with baseline; setup skips must not be suppressed. In a separate invocation,
   enable the candidate on a reference module lacking `polybench_gemm`; require
   the explicit missing-definition failure. A verifier-invalid module with
   duplicate definitions must also fail before any serialization is accepted.
6. Only after these gates may a separately reviewed diagnostic driver scope the
   opt-in environment to original-C frontend generation, leaving reference
   generation disabled. Preserve original C, C99 flags and the exact existing
   `mem2reg,loop-rotate,instcombine,simplifycfg,loop-simplify,gvn,lcssa,print<revpass>`
   pipeline and `-enable-load-in-loop-pre=false`. Reuse the existing parser and
   full ordered region driver with original rules and 5/1/3 schedule. Require
   actual GEMM recognition, complete parent accounting and separate standalone
   ordinary validation. No claim of recognition or admission follows from the
   analysis fixtures alone.

No native runtime result is currently claimed. If LLVM cannot prove an actual
use's required domain, retain that rejection and inspect it; do not silently
erase casts, substitute a reference or weaken the check.
