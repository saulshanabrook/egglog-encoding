# Simplest faithful sources for the reproduction corpus

Reviewed 25 September 2026 after the user selected the author-published
HardBoiled files. This is a source and pipeline review, not another benchmark
campaign. Math and Luminal are unchanged. Recommendations below do not silently
replace the accepted populations or promote incomplete source runs.

The useful boundary is a complete Egglog workload: its real initialization,
active rules and schedule, and original extraction/check or an observed native
extraction result. Once that workload is captured and validated, ordinary replay
does not need the original compiler, device, or paper performance experiment.
Published files are preferable when they already contain that complete work.

## Published collection

The inspected [egglog-benchmarks revision](https://github.com/yihozhang/egglog-benchmarks/tree/a85aa6e2f5195d850fba57700efcf97dc1b507a6/benchmarks)
contains 42 HardBoiled files, 32 Eggcc files, and pointer-analysis inputs. It has
no DialEgg, Churchroad, MISAAL, or SpEQ collection. Pointer analysis remains out
of scope.

- **HardBoiled:** use the selected 42 files from parent revision
  `da432767a04c1803dc7edb5a9f653d90c0fbe623`, which retains the original
  extractions. All 42 have passed ordinary replay with all 2,074 outputs.
  Halide regeneration and missing GPU/AMX paper-cell reconstruction are no
  longer prerequisites for this selected suite. See the
  [source choice and validation](hardboiled-published-suite.md).
- **Eggcc:** the 32 published programs contain initialization and an optimization
  schedule, but none has an extraction or check. They are usable as a separately
  described saturation-only suite. They do not directly replace our
  output-bearing optimizer workloads. Adding an arbitrary query or claiming
  that their table-size output is the optimized program would change the claim.
  Their subset also does not cover our complete source population.

For Eggcc, retain the already completed output-bearing captures rather than
regenerating them or replacing them with those 32 saturation-only programs.
The existing source route preserves custom extraction and feedback between
optimization passes. Missing Gurobi access concerns separate configurations;
it does not prevent reusing the successful non-Gurobi exports.

## Churchroad

The [pinned Churchroad source](https://github.com/gussmith23/churchroad/tree/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721)
has two Egglog libraries and six feature fixtures, not a complete standalone
mapping driver. The inspected evaluation revision `af615fa` has no `.egg`
files. The original Rust driver runs mapping, invokes Lakeroad, feeds generated
commands back into the same egraph, and finally uses a custom extractor. Its
initial Egglog prefix therefore does not contain the complete computation.

Both required circuits already have validated full-session exports. Reuse those
files; no new Yosys, Racket or Lakeroad run is needed to benchmark them. The full
source path remains useful only when regenerating a changed source workload.
See the [current native/replay audit](../local/reproduction/diagnostics/eggcc-churchroad-optimized-refresh-0002/audit-0001.md).

## DialEgg

The six [artifact benchmark templates](https://github.com/AzizZayed/dialegg-cgo-artifact/tree/4d0d522e98c15becdc5e7d711348cb0891ff0d44/bench)
all contain both `;; OPS HERE ;;` and `;; EXTRACTS HERE ;;`. The original
[`runEgglog` implementation](https://github.com/AzizZayed/dialegg-cgo-artifact/blob/4d0d522e98c15becdc5e7d711348cb0891ff0d44/src/EqualitySaturationPass.cpp#L31)
fills these with the MLIR block's actual operations and selected roots, then
overwrites the same `.ops.egg` pathname on later calls. Copying the checked-in
templates alone would omit the program. The newer DialEgg repository still has
these placeholders in its 2mm example at
`96b0b040d7868181554956d7184694085dfecf06`.

Our existing captured files are the simpler runnable deliverable. All 24 required
source configurations already have successful capture and ordinary validation;
there is no need to rerun the paper's machine-code execution or timing scripts.
Saving each actual call before the file is overwritten remains necessary.

One avoidable implementation cost is confirmed: `capture_case` dispatches one
case, and `capture_complete_dialegg` rebuilds the same instrumented frontend for
each uncached case. `prepare_complete_dialegg` always compiles the same three C++
objects and links them, independent of the selected benchmark. Move that build
into reusable preparation, keyed by the source, instrumentation and toolchain.
This is a proposed cache improvement; the current audit did not change it or
rerun any source case.

## SpEQ

The verified [complete artifact](https://zenodo.org/records/10963236) member
index has 73,109 entries. Its only four `.egg` names are unrelated Python package
archives/directories; there is no ready-made Egglog program corpus. The local
member-index SHA-256 is
`23acf74505c56b2e08479b8cfb82a52b4670ef5f95bd3fce36192649615ab136`.

The existing recorder already uses egglog-python's native recording of the
actual parser, rules, schedule and extracts. It does not infer a substitute
`.egg` file from C. For source reproduction, LLVM/REV is needed to derive the
input FIR. For replay, the recorded `.egg` needs neither LLVM nor the Python
frontend. All eight available applications now have successful ordinary replay,
including GEMM; the old seven-success snapshot predates that repair.

The [preserved REV unit-test FIR strings](https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/unittests/Transforms/REV/REVTest.cpp)
offer a shorter starting point for a separately labeled FIR-test suite. They are
not complete original-C application captures, and a known historical PHI
translation error makes silently swapping them into the repaired source corpus
incorrect. Existing eight validated captures should simply be reused. The
[two missing inputs](speq-missing-inputs.md) cannot be recovered by bypassing
compilation or by inventing replacements.

## MISAAL

The inspected original `c098f0f` and current `44ff` source trees have five `.egg`
files: four rule/definition fragments and one complete HVX dot-product unit
example. Neither is a published corpus for the full source-configuration set.
The checked-in generated Python/LLVM machinery therefore cannot be replaced by
an existing complete `.egg` collection in those sources. This is bounded to
the repositories/revisions inspected, not a claim that no other copy exists.

There is nevertheless an unnecessary coupling worth removing: the emitted
Python child completes its Egglog rewrite/swizzle calls in `compile_hydride()`
before calling `run_llvm_legalizer()`. For ARM depthwise convolution, all eight
Egglog calls succeeded and the later selector rejected a vector constant. That
failure is downstream of the Egglog work. Fixing the selector is needed to
claim complete native lowering, but not inherently to replay the already
completed Egglog computation.

The user subsequently chose **complete Egglog export; native lowering not
requested** and explicitly said not to attempt LLVM lowering. Historical
downstream failures remain recorded. Admission still needs
all source-emitted children accounted for, complete Egglog processing for each
selected workload, and successful ordinary replay. If a later Egglog call
depends on earlier native feedback, that feedback cannot be skipped. The new
export path must preserve that input dependency or report a blocker. This change
is authorized but not yet implemented; depthwise has not yet passed standalone
admission, and failed prefixes do not become complete automatically.

By contrast, the live ARM `conv_nn` attempt repeats identical rewriting inputs
while leaving an unlowered `typed_signed-vector_reduce_add`. That loop occurs
inside Egglog processing, before LLVM legalization; removing the downstream
gate would not turn it into a completed optimization. Preserve that distinction
instead of labeling every artifact failure as an unnecessary compiler stage.

The source/log investigation is retained in
`benchmarks/local/reproduction/diagnostics/misaal-arm-depthwise-selector-audit-0001/`.

## Shared cache boundaries

`scripts/suite_reproduction.py::case_identity` hashes the entire population file
and every `VALIDATION_SOURCES` entry into source-capture identities. Those entries
include unrelated family adapters. Consequently, changing a HardBoiled replay
validator or another family's inventory can force unchanged source generation
again. That is more conservative and expensive than necessary.

First remove unrelated family dependencies from the existing identities and
keep validation-only changes at the existing validation boundary. Add no new
stage machinery just for this cleanup. Key each stage by what it consumes. Keep
relevant source/tool hashes and safety policies; do not simply ignore changes
that affect generated programs or validation. Existing raw captures should be
reusable when only replay validation or unrelated family metadata changes.
The performance cache's existing identity rules remain separate and unchanged.

These are targeted simplifications, not a request for another export framework.
The published-input route and existing recorded replays should converge on the
same small corpus manifest and normal benchmark runner. No source acquisition
needs to run during ordinary timing of an already validated `.egg` file.
