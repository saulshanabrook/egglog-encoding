# MISAAL ARM/HVX host-generation recovery

Native preparation now succeeds for all 31 ARM and 39 HVX host generators.
ARM’s full 157-unit selector built in 181 seconds; the prepared library has
SHA-256 `96f0fd7d225a962f12aa6310571baedbb080889820ad9a1c10e0a90b357b29b1`.
Evidence is retained in
`benchmarks/local/reproduction/prerequisites/misaal-arm/attempt-0001/preparation.json`.
HVX preparation and its native concat diagnostic also pass; see
[the detailed recipe](misaal-hvx-preparation.md). ARM blur3x3 now passes complete source optimization and ordinary replay;
the HVX blur3x3 attempt remains in progress. The ARM native parent took
262.6 seconds and peaked at 563 MiB, with one complete Egglog invocation,
all 14 requested native lowering functions and all five final generator outputs.
Its current capture is
`benchmarks/local/reproduction/stages/misaal-arm-blur3x3/complete/46dfa4cbe4fbf61325c69977d9883be0329a67fc0ab2d2525027b709b6f486c4/attempt-0001/capture-result.json`.
These timings describe acquisition only.

A newly identified shared lowering bug affects the old x86 canary as well:
**198 of 198 requested intermediate LLVM functions return `undef`**. That run is
intermediate capture evidence, not validated native optimization. The exact
read-only result is in `MISAAL-LOWERING-AUDIT.json`. The corrected x86 selector
subsequently passed all 198 functions in the retained diagnostic. A **fresh
complete blur3x3 source run and ordinary replay passed on 2026-09-25**:
`benchmarks/local/reproduction/stages/misaal-x86-blur3x3/complete/771795f755a25e4dff5dd7728ea12026978b47a50adfddb1879662a00540d99a/attempt-0001/capture-result.json`.
The native parent took 524 seconds and peaked at about 895 MiB; these are
acquisition diagnostics. One complete independent egraph replay was retained.
The former undefined-result capture remains excluded.

## Inputs and corrected dependency assessment

The source is MISAAL `44ff893445d664cd87f52b08a138260ed2015ba8` with Hydride
`beb825327fc946d65032e96f7cde9acf3d24c13e`, already acquired under
`benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc/sources/MISAAL`.
The detailed input SHA-256 values, coverage sets and all requested case IDs are
in `MISAAL-ARM-HVX-EVIDENCE.json`; no source modules or pickle files were executed
while deriving those counts.

The earlier missing ARM semantics conclusion came from the codegen subtree
alone. The full acquired Hydride checkout supplies
[`code-synthesizer/dsl-ir/ARMSemantics.py`](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/code-synthesizer/dsl-ir/ARMSemantics.py),
[`targets/arm/ARMSemanticGen.py`](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/targets/arm/ARMSemanticGen.py),
`AllSema.py`, `intr.json`, and the real `InstSelectors/arm/arm_wrappers.c.ll`.
The metadata reader's deserialize path imports `AllSema.py`; it does not require
loading the pickle or rerunning ARM ISA semantics generation.

The missing `ARMLegalizer.h` is an output of the existing
[`RoseARMLegalizerGen.py`](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/InstSelectors/arm/RoseARMLegalizerGen.py).
It also writes `ARMLegalizer.cpp` and a selector translation unit per semantic
group. Generation must use the actual MISAAL
[`arm_semantics`](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/lib/sema/ARMSema.py):
its dictionary differs from Hydride's older dictionary in eight shared groups
and renames one representative. The new driver passes `arm_semantics` directly
to the existing generator class; it never substitutes the older dictionary.

Static coverage is complete for these dependencies: 157 frontend groups,
1,152 concrete target instruction names, raw metadata for all 1,152, and all
5,026 required wrapper definitions present among 5,625 supplied definitions.
These are name/metadata coverage checks, not proof of instruction semantics.
The existing wrapper's target triple is `arm64-apple-macosx13.0.0`, consistent
with the ARM Makefile's OS/ISA. Its LLVM12 parse gate is part of preparation.
All nine ARM pattern inputs also exist.

## The SIMD mode repair and its validation boundary

The pinned shared
[`Legalizer.h`](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/InstSelectors/common/Legalizer.h)
initializes `bitsimd` to true. In
[`Legalizer.cpp`](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/InstSelectors/common/Legalizer.cpp),
false selects replacement through `InstToInstMap`, including the necessary
bitcast. True selects the separate PIM/BitSIMD path, which replaces removed
calls with `UndefValue`. The x86, ARM and HVX pass constructors do not override
the default. This explains the retained x86 LLVM's undefined returns even
though LLVM verification succeeded.

`scripts/reproduction_misaal_legalizer.py` provides the narrow repair:
`simd_mode_replacements(source_text, target)` returns an exact patch inserting
`L->bitsimd = false` after allocation of only the selected x86/ARM/HVX legalizer,
before `L->legalize(F)`. It leaves the shared default and actual BitSIMD pass
untouched, rejects ambiguous/drifted contexts, and recognizes an already-fixed
pass. It works on the ARM generator's emitted C++ literal as well as the
checked-in x86/HVX source. The ARM preparer applies it to an isolated generator
copy and saves its diff and before/after hashes. No shared source was edited.

`audit_simd_lowering(llvm_text, required_functions)` records missing named
functions, direct `undef`/`poison` returns, and remaining `llvm.hydride.*` calls.
It must run on the legalized intermediate **before** that result reaches the
live native parent. Ordinary `llvm-as` verification is still required. This
check catches the observed failure; it is explicitly not full LLVM semantic
equivalence, numerical target execution, or proof of arbitrary instruction
selection correctness. Eight focused tests cover the repair boundaries and the
actual failed canary shape. The retained canary's actual required-name manifest
fails the new check for all 198 names.

## Implemented ARM preparation recipe

`scripts/reproduction_prepare_misaal_arm.py` exposes:

```
prepare_misaal_arm(output, template_request, case_ids=None,
                  compiler=Path('/usr/bin/clang++'), cmake=None,
                  boost_include=None, timeout_sec=1800,
                  generator_timeout_sec=120)
```

The in-process API uses the caller's heavy slot; its CLI acquires the shared
lock. The source/template/tool inputs and outputs remain below durable
`benchmarks/local/reproduction`. The API:

1. Verifies the original prepared request and exact MISAAL/Hydride revisions;
   accounts for every selected ARM ID before any build.
2. Statically checks actual frontend/raw metadata/wrapper coverage; verifies
   the runtime wrapper copy equals the pinned original; retains input hashes.
3. Verifies the wrapper with the prepared LLVM12 assembler, under the guard.
4. Copies the original ARM selector generator into its immutable attempt,
   applies only the pass-mode repair, and invokes the generator class with
   actual frontend semantics. The original prepared source stays unchanged.
5. Requires the complete header, main pass and all 157 selector outputs, binds
   their hashes, then compiles those plus original common `Legalizer.cpp` as
   `libARMLegalizer.so`. It uses native Apple Clang, LLVM12, Boost1.81,
   C++14, no RTTI when LLVM lacks it, macOS dynamic lookup, and one build job.
6. Requires a real nonempty library, then calls the generalized existing
   `prepare_misaal_cases` pipeline for the original ARM generators. The x86
   default remains unchanged. Every original generator source and its observed
   headers, selected library, configuration and paper aliases enter its request.

All subprocesses use the existing required guard, 5 GiB cap, warning-pressure
allowance for diagnostics, and 10 GiB disk reserve. Limits are 120 seconds for
LLVM/configure, 600 seconds for selector generation, 1,800 seconds for the
serial legalizer build, and 120 seconds per generator translation/link step.
These are admission ceilings, not measured ARM build forecasts. No installer,
ISA synthesis campaign, device runtime, or numerical benchmark is included.

Example of a single-case guarded preparation:

```sh
.venv/bin/python -m scripts.reproduction_prepare_misaal_arm \
  --template-request benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc/inliner-repair-20260925T055305920155Z/requests/misaal-x86-blur3x3.json \
  --output benchmarks/local/reproduction/prerequisites/misaal-44ff/arm-attempt-0001 \
  --case misaal-arm-blur3x3
```

For all current ARM entries, omit `--case`: the inventory has **31 required ARM
parents**. Generated request commands keep
`target=arm-64-osx-arm_dot_prod-no_asserts-no_bounds_query`, original `-g/-f`
names and the five original AOT output forms. The Makefile's
`HYDRIDE_TARGET=arm`, look-ahead distribution, width16, empty initial hash,
enabled optimizers and disabled frontend patterns remain explicit.
`HL_EXPR_DEPTH` is left unset as in the original optimization recipe;
`Rosette.cpp` defaults to two. `fully_connected` alone adds the source recipe's
`output.type=uint8`. The runtime/benchmark Makefile steps are excluded.

Preparation writes input/generated-source/library hashes and compiler receipts;
its summary remains indexed by every selected case with request or blocker.
Success means prerequisite preparation only. Complete optimization, selected
root accounting, repaired LLVM feedback, native parent completion, ordinary
replay remain separate gates. Proof-mode validation is outside this goal. The old seed may still
identify the historical x86 legalizer: that library is verified as part of the
original environment but is never selected for ARM requests.

## HVX: source-backed repair rationale

Current inventory has **39 Hexagon parents: 31 required and eight extras**.
Original source target identity is `configuration.target = hexagon`, whereas
the generator environment uses `HYDRIDE_TARGET=hvx`. Start with
`misaal-hexagon-blur3x3` from `benchmarks/hexagon/halide/blur3x3`.
All 20 HVX pattern inputs and the three frontend Halide pattern files now exist.
The acquired LLVM12 and already-built Halide both enable the Hexagon backend,
so x86 Linux or target-device execution is not an inherent requirement for
host-side AOT generation. A native canary must still test the full path.

The source
[`HexLegalizerGeneric.cpp`](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/InstSelectors/hexagon/HexLegalizerGeneric.cpp)
contains 307 target names but covers only 306 of MISAAL's 310. Missing names are
`hexagon_V6_vasrh_128B`, `hexagon_V6_vasrw_128B`,
`hexagon_V6_interleave_2_128B`, and `hexagon_V6_interleave_4_128B`;
it additionally contains `hexagon_V6_vassign_128B`. Therefore selecting that
file alone is not complete coverage. The other two C++ selectors are competing
implementations of the same pass: do not glob/link all three.

The two shifts are present in LLVM12; regenerate their mapping from the actual
MISAAL semantics. The two interleave pseudo-ops are absent from LLVM12 intrinsic
enumerations. Their checked-in
[semantics](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/lib/sema/hexsemantics_new.py)
are explicit repeated bitvector concatenation: one 16-bit input twice to 32 bits,
and one 8-bit input four times to 32 bits. This is enough source evidence to
propose a narrow lowering, but no implementation was made here. Its tests must
cover the exact accepted arities/widths and compare the resulting operation to
those semantics; unsupported shapes must fail, not disappear.

A bounded implementation path is:

1. Generate one selector from the frontend's ordinary intrinsic mappings using
   the existing Rose generator, with exact generated-input/output receipts.
   Treat the two pseudo-ops separately. Preserve constant values using the
   existing ARM generator's wide-integer literal strategy; also fix the HVX
   generator's missing final `return false` and apply the SIMD mode repair.
2. Implement the two source-defined concat lowerings directly in native LLVM,
   after validating their actual operand/result shapes. Require meaningful
   equivalence tests and LLVM verification before a parent canary.
3. Make the LLVM-wrapper link optional for this intrinsic-only target, while
   retaining the real wrapper requirement for ARM/x86. Existing ordinary HVX
   lowering uses `Intrinsic::getDeclaration`, not wrapper definitions. This
   removes an inapplicable dependency; it must not create an empty successful
   `hvx_wrappers.ll` placeholder. Verify no unresolved hydride calls remain.
4. Build only this chosen pass with common support and run one guarded complete
   original generator. Require non-undefined selected results before parent
   feedback, then original final outputs and all backend invocations.

The existing request names a nonexistent `wrappers/hvx_wrappers.ll`; until the
reviewed target-specific link/lowering path exists, this is a visible blocker
for every HVX complete-parent request. Merely enabling the CMake target does not
repair it. The original target is
`hexagon-32-noos-no_bounds_query-no_asserts-hvx_128-hvx_v66`, output function
`<name>_hvx128`, `HL_FORCE_HEXAGON_OPT=1`, and three equality-saturation iterations.
Frontend patterns are enabled, unlike ARM/x86. Preserve these differences;
never clone the x86 environment wholesale. `fully_connected` has its own
`output.type=uint8` recipe and exports `HL_EXPR_DEPTH=$(EXPR_DEPTH)` despite no
local default for that Make variable: its empty-value behavior needs an explicit
source-supported configuration decision before request expansion. SDK harness
compilation and Hexagon simulator execution are later timing steps and are not
part of this requested host-generation path.

Public upstream checks are retained in `MISAAL-ARM-HVX-UPSTREAM.json`. Current
MISAAL head remains44ff. Current Hydride default head is0c97d0f9d3f8cd0494e421b9ece4b24488b614e5;
its inspected ARM/HVX selector leaf files are byte-identical to pinnedbeb.
The exact missing header/wrapper paths have no default-branch commit history
from the queried endpoints. That is a bounded negative result, not proof that
no other repository or branch contains a compatible implementation.

## Validation and remaining limitations

24 focused Python tests pass: 11 existing case-pipeline checks, five new ARM
preparation checks, and eight mode/lowering checks. All native processes are
controlled fixtures. Ruff/Mypy and ARM CLI help pass. A real read-only call to
`inspect_arm_inputs` confirms the 157/1152/5026 coverage counts above. This slice
ran no native build, source generator, optimizer, simulator or device program.
