# MISAAL HVX prerequisite recovery

This slice is implementation plus static/source-model validation only. No native
selector generation, C++ build, optimizer, capture, Hexagon SDK, simulator or
target program was executed. A real guarded build and native lowering canary
remain necessary. MISAAL is pinned at
`44ff893445d664cd87f52b08a138260ed2015ba8`; Hydride at
`beb825327fc946d65032e96f7cde9acf3d24c13e`.

## Inputs and exact lowering scope

`inspect_hvx_inputs` reads the actual frontend dictionary with AST literal
parsing, without importing upstream modules. The retained input check in
`MISAAL-HVX-PREPARATION-INPUTS.json` found **114 groups, 310 concrete target
names**: **308** have LLVM12 Hexagon intrinsic IDs, and **two** are source
concat operations. The common matcher accepts `int512_t`; every actual matched
constant has at most **16 significant bits**. New constants exceeding their
stated source width or the common matcher width are rejected.

The relevant source is [MISAAL hexsemantics_new.py at 44ff](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/lib/sema/hexsemantics_new.py).
`hexagon_V6_interleave_2_128B` has arguments `(BV16, 16, 32)` and body
`(concat %arg0 %arg0)`. `hexagon_V6_interleave_4_128B` has arguments
`(BV8, 8, 32)` and body `(concat %arg0 %arg0 %arg0 %arg0)`.
The prepared helper requires those exact definitions and metadata. It does not
use the unrelated, copied 24-entry permutation metadata on those two entries.

The LLVM lowering requires exactly three arguments, an input `<1 x i16>` or
`<1 x i8>`, two matching i32 constant width annotations, and an output `<2 x
i16>` or `<4 x i8>`. It obtains an already-legalized child's value through the
common mapping accessor, bitcasts to an integer, zero-extends to i32, repeats
with shifts/or, and bitcasts to the exact original result type. Bad arity,
shape or widths fail explicitly. Repetition makes the result independent of
which repeated group is called the high or low group.

These types follow [RosetteLifter.py lines105–119,168,233](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/rosette-lifter/RosetteLifter.py#L105)
and [RoseLLVMCodeGen.py lines38–55,89–125](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/codegen/llvm/RoseLLVMCodeGen.py#L38):
bitvectors retain their fixed-vector types, opaque call operands retain source
arity, and ordinary integer annotations are i32. Shapes outside this reviewed
contract are unsupported and fail; they are not silently coerced.

## Selector preparation

New modules:

- `scripts/reproduction_prepare_misaal_hvx.py`: immutable guarded preparation,
  native library build, then original host generator builds/requests.
- `scripts/reproduction_misaal_hvx_lowering.py`: exact source contracts and
  private-copy generator repairs.
- `scripts/reproduction_prepare_misaal_cases.py`: narrowly adds target
  `hexagon`, preserving existing x86/ARM paths.

The original [RoseHexLegalizerGen.py](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/InstSelectors/hexagon/RoseHexLegalizerGen.py)
is copied under the attempt's `sources/hvx/`. Saved exact-context patches:

1. Add the two checked concat implementations; ordinary groups still use the
   original `Intrinsic::getDeclaration`, argument permutation and predicates.
   The new driver uses **MISAAL's actual frontend dictionary**, excluding only
   the two operations now handled explicitly. This restores the two ordinary
   shift intrinsics missing from the old checked-in generic selector.
2. Parse the source `0x`/`0b` constant prefixes with `int(..., 0)`. The original
   generator interpreted binary `0b1` as hexadecimal 177. All four actual
   binary literal spellings (`#b0`, `#b00`, `#b1`, `#b11`) have regressions.
3. Emit exact hexadecimal Boost `_cppi` literals instead of oversized C++
   decimal literals; normal intrinsic mapping remains unchanged.
4. Add the missing terminal `return false` in instruction selection.
5. Set **only** `HexLegalizationPass`'s new instance to `bitsimd=false`, using
   the shared reviewed helper. The common default and BitSIMD path stay intact.

Only generated `HexLegalizer.cpp` and original common `Legalizer.cpp` are
compiled; competing checked-in selector variants are not globbed into the
library. The output is **`libHVXLegalizer.so`**, matching the actual
[Halide frontend path/flag selection, misaal.cpp lines157–201](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/frontends/halide/src/misaal.cpp#L157).
LLVM12, Boost1.81, compiler/CMake and source identities are retained. Each step
uses `Preparation.step`: one build job, required memory guard, diagnostic
warning-pressure allowance, 10GiB disk floor, selector build limit1800s,
selector emission limit600s, per-generator compile/link limit120s. The API
never acquires a nested lock; the CLI acquires the shared heavy-job lock.

## Immutable receipt and optional wrapper contract

After successful native build **and** a nonempty real library output, the
preparer seals `selector-preparation.json` before emitting any requests:

```json
{
  "status": "success",
  "target": "hvx",
  "revision": "44ff893445d664cd87f52b08a138260ed2015ba8",
  "hydride_revision": "beb825327fc946d65032e96f7cde9acf3d24c13e",
  "legalizer_path": "<attempt>/legalizer-build/libHVXLegalizer.so",
  "legalizer_sha256": "<actual built bytes>",
  "input_hashes": {},
  "generated_sources": {},
  "prepared_sources": {},
  "lowering_contract": {},
  "steps": []
}
```

Empty mappings above are schema placeholders; real receipts populate actual
hashes and step paths. `lowering_contract.native_lowering_validation` explicitly
remains `pending actual canary`. The final outer `preparation.json` separately
indexes **every selected case**, with build failure evidence or a verified
request path. There is no receipt/request hash cycle.

Each HVX request binds `hvx_link_contract` with `mode: intrinsics-only`, the
**exact absent** original `LOW/wrappers/hvx_wrappers.ll` path, and the sealed
selector receipt path/SHA. Parent implemented the capture-side omission gate
separately. It must omit only this path from the original llvm-link invocation,
retain both original and actual argv, and execute real llvm-link, llvm-dis and
opt. No empty wrapper is written. All selected-result and final LLVM gates
remain required, including no residual `llvm.hydride.*` calls or direct
undefined/poison returns in the required functions.

The original wrapper is used only by
[RoseLowLevelCodeGen.py lines44–56](https://github.com/akothen/Hydride/blob/beb825327fc946d65032e96f7cde9acf3d24c13e/codegen-generator/tools/low-level-codegen/RoseLowLevelCodeGen.py#L44)
in `llvm-link original.ll wrapper -o linked.bc`. Omitting its exact nonexistent
argument is justified here because all ordinary output instructions are LLVM
intrinsics and the only two pseudo instructions have explicit IR lowering.
Actual native validation remains necessary.

## Original HVX graph-generation configuration

The inventoried target is `hexagon`; the compiler's environment spelling is
`hvx`. Requests retain the [original Makefile](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/benchmarks/hexagon/halide/Makefile#L74):
`HL_FORCE_HEXAGON_OPT=1`, enabled Hydride/MISAAL, **three** saturation iterations,
frontend patterns enabled, original output types and
`target=hexagon-32-noos-no_bounds_query-no_asserts-hvx_128-hvx_v66`.
The output basename is `<name>_hvx128`. Ordinary HVX recipes leave
`HL_EXPR_DEPTH`, `HL_SYNTH_BW`, and `HYDRIDE_INITIAL_HASH` unset; x86 defaults
are explicitly removed. Cold per-parent pattern-cache behavior is unchanged.

`fully_connected` keeps `output.type=uint8`, synthesis width16 and
`HYDRIDE_INITIAL_HASH=empty_hash`. Its Makefile exports `HL_EXPR_DEPTH` from
`EXPR_DEPTH`, but defines no default for that variable. Empty input reaches
[Rosette.cpp lines3569–3574](https://github.com/RafaeNoor/MISAAL/blob/44ff893445d664cd87f52b08a138260ed2015ba8/frontends/halide/src/Rosette.cpp#L3569),
which computes `0 - '0' = -48`. Parent approved explicit **`EXPR_DEPTH=2`**,
matching that source's unset default. This is recorded in
`request.configuration_variances`; it is not silently claimed as the original
empty-value invocation. Inventory source/configuration identities stay exact.

## Proposed first native preparation (not run)

Use the current verified x86 environment request from the continuation after
its legalizer repair. The earlier inliner-repair request remains the known
fallback path; it identifies the older x86 legalizer, while this preparation
builds a separate corrected HVX selector. Pass CMake explicitly: it is absent
from shell PATH. Pass Boost explicitly or let the HVX preparer derive it from
`seed.preparation`, not the relocated x86 legalizer directory.

```bash
.venv/bin/python -m scripts.reproduction_prepare_misaal_hvx \
  --output benchmarks/local/reproduction/prerequisites/misaal-hvx/<fresh-attempt> \
  --template-request <current-verified-x86-request.json> \
  --case misaal-hexagon-blur3x3 \
  --cmake /Users/saul/.cache/uv/archive-v0/WdkpDVz4tYcf_Bsl/lib/python3.14t/site-packages/cmake/data/bin/cmake \
  --boost-include benchmarks/local/reproduction/prerequisites/misaal-44ff/attempt-20260925T051740Z-ef4010cc/boost_1_81_0
```

The proposed CMake path was read from retained Halide `CMakeCache.txt`; it has
not been executed in this slice. Omit `--case` to prepare all39 inventoried
Hexagon generators (31 paper-required, eight artifact extras). This only builds
host generators; complete source optimization belongs to the coordinator.

## Validation completed here

- Exhaustive source-concat vs zero-extend/shift/or **model** comparison: all
  65,536 sixteen-bit inputs and256 eight-bit inputs.
- Exact source/arity/width drift rejection, terminal false/mode/shape guards,
  preserved normal mapping, 511-bit emitted literal and four binary literals.
- Mocked immutable preparation, ordinary intrinsic coverage, real-output
  existence checks, resource stop, missing LLVM intrinsic/library/selector,
  every selected-case accounting, original HVX request semantics and receipt
  tampering. These are **not** native LLVM correctness tests.
- Actual read-only input check against retained44ff/beb and installedLLVM12:
  114/310/308+2 counts above. No selector was generated from this full dictionary.
- Ruff, Mypy and CLI help pass. Focused tests include existing x86/ARM behavior.

Before admitting any HVX workload: guarded real build, tiny native lowering
fixtures covering concat2/4 values and invalid shapes, original blur3x3 parent
completion with every backend call accounted for, all final native LLVM gates,
and ordinary/strict replay of standalone exports must pass. A failed source
parent or residual pseudo instruction remains an explicit failure.
