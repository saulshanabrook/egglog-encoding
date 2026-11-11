# MISAAL HVX prerequisite recovery

Native prerequisite preparation completed on 2026-09-25: the real selector and
all 39 original host generators built under the guard. The exact concat
lowering passed 197,376 native LLVM value checks and 36 rejection checks; see
[misaal-hvx-concat-diagnostic.md](misaal-hvx-concat-diagnostic.md). Full source
optimization and ordinary replay remain separate gates; the first blur3x3 run
failed in native legalization after three backend calls. The portable semantic
repair described below has passed the actual LLVM fixture gates described at the end of this document. The full source canary is still a separate gate. No target program or simulator has run. MISAAL is pinned at
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
   The new driver uses **MISAAL's actual frontend dictionary**, excluding the concat and portable source groups now handled explicitly. This restores the two ordinary
   shift intrinsics missing from the old checked-in generic selector.
2. Parse the source `0x`/`0b` constant prefixes with `int(..., 0)`. The original
   generator interpreted binary `0b1` as hexadecimal 177. All four actual
   binary literal spellings (`#b0`, `#b00`, `#b1`, `#b11`) have regressions.
3. Emit exact hexadecimal Boost `_cppi` literals instead of oversized C++
   decimal literals; normal intrinsic mapping remains unchanged.
4. Add the missing terminal `return false` in instruction selection.
5. Set **only** `HexLegalizationPass`'s new instance to `bitsimd=false`, with explicit pass-local initialization. The common default and BitSIMD path stay intact.

Only generated `HexLegalizer.cpp` and a checked private copy of common
`Legalizer.cpp` are compiled; competing checked-in selector variants are not globbed into the
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
intrinsics and supported source pseudo instructions have explicit IR lowering.
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

## Repeating native preparation

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

This CMake path was read from retained Halide `CMakeCache.txt` and was used
for the successful native build. Omit `--case` to prepare all39 inventoried
Hexagon generators (31 paper-required, eight artifact extras). This only builds
host generators; complete source optimization belongs to the coordinator.

## Initial implementation validation

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
and ordinary replay of standalone exports must pass. Proof-mode validation is
outside this source-reproduction goal. A failed source
parent or residual pseudo instruction remains an explicit failure.

## Actual preparation evidence

The first attempt stopped on the upstream Python import of missing `toml`.
The isolated dependency continuation adds pinned `toml==0.10.2` without
modifying the original Python environment. Its request is
`benchmarks/local/reproduction/prerequisites/misaal-44ff/selector-python-attempt-0001/request.json`.

The successful second attempt is
`benchmarks/local/reproduction/prerequisites/misaal-hvx/attempt-0002/preparation.json`.
Its selector built in 6.5 seconds; all 80 serial generator compile/link steps
passed. The library SHA-256 is
`e8c7dd2eda2a070444c31bb1419c42110c95393ecc8e8377d1691865bbebe229`.
These are acquisition diagnostics, not performance observations or proof of
complete source optimization. The prepared requests were copied unchanged
into `prerequisites/misaal-all-targets-attempt-0001/requests`.


## Portable semantic repair after the first optimization canary

The opt-in deduplication canary `3b9f8d9f.../attempt-0001` reached three actual
Egglog calls. Its first native `opt` failed in ADCE after constructing
`llvm.hexagon.V6.vlsrw.128B(vector, <null operand!>)`. The parent was stopped
with retained manual-stop evidence after the required child failed. This is
not a source-complete result.

The updated preparer changes only private selector/common sources. Full-file
pins cover the active frontend, swizzle formal dictionary, original generator
and common implementation; additional group digests bind the exact formal
bodies and metadata used by the portable lowering. Saved patches, original
inputs and every private source hash are retained. Egglog input expressions,
patterns, schedules, costs, cache transitions and extraction are unchanged.

- **Full scalar shift:** source `vlsrw` has `(bvand RtV RtV)`, so shift counts
  at least32 produce zero. HVX itself masks the count to five bits, as shown in
  [Qualcomm's semantics](https://github.com/qemu/qemu/blob/v9.2.0/target/hexagon/imported/mmvec/ext.idef#L753-L760).
  The repair uses portable vector `lshr` by `RtV & 31`, then unsigned
  `RtV < 32 ? shifted : zero`. The mask avoids LLVM poison; the selection
  preserves the active formal for every 32-bit count. No Hydride formal is
  substituted. Exact arity, widths, result type and constant annotations gate
  this branch. The original missing scalar permutation is excluded from the
  ordinary selector generator.
- **Half extraction:** active `vassign` extracts low1024 bits of2048;
  active `lo` adds source offset1024 and extracts high1024. Their target
  metadata names the opposite half; LLVM's actual meanings are confirmed in
  [LLVM12's selection rules](https://github.com/llvm/llvm-project/blob/llvmorg-12.0.1/llvm/lib/Target/Hexagon/HexagonIntrinsicsV60.td#L21-L25).
  Portable fixed-vector shuffles implement the active formals, followed by
  the exact byte-vector result type. The mismatched ordinary groups are
  excluded, not aliased to the wrong names.
- **Swizzle:** only the four declared contexts of active `hvx_swizzle_1` are
  supported. Masks are derived from its formal bit offsets, checked for exact
  alignment/output size/bounds, and emitted as fixed LLVM shuffles. The
  observed1024-bit/16-bit context interleaves lanes `[0,32,1,33,...,31,63]`.
  Other names or parameter shapes remain explicitly unsupported.
- **Intrinsic safety:** the private common permutation routine validates
  arity, valid indices, uniqueness and complete destination coverage before
  inserting a cast. Mapped types must match exactly. The pass calls
  `verifyFunction` immediately after legalization and fails before any later
  ADCE pass if IR is invalid. This is an executed verifier call, not a log
  assertion or post-success audit. Other target families keep their sources.

Portable packing requires the little-endian layout used by this HVX path.
The remaining305 ordinary concrete intrinsic names retain original mapping.
No claim is made that their original semantics are independently verified.
The native residual-call audit and source-parent completion gates still apply.

The focused Python tests interpret the retained original formal bodies and
compare all shift boundaries, every swizzle lane and both distinguishable
halves. They also check source drift, private-copy identities, permutation
preflight placement and verifier placement. **These do not compile LLVM.**

After review, run the existing guarded preparer for only blur3x3 in a fresh
attempt. Before the full source canary, compile
`tests/fixtures/misaal-hvx/lowering-harness.cpp` with that attempt's
`generated/HexLegalizer.cpp` on the include path and its private
`sources/common/Legalizer.cpp` as the second translation unit. Use the same
LLVM12 includes/library, Boost1.81, one job and guard as preparation. A command
recipe (run through the shared bounded native runner, never concurrently):

```bash
/usr/bin/clang++ \
  $(/opt/homebrew/opt/llvm@12/bin/llvm-config --cxxflags) -std=c++14 \
  -I<attempt>/generated -I<attempt>/sources/common -I<boost-1.81> \
  tests/fixtures/misaal-hvx/lowering-harness.cpp \
  <attempt>/sources/common/Legalizer.cpp \
  $(/opt/homebrew/opt/llvm@12/bin/llvm-config --ldflags --link-shared --libs core analysis --system-libs) \
  -Wl,-rpath,/opt/homebrew/opt/llvm@12/lib -o <attempt>/lowering-harness
```

The harness invokes the actual generated pass and constant-folds its portable
LLVM output; it executes no HVX instruction or target program. Run `all` and
require its19 value/permutation checks. Run each rejection separately:
`missing`, `duplicate`, `negative`, `large`, `short`, `width`, `bad-swizzle`,
and `invalid-ir`. Require nonzero exit and the relevant `MISAAL` diagnostic.
For `invalid-ir`, additionally require the verifier failure and absence of
`ADCE_WOULD_START`. Merely failing compilation or crashing is not a passed
rejection. Preserve commands, hashes, logs and results as diagnostic evidence.
Only after these pass should the original guarded blur3x3 parent be retried
with fresh caches and the separately reviewed deduplication opt-in.


## Portable repair: actual LLVM fixture results

The immutable `benchmarks/local/reproduction/diagnostics/hvx-native-gate-0001/`
attempt built the repaired selector and original blur3x3 host generator. Its
first harness run exposed a test-harness issue: LLVM returned a constant bitcast,
which the harness inspected without first folding it using the module's data
layout. The two-line harness correction leaves the production lowering and
expected lane values unchanged.

`hvx-native-gate-0002/` compiled the corrected harness against that same sealed
selector. All **19 positive checks** and **eight intended rejections** passed
review of their actual exit statuses and diagnostics. The last rejection also
confirmed that invalid LLVM IR stops before ADCE. The automated continuation
receipt remains a failure because its diagnostic matcher expected `LLVM ERROR:`
at the start of a line; LLVM printed the prefix immediately after `i32`.
The original failure receipt was not changed. A separate hash-bound audit,
`hvx-native-gate-0002-audit.json`, and root review,
`hvx-native-gate-root-review.json`, record the accepted native fixture evidence.

These results establish the narrow lowering prerequisite. They do not establish
completion of the original optimizer or admit any HVX workload to the corpus.
The subsequent full blur3x3 parent must still finish every original child,
return valid LLVM, and pass ordinary standalone replay.

## Fresh combined-build native fixture gate

The clean combined preparation `de24509065a91a0011099031af73b866aad56a8f4ccd70149684696c620846b1/attempt-0001` passed the native fixture gate at `benchmarks/local/reproduction/diagnostics/hvx-fresh-gate-0001/attempt-0001`: 19 portable value/permutation checks and all eight expected rejections. The harness was compiled from this preparation's generated selector and private common sources, with pinned compiler/LLVM/Boost inputs. It does not cover every ordinary intrinsic or the concat handlers, execute a target device, or establish full source-parent completion. The original matcher failure remains historical evidence; the new matcher accepts only the exact observed invalid-IR prefix with its verifier context.

A separate safety audit found that native pattern synthesis launches Racket in a new process group. Earlier source-attempt RSS therefore measures only the initial group. A longer full-parent canary must wait for registered detached-group accounting and cleanup to pass real safety fixtures. Warming the pattern cache is not a transparent substitute: the source deliberately takes different cold, raw-abstraction, and abstract-load branches.
