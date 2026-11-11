# SpEQ PolyBench GEMM frontend gaps

The original C is available, and the native LLVM frontend has been exercised. The remaining failures are in REV/FIR construction and application recognition; installing x86 Docker does not by itself repair them. No replacement `.egg` or reference program is admitted.

The standard SCALAR_LB pipeline exposes three concrete issues:

1. REV prints the latch comparison operand as the exclusive loop end. In the retained do-before-test loops, the true ends are 1100, 1200, and 1000, while the comparisons use 1099, 1199, and 999. The same operand also enters `makeLevelBounds`, so changing printed ranges alone is insufficient.
2. Parent loops whose writes occur in child loops emit empty memory results. A correct summary must compose completed child states with direct stores and conditional merges, in order. Every parent needs a fresh result name; reusing a child name collides with the parser's result table.
3. The apparent scalar-plus-memory result includes a pure `zext` of the outer loop index, exported through LCSSA. This particular value can potentially be represented as a captured invariant expression, preserving its definition and uses. It is not a mutable scalar recurrence. Genuine mixed scalar/memory state would require a coordinated FIR language extension.

A bounded repair could share exact SCEV trip-count normalization for supported positive unit-step loops, compose single-array memory states bottom-up, and preserve proven pure invariant projections outside fold state. This is a proposal, not implemented behavior. It needs real LLVM tests for current/next-IV comparisons, zero-trip guards, overflow, nested/conditional stores, fresh result names, and scalar closure. Original C, active passes, references, rules and the 5/1/3 schedule must remain intact.

Even a correct complete FIR is not yet evidence of GEMM recognition. SCALAR_LB removes positivity guards that remain in the original symbolic GEMM reference; active rules do not fold constant comparisons or eliminate those guards. The C99 lane retains that control-flow shape but separately needs dominating SSA closure, chained-GEP lowering and memory typing. Do not add artificial guards or substitute references to force a match. The no-GVN run is only a diagnostic and is not the original pipeline.

## Retained evidence

- Original `polybench_gemm` C SHA-256: `e0fc07f40f59e83fc57f1d4e1e99f1718ffce106dcdc44c3e30ed88848228aea`.
- Standard SCALAR_LB `analysis.ll` SHA-256: `d4d52a78d85325724a444b4b55b4520ce3fa13f739cf151596a1c9a8562c0230`, under `benchmarks/local/reproduction/stages/speq-polybench_gemm/complete/4e89ad7ea7a0f8316f7bbf89d6e8815cd74278638d04922dd250575c45b54a89/attempt-0001/capture/speq/speq-polybench_gemm/source/frontend/`.
- No-GVN diagnostic `benchmarks/local/reproduction/speq-scalar-no-gvn/probe.stderr.log` SHA-256: `f54443c9b9ab105041f71f7d74bcb0d4e3d4cfaa80e981d9fb3f36d00aca3666`.
- Original frontend: `benchmarks/local/sources/speq/lleq/llvm/lib/Analysis/REVPass.cpp`, especially `makeLevelBounds`, `translateLoopBody`, `findLiveOut`, and loop-range emission.
- Original parser: `benchmarks/local/sources/speq/artifact/parseIR.py`, especially `Fold`, `Abstraction`, `MkFold.top`, and `ToEggAbstract`.
- LLVM's loop-bound interpretation is documented in the [LLVM 17 source](https://raw.githubusercontent.com/llvm/llvm-project/llvmorg-17.0.6/llvm/lib/Analysis/LoopInfo.cpp).

The independently validated PHI-polarity repair is a separate, smaller change. Its [diagnostic and acquisition opt-in](speq-phi-repair.md) do not resolve these PolyBench gaps. No author message was sent.
