# Pack32: a distinct surviving native opportunity

**Retain this family for an encoding integration.** Untouched EggCC and LLVM 18 O3 both retain a redundant comparison inside a loop over changing packed fields. Folding only that comparison removes a compare/select pair from the executed native loop. The source, exact EggCC emission, and manual fold agree on every checked output. This is a prospective optimization, with no measured speedup, compiler bug, or completed encoding integration.

The retained evidence is [`pack32-screen/`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/). This is a synthetic packed-key classification loop derived from the [ranked packing hypothesis](fresh-source-hypotheses.md), not an existing production benchmark.

## The mathematical producer and consumer

For `0 <= a,b < 2^32`, define `P32(a,b)` as the signed i64 word whose bit pattern is the concatenation of the two 32-bit fields. The source computes it with existing Bril operations:

```text
high = a * 4294967296
packed = high + b                 both operations wrap at 64 bits
```

The 64-bit unsigned pattern uniquely decodes into its high and low halves. Signed interpretation changes neither the bits nor equality, so `P32` is jointly injective on this domain. General binary `Add`, `Mul`, or unrestricted packing is not injective.

[`source.bril`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/source.bril) explicitly guards all four initial fields `a,b,c,d` to `[0,2^32)`, and bounds the iteration count `n` to `[0,1,000,000]`. Each iteration updates `(a,c)` by `+1` and `(b,d)` by `+3`, masking each result with `0xffffffff`. Thus every iteration preserves the field domain while the comparisons remain dynamic. These masks maintain bounds; they supply no disequality seed.

The nested path is:

```text
P32(a,b) = P32(c,d)              first true Eq branch
  => a=c and b=d                marked binary cancellation

P32(c,a) != P32(a,b)             second false Eq branch
  => a!=b                       reverse congruence, using c=a
  => c!=d                       transport through both cancellation equalities
  => c+7 != d+7                 marked fixed translation
```

The last predicate is tested by an actual source branch. Its impossible true arm adds `99` to the sum; its false arm adds `7`. Other paths add `5` when the second packed comparison is equal and `3` when the first comparison is unequal. Invalid inputs print `-2`.

The prospective compiler consumer is a false predicate for the exact final `If`, followed by EggCC's existing false-`If` elimination in `interval_analysis.egg`. The manual comparator changes only `br target .unexpected .expected` to `jmp .expected`; [`manual.diff`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/manual.diff) retains that exact one-line fold. It leaves both packed comparisons, the loop, field updates and every other branch unchanged.

This differs from the earlier same-mask and alias workloads. A lossless **binary** representation supplies two component equalities, and the second packed disequality consumes an equal sibling established by that cancellation. It uses no `NoAlias` fact or memory operation. The dynamic fields would be equality-sort values in the private theory; comparing primitive width or mask metadata cannot establish their component equalities or disequalities.

## Independent oracle and semantic negatives

[`oracle.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/oracle.json) was written before compiler execution. It compares wrapping multiplication/addition with independent byte concatenation and decodes the resulting signed bytes back into the original fields. It checks 4,177 full-width pairs, including signed-word and half-word boundaries and fixed-seed samples. An additional exhaustive bit-string decode covers every pair for field widths 1 through 8. This finite evidence accompanies the general decoding argument; it is not an exhaustive 32-bit search.

The oracle also retains concrete counterexamples to weakened laws:

| Missing premise | Counterexample |
| --- | --- |
| High-field upper bound | `P32(2^32,0) = P32(0,0) = 0`, with different fields. |
| Low-field upper bound | `P32(0,2^32) = P32(1,0)`, with different fields. |
| Identical widths | `P32(0,65536) = P16(1,0) = 65536`, with different fields satisfying each constructor's own domain. |
| Equal sibling for reverse disequality | `P32(0,0) != P32(0,1)` permits equal high fields; `P32(0,0) != P32(1,0)` permits equal low fields. Neither child disequality follows from the parent difference alone. |

The initial oracle's separate different-width row used a high field outside the 16-bit domain. [`oracle-correction.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/oracle-correction.json) records the corrected, independently byte-checked row above; the initial JSON and driver remain preserved. The executed different-width native fixture below already satisfied both domains and is unchanged.

Three executable negative fixtures weaken the source assumptions independently. Their exact source and EggCC-emitted programs are interpreted and executed natively:

| Negative fixture | Arguments `(a,b,c,d,n)` | Actual source and emitted native result | Result if the final branch were incorrectly folded |
| --- | --- | --- | --- |
| Missing `a < 2^32` guard | `(4294967296,0,0,0,1)` | `99` | `7` |
| First comparison uses a 16-bit second packing width | `(0,65537,1,1,1)` | `99` | `7` |
| First packed-key equality is absent; both fields in the later pair are unresolved | `(1,0,0,0,1)` | `99` | `7` |

These are valid i64 programs and counterexamples to applying the proposed optimization outside its admitted fragment. They are not compiler bugs. [`negative-results.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/negative-results.json) records all six direct native executions and the oracle's invalid-fold prediction.

## What survives the actual backend

The three positive arms use the same admitted U0 compiler at `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, copied Tiger, runtime and LLVM 18. Each lowers with `--optimize-egglog false --optimize-bril-llvm O3_O3`; the optimized arm lowers the exact emitted Bril without another EggCC optimization.

Both the source and EggCC-emitted LLVM retain `icmp eq c,d` and `select ...,99,7` inside the loop after the two packed comparisons. LLVM removes the common `+7` itself, but does not prove the remaining component inequality. The actual ARM64 entry loop still executes that extra `cmp` and `csel`. The manual fold removes them; its remaining packed-key results are selected without the impossible `99` case. The comparison is evaluated within the loop, rather than being hoisted into an entry check. Compact functions, full LLVM, native disassembly and direct diffs are retained beside each executable.

[`inspection.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/inspection.json) records five versus four i64 equality comparisons in each LLVM function, with the impossible score present only in source/U0 emission. These structural counts do not predict a speedup. The final serialized graph also retains the source mechanism: packed applications for three dynamic field pairs and the translated target `Eq` in class `Expr-399`. Its two `Eq` rows compare the translated operands in opposite orders. Graph IDs are snapshot-local and must be rediscovered during integration.

All 64 captured compiler/native/disassembly commands exit zero, with no timeouts. The positive matrix has eleven argument rows in each of three native arms: 33 exact output checks. It includes equal/different keys, equal fields, signed packed words, 32-bit field wraparound, zero/one/1,024 iterations, and invalid input bounds. Six additional native runs cover the three negative fixtures. Source, manual and exact emission all interpret to `56\n` for header arguments `(1,2,1,2,8)`; each negative source/emission interprets to `99\n`. [`native-results.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/native-results.json) retains the positive matrix.

[`run.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/run.py) records the exact source generation and execution procedure. It uses 180-second compiler and 30-second native bounds, one Rayon thread, the LLVM 18 environment and U0 runtime. Each command has argv, cwd, environment, input/executable hashes, stdout, stderr, numeric exit and elapsed time. The durations are diagnostic, not performance observations. [`identities.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/identities.json) binds the compiler, Tiger, runtime, tools and input bytes. The driver refuses to overwrite existing captures. [`inspect.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/pack32-screen/inspect.py) regenerates derived inspection artifacts.

## Remaining acceptance work

The screen supports pursuing the family. It does not yet prove that a generic encoding integration reaches the endpoint. Such an integration must recognize bounded `P32` applications, materialize their semantic wrappers, localize the first equality and later disequality into the exact target scope, and preserve the current loop's domain invariant. It must use a private graph and export only the checked target predicate; the contextual component equalities must not be unioned globally in EggCC.

Require cancellation knockout/rescue, reverse-query and marked-translation controls, a primitive-null comparator on the same graph/seeds, crossed-scope and missing-domain negatives, and actual extraction/native replay. LLVM's independent translation cancellation means the benefit must be attributed to the packed-component reasoning rather than a claim that LLVM needs help canceling `+7`. A larger faithful manual packing rule remains a fair comparison. Only after integration and those controls would measured compilation/runtime evidence be meaningful.

No compiler or engine source, manifest, build, broad test suite or timing campaign was changed or run. No source-fixture revision was needed to obtain the surviving native difference.
