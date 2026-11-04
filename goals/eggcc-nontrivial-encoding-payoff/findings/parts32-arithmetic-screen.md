# Parts32 attempt 2: arithmetic form survives the native screen

**Retain this family for encoding integration.** The arithmetic formulation passes unchanged U0's type analysis and extraction. Both the source and exact EggCC emission retain a redundant test inside the LLVM 18 O3 native loop. Folding only that branch removes the test and permits LLVM to vectorize the loop. This is an optimization opportunity, with no measured speedup or completed encoding integration.

This attempt has its own evidence root, [`parts32-arithmetic-screen/`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/). The earlier [direct-`Shr` attempt](parts32-screen.md), its typing failure and all its evidence remain unchanged. No compiler or engine source was edited in either attempt.

## Why the arithmetic replacement is exact

Let `B = 2^32` and `r = Low32(x) = x & (B-1)` for any signed i64 word `x`. Euclidean division gives

```text
x = q*B + r,  0 <= r < B,
-2^31 <= q <= 2^31-1.
```

Consequently `x-r = q*B` lies in `[-2^63, 2^63-2^32]`. The subtraction is representable even at both signed endpoints; wrapping subtraction therefore equals mathematical subtraction. Division by the positive constant `B` is exact, so truncation toward zero returns `q`. It cannot trigger the signed MIN / -1 overflow case. Thus

```text
High32(x) = (x-Low32(x))/4294967296
```

equals arithmetic right shift by 32 for every i64 word. At MIN the difference is MIN and the quotient is `-2147483648`; at MAX the difference is `9223372032559808512` and the quotient is `2147483647`. This formulation uses only `Bitand`, `Sub` and `Div`, all registered integer operators in U0's `type_analysis.egg:284–288`, with existing Bril bridges and wrapping interpreter semantics.

[`oracle.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/oracle.json) records this general bound argument, twelve boundary witnesses, and independent checks on 4,108 full-width words. The checker reads low/high halves from signed byte strings and compares that representation with exact integer subtraction and truncating division. It also exhaustively checks representability, exact divisibility, reconstruction and uniqueness over every signed `2w`-bit word for `w=1..8`. The mathematical bounds prove the full-domain claim; these finite checks validate the executable oracle and boundary behavior.

## Combined mechanism and actual source endpoint

The intended private theory uses marked unary `Parts32` with the justified representation identity `Parts32(x)=Pair(Low32(x),High32(x))`. On the source path `x!=y` and `Low32(x)=Low32(y)`:

```text
x != y
  => Parts32(x) != Parts32(y)       marked forward disequality
  => Pair(Low32(x),High32(x)) != Pair(Low32(y),High32(y))
                                    representation identities
  => High32(x) != High32(y)         reverse congruence, equal low sibling
```

`Pair` itself need not be marked. The equal low sibling is a dynamic source equality, and the original word disequality is a separate source constraint. The prospective compiler consumer is a false predicate for the exact final `If`, followed by EggCC's existing false-`If` elimination. This is neither a primitive-field conflict detector nor a `NoAlias` example.

[`source.bril`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/source.bril) implements that nested path in a hot loop over full signed i64 words. It first tests word equality, then low-half equality, then high-half equality. The impossible final true arm contributes `99`, the expected false arm contributes `7`, equal words contribute `5`, and unequal low halves contribute `3`. Each iteration updates `x` by `2^32+1` and `y` by `2*2^32+1`, with wrapping arithmetic. There are no bounds assumptions on the words; only the iteration count is guarded to `[0,1,000,000]`.

The exact [`manual.diff`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/manual.diff) replaces only the final `br target .unexpected .expected` with `jmp .expected`. The two earlier conditions, arithmetic partition, updates and loop remain unchanged in the input comparator.

## What the backend retains

All positive arms use the admitted original-dependency U0 compiler `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, the same copied Tiger/runtime, and LLVM 18. Source, exact U0 emission and manual comparator are lowered independently with `--optimize-egglog false --optimize-bril-llvm O3_O3`.

LLVM simplifies the arithmetic high calculation and its equality comparison into a test on `x xor y`: the high halves are equal exactly when that unsigned XOR is less than `2^32`. It retains that test and the `99`/`7` selection inside the scalar loop, despite the path's unequal-word and equal-low constraints. The manual fold removes the target and LLVM vectorizes the remaining loop. The actual native `main` entry, as well as exported `_main`, has this scalar-versus-vectorized difference. This is a code-shape observation, not a performance result.

[`inspection.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/inspection.json) records the exact functions, score presence, vector operations and hashes. Full LLVM, native disassembly, compact functions and direct diffs are retained beside each executable. The three post-schedule U0 graphs have 19,496, 19,794 and 18,361 nodes. Their high-half `Div` applications and target equalities remain present; the inspection records matching graph-local rows. This establishes an actual endpoint, while its private-theory translation and causal controls remain unimplemented.

## Positive and negative output controls

All 78 captured compiler/native/disassembly commands exit zero, with no timeouts. The eleven positive input rows run in source, exact emission and manual native arms: 33 exact output checks. They include MIN/MAX, negative words, wrapping updates, equal words, equal/unequal lows, zero/one/1,024 iterations, and an invalid iteration count. All three Bril interpretations give `56\n` on header arguments `(0,4294967296,8)`. [`native-results.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/native-results.json) retains the matrix.

Five weakened-premise programs are separately interpreted and lowered in both source and U0-emitted arms. Each actually prints `99`; incorrectly applying the fold would print `7`:

| Missing or incompatible premise | One-iteration input `(x,y)` | Why the target can be equal |
| --- | --- | --- |
| Original word disequality absent | `(0,0)` | Both words and both parts are equal. |
| Equal-low requirement absent | `(0,1)` | Unequal low halves account for the word difference; highs both zero. |
| Low mask narrowed to 31 bits, divisor still `2^32` | `(0,2^31)` | The incomplete partition loses bit 31; truncating division returns zero. |
| Divisor widened to `2^33`, low mask still 32 bits | `(0,2^32)` | The high quotient loses bit 32; both quotients are zero. |
| High divisors differ, `2^32` and `2^16` | `(2^48,2^32)` | Both lows are zero; both observed high values are 65536. |

[`negative-results.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/negative-results.json) retains these ten direct native executions. The width examples reject mismatched or incomplete partitions. A different correctly matched power-of-two partition can itself be lossless; the negative result is not a claim that every width other than 32 is invalid.

## Remaining acceptance work

No generic encoding was run in this screen. The next experiment must translate the exact local word, low and high expressions into a private theory, import the justified `Parts32` representation identities, seed the two source path facts, and query the high-half disequality. It must then export a false predicate only at the matching target scope and run actual extraction/native replay. Component facts must not escape into parent or sibling contexts.

Require marked-`Parts32` removal/rescue, representation-identity removal/rescue, equal-low removal, original-disequality removal, query/consumer knockout, primitive-null and faithful manual controls, and the incompatible-parameter/scope negatives. A specialized complete rule for this partition is a fair manual comparison; this screen makes no claim of unique logical expressiveness. Only a working encoding integration and measured comparison could satisfy the goal's payoff requirement.

[`run.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/run.py) records the oracle, exact source generation and bounded procedure. It uses 180-second compiler bounds, 30-second native bounds, one Rayon thread and the admitted LLVM 18/U0 environment. Each captured command records argv, cwd, environment, file/executable hashes, streams, numeric exit and timeout. Diagnostic elapsed times are not performance observations. [`identities.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/identities.json) binds the reused tools/runtime/binaries and input bytes; [`inspect.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-arithmetic-screen/inspect.py) regenerates the derived inspection. Existing captures refuse overwrite.

No compiler or engine source, manifest, build, broad test suite, timing campaign or attempt-1 artifact was changed. U0 remains clean.
