# Parts32: closed at the direct-shift IR gate

**Close this direct-`Shr` workload under unchanged U0.** The partition law is sound, and both source and manual Bril interpretation succeed. U0 optimization fails before extraction because the two `Shr` results have no inferred type. Consequently this screen establishes no emitted/native comparison, optimization opportunity, measured speedup or encoding payoff.

The evidence root is [`parts32-screen/`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/). No compiler or engine source was edited to bypass this gate.

## Proposed combined mechanism

For every signed i64 word `x`, let `Low32(x)` be the unsigned low 32 bits and `High32(x)` the arithmetic right shift by 32. The low half and signed high half reconstruct the original word uniquely, so `Parts32(x) = Pair(Low32(x), High32(x))` is injective over all i64 bit patterns.

On the feasible source path `x != y` and `Low32(x) = Low32(y)`, the intended private theory would use:

```text
x != y
  => Parts32(x) != Parts32(y)       marked unary forward disequality
  => Pair(Low32(x), High32(x)) != Pair(Low32(y), High32(y))
                                    imported representation identities
  => High32(x) != High32(y)         reverse congruence, equal low sibling
```

`Pair` need not be marked injective for the last implication. The source uses an actual nested branch comparing the high halves; its impossible true arm contributes `99`, while the expected arm contributes `7`. Other paths contribute `5` for equal words and `3` for unequal low halves.

[`source.bril`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/source.bril) loops over full signed words, updating `x` by `2^32+1` and `y` by `2*2^32+1` with wrapping addition. Only the iteration count is bounded, to `[0,1,000,000]`. All shifts are fixed valid amounts. The exact [`manual.diff`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/manual.diff) replaces only the final conditional branch with the expected arm.

## Independent oracle and retained negatives

[`oracle.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/oracle.json) was written before compiler execution. It independently splits signed eight-byte words into a signed four-byte high half and unsigned four-byte low half, reconstructs the original bytes, and compares the result with a sign-extension model of the shift. It checks 4,107 full-width words, including signed boundaries and fixed-seed samples, plus 2,048 deliberately equal-low word pairs. Exhaustive reconstruction and uniqueness checks cover all signed `2w`-bit words for `w=1..8`.

The mathematical reconstruction is the general argument. These finite checks exercise its implementation and the loop oracle; they do not exhaust all i64 words or constitute execution of the generic encoding.

All four negative fixtures are preserved but **were not compiler-executed**, because the positive program failed the earlier extraction gate:

| Missing or wrong premise | Counterexample | Oracle result at the target | Invalid manual fold |
| --- | --- | --- | --- |
| No `x != y` requirement | `x=y=0` | Equal highs: `99`. | `7` |
| High shift 33 with low width 32 | `x=0`, `y=2^32` | Low and observed high parts both equal: `99`. Bit 32 is lost. | `7` |
| Different high widths, 32 and 16 | `x=2^48`, `y=2^32` | Both lows are zero and both observed highs are 65536: `99`. | `7` |
| No equal-low requirement | `x=0`, `y=1` | Words differ but highs equal: `99`. | `7` |

Each source fixture uses one iteration and records its oracle-only status. The first and last negatives show that both path facts are required. The width negatives reject importing a lossless common representation for incompatible or incomplete partitions.

## Reproduced U0 failure

U0 is the admitted original-dependency compiler at `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, binary SHA-256 `d86869982413d4561cf713cc769c96eb1c9bfefe46fa459a2692c53a7aa93cf0`. The executed commands are captured in `commands/` with argv, cwd, environment, input/executable hashes, stdout, stderr, numeric exits and timeouts:

| Command | Result |
| --- | --- |
| Source `parse --interp` | Exit 0, original/result `56\n`. |
| Manual `parse --interp` | Exit 0, original/result `56\n`. |
| Source `optimize`, with context | Exit 101 after 0.16 seconds; no successful emission or run-data JSON. |

The optimizer's error is:

```text
function body eclass has no HasType — tiger cannot regionalize
function "main" body eclass Expr-720
```

[`failure-inspection.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/failure-inspection.json) and the copied [`tiger-crash.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/tiger-crash.json.gz) preserve the exact failed graph. Both `Shr` rows, `Expr-371` and `Expr-373`, have typed operands but no `HasType` result. The function body is also untyped. The crash graph has 12,330 nodes and SHA-256 `4ef55b6fee079bc59d165793776d04023c30dafb2534f5070e5bcc056d2bea7d`.

Current source explains the gap:

- The Bril bridge accepts `ValueOps::Shr` in `src/rvsdg/to_dag.rs:239` and emits it in `from_dag.rs:163`.
- `dag_in_context/src/interpreter.rs:262` implements signed i64 right shift. The fixed shift 32 is valid.
- `type_analysis.egg:283–310` assigns ordinary integer binary-result types through its `bop-of-type` table. It includes arithmetic and `Bitand`, while omitting `Shr` and `Shl`. There is no other `Shr` typing rule in that file. The failed graph demonstrates the resulting missing types in this workload.

This is an adjacent compiler support defect exposed by ordinary baseline execution. The generic encoding did not diagnose it, so it does not satisfy the goal's nontrivial encoding-bug requirement. No repair, localization patch or broader claim about shift support was attempted.

## Disposition and limits

The screen stops at this concrete IR gate, as requested. It does not claim that LLVM proves the target, that the Parts32 law is unsound, or that all equivalent source formulations are ruled out. In particular, native code and all negative compiler executions remain untested. A future separately admitted formulation could express arithmetic high bits using exact supported arithmetic; that is an unexecuted follow-up, not evidence from this screen.

[`run.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/run.py) retains the planned bounded procedure and stops on the failed positive optimizer invocation. [`inspect-failure.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/inspect-failure.py) preserves the crash and derives its typing diagnosis. Source identities are in `failure-inspection.json`; binary/runtime/tool/input identities are in [`identities.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-screen/identities.json). There were three captured compiler commands, two successes, one explicit optimizer failure, zero timeouts and zero native runs. No build, broad test suite, timing campaign, compiler/engine edit or encoding experiment was performed. U0 remains unchanged.
