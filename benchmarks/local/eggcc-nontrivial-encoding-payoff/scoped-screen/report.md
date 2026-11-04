# Scoped cancellation and same-mask native screens

The same-mask family survives the native endpoint screen. Untouched EggCC and LLVM 18 at `O3_O3` retain a redundant equality test; manually removing precisely that branch removes three arm64 instructions in each emitted entry function. This is an optimization opportunity, not a measured speedup. No encoding integration was implemented and no compiler bug was found.

The separate cancellation family fails the generated-runtime screen: LLVM already removes the target equality. Untouched EggCC's Bril still contains it, but the baseline and manually folded native entry functions have identical disassembly. No revision of either source fixture was needed.

## Exact source and compiler

The untouched source is `/private/tmp/eggcc-nontrivial-encoding-payoff-u0` at EggCC `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, the newly admitted remote main. Its source manifest and copy provenance are in `../admission/manifest.json` and `../admission/source-files.json`. All copied compiler/runtime hashes were independently checked against that manifest; [admission-verification.json](admission-verification.json) records the check.

| Artifact | SHA-256 |
| --- | --- |
| Compiler | `d86869982413d4561cf713cc769c96eb1c9bfefe46fa459a2692c53a7aa93cf0` |
| Paired Tiger | `130eaba8bb575e196b8e18898826356269efe6e28a56b9d3690ef42647d3b201` |
| Cancellation source | `caae5e8941c3808f3298106a50deac3f202e75148f06d0642049a52ffbbdd7af` |
| Cancellation manual | `6543f0011b7569ecb622fc2b241a05aca623a8d86639811fbf7cba160b1628e9` |
| Cancellation negative | `cf872487facd9c7f3f5107d987462493056d16b623f585d8e0c11807899a6a02` |
| Same-mask source | `f02b4d342c7cff6337d099ede37d6ad413ceaffdf0f871d2d88264d0f0e61d4b` |
| Same-mask manual | `b32037e39cb8d64287149388fa1292b7aa9863afe3b47fb4ecd4b2b89af5bf57` |
| Same-mask negative | `f41616c3c4c8940634ac0eb12d6953c3e0ab510b550357cc3e03dcbbb9184a00` |

The ordinary `tests/passing/small/add.bril` canary prints exactly `3\n` in source interpretation, optimized interpretation and direct generated-program execution. CLI help was recorded. The driver uses the relocated U0 for every compiler cwd and `EGGCC_ROOT`; the nested abandoned source root was not used for these runs.

## Cancellation: the backend already proves the fact

The source has three nested conditions:

```text
(x + 1) = (y + 1)
x != z
target: (y + 7) = (z + 7)
```

All arithmetic is wrapping i64 arithmetic. Addition by a fixed word is a bijection, including at wrapping boundaries. Therefore the first condition implies `x=y`; together with `x!=z`, this implies `y!=z`, then `(y+7)!=(z+7)`. The target's true branch prints 99 but is infeasible. Its false branch prints 7. The other source paths print 5 or 3.

[source.bril](cancellation/source.bril) and [manual.bril](cancellation/manual.bril) differ only by changing `br target .unexpected .expected` into `jmp .expected`; [manual.patch](cancellation/manual.patch) preserves the exact difference. Untouched EggCC retains the target and 99 arm in [optimized.bril](cancellation/optimized.bril). LLVM removes them from both original and optimized lowering. Both then compute only `x==y` and `x==z` and select among 3, 5 and 7.

The baseline and manual [entry disassemblies](cancellation/optimized-native/main.asm) are byte-for-byte equal, with SHA-256 `2fb544c6fdb3f6a58b66fbd26ddca53859f25f0e7264f057d53472987e134e73`. This closes this fixture's generated-runtime payoff lead. It does not prove a global limit on cancellation or establish any compile-time result.

Six direct-native cases cover two feasible positive paths, equality and outer-false controls, and wrapping boundaries. Each was run against the source, exact EggCC emission and manually folded source: all 18 executions match the independent wrapped-integer evaluator in [run.py](run.py). [native-results.json](cancellation/native-results.json) contains every argument and exact output.

The nearby negative changes the outer comparison to `(x+1)=(y+2)`. At `x=1,y=0,z=0`, that equality holds, `x!=z` holds, and the target is true, producing `99\n`. Source and optimized interpretation and both direct-native paths retain that result. A cancellation rule must require the same translation constant.

## Same mask: a native opportunity remains

Here `m` is a dynamic common argument rather than a fixed primitive observation:

```text
(x & m) != (y & m)
target: (x + 7) = (y + 7)
```

Ordinary congruence gives `x=y => (x&m)=(y&m)`. Its contrapositive yields `x!=y` from the false outer equality; injectivity of the common fixed translation then gives `(x+7)!=(y+7)`. No claim that bit-and is injective is needed. A primitive comparison among masks or translation constants cannot determine this relationship between the dynamic `x` and `y` values.

[source.bril](same-mask/source.bril) and [manual.bril](same-mask/manual.bril) again differ only at the target branch. EggCC retains both shifted arguments, their equality and the infeasible 99 arm in [optimized.bril](same-mask/optimized.bril).

LLVM cancels the two additions, but retains a test of `x==y` and a select between 99 and 7 under the outer masked comparison. The resulting baseline core is:

```llvm
%0 = xor i64 %y, %x
%1 = and i64 %0, %m
%outer = icmp eq i64 %1, 0
%target = icmp eq i64 %x, %y
%inner = select i1 %target, i64 99, i64 7
%result = select i1 %outer, i64 3, i64 %inner
```

The manual core has only the xor, and, outer comparison, and select between 3 and 7. Final native disassembly confirms this difference in both `__main` and the inlined C argument wrapper `_main`: the baseline additionally materializes 99, compares the dynamic arguments, and selects the inner result. See [baseline entry disassembly](same-mask/optimized-native/main.asm), [manual entry disassembly](same-mask/manual-native/main.asm) and their `main.ll` siblings. Entry assembly hashes are respectively `423e23631becf38f37475e82336a33826cd5aa377b754f0c2e62b4b549c4e279` and `2962ce3959f43b2bab8134da32267795495da200883acc8c8f838310af2c0152`.

Six direct-native cases cover two positive paths, equal-value and equal-masked-value controls, and two wrapping-boundary cases. All 18 source/emitted/manual executions match the independent expected outputs in [native-results.json](same-mask/native-results.json).

The negative uses different masks: `(x&m)!=(y&n)`. At `x=y=1,m=1,n=0`, the outer disequality holds while the translated children are equal, so the target correctly prints `99\n`. Source and optimized interpretation and both direct-native paths agree. Reverse congruence must require a common canonical mask sibling.

## Reproduction and interpretation limits

[run.py](run.py) records every argv, cwd, relevant environment field, timeout, exit code and stdout/stderr hash under `commands/`. Compiler and lowering calls have a 180-second timeout; direct native calls and disassembly have a 30-second timeout. Lowering uses `--optimize-egglog false --optimize-bril-llvm O3_O3`, the same admitted runtime and LLVM 18 for every variant. `RAYON_NUM_THREADS=1`; the memory guard is absent. The fixture's `# ARGS:` controls the selected interpreter witness; native matrix rows pass explicit arguments.

The retained sequence was `run.py canary`, `run.py cancellation`, `run.py same-mask`, then `run.py negative cancellation` and `run.py negative same-mask`, followed by native disassembly. The driver deliberately refuses to overwrite command directories; a replay needs a fresh output root. It records 81 subprocess commands, including the preserved first adapter attempt. That attempt incorrectly treated `--interp` stdout (`7\n`) as Bril and received a parse error. The corrected path emits Bril in a separate command without `--interp`; this was a harness error, not a compiler finding.

Interpreter agreement was checked using present `original_interpreted` and `result_interpreted` strings. Uninterpreted emission/lowering JSON nulls were never counted as output agreement. Graph dumps, exact emitted Bril, full LLVM and native binaries remain under the respective family directories. [summary.json](summary.json) records the dispositions and exact native matrix; [files.json](files.json) hashes the retained evidence.

There are no runtime measurements here. Process durations are command diagnostics only. These tiny print-dominated fixtures establish whether a native endpoint difference exists; a surviving result still needs actual encoding integration, its causal controls, and a bounded hot workload before any speedup claim. Neither screen exercises the generic encoding itself.
