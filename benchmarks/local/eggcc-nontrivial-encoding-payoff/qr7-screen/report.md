# QR7: early forwarding survives as a native phase-ordering opportunity

**Retain the early-forwarding hypothesis for a bounded encoding integration.** Untouched EggCC retains the load, and forwarding it earlier changes the executed native program from a vectorized sum loop to a closed arithmetic sum. A six-pair manual pilot measured 3.158 ms versus 1.855 ms median process wall time at ten million iterations. No encoding was implemented, so this is manual opportunity sizing, not an encoding speedup or a completed goal result.

The direct prediction that the executed native program would retain the memory load was falsified. LLVM forwards it after inlining into C `main`, but leaves a vectorized reduction loop. The exported Bril `_main` still has the memory loop; reporting that exported function as the actual executed entry would be misleading. [entry-inspection.json](entry-inspection.json), the compact LLVM and assembly sections, and their diffs retain the distinction.

## Workload, mathematical law, and exact manual change

[source.bril](source.bril) takes dynamic `x`, `y`, and `n`. It first requires `0 <= x,y < 64` and `0 <= n <= 10,000,000`, then enters nested true branches for equal quotients and equal remainders:

```text
qx = x / 7;       qy = y / 7;
if qx == qy:
    rx = x - 7*qx;    ry = y - 7*qy;
    if rx == ry:
        allocate p[64]; pi = p+x; pj = p+y;
        *pj = -3;
        for count = 0 .. n-1:
            *pi = count;
            value = *pj;
            sum += value;
        free p;
        print sum;
```

For truncating division by fixed positive 7, `x = 7*qx + rx`. Thus equal ordered pairs `(qx,rx)=(qy,ry)` imply `x=y`. The multiplication and remainder stay representable for this divisor even on the full signed-i64 domain; the actual workload uses nonnegative bounded indices. Both local pointers designate the same in-bounds cell in one live allocation. There are no intervening calls or frees. Therefore each load reads `count`, and the expected sum is `n(n-1)/2` without overflow under the guard.

[manual.bril](manual.bril) differs by exactly one instruction ([manual.diff](manual.diff)):

```diff
-  value: int = load pj;
+  value: int = id count;
```

The initial sentinel store remains in both inputs. It makes all negative variants valid initialized-memory programs when the weakened conditions allow `x!=y`.

The proposed generic route is `K7(v)=Pair(Q7(v),R7(v))` in a private value graph. Equality of both components gives equal `K7` outputs by congruence; marked `K7` cancellation gives `x=y`; pointer congruence then exposes the actual existing same-address store-forward rule in `dag_in_context/src/optimizations/mem_simple.egg:107`. `Q7` and `R7` individually remain unmarked. This uses symbolic equality-sort children and a lossless two-component key. It differs from same-mask reverse disequality and the earlier `NoAlias` commute case. Disequality is not necessary to this minimal route.

## Correctness and negative boundaries

[oracle.py](oracle.py) uses independent exact-integer truncating division, rather than the optimizer's rewrites. [oracle-results.json](oracle-results.json) records the reconstruction proof, signed MIN/MAX and 10,000 seeded full-width samples, and exhaustive injectivity checks for all 4,096 pairs in the workload's `[0,64)` domain. Sampling is not an exhaustive proof over i64.

Four positive arms were checked: source, exact U0 emission, one-line manual input, and that manual input optimized through the same U0 schedule. Source/optimized interpretations agree at the header witness, producing `28\n`. All 44 direct-native rows pass across these arms: equal keys, zero/one/1,024 iterations, both nonmatching source branches, and invalid bounds. The exact rows are in [native-results.json](native-results.json) and [matched-manual-native-results.json](matched-manual-native-results.json).

Three counterexample programs are separately interpreted and lowered both before and after U0 optimization. All six native witnesses produce `-24\n`, rather than the `28\n` that forwarding `count` would incorrectly predict:

| Negative | Witness | Why equality is unsupported |
|---|---|---|
| Omit quotient condition | `x=5,y=12,n=8` | Equal remainder 5, different quotients. |
| Omit remainder condition | `x=7,y=8,n=8` | Equal quotient 1, different remainders. |
| Use divisor 7 for x and 8 for y | `x=8,y=9,n=8` | Both key pairs are `(1,1)`, but the reconstruction maps differ. |

[negative-results.json](negative-results.json) retains actual source/optimized interpretations and native outputs. The proposed fragment's independent oracle rejects divisor zero and negative/unknown divisors before evaluation; no invalid division is executed. This is an admission boundary for the future model, not evidence of an implemented compiler guard. The two ordinary nonmatching branches return `-1` and `-2`, respectively, and invalid bounds return `-9`.

The first omitted-quotient fixture replaced its guard with an unconditional jump. U0's CFG conversion panicked at `fixedbitset` index 10, size 10, with its now-unreachable diagnostic block present. The source, successful interpretation, failed command, and original runner remain preserved. The revised negative branches on the already-true outer `valid` condition, retaining CFG edges while still omitting the quotient requirement. That revision passes. This compatibility failure is not attributed to the encoding and is not counted as the required compiler bug.

## Baseline and backend evidence

All compilation uses admitted U0 `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, release binary SHA-256 `d86869982413d4561cf713cc769c96eb1c9bfefe46fa459a2692c53a7aa93cf0`, its paired Tiger/runtime, `--with-context`, and LLVM 18 `O3_O3`. Both timed inputs pass through the identical U0 schedule before independent native lowering.

U0 exports three source graphs with 7,396, 11,595, and 18,627 nodes. Each retains at least one load; the middle graph contains two after transformations. All have zero `DidMemOptimization` and zero `NoAlias` rows. Exact emitted Bril still stores through one loop-carried pointer and loads through another. This is an equality/must-alias opportunity; no different-address claim is needed.

LLVM simplifies the remainder test under quotient equality to `x==y`. In the exported `_main`, it still leaves one load and two stores (one store initializes the sentinel). In the executed C `main`, inlining exposes enough information to remove memory operations, but a vectorized reduction and scalar remainder loop survive. In contrast, the manually forwarded input produces an acyclic arithmetic sum in both functions. The actual entry has two cyclic basic-block components in baseline and none in the matched manual arm; [entry-inspection.json](entry-inspection.json) verifies this from the retained LLVM control-flow graph. The native assembly confirms vector additions and a backward loop branch only in baseline's executed entry.

Therefore the surviving hypothesis is specifically that **earlier same-address forwarding enables a stronger later optimization cascade**. It is not a claim that LLVM cannot infer the key equality or ultimately forward the load.

## Frozen small pilot

[design-freeze.json](design-freeze.json) was written before measurement and binds sources, emitted programs, binaries, scripts, correctness evidence, exact arguments, six balanced randomized arm orders, and timing boundaries. Two warmups per arm precede the six measured pairs. Every process is invoked with dynamic arguments `12 12 10000000` and must print exactly `49999995000000\n`.

| Matched arm | Median process wall time | Observed range |
|---|---:|---:|
| Source → U0 → LLVM | 3.158 ms | 2.989–3.223 ms |
| One-line manual → U0 → LLVM | 1.855 ms | 1.816–1.992 ms |

The median paired baseline/manual ratio is 1.669; all six paired ratios exceed 1.60. This small pilot includes process startup, argument parsing, allocation/free, computation and printing; it excludes compilation and receipt writes. It does not measure the cost or generated code of an encoding integration, establish statistical acceptance for the goal, or substitute for the required full campaign. Raw observations, warmups, outputs and receipts are in [pilot-observations.json](pilot-observations.json), [pilot-summary.json](pilot-summary.json), and `pilot-commands/`. No additional workload or repetition was selected after inspecting the pilot.

## Integration cost and next gate

The mathematical representation is bounded, but this is not an annotation-only integration. In source graph 1 the quotient and remainder assumptions are separate `InIf` contexts (`Assumption-217` and `Assumption-247`), while the load address is a projection of another local `Arg` under `Assumption-313`. Loop inversion and later passes change those paths. [inspection.json](inspection.json) retains shortest finite address-to-`Arg` paths as diagnostic evidence; those paths do not prove ancestry or unchanged loop-slot transport.

A correct bridge must recover both exact guarded comparisons, recognize the same fixed divisor and remainder construction, transport their operands through the enclosing input tuples, prove unchanged local loop-pointer identities, and export equality only for the corresponding local expressions. It must isolate impossible scopes and avoid equating shared unscoped values. This is substantial checked plumbing compared with adding a constructor flag. It can reuse the general private-scope/tuple/loop transport required by the existing alias work; no wholesale IR or alias redesign is indicated by this screen. Whether that shared machinery already suffices remains unverified.

The next implementation gate is an actual private-graph `K7` cancellation and exact local same-address bridge, with cancellation knockout/rescue, consumer knockout, the same-source primitive-null/manual controls, and the negative boundaries above. Close the direct native memory-load prediction as falsified; retain the observed early-forwarding phase-ordering opportunity only if it can be reached through that bounded integration. No new compiler/engine source, commit, broad validation suite, or proof support was added here.

## Reproduction artifacts

`run.py` provides separate preparation, baseline, revised negatives, and matched-manual phases; each command directory refuses overwrite. `run-v1.py` and `run-v2.py` preserve prior adapter versions. Existing receipts must be kept when replaying into a fresh directory. `inspect.py` derives exported-function and graph evidence, while `entry-inspection.py` establishes the actual-entry correction. `pilot.py` refuses a second freeze or overlapping result directories. The captured compiler commands use 180-second bounds, native witnesses and pilot invocations use 30-second bounds, and no external memory-pressure guard is enabled. The one CFG failure remains explicit among 88 screen commands; all 16 pilot invocations succeed.
