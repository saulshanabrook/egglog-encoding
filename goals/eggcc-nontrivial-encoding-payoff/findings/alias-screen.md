# Dynamic same-base alias candidate: baseline/backend screen

**Disposition: retain for encoding integration, with an explicit loop-transport dependency.** Untouched EggCC retains a redundant load, and its LLVM 18 `O3_O3` backend retains the load in the executed native loop. Replacing only that load with the value of the first store changes native code materially while preserving all checked outputs. A follow-up graph query identifies the exact transport route: one new guarded `NoAlias` loop rule is needed; the existing `If` transport and memory consumers then match. This is a prospective speedup opportunity; this screen establishes neither an encoding integration nor a measured speedup or compiler bug.

The retained evidence root is [`alias-screen/`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/). The input is a source-derived microcase of EggCC's existing `mem-simple` optimization, rather than an existing benchmark-suite workload.

## Program and semantic argument

[`source.bril`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/source.bril) accepts dynamic integers `i`, `j`, and `n`. An entry guard requires `0 <= i,j < 2` and `0 <= n <= 1,000,000`; invalid inputs print `-2`. The equal-mask branch prints `-1`. The false branch of `(i & 1) == (j & 1)` allocates three integer cells, sets `pi = p + (i + 1)` and `pj = p + (j + 1)`, and executes:

```text
for count = 0 .. n-1:
    *pi = count
    *pj = 0
    sum += *pi
```

Both pointers address cells 1 or 2 of the same live allocation. The false branch implies `(i & 1) != (j & 1)`, hence `i != j` by reverse congruence. Translation by the same fixed integer preserves this disequality; distinct in-bounds offsets within this allocation designate distinct cells. Therefore `*pi` equals `count` after the two stores. The expected output is `n(n-1)/2`, with no overflow under the guard. No calls or frees intervene between allocation and the loop; the allocation is freed once after it. The pointers and indices remain unchanged across iterations.

The prospective generic chain is:

```text
Mask(i, 1) != Mask(j, 1)
  => i != j                         reverse congruence, same mask
  => Shift1(i) != Shift1(j)          marked fixed translation
  => Cell(p, Shift1(i)) != Cell(p, Shift1(j))
                                    marked live, in-bounds cell identity
  => NoAlias(pi, pj)                 checked host bridge
```

`Mask` itself is not injective. These are symbolic equality-sort values; the chain cannot be replaced by comparing two stored primitive children of one constructor. This screen has not yet run the chain, its ablations, or the primitive-null comparator.

## Existing consumer and observed baseline

The unmodified source consumer is `dag_in_context/src/optimizations/mem_simple.egg` at U0 `a0bbec127f83249074a46af3fd6f6126c90fe0fb`. Its write/load commute rule (line 70) uses `NoAlias` to move a load before a write to another address. Its store-forward rule (line 107) then replaces the load from the preceding store to the same address with the stored value. For this input the required fact is `NoAlias(pj, pi)`.

U0's existing `NoAlias` producers use signed interval bounds for a base/nonzero offset or two offsets differing by a known nonzero `Add`/`Sub`; they do not consume a false `Eq` of masked indices. They propagate an existing fact into `If` inputs and symmetrize it. The executed optimizer generated zero `NoAlias` and zero `DidMemOptimization` rows in each of its three retained graphs. The graphs have 6,184, 11,520, and 17,340 nodes. Each still contains the hot load; the second contains two load rows after transformations. The exact emitted Bril retains:

```text
store v48_ v46_;
store v49_ v50_;
v53_: int = load v48_;
```

The manual comparator [`manual.diff`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/manual.diff) changes exactly one input instruction:

```diff
-  value: int = load pi;
+  value: int = id count;
```

Both stores remain in the comparator input. No optimizer rule, manifest, engine source, runtime, schedule, or compiler configuration changes.

## Backend and correctness evidence

All three arms—source, exact EggCC emission, and manual comparator—were lowered independently with `--optimize-egglog false --optimize-bril-llvm O3_O3`, the same copied compiler/Tiger, LLVM 18, and U0 runtime. [`inspection.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/inspection.json) and the compact `.ll`/`.asm` extracts beside each native executable record the result:

| Native arm | Hot loads / stores in LLVM `_main` | Actual native entry point |
| --- | --- | --- |
| Source | 1 / 2 | Scalar store–store–load loop. |
| EggCC emission | 1 / 2 | Scalar store–store–load loop. |
| Manual one-line comparator | 0 / 0 | Closed arithmetic expression; loop eliminated after inlining. |

The exported manual `_main` is vectorized; the actual `main` entry inlines it and computes the sum without a loop. The baseline assembly still executes `str`, `str`, `ldr` in its loop. These are structural observations, not timing measurements. Native binaries, full LLVM, full disassembly, compact functions and their diffs are retained.

The source, manual comparator, and exact emitted Bril each interpret to `28\n` for the header arguments `0 1 8`. Direct native execution checks eleven argument rows in each arm: both distinct index orders, zero/one/eight/1,024 iterations, both equal-index cases, and invalid lower/upper index and iteration bounds. All 33 native runs exit zero and match the independently calculated exact output. [`native-results.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/native-results.json) retains every row. This finite matrix supports the screen; the source-level argument above supplies the intended guarded law.

All 43 captured experimental commands succeed without timeout. Compiler commands have a 180-second bound; native executions have a 30-second bound. The driver sets `RAYON_NUM_THREADS=1`, the LLVM 18 environment, and `EGGCC_ROOT=/private/tmp/eggcc-nontrivial-encoding-payoff-u0`; no memory-pressure guard is enabled. Each command receipt records argv, cwd, relevant environment, input/executable hashes, exit, timeout, stdout, stderr and elapsed time. Elapsed times are diagnostic and are not performance evidence. [`identities.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/identities.json) binds the reused binaries/runtime/tools and original inputs to admission. [`run.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/run.py) records the exact procedure; it deliberately refuses to overwrite its existing command captures. [`inspect.py`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/inspect.py) can regenerate the derived inspection from those captures. The shared add.bril native canary is in the sibling `scoped-screen/` evidence and was not repeated here.

## Reachability through the actual contexts

The follow-up [`reachability/transport.json`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/reachability/transport.json) performs explicit relational joins over the first retained graph. It uses actual `Get` rows, equal canonical classes and matching control-region rows. It does not infer ancestry from arbitrary paths through analysis nodes. The graph SHA-256 is `51df3de7f524263c4587447135345a94fca6eb371d4b10e383b510ff6f52563b`.

The receipt also retains constructor-only expression paths: the false branch body reaches the `DoWhile` through `Single → Print → Get`; the loop body reaches the inner `If` through `Concat`; and that `If`'s true body reaches the hot load through `Concat → SubTuple`. This search stops at `Arg`/`Const` leaves and never follows their context parameters or analysis-function rows, avoiding a false ancestry argument through the graph's context cycles.

The masked predicate is evaluated in the valid-input branch (`Assumption-184`). Its false `InIf` is `Assumption-216`, with its own argument tuple. The operands are passed unchanged through that `If`:

| Value | Predicate-side class | `If` input slot | False-branch class |
| --- | --- | --- | --- |
| `i` | `Expr-186` | 5 | `Expr-230` |
| `j` | `Expr-189` | 4 | `Expr-234` |
| Common mask `1` | `Expr-187` | 1 | `Expr-228` |

Thus the private false-branch theory may assert disequality between masks of its **localized** operands. It must not assert the parent operands disequal in EggCC's main graph. The false-branch pointer applications already exist: `Expr-232 = PtrAdd(Expr-226, Add(Expr-230, Expr-228))` and `Expr-236 = PtrAdd(Expr-226, Add(Expr-234, Expr-228))`. `Expr-226` is projection 0 of the same allocation. A checked live-region bridge would therefore export the branch-local pair `(Expr-232, Expr-236)`.

The next region is `InLoop(inputs, outputs)` in `Assumption-258`. The graph supplies the following exact equalities, where output position 0 is the loop predicate:

| Pointer | Loop input | Loop argument | Body output | Consequence |
| --- | --- | --- | --- | --- |
| `pi` | slot 5, `Expr-232` | slot 5, `Expr-272` | slot 6, `Expr-272` | Unchanged each iteration. |
| `pj` | slot 6, `Expr-236` | slot 6, `Expr-274` | slot 7, `Expr-274` | Unchanged each iteration. |

These are canonical-class equalities, not a guess based on source variable names. They support this narrow missing transport law by induction on executing iterations:

```text
NoAlias(inputs[i], inputs[j])
outputs[i+1] = Arg_L[i]
outputs[j+1] = Arg_L[j]
--------------------------------
NoAlias(Arg_L[i], Arg_L[j])
```

Both invariant premises are required. The actual loop's positions 0, 1 and 3 fail this test. The current interval analysis already uses an analogous passthrough condition to carry bounds into loops (`interval_analysis.egg:434–457`), while `mem_simple.egg` has no loop `NoAlias` rule.

Inside this loop, the hot operations are under a further true `InIf`, `Assumption-287`, whose input tuple is exactly the loop argument (`Expr-259`). The **existing** `NoAlias`-into-`If` rule maps its positions 5 and 6 to `Expr-289` and `Expr-291`. After symmetry, `NoAlias(Expr-291, Expr-289)` is the exact write-address/load-address pair required by the commute rule. The load is `Expr-297`; its state is the second write `Expr-296`, whose previous state is the first write `Expr-295`. That first write uses address `Expr-289` and count value `Expr-293`. Commute followed by store forwarding therefore replaces the loaded-value class `Expr-301` with `Expr-293`.

The relational replay falsifies reachability using only a hypothetical branch-local `NoAlias` seed plus existing transport: closure contains only `(232,236)` and its reverse. Enabling the proposed **both-invariant** loop law reaches `(272,274)`, then the existing `If` rule reaches `(289,291)` and the exact consumer pair. This replay is a graph query, not an execution of modified EggCC rules. It establishes concrete rule instances and identifies the missing premise; compiler execution, extraction and scheduling remain untested.

## What the generic encoding already does

[`generic-chain-safe.egg`](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/alias-screen/reachability/generic-chain-safe.egg) runs the finite symbolic chain in the existing E1 release binary, SHA-256 `1a7d6ddcf1e59000a9499bf9e4950e03a1934ee3be130769549040a47c4d43b7`. Both NEE and EE finish successfully under `--strict-mode`, with 30-second bounds. The probe starts with unknown index/cell disequality, asserts only same-mask parent disequality, and checks the child, translated and live-cell disequalities. It also checks that removing either marked forward wrapper, changing the translation constructor, or allowing both mask positions to vary does not establish the corresponding target. This is evidence about that reused binary, rather than fresh engine admission or EggCC integration. The feature source inspected alongside it documents sibling-guarded reverse congruence and marked forward witness search in `disequality.rs:46–55,119–126`.

Two initial probe invocations failed because globals named `x`/`y`, with or without `$`, collided with private generated variable names. The retained failing inputs and receipts remain under `reachability/commands/`; the successful fixture uses distinct `$probe-...` names. These setup failures do not establish a semantic failure of the chain or a qualifying EggCC bug.

| Required piece | Classification | Evidence / work still required |
| --- | --- | --- |
| Same-mask parent disequality to index disequality | Existing generic encoding capability | Successful NEE/EE finite probe; shared sibling is materialized. |
| Index disequality through fixed translation and live cell | Existing generic encoding capability, conditional on sound wrapper semantics | Successful finite probe. Do not mark binary `Add` or general `PtrAdd` injective. |
| False-`Eq` producer and operand localization | New bounded EggCC plumbing | Exact input/argument projection map exists; implement scope checks and private seeding. |
| Bounds, common live allocation, width, no free/call/escape | New checked EggCC semantic bridge | True for this source grammar; not established by the disequality encoding. |
| Branch pointers to loop pointers | New bounded compiler transport | Both invariants are witnessed; existing `NoAlias` transport is insufficient. |
| Loop pointers to the hot `If` pointers | Existing EggCC rule | Exact matching `If` and projection rows are present. |
| `NoAlias` to load replacement | Existing EggCC rules | Exact commute and store-forward matches are present. |
| Fact lifetime and final extraction | Unimplemented host integration discipline | Need a frozen/one-shot consumer, canonical-class revalidation and actual optimizer replay. |

No missing generic disequality law was found for this exact chain. The missing reachability step is a guarded compiler transport rule. The remaining work is bounded but material; the graph alone does not authorize unrestricted scope copying, general pointer injectivity or persisting branch facts through later class merges.

## Remaining integration requirements

1. Use a private reasoning graph for the exact branch. Adding branch-dependent disequality to the main e-graph would be unsound.
2. Prove the source guard and allocation premises. The entry guard is a Boolean conjunction; the current host must not be assumed to have decomposed it into all interval facts. A bounded grammar may establish those facts explicitly, or the fixture can be revised only with a recorded, source-backed reason.
3. Implement and execute the exact projection and guarded loop transport established above. These IDs are graph-local receipts, not interchangeable scopes or stable IDs for future invocations. Recompute the witnesses for every current snapshot.
4. Emit `NoAlias` for the exact local pointer pair only after checking bounds, width, shared live allocation, context ancestry and unchanged pointer transport. `mem-simple` currently pushes facts into `If`, with no general loop propagation rule. Match the consumer's actual local expressions or justify a new narrow bridge.
5. Run generic-chain knockout/rescue, host-bridge and consumer knockout, same-input primitive-null/manual controls, and semantic negatives before calling the mechanism nontrivial. Different masks, different translations, equal-index paths, varying siblings, escape/free/call cases and unrelated scopes must not inherit this fact.
6. Only after successful integration and native correctness, run a measured campaign on an appropriate larger iteration count. A source/manual code difference alone does not meet the goal's payoff gate. Revisit a production-shaped workload if this microcase is too narrow for the paper.

No source-fixture revision was needed for the baseline/backend screen. The follow-up uses only private probe fixtures and exact graph queries; no compiler/engine source, full test suite, build or timing campaign was changed or run.
