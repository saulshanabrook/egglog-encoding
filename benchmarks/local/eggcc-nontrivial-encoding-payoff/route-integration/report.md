# Tagged paired routing reaches EggCC's actual false-Eq consumer

The bounded Route integration passes its mechanism and emitted/native-code gates on the retained constructed input. Generic reasoning over equality-sort children is necessary in the causal matrix, and two true intermediate-fact rescues pass. This is supporting evidence: no pre-existing compiler bug or measured runtime speedup is claimed. Full host validation is reported separately below; no snapshot is accepted.

The isolated sources are `/private/tmp/eggcc-route-candidate` and `/private/tmp/encoding-route-candidate`. They start from pinned U0 `a0bbec127f83249074a46af3fd6f6126c90fe0fb` and the byte-verified Parts32 engine selection. The root checkout, other studies, shared hypothesis ledger, paper and proofs were not edited. There was one bounded implementation and no semantic/importer revision. A compile-time reference mismatch and one inherited sidecar needless borrow were corrected before freezing the evaluated binary.

## Exact law and source admission

For a Boolean selector and total wrapping-i64 payloads,

```text
Route(p,a,b) = (p, Select(p,a,b), Select(p,b,a)).
```

The retained first field reconstructs `p`. The remaining fields reconstruct `(a,b)` when `p=true` and `(b,a)` when `p=false`. Therefore the tagged map is jointly injective. Ordinary Select and the two-output map without its selector tag are unmarked. Changing the selector while swapping the payloads preserves the untagged output, so annotating that map would be unsound.

The source fixture is the exact retained routing source from `lossless-key-screens/.../execution-02/routing/source.bril`. Its dynamic selector is `p=(q<r)`; it has both complementary Selects on each pair, two true Eq guards over their outputs, a false guard over `c+z=a+w`, and the target `3*z=3*w ? 99 : 7`. The importer follows the exact enclosing If input projections back to one lexical root. It admits only matching complementary Selects with the same localized selector and a matching Add/Mul3 tail. It accepts pure total scalar expressions built from input slots, constants, Add, fixed Mul and this exact LessThan/Select form. It does not model partial payloads, state, calls, effects, arbitrary predicates or general path facts.

The first actual-host pilot succeeded. Its receipt retains the actual source expressions and contexts, translated words, complete private program, intermediate facts and exact export. It found `a=Slot(0), b=Slot(1), c=Slot(2), d=Slot(3), z=Slot(4), w=Slot(5)`. No enumeration or observation of the selector's Boolean result occurs inside the private graph.

## Actual generic encoding

The graph has equality sorts `Selector`, `Word` and `Key`. `p` is an opaque equality-sort Selector value. `Select`, `Triple` and `Add` are unmarked. `Route` and `OddMul(_,3)` are marked. Its rows and source seeds are:

```text
uab=Select(p,a,b)     vab=Select(p,b,a)
ucd=Select(p,c,d)     vcd=Select(p,d,c)
kab=Route(p,a,b)      kcd=Route(p,c,d)
pab=Triple(p,uab,vab) pcd=Triple(p,ucd,vcd)

kab=pab              kcd=pcd                 representation identities
uab=ucd              vab=vcd                 source true guards
Add(c,z) != Add(a,w)                         source false guard
```

Generic congruence gives `pab=pcd`; the identities give `kab=kcd`. Marked cancellation then gives `a=c` and `b=d`. The committed unequal Add applications have one equal sibling, `a=c`, so generic reverse disequality derives `z!=w`. Marked forward disequality gives `OddMul(z,3)!=OddMul(w,3)`: multiplication by odd 3 is a bijection modulo 2^64. The checked exact contextual target Eq is then unioned with a false constant in EggCC's main graph. The private equalities and disequalities remain local to that target.

Manual computes an independent finite least fixed point over the same application rows, primitive columns, representation identities and dynamic seeds. It uses generic congruence, marked cancellation, sibling-guarded reverse reasoning and marked forward reasoning; it does not recognize a Route theorem and jump directly to the target. Its emitted Bril and native entry match Encoding byte for byte. No unique logical expressive power is claimed.

SeedOnly materializes the complete private program and skips inference and witness queries. PrimitiveOnly preserves that same program, annotations, seeds and identities, and actually scans the same manual rows for fixed primitive columns while disabling every inference involving equality-sort children. Its receipt records eight coefficient comparisons across the congruence and disequality scans: all compare `OddMul.coefficient=3` and are equal. Select and Route have no primitive selector tag; their selector is equality-sort. No primitive mismatch or dynamic witness exists, and the null exports nothing. The inspector verifies byte equality of the SeedOnly/PrimitiveOnly program and Encoding's program before its explicit saturation command.

## Causal endpoint matrix

Every arm uses the identical source and 20 input rows, including ten payload/tail cases under both selector outcomes, signed extrema and wrapping boundaries. Baseline means exact U0 emitted-Bril and native-entry hashes; optimized means exact Encoding hashes.

| Arm | Retained causal fact | Endpoint |
| --- | --- | --- |
| U0 / B1 (`off`) | no private inference/export | baseline |
| SeedOnly / PrimitiveOnly | same graph, seeds and identities; no equality-sort inference | baseline |
| Cancellation off | tagged keys equal, `a=c` absent | baseline |
| Identity off | products equal, tagged-key equality absent | baseline |
| Reverse off | `a=c`, Add-result disequality; `z!=w` absent | baseline |
| Forward off | `z!=w`; Mul3 target witness absent | baseline |
| Query off | `z!=w`; target query suppressed | baseline |
| Bridge off | exact target disequality retained; export suppressed | baseline |
| Application off | target witness and export retained; only main-graph union suppressed | baseline |
| Equality rescue | Route cancellation disabled; seed **`a=c`**; `b=d` remains unknown; infer `z!=w` and target | optimized |
| Disequality rescue | Route cancellation and reverse reasoning disabled; seed **`z!=w`**; `a=c` remains unknown; infer target | optimized |
| Manual / Encoding | complete cancellation/reverse/forward chain | optimized |

The rescues seed genuine intermediate facts, not the final target. The application knockout retains the final private witness and export decision but restores exact baseline code, localizing the endpoint change to the consumer union.

U0's LLVM `@_main` has four i64 equality comparisons and two conditional branches. Encoding/Manual have three and zero. U0's native executable entry retains the dynamic `z,w` comparison and `mov ... #0x63`/99 selection; Encoding removes them while retaining the dynamic key and Add tests. Complete LLVM, disassembly and extracted entry bodies are retained. This is executed native work, not just a serialized-IR difference.

## Oracles and negatives

The matrix checks 300 positive/causal native outputs, 36 semantic-negative outputs, 40 no-context outputs and 26 direct source-native outputs. All match the independent wrapping-i64 oracle. Separate exact-`# ARGS` source and emitted interpreter checks cover the same 402 combinations. The interpreter driver uses immutable per-input files because this pinned CLI reads the header rather than positional interpretation arguments.

Each of the six semantic negatives reaches `99`; U0, B1, SeedOnly, PrimitiveOnly, Manual and Encoding preserve its exact emitted/native baseline and export nothing:

- omit the first routed-output guard;
- omit the second routed-output guard;
- use structurally different dynamic selectors;
- change the selector and swap the payloads while omitting the common tag evidence;
- use even multiplier 2 with `z=0,w=MIN`;
- put the target under the true Add-equality branch.

Running without context support creates no query or export, preserves baseline code and passes both selector outcomes. The independent law checker exhausts 174,752 tagged inputs across widths 2 through 8, checks odd-Mul3 permutation behavior at those widths, and reconstructs 4,121 boundary/random i64 pairs under both selectors. It retains the untagged swapped-payload collision and even-multiplier counterexample. These are mechanism and correctness checks, not workload timing.

## Validation and limits

Final results and exact receipts are in `validation.json`. The two focused Route tests, all 66 DAG library tests, and all 18 registered engine injectivity/disequality tests pass. Root and DAG formatting pass. The final candidate produces zero new lint diagnostics: DAG Clippy still rejects two unchanged host locations, and root Clippy rejects an unchanged direct-jump optimizer location also checked on pinned U0. These failures remain explicit.

The exact post-recovery full host `make test` passes all 31 root unit tests and 2,421 file tests, with two doc tests ignored and no disk error or timeout. It still exits 2 on 13 pending snapshots, stopping before the Makefile's DAG release step. Their names and SHA-256 hashes exactly match the frozen Parts32 E1 set. No snapshot was accepted, so full host validation remains failed and this result remains supporting evidence. The exact standalone DAG release step also passes all 66 tests, with no pending DAG snapshots. Root and DAG doc-test summaries are retained in the receipts.

Two earlier full host runs were contaminated by a real filesystem-full event: the first has seven failing file tests and 12 disk-error occurrences; the second has 33 failures and 64 occurrences. Both logs are preserved and neither is used as the required host outcome. After disposable cache recovery, the one exact source/configuration-preserving retry above has zero disk errors and all functional tests pass. The first CLI-help capture also failed while writing its receipt; its explicit capture-failure record and successful retry are preserved. All 402 native and 402 interpreter oracle checks completed before that capture failure and retain verified hashes.

All 884 retained selected-engine files are byte-identical to the affine engine selection. All 876 retained source files also match the immutable initial Parts32 archive plus its five frozen final overlays; the other eight retained files are generated `.log` outputs, not engine source. The selected engine's earlier full `make check` receipt therefore applies to these exact engine bytes; fresh focused engine tests also pass. This does not substitute for the fresh host checks.

`identities.json` freezes admitted U0, candidate and engine source manifests, source archives, patch, binaries, runtime, fixtures, drivers, reports and every command/output receipt. `python3 inspect.py` is a read-only artifact audit. `reproduce.md` separates reproduction steps from this explanation. Command elapsed values are operational timeout diagnostics; no performance samples, hot-driver experiment or timing campaign were collected. The constructed acyclic source is not a demonstrated corpus optimization and cannot establish the goal's required speedup or pre-existing bug by itself.
