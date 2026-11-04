# Fresh source pass: three total lossless-key hypotheses

**Screen reversible two-word affine keys first.** They can produce equality-sort child equalities, which unlock a sibling-guarded reverse-disequality step and a separate marked propagation step. Unlike Pack32, Parts32 and bounded quotient keys, the proposed law is valid for every i64 bit pattern. Paired Select routing and order-tagged sorting are distinct lower-ranked alternatives. No compiler execution, timing, build, source change or new payoff result is reported here.

This read-only pass reviewed the existing goal findings and current compiler source. The adjacent `../eggcc` checkout is at `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`, whereas the admitted U0 is `a0bbec127f83249074a46af3fd6f6126c90fe0fb`. Relevant interval, memory and CICM source differs. All final line references below use the pinned copy `/private/tmp/eggcc-nontrivial-encoding-payoff-u0`, rather than assuming that adjacent HEAD is U0. The only written artifact from this pass is this report.

## Ranking and admission state

| Rank | New hypothesis | Concrete existing consumer | Cheapest next falsifier | Admission state |
| --- | --- | --- | --- | --- |
| 1 | Reversible two-word wrapping affine key | Existing false-If elimination; optionally store forwarding after a separately checked equality bridge | U0 versus exact target-folded source, same native backend; close if U0 already folds or native code is identical | Sound total law and supported operators; constructed trigger and endpoint untested |
| 2 | Paired Select routing with a shared dynamic selector | Existing Select-producing optimization and false-If elimination; optional same-address forwarding | Same baseline/manual screen with both selector outcomes; close if Select specialization already removes the target | Sound total law, directly supported Select producer; complete paired-key trigger is new |
| 3 | Order-tagged signed sorting key | Existing false-If elimination, or same-address store forwarding | Same native screen; close if LLVM already combines min/max/order guards | Sound total law and supported operators; no current corpus full-key producer identified |

These are hypotheses for **constructed compiler workloads**, not claims that an existing benchmark already contains the complete trigger. Source searches found a real Fibonacci pair update, a direct Select fixture and a conditional-swap benchmark, but none establishes the complete equal-key relation followed by the proposed new consumer. Do not present those near matches as applications already demonstrated.

## Shared mechanism and consumer

Use equality sorts for dynamic words and products in a private pointwise graph. Import only total pure scalar expressions, exact same-scope source equalities and feasible branch facts. A product representation is an immutable semantic product, not an annotation on EggCC's general associative `Concat`.

Each proposed key can supply the first step of this common chain:

```text
Key(a,b) = Key(c,d)               source field-equality guards + congruence
  => a=c, b=d                    generic marked-constructor cancellation
Add(c,z) != Add(a,w), a=c
  => z!=w                        generic reverse congruence with equal sibling
  => Mul3(z) != Mul3(w)           marked propagation
  => Eq(3*z,3*w) = false          exact contextual consumer bridge
```

`Add` is **unmarked**. Its reverse step uses congruence contraposition, so wrapping does not weaken it. `Mul3(x)=3*x mod 2^64` is injective because 3 is a unit modulo `2^64`; this is a total word law. Marking ordinary binary Add or Mul jointly injective would be unsound. No Neg/Abs, division, shifts, numerical bounds, loop-literal induction, memory lifetime certificate or sampled concrete value is needed.

Both encodings are essential to this selected chain: without key cancellation, the Add result disequality has two unresolved children and cannot isolate `z!=w`; without reverse disequality, key equality alone does not answer the target; without the final marked law, the target disequality is unavailable to generic closure. The odd-multiplier tail is not proposed as a new standalone payoff: the new producer is the lossless two-field key and its equality consumed by the reverse step.

The existing endpoint is [interval_analysis.egg:284](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interval_analysis.egg:284), which eliminates an If whose predicate has false upper bound. Current true-Eq handling at [interval_analysis.egg:408](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interval_analysis.egg:408) transfers numeric bounds; it does not itself install arbitrary symbolic component equalities. The existing memory endpoint is [mem_simple.egg:107](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/mem_simple.egg:107), which forwards a store into a same-address load. A memory variant needs an exact local pointer-equality bridge; an exported `Eq=true` alone is not evidence that store forwarding consumes the equality.

Primitive-only null: retain the same private graph, guards and every matrix coefficient, selector identity or tag literal. Disable dynamic equality-sort cancellation and disequality propagation. Those primitive fields cannot decide `a=c` or `z!=w` for the same symbolic inputs. A faithful hand-written **dynamic** multi-rule implementation can derive the same facts and is a required fair comparison; no unique logical power is claimed.

Do not hard-code a host gate accepting only `Key/Key -> Add/Add -> Mul3/Mul3`. Import the admitted expression fragment and query the actual target. An additional two-stage key/routing positive is useful after the one-stage screen, because it distinguishes a reusable closure from one fixed pattern.

## 1. Reversible two-word wrapping affine key

Define, over i64 bit patterns with wrapping arithmetic,

```text
u(a,b) = a + 2*b
v(a,b) = 2*a + 3*b
F(a,b) = (u(a,b), v(a,b)).
```

The determinant is `-1`, which is a unit modulo `2^64`. More directly,

```text
a = 2*v - 3*u   (mod 2^64)
b = 2*u - v     (mod 2^64).
```

Therefore `F` is jointly injective in its two **dynamic equality-sort** arguments, without range premises. In the private graph, declare marked `Affine(Word,Word)->PairValue` and import `Affine(a,b)=Pair(u(a,b),v(a,b))` for actual source occurrences. Two source integer-Eq guards over the components make the Pair values equal; marked cancellation then produces both child equalities.

Source support is exact: wrapping Add/Sub/Mul semantics are [interpreter.rs:239](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:239); input translation is [to_dag.rs:231](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/to_dag.rs:231), and output translation is [from_dag.rs:151](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/from_dag.rs:151). Their Int typing facts exist at [type_analysis.egg:285](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/type_analysis.egg:285). The current [peepholes.egg:24](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/peepholes.egg:24) and [canonicalize.egg:3](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/utility/canonicalize.egg:3) provide local arithmetic simplifications, not a general simultaneous-equation cancellation analysis. That source observation does not prove LLVM misses the endpoint.

A related actual pair producer exists in [small-fib.bril:21](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/tests/passing/small/small-fib.bril:21): `(prev,curr) -> (curr,prev+curr)`. This is another reversible determinant-minus-one map. It is evidence that reversible word-pair updates fit the compiler's workload language, not an existing equality guard or payoff. Use the two-nontrivial-field `F` above for the first screen; a direct forwarded component in the Fibonacci map makes it a weaker stress case.

**Smallest workload.** Six dynamic word inputs `a,b,c,d,z,w`; two nested true-Eq component guards; then the false branch of `c+z == a+w`; then the target `3*z == 3*w`. A valid positive is `a=c=1,b=d=2,z=3,w=4`. Start with this acyclic shape for the native screen. A later hot driver must execute the complete guards and consumer on fresh per-iteration dynamic tuples, with observable result accumulation; merely putting an invariant target in a loop lets the backend hoist it and does not establish a hot payoff.

**Cheapest falsifier.** Compile untouched U0 and the exact manual target-false source using the admitted native path. First inspect correct outputs and emitted/native code. Close if baseline already folds or native code is identical. Do not implement the key or time a branch that the backend removes.

**Mechanism tests if the screen survives.** Drop either component equality; both must block cancellation. For first-component-only, `(a,b)=(0,1),(c,d)=(2,0),z=w=0` is a feasible counterexample to the target-false conclusion. For second-component-only, use `(0,2),(3,0),z=w=0`. A singular matrix `(a+2b,2a+4b)` must never receive this annotation. Include signed MIN/MAX inputs to exercise wrapping, differing contexts, true instead of false Add sibling, and a noninjective even-multiplier target. Retain `a=c`, `z!=w` and target DQ receipts; run fixed-input cancellation knockout, reverse-step knockout, intermediate rescue, target-consumer knockout, faithful manual closure and primitive-only null.

**Why new and qualifying if measured.** This is neither fixed translation, a mask, quotient/remainder reconstruction, bounded digit packing nor low/high decomposition. A dynamic component equality is produced by joint cancellation and then causally consumed by a different constructor's reverse rule. A speedup remains unproved until the actual host, causal matrix and repeated matched endpoint measurement succeed.

## 2. Paired Select routing

For an arbitrary common Boolean `p`, define

```text
R_p(a,b) = (select(p,a,b), select(p,b,a)).
```

For either selector outcome this is a permutation of `(a,b)` and is its own inverse. Thus equality of both routed outputs for the same dynamic `p` implies `a=c,b=d` without learning whether `p` is true or false.

Use a marked semantic constructor with an explicit selector tag:

```text
Route(p,a,b) = Triple(p, select(p,a,b), select(p,b,a)).
```

This is jointly injective in `p,a,b`. **Do not** mark the untagged ternary map `(p,a,b)->R_p(a,b)` jointly injective: flipping `p` and swapping the payloads preserves its output. The tag is an equality-sort Boolean child, not a primitive `true/false` mismatch detector. The same `p` occurs structurally on both sides, so no unsupported Boolean-Eq operation is required.

The source already accepts direct Select at [to_dag.rs:281](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/to_dag.rs:281), emits it at [from_dag.rs:292](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/from_dag.rs:292), and has a real input in [simple_select_after_block_diamond.bril:7](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/tests/passing/small/simple_select_after_block_diamond.bril:7). The actual [select.egg:4](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/select.egg:4) optimization also creates Select from small pure If outputs. Restrict the first law to total scalar payloads: the interpreter is lazy at [interpreter.rs:221](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:221), while output conversion visits both payloads before emitting Select, so Div/effects would introduce unrelated semantic questions.

**Smallest workload.** Two nested true integer-Eq checks on the routed outputs of `(a,b)` and `(c,d)`, with `p=lt(q,r)` remaining dynamic. Append the shared Add-reverse/Mul3 tail, or use `a=c` for one same-address store/load. The source graph must retain both selector outcomes across input checks. A two-stage routing network with different dynamic selectors is a later genericity control; repeated routing with the same selector is too easy for ordinary Select simplification.

**Cheapest falsifier.** U0/manual code comparison, exercising `p=true` and `p=false`. Close if baseline/native Select specialization already removes the target. The one existing Select input is only an operator canary; it does not provide the full paired-output guard.

**Negatives.** Compare only one routed output; vary the selector without retaining its tag; cross contexts; supply an effectful or potentially partial payload; or deliberately mismatch one network stage. A single output cannot identify both inputs. After a successful native screen, require the same exact-input cancellation/reverse/rescue/manual/null matrix as hypothesis 1.

**Why new and qualifying if measured.** This is reversible control-dependent routing, not arithmetic range reconstruction. The selector remains symbolic, and paired output equality produces payload equality through a generic marked constructor. It can share the disequality consumer without relying on the known same-mask law.

## 3. Order-tagged signed sorting key

Define the integer tag `tag(a,b)=select(a<b,1,0)` and

```text
O(a,b) = (smin(a,b), smax(a,b), tag(a,b)).
```

This is injective over all signed i64 pairs. Tag 1 reconstructs `(a,b)=(min,max)`; tag 0 reconstructs `(a,b)=(max,min)`. Ties are harmless because min=max. There is no subtraction/Abs overflow or bounded-domain premise. Without the tag, swapping unequal inputs is a concrete collision.

The exact min/max semantics are [interpreter.rs:251](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:251); source/output translations are [to_dag.rs:236](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/to_dag.rs:236) and [from_dag.rs:160](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/from_dag.rs:160); type support is [type_analysis.egg:289](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/type_analysis.egg:289). Use integer tags because the source Eq operator is integer equality. The conditional swap at [bubblesort.bril:50](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/benchmarks/passing/bril/mem/bubblesort.bril:50) is a real sorting producer, but its writes and discarded comparison tag do not supply this complete key. No current full-key corpus trigger was found.

**Smallest workload.** Three nested true integer-Eq guards compare the min, max and integer-tag outputs of `(a,b)` and `(c,d)`. Feed recovered `a=c` into the common reverse-DQ chain, or feed it to the same-address memory consumer. Both ascending and descending pairs, equal pairs and signed extremes are valid controls. A pure explicit `smin/smax` microcase is smaller than adapting the effectful bubble-sort loop.

**Cheapest falsifier.** U0 versus exact manually folded target under the same backend. LLVM may already combine signed min/max/order conditions; close on identical code. Do not implement an encoding just because the algebraic law is sound.

**Negatives.** Omit the tag and use `(a,b)=(1,2),(c,d)=(2,1)`; omit either numeric field; cross scopes; or use floating min/max, whose NaN behavior is outside this law. Require retained component equality and reverse-DQ facts plus the same causal matrix if the endpoint screen survives.

**Why new and qualifying if measured.** This is lossless canonicalization with explicit orientation, using total order semantics. It materially differs from bounded word packing and quotient keys. The sort tag's literals do not themselves determine whether dynamic source components agree.

## Rejected fresh directions and stopping boundaries

- **Generic structural disequality for Pointees convergence:** [memory.egg:339](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/memory.egg:339) waits for two `Resolved-Pointees` values before raw `!=` advances the fixed point. Replacing the duplicated recursive resolution machinery at [memory.egg:88](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/memory.egg:88) with generic multi-constructor disequality initially looked attractive. It is not an admitted production hypothesis: [schedule.rs:101](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/schedule.rs:101) explicitly does not run memory-helpers, and [schedule.rs:120](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/schedule.rs:120) disables memory. Re-enabling the old analysis would confound a claimed encoding speedup and may exceed a bounded consumer change.
- **Sign/magnitude keys:** `(abs(x),x<0)` could be injective on a suitable domain, but [interpreter.rs:342](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:342) calls signed `.abs()`, making MIN and build-mode behavior a needless premise. Order-tagged sorting supplies a total alternative. Do not open a new bounded-domain bridge solely for this variant.
- **LCG-state cancellation:** the existing [mat-mul.bril:5](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/benchmarks/passing/bril/mem/mat-mul.bril:5) update uses odd multiplier `25214903917` modulo `2^48`. It is injective on one chosen residue interval, but the signed remainder representation and branch/substitution preservation require domain evidence; the current corpus has no complete paired-state equality consumer. This pass does not admit it as a fourth endpoint hypothesis.
- **Term/CICM structural comparison:** current [conditional_invariant_code_motion.egg:15](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/conditional_invariant_code_motion.egg:15) already keys both candidates by the same extracted Term. Merely annotating syntax does not establish an avoided comparison or new consumer. A fresh measured index bottleneck would be required.

Proceed with at most one smallest actual-host/native screen per admitted family, then one evidence-justified revision if needed. If every baseline/manual endpoint is identical, close these bounded leads without generic integration or timing. This pass finds no new qualifying bug and makes no performance claim.
