# Fresh source hypotheses after the tuple screen

**The strongest new encoding-specific lead is lossless quotient/remainder keys feeding same-address store forwarding.** It has a sound multi-constructor cancellation mechanism and an existing compiler consumer. Its actual producer, native endpoint, and payoff remain untested. The first action should be a small baseline/manual native screen, not an implementation.

This is a source-only pass over clean U0 `a0bbec127f83249074a46af3fd6f6126c90fe0fb`. No compiler execution, build, test suite, or source edit was performed. The existing [same-mask screen](../../../benchmarks/local/eggcc-nontrivial-encoding-payoff/scoped-screen/report.md) and [alias screen](alias-screen.md) remain prospective opportunities: the former preserves a redundant native comparison; the latter preserves a store–store–load loop. The new families below change the mathematical producer or audited invariant; merely substituting another mask or displacement would not be new.

| Rank | Family | Generic mechanism | Existing consumer | Prospective payoff and cheapest falsifier |
|---|---|---|---|---|
| 1 | Lossless quotient/remainder key → must-alias | Product congruence → injective key cancellation → dynamic child equality → pointer congruence | `mem-simple` same-address store forwarding, duplicate/shadowed writes | Plausible hot-load elimination. Compare untouched output with exactly the manually forwarded input under the same native backend; close if baseline already forwards or native code matches. |
| 2 | Bounded two-field word packing → component constraints | Binary injectivity; equal-sibling reverse disequality; propagation through a second constructor | Existing false-`If` elimination, or same-address forwarding after component equality | Potential packed-key lookup simplification. First test whether backend known-bit analysis already supplies the component result. |
| 3 | Symbolic print-order trace audit | Dynamic value DQ → `PrintEvent` DQ → injective trace-node DQ → contradiction with a real state equality | Existing state-transforming rewrites, audited before extraction | Bug search only; no suspect merge identified yet. First census a bounded print-only fragment for an actual merged state pair with distinct ordered symbolic events. Close on no producer. |
| 4 | Recursive multiplication accumulator identity | A symbolic nonzero result could propagate through an odd multiplier into a return conflict | Existing `rec-to-loop` accumulator rewrite | Concrete source-level bug suspicion, but encoding qualification is doubtful. First a zero-recursion baseline/native probe; never count a primitive consistency detector as the goal result. |

## 1. Lossless quotient/remainder keys

For a fixed positive divisor 7, define

\[
Q(x)=\operatorname{trunc}(x/7),\quad R(x)=x-7Q(x),\quad K(x)=(Q(x),R(x)).
\]

`K` is injective: `K(x)=K(y)` implies `x=7Q(x)+R(x)=7Q(y)+R(y)=y`. Division by 7 is total over i64, including signed MIN; `7Q(x)` and the remainder stay representable, so this identity agrees with the source's wrapping multiplication/subtraction. Current [`interpreter.rs`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:239) defines wrapping Add/Sub/Mul/Div. The current Bril bridges support all three required operations ([`to_dag.rs`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/to_dag.rs:232), [`from_dag.rs`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/from_dag.rs:151)); no new executable IR operator is required.

Use a **private scope-local value graph**, with unmarked `Q7` and `R7`, an immutable product constructor `Pair`, and marked unary `K7`. For every admitted dynamic value `v`, import the justified identity `K7(v)=Pair(Q7(v),R7(v))`. A source path establishing `Q7(x)=Q7(y)` and `R7(x)=R7(y)` then yields:

```text
Pair(Q7(x), R7(x)) = Pair(Q7(y), R7(y))    congruence
K7(x) = K7(y)                            representation identity
x = y                                    generic injectivity cancellation
p+x = p+y                                ordinary pointer congruence
load(p+y, store(p+x, value, state)) = value
                                         existing store-forward rule
```

The actual existing consumer is [`mem_simple.egg:107`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/mem_simple.egg:107). This is **must-alias** reasoning, unlike the completed alias screen's `NoAlias` commute. A bounded array and guarded indices suffice; the new bridge need not invent a different-address/lifetime certificate. Context transport still must prove that the exact local pointers correspond to these dynamic indices. Existing true-`Eq` interval rules transfer numeric bounds, rather than the required symbolic quotient/remainder identity ([`interval_analysis.egg:408`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interval_analysis.egg:408)). A source scan found no quotient/remainder reconstruction rule in the current peepholes.

A first valid microcase should compare dynamic quotient/remainder pairs, then store through `p+x` and load through `p+y` inside the equal-key branch. Keep ordinary array bounds and a finite iteration count explicit. Compare the exact one-load replacement before implementing a private graph. If the native difference survives, demand the real graph match and cancellation knockout/rescue before timing. A larger faithful hand-written quotient/remainder rule is a fair control; it is not evidence of unique logical power. Comparing primitive divisor/offset metadata cannot determine the equality of dynamic `x` and `y` on the same graph and seeds.

For a joint variant, an additional genuine path constraint `x != z` gives `y != z` after cancellation, and a separately justified marked translation can carry that to a later test. That variant is optional. Do not add constraints or wrappers merely to claim that disequality was necessary to the must-alias example.

Negatives: quotient equality alone, remainder equality alone, unequal divisors, different scopes, absent exact pointer transport, infeasible path, and out-of-bounds accesses. General variable/zero/-1 divisors are outside this first fragment.

## 2. Bounded two-field word packing

For `0 <= a,b < 2^32`, let `P(a,b)` have the i64 bit pattern `(a << 32) + b`. The high and low halves do not overlap, so `P` is jointly injective on this restricted domain. `Shl`, `Bitand`, Add and integer Eq are present in the current [schema](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/schema.egg:90) and [interpreter](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interpreter.rs:238). The fixed shift 32 is valid; signed interpretation of the final word does not change bit-pattern equality.

This admits a genuinely binary private constructor with equality-sort children:

```text
P(a,b) = P(c,d)        => a=c and b=d       marked cancellation
P(c,e) != P(a,f), a=c => e!=f              reverse congruence, equal sibling
e!=f                  => Shift1(e)!=Shift1(f)
                                             marked propagation
```

The second inference does not need injectivity; the first and third do. Two unresolved children in the second line must remain a disjunction. This differs from the same-mask lead's one-common-mask reverse inference: a lossless two-field encoding produces actual component equalities, and a later packed-key difference can consume those equalities to isolate another differing field.

Natural endpoints are a redundant field comparison in a packed-key lookup, feeding existing [false-`If` elimination](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/interval_analysis.egg:283), or a same-address memory match after component cancellation. Native known-bit analysis may already solve this; inspect the exact manual endpoint before implementing. A full 64-bit argument in either field invalidates the law, so the two 32-bit domain proofs are required, not inferred from purity or field names. Also test different field widths, missing bounds, both fields varying, and crossed scopes.

No current suite producer or executed hot workload has been established. This is a second new family to screen only after the stronger quotient/remainder opportunity, not an accepted optimization.

## 3. Symbolic print-order traces

An ordered print trace is a natural immutable value, unlike a raw write-order trace: changing the order of disjoint writes may be legal, whereas changing the order of distinct printed i64 values is observable. Restrict a first audit to acyclic print-only state chains, with a common incoming state and one exact feasible branch. Define marked constructors `PrintEvent(Value)` and `Snoc(Trace, Event)`. A source-derived equality-sort constraint `x!=y` then gives distinct events and distinct traces, including `[...,x,y] != [...,y,x]`, through generic marked propagation. Importing a compiler equality between the corresponding state expressions must not equate their trace observations.

The existing producer candidates are actual state transformations: [`state-edge-passthrough`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/passthrough.egg:56), [`rec-to-loop`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/rec_to_loop.egg:1), and finite [unrolling](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/loop_unroll.egg:114). Print order already belongs to the compiler's semantic checks ([translation tests](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/src/rvsdg/to_dag.rs:410)). The new contribution would be a symbolic equality-sort audit before extraction, not another sampled primitive Boolean wrapper.

This lead has **no identified bad producer yet**. The cheapest falsifier is a source/graph inventory for two state representatives that the bounded oracle can fully interpret and whose symbolic print order differs. Do not build an effect interpreter or generate planted faults if that inventory is empty. Exclude loads, writes, frees, unknown calls, unbounded loops, path enumeration and divergence from the first oracle; they need different semantics. A conflict based only on trace-length tags or one sampled primitive printed value would not demonstrate the proposed nontrivial mechanism. This is lower priority than the two endpoint-oriented families.

## 4. Adjacent bug suspicion: multiplication's false-path accumulator

Current [`rec_to_loop.egg:70`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/rec_to_loop.egg:70) registers `(Accum-Bop (Mul) 1 (Mul))`. The accumulator rewrite initializes its loop input from `initial-int`, but its outer false branch unconditionally appends `Const(Int 0)` ([line 142](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/rec_to_loop.egg:142)); it then combines the base result and that slot with `base-case-op` ([line 149](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/rec_to_loop.egg:149)). Therefore a matching recursive multiplication function called on its initial base-case path appears liable to return `base * 0` rather than `base`. The normal parallel schedule includes this rewrite before inlining ([`schedule.rs:228`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/schedule.rs:228)).

This is a source suspicion, not a reproduced bug: matching, extraction choice and native behavior remain untested. The cheapest probe is a valid recursive multiplication function with a nonzero base, evaluated at zero recursive steps, plus a positive-recursion control. The source's multiplication arithmetic is wrapping, so a small positive case avoids unrelated overflow concerns.

A naturally symbolic base such as `3*x`, under `x!=0`, could support an odd-multiplier equality-sort disequality audit. But the bug is already suggested directly by the mismatched neutral constants. Do not manufacture extra wrappers or count a constant-output/Boolean consistency detector as qualifying. Retain it as a separate compiler-bug probe unless a same-input primitive-null comparison shows that generic equality-sort reasoning materially contributes to diagnosis.

## Dispositions from this pass

Admit quotient/remainder and two-field packing only to the existing cheapest-falsifier stage, with all source/domain conditions above. Keep the symbolic print audit as a low-priority source-backed inventory request; it has no known bad merge. Keep recursive multiplication as an unverified adjacent bug suspicion with an explicit encoding-qualification gap. General `Concat`, structural types, the old CSR/NoAlias cases, syntactic `Term` annotation alone, and fixed-shift renamings do not become new candidates in this pass.
