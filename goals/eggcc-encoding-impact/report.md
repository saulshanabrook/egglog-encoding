# Detecting an EggCC miscompile with an injective observation wrapper

An injective wrapper can turn concrete evaluation results into a consistency check on an e-graph. This case demonstrates that check on a real EggCC miscompile: an optimization merges a branch expression with `false`, even though the expression evaluates to `true` on the selected input. Congruence carries the bad merge to the recorded results, and the wrapper's injectivity rule reports a contradiction.

We first found the miscompile by comparing source and optimized execution, then built the observation harness to catch that same failure inside the optimizer. The annotation expresses a reusable consistency contract; a hand-written checker over the same observations catches the same conflict. The experiment demonstrates detection, rather than automatic discovery or repair of the faulty rule.

The selected compiler baseline is `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. Exact rules and encoding laws are in the [reference](reference.md); commands and artifact identities are in [rerun.md](rerun.md).

## The rewrite that is unsound

The [minimized Bril program](/Users/saul/p/wt/eggcc/encoding-impact/tests/encoding_impact/arithmetic/mul-minimal-max.bril) does this:

```text
if 0 < x:
    answer = (x * 2) < 0
    print answer
```

For `x = MAX = 2^63 − 1`, execution takes the positive branch. Bril's [signed 64-bit wrapping arithmetic](https://capra.cs.cornell.edu/bril/lang/core.html) gives `MAX * 2 = −2`, so the source prints `true`. EggCC instead produces a program whose taken branch prints the constant `false`. All three native extraction passes complete.

Inside that branch, two interval-analysis rules ignore overflow:

```text
lo(x) > 0 ∧ lo(y) > 0   ⇒ lo(x * y) ≥ 1
lo(x) ≥ 0 ∧ lo(y) ≥ 0   ⇒ lo(x * y) ≥ 0
```

Here `lo` denotes a lower bound. Both rules apply to `x` and `2`. Either inferred product bound makes the interval upper bound of `(x * 2) < 0` equal to `false`. A further rule then unions the comparison with a Boolean constant:

```lisp
(rule ((= false (either-unwrap-right (maybe-unwrap (hi-bound expr))))
       (HasArgType expr ty)
       (ContextOf expr ctx))
      ((union expr (Const (Bool false) ty ctx)))
      :ruleset interval-analysis)
```

Call the branch's comparison `e` and that exact constant `z`. The faulty chain ends with **`union(e, z)`**. The [captured graph](../../benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/graph-witnesses.json) contains the product lower bound `1` and the comparison in the false constant's e-class; the [emitted Bril](../../benchmarks/local/eggcc-encoding-impact/compiler/arithmetic-screen/localization/runs/mul-minimal-max/A-emit/optimized.bril) prints `false`. Graph inspection and rule-removal experiments support this explanation, rather than a recorded complete rule-firing trace.

## Attaching the check to those exact expressions

EggCC represents the branch's inputs as projections from a region argument. In the failing run, its concrete contents are `[StateV, 0, MAX, 2]`: projection 1 is zero, 2 is `x`, and 3 is two. Constants carry both the region's argument type and its context, here `InIf true pred inputs`.

The observer constructs `z` with **that same type and context**. Thus `z` is the same constructor application the interval rule above uses, rather than an unrelated false constant. The comparison `e` is translated through the same expression-conversion cache as the optimizer's program.

The observer evaluates supported pure expressions at reached input/context pairs. Its restricted walker uses wrapping arithmetic and cross-checks the result with EggCC's `interpret_expr` helper after validating the fragment, types and context. It records each point separately. The failing branch has point token `1`; the token identifies the observation point, not the number MAX.

The following is one connected, schematic excerpt of the actual setup. Names are shortened; the term shapes, projection indices and point come from the [retained pass-0 observations](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/original-release-red/injective/evidence-archive/pass-00/observations.json). `ty`, `pred` and `inputs` stand for existing terms from this program.

```lisp
; Existing program expressions inside the taken branch:
(let ctx     (InIf true pred inputs))
(let arg     (Arg ty ctx))
(let product (Bop (Mul) (Get arg 2) (Get arg 3)))
(let e       (Bop (LessThan) product (Get arg 1)))
(let z       (Const (Bool false) ty ctx))

; Added harness declarations. Only the immutable Boolean wrapper is injective.
(sort ObservationValue)
(constructor ObservedBool (bool) ObservationValue :injective)
(constructor EvalBoolAt (Expr i64) ObservationValue)

; Among the facts seeded BEFORE the optimization schedule:
(union (EvalBoolAt e 1) (ObservedBool true))
(union (EvalBoolAt z 1) (ObservedBool false))

; DURING the schedule, the faulty interval reasoning derives (union e z).
; The harness does not seed that Expr equality.
```

These facts attach expected values to expressions through `EvalBoolAt`. They do **not** assert `e = Const(true)` or an Expr disequality. The full setup also observes contextual true/false literals and the root predicate; the two unions above are the ones that explain this failure.

Both links matter. Using the wrong type or context for `z` would attach the observation to a different constant. Using different point tokens would leave the two `EvalBoolAt` applications unrelated even after `e` and `z` merge.

## Why the injectivity audit rejects the rewrite

When the optimization derives `e = z`, ordinary congruence forces:

```text
e = z
    ⇒ EvalBoolAt(e,1) = EvalBoolAt(z,1)
    ⇒ ObservedBool(true) = ObservedBool(false).
```

The last equality violates the declared injectivity of `ObservedBool`. Its native Boolean payloads differ, so the annotation's generated rule panics. The relevant generated rule is equivalent to:

```lisp
(rule ((= (ObservedBool a) (ObservedBool b)) (!= a b))
      ((panic "injective primitive arguments differ"))
      :ruleset injectivity)
```

This is schematic rule text. After the source schedule, the harness runs `(run-schedule (saturate injectivity))`. In the MAX run it rejects pass 0 **before serialization and Tiger extraction**. Successful compilations run three passes with fresh graphs, collecting observations again for each pass.

The retained conflict is `(ObservationConflict 5 2 1 true false)`: seed 5 is this comparison, seed 2 is this branch's false literal, and point 1 has region input `[StateV, 0, MAX, 2]`. The [control review](findings/corrected-control-evidence-review.md) checks the same witness in actual Manual and Injective runs.

`EvalBoolAt` remains unmarked: agreement at one input does not imply equal expressions or equal points. Multiplication is also not being declared injective. The arithmetic truth comes from concrete evaluation; the encoding checks whether later e-graph equalities respect it. It allows the bad union to occur, then detects the conflict. Identifying the responsible multiplication rules required separate inspection and removal experiments.

## What EggCC already checked, and what we added

Baseline EggCC already had a [hand-written constant-conflict guard](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/fresh-engine-control/source/dag_in_context/src/type_analysis.egg). It checks equal `Const` applications with different values when a matched constant has an `InFunc` context. It also had interpreter-based tests and CLI support for recording source and optimized execution results.

This bad equality escapes the in-graph constant guard. It is branch-local (`InIf`), and the optimizer merges a comparison with `Const(false)` without deriving `Const(true)` in that class. Observing that the comparison returns true at MAX does not itself union the Expr with a true constant. Its observed result lives in the separate `ObservationValue` sort.

The new coverage therefore comes from **seeding concrete observations**. We implemented two equivalent ways to audit them:

| Checker | Condition that triggers rejection | Origin |
| --- | --- | --- |
| Manual | Two `ObservationSeed` rows have the same committed Expr and point, but true/false payloads. | New hand-written witness and panic rules in this harness. |
| Injective | Equal `ObservedBool` applications have unequal primitive payloads. | Generic rule generated by the `:injective` annotation. |

Both modes record conflict witnesses before their audit. The experiment's Manual checker was not an existing EggCC observation mechanism, and Injective does not replace the baseline constant guard. Adding the observation facts **without either audit** still produces the wrong output. This common-seed control shows that observations alone, or the old guard, do not already reject the case. The [reference](reference.md#existing-and-experimental-checks) contains the exact old and new rules.

## From the conflict to a rule change

The conflict says that the graph equated expressions which disagree at the same feasible point. It does not name which rewrite caused that equality. Graph inspection and exported-graph experiments narrowed the cause to the two multiplication-sign rules above. Removing only the strictly positive rule is insufficient: the nonnegative rule independently supports the wrong conclusion.

We built a diagnostic compiler with **both rule blocks deleted**, then ran the same MAX program:

| Configuration | Result on MAX |
| --- | --- |
| Original rules, observer off | Completes; source `true`, optimized `false`. |
| Original rules, observations but no audit | Completes with the same wrong `false`. |
| Original rules, Manual audit | Rejects the conflicting observations in pass 0. |
| Original rules, Injective audit | Rejects the conflicting wrappers in pass 0. |
| Both rules deleted, any of these four modes | Completes all three passes; source and optimized result are `true`. |

The [rule reference](reference.md#eggcc-rule-change) shows the literal before/after source. This actual source-modified release confirms the localization; an additional nearby-control matrix records 21 successful output matches and three expected unsupported-grammar rejections. The original source was restored afterward. A proper repair needs justified overflow-aware bounds or removal of unsafe deductions. The experiment implements the deletion control, not a replacement analysis or a production fix.

## Contribution and limits

The Boolean payload test is deliberately small. It exercises the primitive-mismatch part of injectivity, not cancellation of equality-sort children or a richer structural invariant. A manual checker is equally capable of detecting this conflict. The encoding's contribution here is expressing the observation-consistency contract through a constructor annotation and ordinary generated rules.

The compiler example is subtle because a branch-local unsound equality must be connected to a concrete counterexample in the **same graph, type, context and observation point**. That connection lets congruence expose a real miscompile that the existing constant guard misses. The prototype handles supported pure expressions on reached paths; it does not validate arbitrary calls, loops, memory or every possible input.

This is a compact correctness case study for the selected baseline. It establishes neither unique bug-finding power nor a compiler speedup, a current-upstream bug, or automatic rule repair. A stronger claim about structural injectivity or enabled optimizations would need an additional example. The [candidate map](candidate-map.md) records unexplored leads. [Descriptive costs and their host/protocol limitations](study-record.md#repeated-descriptive-cost-observations), [validation and known compiler gate failures](study-record.md#validation-and-limitations), and [reproduction instructions](rerun.md) remain separate from this explanation.

## Separate encoding exercise: querying before the bad merge

The same initialized graph also exercises the remaining-child disequality query:

```text
true ≠ false ⇒ ObservedBool(true) ≠ ObservedBool(false)
             ⇒ EvalBoolAt(e,1) ≠ EvalBoolAt(z,1)
             ⇒ e ≠ z, because the point arguments are equal.
```

This query exposes through the graph a difference the concrete observer already knew. It is **not needed for bug detection**, does not prevent a later union, and is disabled in the timed arms. On identical initialized-graph replays the extended query finds the MAX witness while the old query, with only unary reverse inference, does not; both are unknown for a fresh x=1 graph. The [reference](reference.md#optional-pre-schedule-query) gives the law and replay scope. This is an additional engine-coverage demonstration, rather than another step required by the checker above.
