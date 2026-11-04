# Injectivity, disequality and the EggCC observation checker

This reference describes the implementation used by the [case-study explanation](report.md). The encoding workspace is based on `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`, with the recorded E1 and harness patches; EggCC is based on `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`, with the observation patch. Exact source/binary identities and commands are in [rerun.md](rerun.md).

## Mathematical laws

The letters denote values of compatible sorts; each occurrence of `f` is the same constructor.

| Law | Inference | Requires `:injective`? |
| --- | --- | --- |
| Congruence | `(∀i. aᵢ = bᵢ) ⇒ f(a₀,…,aₙ₋₁) = f(b₀,…,bₙ₋₁)` | No |
| Cancellation | `f(a₀,…,aₙ₋₁) = f(b₀,…,bₙ₋₁) ⇒ (∀i. aᵢ = bᵢ)` | Yes |
| Forward disequality | `(∃i. aᵢ ≠ bᵢ) ⇒ f(a₀,…,aₙ₋₁) ≠ f(b₀,…,bₙ₋₁)` | Yes |
| Remaining-child disequality at position k | `f(a₀,…,aₙ₋₁) ≠ f(b₀,…,bₙ₋₁) ∧ (∀j≠k. aⱼ = bⱼ) ⇒ aₖ ≠ bₖ` | No |

Remaining-child disequality is congruence's contrapositive. In the unary case there are no sibling premises, so `f(a) ≠ f(b) ⇒ a ≠ b` holds even for an unmarked constructor. In the binary case, parent disequality alone gives `a ≠ c OR b ≠ d`; neither particular child difference follows without further information. Different constructor names imply no disjointness.

## Injectivity declaration and generated rules

```lisp
(constructor F (Term i64) Term :injective)
(run-schedule (saturate injectivity))
```

`:injective` is accepted on constructors and datatype variants. The extension clears the annotation before core desugaring and adds ordinary rules to the shared `injectivity` ruleset. For this signature their effects are:

```text
F(a,n) = F(b,m)              ⇒ union(a,b)
F(a,n) = F(b,m) ∧ n ≠ m      ⇒ panic
```

Equality-sort fields are unioned; primitive fields use native inequality and panic if inconsistent. No primitive-disequality relation is needed. Rules include subsumed rows. Containers and non-unionable equality-sort arguments are rejected for marked constructors. The annotation also records constructor-name metadata for structural queries, not derived value pairs.

Implementation: [injectivity.rs](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/injectivity.rs). Cancellation runs only when scheduled. Saturating it can propagate unions through successive marked layers.

## Asserted disequality

`(disequal a b)` is an action on values of the same unionable equality sort. Primitive operands use native `!=` instead. The graph selects one assertion layout:

| Layout | Representation of `a ≠ b` | Contradiction |
| --- | --- | --- |
| NE relation, CLI `nee` | Store ordered `NE_S(a,b)`; read queries check both orientations. | Canonicalization gives `NE_S(x,x)`. |
| Equality embedding, CLI `ee` | `union(Eq_S(a,b), F)` in a private truth sort. | Private normalization equates `T` with `F`. |

Both layouts use ordinary tables and rebuilding. Neither prevents a later union. `(check-contradiction)` saturates the private disequality rules and succeeds when a contradiction is present; it does not run `injectivity`.

For completeness, the equality embedding's private rules, with right-hand equality denoting union, are:

```text
Eq_S(x,y) = T                 ⇒ x = y
Eq_S(x,y) = F                 ⇒ Eq_S(y,x) = F
Eq_Truth(Eq_S(x,y),F) = F      ⇒ x = y
Eq_S(x,y) = F                 ⇒ Eq_S(x,x) = T
Eq_S(x,y) = F                 ⇒ Eq_S(y,y) = T
```

The implementation installs representation support lazily. The EggCC observation experiment seeds observation-result equalities and uses native Boolean differences; it does not assert Expr disequalities through either layout.

## The read-only `known-disequal?` query

```lisp
(check (known-disequal? a b))
```

The operands must have the same unionable equality sort. The predicate returns Unit when it finds a finite witness and is undefined otherwise. Undefined means unknown, not equal. Rule-body consumers require `:naive`, because the predicate reads tables beyond explicit body atoms.

The witness search combines stored disequalities, marked forward disequality and remaining-child reverse congruence. A primitive mismatch is checked natively. It reads existing committed rows, including subsumed rows; a per-call typed queue, visited-pair set and transient parent index follow possible witnesses. It creates no constructor applications, unions, persistent derived-pair relation or persistent query cache. Observation rows and explicitly asserted constraints still use storage.

The added remaining-child fragment supports scalar constructor tables with unionable output and focused argument; all siblings must be primitive or unionable equality sorts. Containers, custom function tables, direct primitive query operands and term/proof-mode queries are outside this fragment. Private disequality representation constructors are excluded from reverse indexing.

The query does not run injectivity or arbitrary joint schedule closure. Committed sibling equalities or parent witnesses may make a later query succeed, so consumers rerun after changes. `(check-contradiction)` closes only its private normalization. The search is incomplete: even unequal `T(a,k,a)` and `T(b,k,b)` alone leave `a ≠ b` unknown, because two unresolved positions remain. No cost reduction or unrestricted completeness claim follows from avoiding stored derived pairs.

Implementation and further details: [disequality.rs](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs), [reviewed encoding findings](findings/encoding.md), and the [mathematical example](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/tests/injectivity/injectivity-disequality.egg).

## EggCC observation declarations and modes

The implementation in [observations.rs](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/observations.rs:561) uses:

```lisp
(sort ObservationValue)
(constructor ObservedBool (bool) ObservationValue :injective)
(constructor EvalBoolAt (Expr i64) ObservationValue)
(relation ObservationSeed (i64 Expr i64 bool))
```

The `:injective` annotation appears only in Injective mode. The fields of `ObservationSeed` are seed identity, Expr, point token and observed Boolean. A feasible observation adds `union(EvalBoolAt(e,p), ObservedBool(v))`. `Expr` and `EvalBoolAt` stay unmarked in every mode.

| Mode | Observations | Consistency audit after the source schedule |
| --- | --- | --- |
| Off | None | None |
| Common seed | Same logical seeds and unmarked Boolean wrapper | None |
| Manual | Same logical seeds and unmarked Boolean wrapper | Reject true/false observations for the same committed Expr and point. |
| Injective | Same logical seeds; Boolean wrapper marked | Saturate `injectivity`; equal wrappers with unequal primitives panic. |

The implementation also records conflict witnesses. Manual and Injective are equivalent consistency checks for these observations, with the annotation/representation difference retained. Auditing occurs before serialization/Tiger extraction. The observer supports a bounded pure grammar and actual feasible contexts, not arbitrary effects, calls, loops, floats or division. Its restricted walker cross-checks pure Boolean results with the existing `interpret_expr` helper after validating the fragment.

## Existing and experimental checks

The selected baseline's [type_analysis.egg](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/fresh-engine-control/source/dag_in_context/src/type_analysis.egg) contains this literal rule in `error-checking`:

```lisp
(rule ((= (Const c1 ty1 ctx1) (Const c2 ty2 ctx2))
       (= ctx1 (InFunc name))
       (!= c1 c2))
      ((panic "Unsoundness detected: const values differ at top level"))
      :ruleset error-checking)
```

The baseline schedules `error-checking` from its [schedule.rs](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/fresh-engine-control/source/dag_in_context/src/schedule.rs). This guard requires a pair of conflicting `Const` expressions and an `InFunc` context. It is not a general check of concrete evaluations in branch contexts. Baseline [interpreter-based test checks](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/fresh-engine-control/source/dag_in_context/src/lib.rs) and [CLI interpretation fields](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/fresh-engine-control/source/src/util.rs) also predate this experiment.

The following literal rules in [observations.rs](/Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/observations.rs:571) were added for this experiment:

```lisp
(relation ObservationSeed (i64 Expr i64 bool))
(relation ObservationConflict (i64 i64 i64 bool bool))
(ruleset observation-witness)
(rule ((ObservationSeed a e p true) (ObservationSeed b e p false))
      ((ObservationConflict a b p true false)) :ruleset observation-witness)
(ruleset observation-manual-audit)
(rule ((ObservationConflict a b p true false))
      ((panic "observation-manual-audit: conflicting feasible Bool observations"))
      :ruleset observation-manual-audit)
```

All enabled modes materialize witness rows before their selected audit. Manual runs `observation-manual-audit`; Injective saturates `injectivity` instead. The latter's primitive-argument rule rejects the same observation conflict. The harness seeds both true and false contextual literal nodes, but does not union a concretely true Expr with `Const(true)`; it unions only `EvalBoolAt` results with wrappers. Common-seed execution retains the observations without either rejecting audit and still miscompiles MAX.

## Optional pre-schedule query

For the example's comparison `e`, same-context false literal `z` and shared point `p`, the seeded results support:

```text
true ≠ false
    ⇒ ObservedBool(true) ≠ ObservedBool(false)        [marked forward disequality]
    ⇒ EvalBoolAt(e,p) ≠ EvalBoolAt(z,p)              [seeded result equalities]
    ⇒ e ≠ z                                        [remaining-child reverse congruence]
```

The last inference uses equality of the second arguments; `EvalBoolAt` is unmarked. With distinct points this route provides no Expr-disequality conclusion. The actual probe is emitted only for reached `LessThan` expressions whose left operand is `Mul`. It runs before the source schedule and is disabled in cost arms. It is not a consistency audit and does not prohibit later unions.

On identical exported initialization files, [replay results](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/initialized-replay/results.json) give MAX unknown with the old query, whose reverse inference was unary-only, and known with the extension; fresh x=1 is unknown on both. An actual new-engine diagnostic also exercises the pre-schedule query. The old/new comparison is initialization-only replay, not a full old-query compiler endpoint. Different-point and other fragment limits are covered by the [encoding findings](findings/encoding.md).

## EggCC rule change

The two deleted blocks occur in the original [interval_analysis.egg](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/recovery/interval-original.egg). These are literal source excerpts:

```lisp
; positive * positive is positive
(rule (
        (= lhs (Bop (Mul) x y))
        (= lo-x (either-unwrap-left (maybe-unwrap (lo-bound x))))
        (= lo-y (either-unwrap-left (maybe-unwrap (lo-bound y))))
        (> lo-x 0)
        (> lo-y 0)
      )
      ((set (lo-bound lhs) (maybe-some (either-left 1))))
      :ruleset interval-analysis)

; non-negative * non-negative is non-negative
(rule (
        (= lhs (Bop (Mul) x y))
        (= lo-x (either-unwrap-left (maybe-unwrap (lo-bound x))))
        (= lo-y (either-unwrap-left (maybe-unwrap (lo-bound y))))
        (>= lo-x 0)
        (>= lo-y 0)
      )
      ((set (lo-bound lhs) (maybe-some (either-left 0))))
      :ruleset interval-analysis)
```

`lo-bound` supplies a lower bound; the `maybe`/`either` wrappers select an available integer bound. Both rules infer a product bound from operand signs without checking signed overflow.

The surrounding original rules connect these bounds to an expression equality. The following descriptions are schematic; line numbers refer to the same frozen original interval source:

| Source | Condition and effect |
| --- | --- |
| Lines 328–342, true-branch context | In the context where `0 < x` is true, set the lower bound of `x` to `1`. |
| Lines 213–219, less-than upper bound | Set `hi(a < b)` to `bool-<(lo(a), hi(b))` when both integer bounds are available. |
| Lines 78–85, Boolean upper bound | If `hi(e)` is false, union `e` with a `false` constant of the same type and context. |

**After the diagnostic change, both blocks are absent.** The [modified interval source](../../benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/recovery/interval-corrected-expected.egg) is otherwise unchanged. No replacement overflow-safe rule was implemented. Other arithmetic rules remain. The actual modified release passes the MAX oracle with Off, common seed, Manual and Injective; this is a scoped causal control for the miscompile, not a general soundness result for the remaining analysis.

The [control review](findings/corrected-control-evidence-review.md) binds the executed source variants and verified restoration. The modified package also retains an older, inactive cfg(test) clone expression; the final original package uses its validated borrow-only repair. Exact source differences are recorded in [rerun.md](rerun.md).
