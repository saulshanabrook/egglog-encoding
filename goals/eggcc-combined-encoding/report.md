# Checking nested EggCC types with injectivity and disequality

This experiment connects injectivity and disequality to one existing EggCC type check. A difference between two base types propagates through pointer and tuple constructors until it reaches the compiler's existing mismatch diagnostic. The comparison asks what the generic encoding can express; the current checker is expected to reject the same malformed types.

## The compiler obligation

EggCC represents types as equality-sort values. A function's declared output creates `ExpectType(body,expected,message)`; type analysis produces `HasType(body,actual)`. The existing error rule is:

```lisp
(rule ((ExpectType e expected msg)
       (HasType e actual)
       (!= expected actual))
      ((panic "type mismatch- check RUST_LOG=info for expressions that mismatched"))
      :ruleset error-checking)
```

The rule binds both types and emits a fixed mismatch diagnostic. It runs after type helpers normalize equivalent representations. At that boundary, different IDs represent different supported ground types.

The main internal fixture is a function returning its argument:

```text
input / body's actual type = (Int, Pointer(Int),  State)
declared output type       = (Int, Pointer(Bool), State)
```

The fixture uses real `Function` and `Arg` nodes. `Function` creates the expectation, and `Arg` creates the actual type; the test does not assert the final parent disequality. This is deliberately malformed internal compiler IR. EggCC's source type checker already rejects an analogous ill-typed source program, so this fixture cannot establish a newly discovered compiler bug.

## One difference, propagated through the type structure

Write `P(x)` for `PointerT(x)`, and `[a,b,c]` for the corresponding `TCons`/`TNil` list. The actual inference is:

```text
IntT ≠ BoolT
  ⇒ P(IntT) ≠ P(BoolT)
  ⇒ [P(IntT),StateT] ≠ [P(BoolT),StateT]
  ⇒ [IntT,P(IntT),StateT] ≠ [IntT,P(BoolT),StateT]
  ⇒ TupleT([IntT,P(IntT),StateT])
       ≠ TupleT([IntT,P(BoolT),StateT])
  ⇒ the ExpectType mismatch diagnostic
```

The first fact is a separate type-tag axiom: `IntT` and `BoolT` denote different types. Injectivity alone does not make different constructors disjoint. The subsequent steps use injectivity of `PointerT`, `TCons` and `TupleT`. For `TCons(a,xs)`, either a differing head **or** a differing tail suffices to distinguish two lists. Here, the pointer difference first distinguishes a head, then a surrounding tail. The equal first entry and equal state entry remain equal.

Every child in this chain is an equality-sort value. There is no primitive Boolean mismatch at the end of an injective wrapper. This is the richer interaction compared with the [previous observation checker](../eggcc-encoding-impact/report.md): the disequality query and the structural annotations contribute to the same compiler obligation.

## What changes in the rules

The opt-in integration marks the existing free type constructors and supplies the explicit tag laws. It then derives the same diagnostic predicate with a generic query:

```lisp
(rule ((ExpectType body expected message)
       (HasType body actual)
       (StructuralGroundType expected)
       (StructuralGroundType actual)
       (known-disequal? expected actual))
      ((StructuralTypeMismatch expected actual))
      :ruleset structural-type-consume :naive)
```

The existing error rule consumes `StructuralTypeMismatch` in place of its raw-ID guard; its diagnostic action stays in place. The query follows the structural witness without storing all derived parent pairs. This route uses the contrapositive of injectivity. It does not need equal-output cancellation, remaining-child reverse inference or saturation of the generated `injectivity` ruleset.

An equivalent manual checker is a meaningful comparison. It writes recursive rules for pointer, tuple-list and type mismatch, using the same tag laws. For example:

```text
ManualBaseDQ(x,y) ⇒ ManualListDQ(TCons(x,xs),TCons(y,ys))
ManualListDQ(xs,ys) ⇒ ManualListDQ(TCons(x,xs),TCons(y,ys))
```

The encoding packages this structural reasoning behind constructor metadata and the query API. Hand-written rules can express the same result. No additional detection power follows merely from replacing them.

## What the controls must establish

The existing, manual and combined checks report the nested mismatch. With the same input and tag facts, removing the structural annotations removes the composite query witness. Replacing the consumer's structural query with a lookup of explicit Type tag facts also loses the diagnostic's premise: the two outer values both have the `TupleT` tag. In that control the full structural query still knows they differ, but the consumer does not consult it. A direct `Base`-versus-`TupleT` mismatch still reaches the same diagnostic through the tag-only guard.

Neither missing witness means that the malformed function is accepted. A separate fail-closed audit checks every expectation and actual alternative, reporting unsupported or unknown coverage before extraction. Equal types and helper-equivalent types must validate normally. Valid source controls must separately pass through the native compiler and preserve their expected output.

The same policy rejects inconsistent type metadata: a shared tag-consistency guard runs before equal obligations can count as validated. This matters because merging two explicitly distinct tags violates the contract, even if it makes an expected and actual type equal. The [implementation review](findings/type-review.md) records the initial gap, the regression and the narrow repair; it is not a baseline EggCC bug discovery.

The focused tests establish these outcomes on the same internal fixture:

| Check | Nested pointer/tuple mismatch |
| --- | --- |
| Existing raw-ID guard | Existing mismatch diagnostic. |
| Manual structural rules | Same mismatch diagnostic. |
| Combined annotation/query | Same mismatch diagnostic. |
| Structural annotations removed | No composite witness; explicit coverage-unknown failure. |
| Structural query replaced by tag lookup | Tag-only guard has no witness for the two TupleT values; explicit coverage-unknown failure. The full structural query remains available but is not consulted by this guard. |

The DAG target passes **9 tests**. An independent oracle compares Rust's derived equality on ordinary type trees with the existing, manual and combined checks: nine ground shapes × two assertion representations × three modes give 54 matching comparisons. The representations are a not-equal relation (`nee`) and equality embedding (`ee`), described in [the reference](reference.md#assertion-representations). The central contribution controls and selected boundary controls also run under both; other registered shape/coverage subcases run under `nee`. This is a finite tested shape matrix, not an exhaustive type-solver validation.

The native host test passes in all five modes on a valid Bril program that allocates a pointer, passes it through an identity call, loads and prints its value, then frees it. Both source and optimized interpretation produce `7\n`. Ten actual CLI optimize/emit calls also complete all three production passes. Enabled modes check 5, 5 and 4 type obligations in passes 0, 1 and 2. This valid program is a pipeline correctness control; the internal malformed function supplies the feature-contribution result.

The [checkpoint](../../benchmarks/local/eggcc-combined-encoding/consumer/oracle-final/checkpoint.json) binds the final source, 50 intermediate query observations, ten internal consumer outcomes, 54 oracle comparisons and the separate host/CLI receipts. The final change added only oracle test code, so the earlier host/CLI receipts remain bound by an identical production-code closure. The [reproduction guide](reproduction.md) identifies retained tooling failures and diagnostic-only normalized reparses separately from the ten primary CLI runs.

Repository validation retains known baseline failures: both official `make test` runs stop on the same 13 pending snapshots, and strict Clippy checks report the same three source sites. Fresh selected trials reproduce all 13 snapshot bodies exactly in candidate and control; these official gates remain failed. The full candidate DAG suite passes 83 tests, both roles pass formatting, and the default-off public prologue is byte-identical. [The gate receipt](findings/gates.md) records the complete comparison.

## Interpretation and limits

On finite, normalized, consistent free types, the old raw-ID check and the structural check agree. The focused result demonstrates a richer reusable encoding in an existing compiler check. No new baseline bug, optimization or speedup is established. The pointer constructor concerns type descriptions, not pointer alias analysis; unresolved/symbolic types and arbitrary contradictory type graphs are outside this replacement.

Other proposed directions—fixed-split tuple cancellation, scoped branch values and live pointer keys—remain leads with the limits recorded in [the candidate discovery](planning/consumers.md). This positive integration does not establish their feasibility or exhaust those directions. The previous Boolean observation case remains a separate fallback.

The [reference](reference.md) gives the supported grammar, modes and schedule; [reproduction](reproduction.md) holds commands and evidence details. This separation follows Diátaxis's distinction between [explanation](https://diataxis.fr/explanation/) and [reference](https://diataxis.fr/reference/): this document follows the reasoning and its implications; the reference describes the implemented machinery.
