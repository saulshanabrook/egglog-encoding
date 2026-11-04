# Pointwise observation proposal: semantic review

**Conditional consent for a narrow diagnostic prototype.** The proposed law is sound; no additional encoding axiom or query change is needed. The implementation must enforce feasible points, actual region arguments and typed observations. Detached `interpret_expr` calls alone do not establish those premises. This review authorizes no implementation and claims no executed observer, speedup, all-input guarantee or unique advantage over a manual consistency assertion.

Reviewed the “Alternative next slice: pointwise observation consistency” section of `findings/compiler.md` (SHA-256 `aae144864ca34eeb635f26316df50a37d6776b9334a0a25f0ca1fa2b2696b4d4`) against its cited local APIs at EggCC HEAD `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. Compiler evidence and C2 remain owned by the compiler circle. This was read-only proposal/source review; no builds, tests, experiments, or source edits ran.

## Why the invariant works

For one feasible observation point `p`, let `eval(e,p)` be the deterministic boolean result of an eligible expression under that point's concrete region input. A valid compiler equality between two eligible expressions whose contexts are both satisfied at `p` must preserve that result. Seeding

```text
EvalBoolAt(e,p) = ObservedBool(v)
EvalBoolAt(c,p) = ObservedBool(w)
```

is therefore consistent only if an optimizer equality `e = c` implies `v = w`. `EvalBoolAt` needs ordinary congruence, so it stays **unmarked**. `ObservedBool(bool)` represents exact immutable boolean data; marking it injective correctly rejects a merged true/false payload. Equal observed results must never cancel to equal Exprs or points. There are no asserted Expr disequalities, global concrete-input substitutions or runtime-nonalias claims. Separate observed Int/Bool sorts are appropriate if the prototype later grows; constructor tags supply no implicit disjointness.

The relevant equality contract is agreement at this feasible point, not global equality of contextual functions on arbitrary arguments. In particular, evaluating a contextual Expr in isolation is not evidence that its context is feasible. New point tokens must remain opaque and distinct across differing root inputs, region invocations, contexts and passes. Preserve the external token-to-input/context/type record; do not derive identity solely from an e-class ID that optimizer unions can change.

## Concrete implementation conditions

1. **Collect the actual selected path and region input.** `interpreter.rs:421–429` evaluates the If predicate under the parent argument, evaluates its input, then evaluates only the selected arm with that new input. `children_same_scope` at `schema_helpers.rs:231` deliberately omits If arms and gives no concrete argument for them. A generic recursive child walk, or passing the root input into every nested fragment, is unsound. The observer must follow the same region transition and record it. Never observe a dead arm merely because its tree exists.

2. **Do not confuse detached evaluation with an execution trace.** The public helper at `interpreter.rs:154` creates a fresh VM/cache/memory/log for each call. The interpreter explicitly relies on Rc sharing (`:139`); region entry resets its cache (`:358–366`), and expression memoization uses Rc pointers (`:370`). Constants and Args ignore their stored context/type during evaluation (`:374`, `:453`). Thus the helper checks neither feasibility nor matching argument types. It is usable for a recursively checked effect-free fragment under a previously established region input. Independently evaluating effectful plumbing can replay prints or lose state/cache relationships. For the first slice, either prove the relevant parent predicate/input evaluation is within the supported pure projection/tuple fragment, rejecting unsupported coverage, or implement a narrowly scoped one-execution trace hook. Do not claim that calls to the public helper already provide the latter. A walker cache must include region-point identity, rather than globally memoizing only an Rc pointer.

3. **Enforce a positive grammar and type check.** Begin with only the minimized program's needed integer constants/arguments/projections/tuples, wrapping multiplication, signed less-than, boolean results and selected If transitions; expand explicitly if needed. The interpreter's wrapping Add/Sub/Mul at `:239–246` support an arithmetic extension, but generic purity does not prove totality. Exclude Div, shifts, Neg/Abs endpoint cases, floats, symbolic values, calls, loops and memory until separately justified. Validate tuple bounds and input/Expr types. The observed Expr must return Bool; its matching literal Const must carry the exact region argument type/context. A non-bool value or malformed point is rejected/skipped coverage, not a detected compiler bug.

4. **Use the same contextual tree and printer state.** `build_program` at `lib.rs:209–267` inlines, adds contexts, and then uses one TreeToEgglog and term cache. Observation Expr references and literal counterparts must be printed through those same instances. Avoid reconstructing a lookalike tree in a separate cache. Every pass creates a new build/e-graph (`:943–962`); regenerate scoped observations/tokens for that actual pre-pass tree. Never reuse expression IDs, region arguments or point IDs from the preceding extracted tree.

5. **Keep audit and pipeline claims precise.** Run the injectivity audit after the real source schedule, after rebuilding, and before `serialized_egraph` consumes the e-graph (`lib.rs:960–965`). The finite seeds require no generative saturation. Make any observer-specific rule scheduling explicit, with the manual audit at the identical boundary. This validates selected observed value merges in the e-graph. It does not validate Tiger extraction, reconstruction, frontend conversion, or every expression; those require the separate full-pipeline source/result checks. An earlier primitive panic remains an earlier compiler failure, not an observer detection.

## Equivalent manual control and attribution

The manual oracle is straightforward: retain the same observations as `(Expr, point, primitive_bool)` rows, canonicalize Expr endpoints after the pass, and reject different booleans at the same committed Expr class and exact point token. It should find the same conflicting observation pair as the injective-wrapper audit. This is an equivalent dynamic consistency assertion, not a deliberately weaker baseline.

Keep observation collection, matching literal construction, Expr references, added graph nodes, pass schedule and audit boundary common. A particularly clear comparison uses common EvalBoolAt/ObservedBool seeds in both diagnostic arms, leaves ObservedBool unmarked for the manual arm, and supplies the manual observation rows to both; the injective arm adds only the annotation/audit. Archive the conflicting expression/point/value witness in each. If row-based seeding is chosen instead, document the representation difference rather than calling graph inputs identical.

Adding literal Expr nodes can itself expose optimizer rules or the existing error guard, even without an Expr union in the seeds. Record that possibility: default Off reproduces the baseline mismatch, and a common-seeds/no-audit observation should identify the same wrong merge without a new earlier guard failure. Such a receipt can share the manual arm's pre-audit boundary; it need not add a performance arm. The existing guard in `type_analysis.egg:41–46` requires `ctx1 = InFunc(name)`, so a genuinely feasible branch-local point can extend its detection coverage. Actual incremental coverage still requires the full-host comparison showing that the old guard did not already fire on the common seeded graph. Neither observer has unique power over `dynamicassert` or an equivalent manual conflict relation. This consistency detector itself needs no remaining-child inference; the following optional probe exercises E1 separately.

## Additional E1 pre-pass probe

The coordinator's proposed extension is **sound within the same point contract**. After observation initialization, but before the optimization schedule, the query can follow this path:

```text
EvalBoolAt(test,p) = ObservedBool(true)
EvalBoolAt(false_literal,p) = ObservedBool(false)
ObservedBool's marked primitive payload gives the result-pair disequality
unmarked binary reverse congruence, with common sibling p, gives:
known-disequal?(test,false_literal).
```

This is a counterexample to those Exprs being equivalent functions over their common valid domain: they disagree at one feasible input. It is **not** a claim that they have unequal runtime values at every input. It supplies no NoAlias premise and should not be materialized as a new global compiler fact. The query remains read-only; the point/value observation contract provides its semantic justification.

Conditions and decisive controls:

- ObservationPoint must be a primitive token or an ordinary **unionable** equality sort for this E1 fragment. A relation-generated non-unionable point sort makes the constructor ineligible. Opaque point identities must have no normalizing/refinement unions that collapse distinct evaluations.
- Run the diagnostic after the common finite seeds are committed and before the optimizer can perform the wrong union. Do not schedule injectivity on an already inconsistent result class first and then present the abort as a pre-pass query result. Preserve an explicit before-schedule receipt and a separate after-schedule consistency-audit receipt.
- In a graph seeded only for MAX, the reached comparison versus its same-context false literal should be known-disequal. In a **fresh graph seeded only for x=1**, both observed booleans are false, so this pair should remain unknown. If observations for MAX and x=1 coexist, the MAX counterexample can legitimately establish the Expr pair's inequivalence even though the two agree at x=1; `known-disequal?` has no point argument and its result is not “unequal at this selected input.”
- True and false results at **different** point tokens alone must not establish this Expr pair's disequality: the reverse equal-sibling premise is missing. Test this in an otherwise witness-free graph. Dead/unreached contexts produce no observation point and therefore no path. Wrong type/context/input records must be rejected before query construction, as above.
- Use the same seeded source with the prior unary-only query and the E1 query, holding all annotations/initialization fixed. The former should remain unknown and the latter succeed; validate this rather than inferring a version result from inspection. The manual pre-pass equivalent simply finds different recorded bools for the two Exprs at the same point. It needs no injectivity or query implementation.
- Unknown is a normal diagnostic outcome, never equality or an observer error. A positive-only `(check ...)` must not make supported nonconflicting inputs abort merely because the probe is unknown. Ordinary mode remains required; a rule-based probe still needs `:naive`.

This would connect E1 to a real source-derived contextual counterexample while leaving its role honest: improved read-only witness coverage, not new detection capability. After the bad union the graph is already inconsistent with the observations; the marked-wrapper/manual audit detects that conflict independently. A query of a collapsed self-pair at that point is not the intended demonstration. Full-host identity/path/plumbing controls remain necessary; a replay can show the algebraic coverage delta only.

## Smallest acceptable vertical slice and controls

Use the reduced valid `mul-minimal-max.bril`, with x=1 and unreached-branch x=0/-1 controls, one entry function and explicit context-enabled configuration. Start with the one reached branch comparison and its matching false literal. A full-optimizer Rust test can establish this first, followed by actual CLI configuration/input plumbing and a three-pass receipt before reporting full-host support. Keep the native extraction/reconstruction path for accepted controls.

Required observations and controls:

- **Baseline and positive:** Off completes with the already reproduced true→false result. The common-seed manual and injective arms reject the same invalid branch comparison merge before Tiger, with expected point/input/type/context and true/false payloads. Distinguish the new diagnostic from the existing Const guard.
- **Correct feasible values:** x=1 passes both audits and finishes with matching non-null source/optimized output. A real source-rule-corrected compiler variant should also pass on MAX and produce true; an exported filtered replay alone does not establish that full-host control.
- **Impossible/dead:** x=0/-1 have zero recorded observations for the positive arm, pass both audits, and retain correct full-pipeline output. Add a syntactically present contradictory/dead branch and explicitly check it supplies no point; mere absence of a panic is insufficient.
- **Distinct points/inputs:** the same Expr may legitimately return true and false at two different concrete inputs. Seed those valid observations under separate tokens in one focused test and require both audits to accept. Also check context/region tokens cannot be conflated. Reusing the wrong root/region input must be rejected by the collector's identity/type contract.
- **Types and unsupported grammar:** a non-bool observed result, wrong region argument type, wrong matching Const metadata, and unsupported call/loop/memory forms are rejected or explicitly skipped before semantic assertions are generated. These are observer validation controls, not baseline compiler bugs.
- **No semantic backflow:** inspect generated initialization for no observation-induced Expr unions or Expr disequalities; merging equal observed values at different points must not merge those points or their Expr arguments. Only Eval results are unioned with ObservedBool payloads.

Report pass-local supported/skipped point counts and diagnostic graph growth. A hand-seeded egglog example or exported-program replay can validate the annotation algebra, but not the host path collector, exact contextual/tree identity, CLI argument plumbing, real pass hook or final executable behavior. The useful claim, if these gates pass, is “a restricted concrete observation contract detects this real silent branch-local merge that the prior top-level guard missed.” It is not a speedup, an all-input proof or general contextual Expr injectivity.

## Review command/source record

Commands ran from `/Users/saul/p/egglog-encoding` for proposal reads and `/Users/saul/p/wt/eggcc/encoding-impact` for the cited source reads. Read `findings/compiler.md`, searched the goal's planning/findings for `observation|EvalBoolAt|ObservedBool|TreeToEgglog|pointwise`, and read `planning/consumers.md:12–70`. Targeted source commands were `sed -n` on interpreter ranges `120,190`, `235,275`, `350,392`, `390,475`; DAG lib ranges `209,300`, `300,335`, `925,1030`; schema_helpers `220,290`; type_analysis `35,55`; plus `rg -n 'Expr::If|Expr::Const|Expr::Arg|Expr::Function|eval_cache' dag_in_context/src/interpreter.rs` and `git rev-parse HEAD`. All succeeded; no application modules were imported/executed. SHA-256 of those four source files at review: interpreter `dd991459c2baa77f52ba03a0533147c4b134a2da0ed343f105cb049e415f0491`; schema_helpers `5de15f1b5868d5af9c5949ca19019ba8320eb73bd7b7f258ec4259b8ded003de`; DAG lib `4bb63364320fd1079870d3326c11f7b13113f5d965cb3c3fe6f91a6949910e64`; type_analysis `9924928fa7927189c36f0b65b1cd68d5914850b7fc9e6cfe00f118e39a7c81de`.
