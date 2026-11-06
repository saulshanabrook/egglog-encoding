# Task P: nested application join drivers

## Approach and semantic constraint

The original planner ignores an entire application atom if one of its operands
is an application. The implementation will expose the application's recursive
reads as independent join drivers. Once a nested operand is determined and its
value is held, its enclosing application can also drive a join. All comparisons
of determined values use the supplied congruence relation; `min` remains excluded.

This deliberately avoids assuming that liveness means an exact spelling is
stored. `exprHoldsWith` requires recursive liveness, but `liveWith` can accept an
unstored congruent spelling. The suggested proof's assertion that every nested
instance is held is therefore false. The existing equivalence lemmas also cover
arbitrary `cl` and arbitrary finite databases, without index invariants. Using
required recursive reads preserves that stronger contract.

The nested plans read the live `FView` rows, including their partially known
children, rather than destructuring `HasChild` columns. Thus a bound `c0` filters
the nested driver's rows modulo `cl`; binding `c1` then filters them further
before `e` is proposed. The enclosing row becomes a driver when its application
operands evaluate to held terms. Unsupported combinations still fail the final
pattern test. This is conservative narrowing, not an assumption that a partial
structural match exactly decides an outer row.

## Statement and interface changes

All existing public theorem statements in `Interp.lean` are unchanged
(checked against `HEAD`, including attributed `csimp` theorems), including
`joinCands_mem`, `matchJoin_eq`, `matchQueryJoin_eq`,
`matchQueryJoin_eq_matchQuery`, `matchQueryWith_eq_join`, and
`matchQuery_eq_join`. Every paper assertion keeps its name and statement.

- `Egglog.joinPlan` and `Egglog.Relational.joinPlan` now return `List JoinAtom`
  instead of `Option JoinAtom`: one pattern can contribute multiple read plans.
- Private `joinKnown_holds` replaces its `joinDrivable es = true` premise with
  `joinReady ρ es = true`. This supplies determined application values.
- Private `joinConsistent_of_congrTuple` drops its `joinDrivable` premise; it
  now works for any evaluated operand list.
- Private `joinPlan_ctor` is replaced by `joinAtomPlan_ctor`, describing one
  ready application read with an explicit original-pattern variable list. Its
  premise uses `joinAtomPlan`, and its first conclusion gives readiness.
- Added recursive planning/readiness definitions and private evaluation
  extension / recursive-read completeness lemmas. No existing definition other
  than the two `joinPlan` functions changes type.

No imports changed. No `Spec/`, aggregate-module, paper, test, compiler, or script
edits. Existing unrelated worktree changes remain untouched.

## Validation

- `source /tmp/proof-port-env.sh` supplies the required launcher shim and PATH.
- `lake build EgglogSemantics EgglogPaper difftest`: passed in **34.137 s**,
  including every `assert_no_sorry`; log `/tmp/port-P-build-initial.log`.
  Final rebuild after formatting: **34.390 s**, passed; log
  `/tmp/port-P-build-final.log`. The changed modules retain only the pre-existing
  unused `d` warning on `Query.decided`.
- Focused checks in `/tmp/PortPRegression.lean`: passed using
  `lake env lean /tmp/PortPRegression.lean`. Cover nested `c1`/`e` narrowing,
  general/relational agreement, repeated variables, wrong arity, subsumed nested
  reads, determined application operands, rejection of `min`, an arbitrary empty
  relation, and an unstored congruent spelling.
- The last case stores `Outer(F(B), 7)` and asserts `A = B`. `F(A)` is absent from
  `terms` but live, and the nested query still retains `x = A, z = 7`. This is a
  concrete counterexample to the suggested held-instance premise, not a new
  semantic discrepancy.
- Axiom audits of the five completeness/equivalence/`csimp` lemmas report only
  `propext`, `Classical.choice`, and `Quot.sound`; no new axioms or sorry proofs.
- `.lake/build/bin/difftest congruence 64 --views=indexed`: **104 tested,
  0 failures, 0 outside domain**, exit 0, **196.557 s** (3 min 16.6 s).
  Log and timing: `/tmp/port-P-congruence.{log,time}`.
- `.lake/build/bin/difftest /tmp/port-P-compiled compiled --views=indexed --phased`:
  **104 compiled cases written**, exit 0, **302.338 s** (5 min 2.3 s).
  Log and timing: `/tmp/port-P-compiled.{log,time}`. Both corpus runs were launched
  concurrently and overlapped the final rebuild. Because this wall time is near
  the upper end of the requested few minutes, the export was measured again
  without the other validation processes: **104 cases, exit 0, 315.842 s**
  (5 min 15.8 s), `/tmp/port-P-compiled-solo.{log,time}`. The measured runtime is
  therefore about five minutes, not two or three. `rand-19` itself took about
  **54.7 s** between its program and expected-result file writes in this run.
  Verified 104 matching `.egg`/`.expected` pairs and nonempty expected files.
- `git diff --check`: passed. No heartbeat increases, `sorry`, `axiom`, or
  `native_decide` added.

## Outcome

Both runtimes now drive the previously Cartesian nested variables. Completeness
and both compiled matcher equivalences retain their original unconditional
statements. No new semantic discrepancy was found; the false held-instance
premise discussed above is handled conservatively. No import changes are needed
in `EgglogSemantics.lean` or `EgglogPaper.lean`.
