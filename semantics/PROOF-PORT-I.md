# Task I: matching reads `Expr.rows`

## Status

The proof port builds. All 76 scoped proof modules, five of the six scoped tests,
and `EgglogPaper` build, including all 25 unchanged `assert_no_sorry` checks.
The full `lake build EgglogSemantics EgglogPaper` is blocked only by
`Tests/SemanticCong.lean`'s `relational_literal_subsume_agrees`: after translating
its removed lookups to evaluation/rows tests, Lean proves its claim false.
The semantic discrepancy and pending clarification are detailed below.

Validation uses only local `lake build`/`lake env lean` commands with
`source /tmp/proof-port-env.sh`; no Makefile or network checks. The initial
launcher configuration failure was resolved by that supplied shim.

- Full build log: `/tmp/proof-port-i-build-6.log` (1104 jobs; only the marked-literal
  regression fails).
- Successful independent gate: `/tmp/proof-port-i-independent.log` (1067 jobs),
  from `lake build EgglogPaper EgglogSemantics.Proofs.Assignments
  EgglogSemantics.Tests.Examples EgglogSemantics.Tests.SourceProofCorrectness
  EgglogSemantics.Tests.SourceProof EgglogSemantics.Tests.ProofPass
  EgglogSemantics.Tests.SubtermExistence`.
- Both `/tmp/proof-port-i-literal.lean` and
  `/tmp/proof-port-i-literal-rows.lean` pass `lake env lean` and prove the mismatch
  using `decide +kernel`.

Changed 15 scoped Lean files plus this note. Original Lean sources are saved
under `/tmp/proof-port-i-original`, and the task-local diff is
`/tmp/proof-port-i.diff`. Comparing those originals confirms all changed Lean
files are in scope, including unchanged root files and `Proofs/Congruence/`.
Scoped `git diff --check`, added-line whitespace/length checks, and the
proof-construct scan pass. No `sorry`, `axiom`, `native_decide`, or heartbeat
increase was introduced.

`Proofs/Lookup.lean` and `Proofs/InterpLookup.lean` are retained under their
existing module names as the home of evaluation/rows bridges. No root import
change is needed. The removed lookup judgements are not reintroduced;
`Lookup` and `LookupList` survive only as theorem namespaces.

## Statement changes

All theorem names are retained. These are all 20 theorem statement changes
and the one predicate definition change:

1. `Lookup.eval`, `Lookup.exists_cong`, `Lookup.of_eval`, `Lookup.of_agreeOn`,
   `Lookup.mono_live`, and `Lookup.transport`: replace each former
   `Lookup db σ e t` with
   `e.eval σ = some t ∧ ∀ u ∈ e.rows σ, u ∈ db.live`.
2. `LookupList.eval`, `LookupList.of_eval`, `LookupList.of_agreeOn`,
   `LookupList.mono_live`, and `LookupList.transport`: make the corresponding
   replacement with `Expr.evalList es σ = some ts` and live `Expr.rowsList σ es`.
3. `Lookup.lookupWith`, `LookupList.lookupListWith`, `lookupWith_lookup`,
   `lookupListWith_lookup`, and `lookupWith_iff`: semantic evidence is the
   conjunction above; executable evidence is evaluation together with
   `(rows).all (d.liveWith d.closureF) = true`, replacing removed executable
   lookup functions.
4. `Matches.storedCases`: its branch evidence is evaluation plus live rows,
   with the new `Matches` constructors reconstructed from that evidence.
   All original stored witnesses and represented-binding hypotheses remain.
5. Definition `EntryRead` and theorem `patternHolds_entry_of_mem_rows`:
   replace the argument-list lookup evidence with evaluation and live rows.
6. `Egglog.Tests.SemanticCong.min_eval_does_not_imply_lookup`: replace its
   negated lookup conclusion with the negated evaluation/live-rows conjunction.
7. `Egglog.Tests.SemanticCong.relational_literal_subsume_agrees`: replace
   `Relational.lookup ... = some t ∧ lookupWith ... = some t` with
   `e.eval [] = some t ∧ (e.rows []).all (Relational.liveRow d) = true ∧
   (e.rows []).all (d.liveWith d.closureF) = true`. This preserves the old
   agreement assertion; it is the sole remaining failed proof. Its conclusion
   has **not** been changed to disagreement without authorization.

New helpers `Expr.rows_agreeOn`, `Expr.rowsList_agreeOn`, and
`FDatabase.all_liveWith_iff` express environment agreement and the executable
row-liveness bridge. Other changed proofs keep their statements.

## Genuine semantic issue: marked literals

The old `Egglog.Tests.SemanticCong.relational_literal_subsume_agrees` cannot
be restated as agreement of the new executable matchers:

```lean
let t := Term.lit (.int 0)
let d := FDatabase.empty.subsume t
let p := Pattern.expr (.lit (.int 0))
Relational.patternHolds d p [] = false ∧ patternHolds d p [] = true
```

This counterexample passes `decide +kernel` in
`/tmp/proof-port-i-literal.lean`. `Relational.liveRow` rejects any marked term;
`FDatabase.liveWith` ignores literal marks, as does semantic `Database.live`
because `SameRow` relates applications only. This is a real difference on raw
finite databases. Source `Action.subsume f es` only marks applications, so the
counterexample does not demonstrate a failure on states reached by that action.
To preserve the agreement theorem, the owner of `Congruence/Relational.lean`
would need to make `liveRow` ignore literal marks, matching `Database.live`
and `FDatabase.liveWith`. Alternatively the regression can explicitly record
the discrepancy, which is a substantive exception to statement preservation.
No out-of-scope implementation has been edited. User clarification is pending
on recording the mismatch as a regression statement exception versus retaining
the old agreement claim and reporting the build blocked.

The other G/H semantic boundaries concerning `min`, variable bindings, and
subsumption remain unchanged.
