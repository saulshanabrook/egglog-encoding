# Task F: representative bindings

## Status and validation

The full gate passes. Validation uses `source /tmp/proof-port-env.sh` and
`lake build EgglogSemantics EgglogPaper`, with no network or Makefile targets.
Preexisting worktree edits are preserved; original scoped files are backed up in
`/tmp/proof-port-f-original`.

- Initial failure: `Proofs/Match.lean:342`, `ValidEnv.mem_terms` returned the new
  representative-membership premise as held-term membership.
- Added `Database.mem_reps_iff`, `Database.reps_subset_terms`, and binding
  `mem_reps` accessors. Existing `mem_terms` statements are unchanged.
- `lake build EgglogSemantics EgglogPaper` passes (1,100 jobs), including all
  72 scoped proof modules and the six scoped tests: `Examples`, `SemanticCong`,
  `SubtermExistence`, `SourceProof`, `SourceProofCorrectness`, and `ProofPass`.
  Every scoped module is in the root/paper import closure. Final log:
  `/tmp/proof-port-f-final.log`.
- No module remains failing. Existing public interpreter and certificate
  soundness statements are retained. No out-of-scope file was edited.
- The full historical paper assertions from `PROOF-PORT-D.md` and the Task E
  audit, plus representative-specific claims, pass: 52 `assert_no_sorry` checks
  and 24 axiom reports. Reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`. Audit source/log: `/tmp/proof-port-f-audit.{lean,log}`.
- No `sorry`, `axiom`, `native_decide`, or heartbeat-limit change was introduced.
  `git diff --check` passes for the task's edited tracked files.

## Statement changes

- `ValidEnv.mono` takes representative inclusion, replacing equation inclusion.
  `ValidSubst.mono`, `ValidQuerySubst.mono`, `RuleResults.mono`, and `RunRules.mono`
  retain their fixed-substitution/assertion-containment conclusions with an added
  representative-inclusion premise. Positive patterns alone remain monotone.
  Added `Matches.mono`, congruence-based `transport` lemmas for `ValidEnv`,
  `Matches`, `ValidSubst`, `QueryMatches`, and `ValidQuerySubst`, plus
  `QueryHolds.mono`. Query transport assumes positive, ordering-free patterns
  and destination `HasReps`, rather than representative inclusion.
- `querySubst_of_matches_terms`, `querySubst_of_matches` (including the
  `SourceProof` wrapper), `SourceMeaning.validSubst_map`, and
  `validQuerySubst_map` require representative-valued bindings/maps for exact
  agreement with the resulting substitution.
- Added `Database.HasReps`: every represented class has a least held spelling.
  Finite terms/equations imply it; representatives are unique in their class.
  `SourceMeaning.representative_spec` now produces a representative and takes
  `HasReps`. `validQuerySubst_transport`, `firing_transport`, and the one-way
  round transport require it on the destination. `queryHolds_iff` and
  `round_sameMeaning` require it on both states.
- `completion_closed` and `completion_closed_of_saturated` need `HasReps` of the
  original state. `saturation_completion_closed` takes finite initial equations,
  preserved through all passes. `queryHolds_completion_iff` takes
  `HasReps` of both the original state and its completion.
- `SourceMeaning.querySubst_of_matches_transport` normalizes arbitrary held
  bindings and returns congruence-related bindings. Certificate rule soundness
  uses it and head transport directly; its public statement remains unchanged.
- `validEnv_canon` and `mem_matchQuery_iff` use executable representatives in
  place of held terms. The new `mem_repsWith_closureF_iff` bridge requires only
  subterm closure. Public interpreter refinement statements remain unchanged;
  private simulations track finite equations to obtain representatives.
- `mem_matchQuery_of_lookup` and `mem_matchQuery_of_entryReads` require executable
  representative bindings. `Database.Diag.reps_eq_terms` and `Diag.hasReps`
  preserve diagonal/union-free refinement without new public premises.
- `SourceMeaning.matches_transport`, `patternHolds_iff`,
  `mem_matchQuery_of_validQuerySubst`, `queryHolds_iff_matchQuery`,
  `FDatabase.holds_iff_queryHolds`, and the finiteness theorems retain their
  statements. `SameMeaning.reps_eq` proves agreement of representative sets when
  both congruence and held terms agree, retaining `DiagonalRound` and
  `InterpDeletes` statements. Source constructor/literal preservation only
  changes its use of `ValidEnv.mem_terms`.

## Regressions

- `representative_binding_not_monotone`: adding `a = b` to a state holding only
  `b` invalidates the old binding `x ↦ b`.
- `representative_query_transport`: the positive `f x` query survives the same
  change with a congruence-related representative substitution.
- `representative_saturation_exec` / `representative_saturation_succeeds`: with
  `a = b = g(b)` and `f(a)`, the rule `f(x) ⇒ g(x)` terminates, proves its final
  check, and never stores `g(g(b))`. The computation is checked with
  `decide +kernel` and lifted through interpreter refinement.
- `Examples` proves its existing literal and swap bindings are representatives
  using diagonality. `MatchingCounterexamples.mem_matchQuery_ex` checks the
  singleton representative computationally. Other scoped tests need no changes.

## Deleted modules

None.

## Semantic issues and blockers

No blocker remains. A genuine boundary of `Spec/Match.lean` is recorded by
`Falsity.InfiniteRepresentatives.wf` and `no_representative`: assert all equations
`box(n) = box(m)` for integers `n,m`. This store satisfies `Database.WF`, since
only applications are unioned. Its application class has no representative:
`box(n - 1)` is always a smaller held spelling. Literal classes remain isolated.
Thus `WF` alone does not ensure that every represented class has a member of
`Database.reps`; the representative definition does not change the global
order into a well-founded order. The proof API now states `HasReps` where needed.
Finite reachable states discharge it automatically. No specification change is
needed for the finite operational results.

The preexisting full compiler behavior-equivalence proof in
`Congruence/Correctness.lean` remains outside scope; it is not claimed by this
port or by the audits. The existing union/delete refinement restrictions remain.

## Root import changes

No import change is required for `EgglogSemantics.lean` or the build gate.
The new `Proofs/Representatives.lean` is imported transitively. Neither root file
was edited.

To restore the temporarily reduced paper audit, add the same three imports
listed in Task D and restore its assertions (all pass in the separate audit):

```lean
import EgglogSemantics.Proofs.InterpDeletes
import EgglogSemantics.Proofs.Provenance.GeneratedSoundness
import EgglogSemantics.Proofs.Resugar.Soundness
```

The nested-schedule assertions from Task E also pass, as do the new representative
and monotonicity claims listed in `/tmp/proof-port-f-audit.lean`.
