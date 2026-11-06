# Task G: subsumption proof port

## Status and validation

Complete within the authorized scope. All 76 proof modules and all six requested
tests build. The full root import closure, with the two replacement module names,
passes `lake build` (1099 jobs). Temporary copies of both root files also
elaborate successfully, including **every** paper `assert_no_sorry` assertion.
No scoped module remains failing.

No source, implementation, compiler, root import list, paper file, or out-of-scope
test was edited. Preexisting worktree changes were preserved. Validation used
`source /tmp/proof-port-env.sh` and `lake build`; no network, Makefile targets,
proof placeholders, new axioms, `native_decide`, or heartbeat increases were
used. Original scoped files are backed up under `/tmp/proof-port-g-original`.
Scoped `git diff --check` and a forbidden-proof-construct/trailing-whitespace
scan both pass.

Final checks and logs:

- Root-import target list, replacing only `Deletes` → `Subsume` and
  `InterpDeletes` → `InterpSubsume`: `lake build` succeeds, 1099 jobs;
  `/tmp/proof-port-g-all-final.log`.
- `/tmp/ProofPortGAudit.lean`: a copy of the complete root import file with
  those two substitutions; `lake env lean` exits 0 with no diagnostics.
- `/tmp/ProofPortGPaperAudit.lean`: a copy of the paper file with the two import
  substitutions and two assertion replacements below; `lake env lean` exits 0
  with no diagnostics. Every surviving named paper theorem is checked.
- Literal `lake build EgglogSemantics EgglogPaper`: fails **only** because both
  files still import `EgglogSemantics.Proofs.Deletes` and
  `EgglogSemantics.Proofs.InterpDeletes`; first root errors are those bad imports.
  `/tmp/proof-port-g-root-gates-final.log`. The files are explicitly outside scope.

The successful full-module build can be reproduced without changing either root:

```bash
source /tmp/proof-port-env.sh
rg '^import ' EgglogSemantics.lean |
  sed -e 's/^import //' \
      -e 's/Proofs.InterpDeletes/Proofs.InterpSubsume/' \
      -e 's/Proofs.Deletes/Proofs.Subsume/' |
  xargs lake build
```

## Module organization

- `Lookup.lean` adds the mutual lookup/evaluation, environment-agreement,
  liveness, and congruent-substitution bridges early in the dependency order.
- `Subsume.lean` replaces the row-removal theory with retained-existence,
  marks/existence, diagonal marked-row transport, and forgotten-mark facts.
  `RunMarks.eq_empty`, `RunRules.eq_addEqs`, `RunRules.eq_sUnion`, and
  `RunRules.eq_pair` live in the earlier `Writes.lean`; `RunRules.wf` remains
  in `Step.lean`. Importing `Subsume` exposes all of them.
- `InterpBase.lean`, `InterpLookup.lean`, and `InterpRound.lean` split out the
  finite-store invariants, executable lookup bridge, and common action/round
  refinement. `Interp.lean` keeps the source schedule/completeness/observer API.
- `InterpSubsume.lean` replaces the old deletion-specific interpreter argument.
  Its union-free schedule refinement uses the same unrestricted round proof as
  the source path. The compiler execution theorem keeps its name and statement.

## Statement changes

All surviving public theorem names are retained except names explicitly tied to
removed operations, listed below. `Reach.det`, `Eval.det`, both
`exec_programStep` theorems, both `exec_complete` theorems, both `observe_eval`
theorems, and all surviving paper assertions keep their public statements.
The following is the complete substantive signature/definition change inventory;
private helper changes follow the same premises as their public callers.

### Names and state operations

- `Action.DeleteFree`, `Actions.DeleteFree`, `Rule.DeleteFree`, and helper names
  containing `deleteFree` become `SubsumeFree` / `subsumeFree`, still defined
  using `monotoneB`. Action constructor cases become `.subsume`.
- Erasure facts become mark facts: `Action.mark_agree`, `marks_agree`,
  `mark_isSome`, `marks_isSome`, `mark_eq_empty`, `marks_eq_empty`,
  `Action.mem_marks`, and `RunMarks.eq_empty`. Subsumes write their reflexive pair
  and mark their evaluated term.
- `evalAction_eq_some` and `execAction_eq_some` describe insertion plus marking,
  replacing the row-removal alternative.
- `RunRules.eq_sUnion` drops its freedom premise. New unconditional
  `evalAction_eq_write_mark`, `evalActions_eq_writes_marks`, and
  `mem_ruleResults_iff_writes_marks` give the sequential/simultaneous bridge.
- Finiteness continues to mean finitely many equations. `RunMarks.finite`
  separately proves that a round adds finitely many marks; `addSubsumed` does
  not change equations or terms.

### Matching and query construction

- `Matches.expr`, `Matches.eq`, `Matches.expr_iff_cong`, `eq_iff_cong`,
  `expr_iff_infers`, and `eq_iff_infers` require empty subsumption and ordering
  freedom of the expressions. The atom equivalences also require represented
  environment bindings. Equality already supplies existence of both results.
- `Matches.storedCases` now takes represented environment bindings and retains
  `Lookup` evidence in each branch, together with the old stored witnesses.
  `Matches.of_agreeOn` keeps its statement and is moved earlier in the module.
- `Matches.mono`, `ValidSubst.mono`, `ValidQuerySubst.mono`, `Matches.transport`,
  `ValidSubst.transport`, `QueryMatches.transport`, `ValidQuerySubst.transport`,
  `QueryHolds.mono`, `RuleResults.mono`, and `RunRules.mono` add live-set
  inclusion. Existing positivity, representative, and head-freedom premises
  remain. `SourceMeaning.matches_transport` keeps its original statement.
- `SourceProof.premiseMatches_sound` / `premisesMatch_sound` and the two
  `Provenance.Generated` counterparts require empty subsumption and ordering
  freedom. Source checker callers derive these from the fragment and
  `Reach.subsumed_eq`.
- `EntryRead` now carries `LookupList` evidence and a non-subsumed-row condition,
  replacing evaluation alone. `patternHolds_entry_of_mem_rows` makes the same
  change; it, `EntryRead.holds`, and `mem_matchQuery_of_entryReads` use `Closed`,
  `IndexOk`, and `IndexCurrent` rather than subterm closure alone.
- `Falsity.not_matches_empty` requires represented environment bindings;
  otherwise a bare variable is a counterexample.

### Meaning, growth, and saturation

- `Database.SameMeaning.of_inferred`, `of_congr_eq`, `addTerm`, `addEq`,
  `FDatabase.meaning_addEqs` (and its term/list helpers),
  `SourceMeaning.evalLocalActions_transport`, `firing_transport`, and
  `round_sameMeaning` add equality of the subsumed sets.
- `Database.SameMeaning.completion_eq` and
  `Database.sameMeaning_iff_completion_eq` require the same equality because
  completion preserves subsumption.
- `Database.Recorded.contained_of_diag` adds inclusion of subsumed sets;
  `Recorded` itself still records only equations.
- `cmdStep_saturate_iff`, `saturateReach_exists_of_wellFounded`,
  `saturateReach_exists_of_measure`, `not_infinitePasses_of_wellFounded`,
  `changingRunStep_iff`, and `changingRunReach_runReach` compare `SameMeaning`
  instead of equality/inequality of `Cong`.
- `Database.SameMeaning.runRules_of_diag` adds `MarksExist` for both inputs.
  This invariant states that every marked term exists, is preserved by every
  round, and is sufficient to transport arbitrary heads between diagonal
  states. Public union-free interpreter theorems discharge it from `IndexOk`.

### Interpreter

- `FDatabase.IndexOk` gains a field requiring every subsumed spelling to be held.
  Term insertion, unions, subsumption, forgetting marks, and rounds preserve it.
- `patternHolds_matches` adds `IndexCurrent` and represented environment
  bindings; `patternHolds_of_matches` adds `IndexOk` and represented bindings.
  `matches_of_patternHolds` has the same extra requirements.
- `FDatabase.patternHolds_validSubst`, `validQuerySubst_of_mem_matchQuery`, and
  `validQuerySubst_of_mem_matchQuery_diag` add `IndexCurrent`. The public
  `patternHolds_iff`, `mem_matchQuery_iff`, and `queryHolds_iff_matchQuery`
  signatures remain unchanged apart from the stronger `IndexOk` definition.
- `toDatabase_eq_of_fields` adds equality of `subsumed` lists;
  `FDatabase.toDatabase_contained_of_lists` adds their inclusion.
- `execAction_toDatabase`, `execActions_toDatabase`, `execAction_closed`,
  `execActions_closed`, `execAction_subtermClosed`, `execActions_subtermClosed`,
  `closed_execRunRules`, `execRunRules_RunRules`, and `execRunRules_index` drop
  their freedom premises: every action only adds state.
- `execRunRules_induction_ruleset` starts from `P d` and preserves `fireInto`,
  replacing the deletion base and `fireWritesInto` premise.
  `execRunRules_eq_fold_of_subsumeFree` uses `fireInto`; the new
  `execRunRules_eq_fold` has no head restriction.
- `execActions_lists`, `fireInto_lists`, and `execRunRules_lists` preserve all
  three lists (terms, equations, and marks). Existing term-growth APIs retain
  their now-unnecessary freedom premises for compatibility.
- `Eval.ok_iff`, `Eval.failed_iff`, `FDatabase.holds_iff_queryHolds`,
  `exec_programStep_check`, `exec_programStep_check_noUnions`, and
  `observe_eval_of_exec` explicitly read the final query on `forgetSubsumed`.

## Deletions and replacements

Each item records why the removed material no longer applies.

- `Proofs/Deletes.lean`: row removal no longer exists; surviving diagonal
  congruence characterization moved to `Subsume.lean`.
- `Proofs/InterpDeletes.lean`: executable row removal no longer exists; surviving
  diagonal matching and union-free refinement moved to `InterpSubsume.lean`.
- `Database.deleteRows_eq`: the operation is gone; replace the paper assertion
  with `RunRules.eq_pair`.
- `Database.mem_deletedRows_of_diag`: there is no removed-row census;
  application-mark membership is handled by `app_marks_iff_of_diag`.
- `Database.mem_deleteRows_terms_of_diag`: terms are retained; use
  `Database.mem_subsume_terms` and unchanged `addSubsumed_terms`.
- `Database.proper_subterm_mem_deleteRows`: all subterms are retained; the
  special protection rule for deletion no longer exists.
- `Database.SameMeaning.deleteRows_of_diag`: removal transport is obsolete;
  `addSubsumed` and marked-row round transport replace it.
- `Database.deleteRows_empty`: there is no deletion identity; use
  `Database.addSubsumed_empty`.
- `Database.WF.deleteRows`: removal is gone; use `Database.WF.addSubsumed`.
- `Database.Diag.deleteRows`: removal is gone; use `Database.Diag.addSubsumed`.
- `Database.deleteRows_terms_subset`: removal is gone; terms are unchanged by
  `addSubsumed`.
- `Database.finite_deletedRows`, `finite_deleteRows`, and
  `Database.FiniteStore.deleteRows`: no sets are removed; marking leaves the
  equation-finiteness invariant unchanged.
- `actionDeletes_erase`, `actionsDeletes_erases`, `actionDeletes_eq_empty`, and
  `actionsDeletes_eq_empty`: the executable delete collection is gone; the
  common action/head specifications relate writes and marks directly.
- `roundDeletes` and `roundDeletes_eq_RunErases`: there is no deletion phase;
  `execRunRules_subsumed` exposes exactly the specification's `RunMarks`.
- `execRunRules_deletes_writes`: deletion-before-writing no longer applies;
  `execRunRules_RunRules` is now unrestricted.
- `closed_execRunRules_of_deleteAtoms` and `execRunRules_index_of_deleteAtoms`:
  there is no deletion base; the unrestricted closure/index theorems suffice.
- `execWrite_preserves`, `execWrites_preserves`, and `execWrites_closed`: the
  write-only executable functions are gone; `execAction_preserves`,
  `execActions_preserves`, and `execActions_closed` cover every action.
- `execWrite_noUnions`, `execWrites_noUnions`, and `fireWritesInto_noUnions`:
  their executable functions are gone; the existing action/head proofs and
  `fireInto_noUnions` replace them.
- `execWrites_lists` and `fireWritesInto_lists`: their executable functions
  are gone; `execActions_lists` and `fireInto_lists` include marks as well.
- `FDatabase.NoUnions.deleteAtoms`: the operation is gone; use `NoUnions.subsume`.
- `FDatabase.IndexOk.deleteAtoms`, `IndexCurrent.deleteAtoms`, and
  `SubtermClosed.deleteAtoms`: the operation is gone; each has a `.subsume`
  preservation theorem.
- `FDatabase.closed_deleteAtoms_of_eqs_empty`: deletion no longer threatens
  closure; `Closed.subsume` works even with unions.
- `FDatabase.mem_deleteAtoms_terms_of_diag`: filtered membership is obsolete;
  `subsume_terms` identifies the inserted term/subterm list.
- `FDatabase.toDatabase_deleteAtoms`: removal refinement is obsolete;
  `toDatabase_subsume` refines insertion plus marking without diagonality.
- `execRunRules_index_with_deletes`: there are no deletes;
  `execRunRules_index` now covers every head.

`git rm -f` was attempted, but the worktree index is under the read-only main
checkout at `.git/worktrees/extended-proofs2-port-G/index.lock`. No escalation
is available. Both files have been removed from the working tree; their
unstaged deletions are visible to Git. Nothing in the main checkout was edited.

## Regression changes

In `Tests/SemanticCong.lean`:

- `absent_delete_spec`, `absent_delete_exec`, and `absent_delete_sameMeaning`
  become the corresponding `absent_subsume_*` facts: an absent row is inserted
  and marked, with all its columns retained.
- `delete_does_not_preserve_closed` becomes `subsume_preserves_closed`:
  subsumption preserves closure, including self-unions.
- `self_union_delete_sameMeaning` becomes `self_union_subsume_sameMeaning`:
  insertion/marking has the claimed denotation.
- `parent_child_delete` becomes `parent_child_subsume`: both rows stay held.
- `delete_min_disequality_saturation` becomes
  `subsume_min_disequality_saturation`: the old row still exists but is not live;
  the final check reads `forgetSubsumed`.
- `simultaneous_deletes_before_writes` becomes
  `simultaneous_writes_and_subsumes`: all firings use the pre-state and checks
  can see marked rows.
- `union_delete_nonheld_argument` becomes `sameRow_nonheld_argument`: it still
  illustrates the held-children requirement of raw finite closure, not a
  failure of the inserting subsume operation.
- `relational_literal_delete_agrees` becomes `relational_literal_subsume_agrees`:
  literal marks do not hide literals in either matching implementation.
- Added `writes_subsumes_commute`, `subsumed_not_matched_but_checked`,
  `congruent_subsumed_spelling_not_matched`, and
  `subsumption_changes_sameMeaning`.
- Added `unrepresented_variable_lookup`, `min_eval_does_not_imply_lookup`, and
  `unheld_mark_breaks_liveWith` to pin down the semantic boundaries below.

The other five scoped test modules retain their surviving examples and
certificate soundness conclusions. The provenance subsumption counterexample
now demonstrates retained terms and recorded marks rather than removal.

## Semantic boundaries and local workarounds

No change to `Spec/`, `Source/`, or `Impl/` is required for the reached-state
proofs. Four general statements need care:

1. The suggested converse from evaluation/existence to lookup is false for
   unrestricted `min`: in a store containing only literal `0`, `min(0,1)`
   evaluates to an existing `0` but cannot look up `1`. The bridge uses
   `OrderingFree`; executable lookup refinement still handles every expression.
2. `Lookup.var` requires only an environment lookup. An unrepresented binding
   can satisfy an atom in an empty store. Old existence consequences need
   represented bindings, provided by `ValidEnv` in query matching.
3. `SameMeaning` alone need not survive writes on arbitrary raw databases.
   Empty equations with no marks and empty equations marked at `a` have the
   same meaning, but asserting `a` exposes different liveness. Source transport
   carries equality of marks; union-free transport carries `MarksExist` and
   derives equality of observable application marks. Reachable stores satisfy
   the required invariants.
4. The old finite-store `Closed`, `IndexOk`, and `IndexCurrent` allowed unheld
   marked children. A mark at `R(f(b))`, with held `R(f(a))` and `a ~ b` but
   unheld `f(b)`, is missed by the held-children `liveWith` branch. The new
   proof-only `IndexOk.subsumed` rules this out. Actual `FDatabase.subsume`
   inserts the target first and preserves it; the implementation is unchanged.

## Required root changes (outside scope)

In **both** `EgglogSemantics.lean` and `EgglogPaper.lean`:

```diff
-import EgglogSemantics.Proofs.Deletes
-import EgglogSemantics.Proofs.InterpDeletes
+import EgglogSemantics.Proofs.Subsume
+import EgglogSemantics.Proofs.InterpSubsume
```

In `EgglogPaper.lean`:

```diff
-assert_no_sorry Egglog.Database.deleteRows_eq
-assert_no_sorry Egglog.RunErases.eq_empty
+assert_no_sorry Egglog.RunRules.eq_pair
+assert_no_sorry Egglog.RunMarks.eq_empty
```

The paper's comments should also say subsumption/subsume-free. No other paper
assertion name changes. New helper modules are imported transitively; adding
separate root imports for them is optional.
