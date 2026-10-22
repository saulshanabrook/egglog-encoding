# Specification proof port A

This work edits only direct `Proofs/` modules, `Proofs/Source/`, and the four assigned tests.
Validation uses `source /tmp/proof-port-env.sh` and `lake build`; no network or `make check`.
Original scoped files are backed up under `/tmp/proof-port-a-original`.

## Status

- `OrderFinite` / `Term.blt_admissible` restored on 2026-10-22; log `/tmp/proof-port-a-foundation.log`.
- All session B dependencies build: `Term`, `Syntax`, `Database`, `Congruence`, `Eval`, `Match`, `Query`, `Writes`, `Step`, `Closure`, `SameMeaning`, `SourceMeaning`, `SourceModel`.
- All 59 retained scoped modules (including all four assigned tests) build together; log `/tmp/proof-port-a-all.log` (1048 jobs).
- Final gate passed: all 59 retained scoped modules (47 direct proof modules, 8 source proof modules, 4 tests), including the restored semantic round/program bridge and kernel-checked saturation example. No scoped module remains failing.
- `git diff --check` passes for scoped changes. A source scan finds no `sorry`, `admit`, `axiom`, `native_decide`, or heartbeat overrides. An axiom audit of order admissibility, action/matcher/round/program refinement, completeness, and both deletion regressions reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; log `/tmp/proof-port-a-axioms.log`.

## Statement changes

- `Syntax`: removed signature-only lemmas; `Expr.recExpr` drops the removed `ite` case.
- `Term`: removed obsolete store-invariant dependency; term statements unchanged.
- `Database`: removing signature/environment/entry operations and the `WF.envInTerms` obligations; surviving equation, term, rule, and environment-list facts retained.

## Semantic issues and blockers

Existing changes outside scope are left intact.

- Exact `FDatabase.toDatabase_addTerm` is false: the finite store asserts every subterm reflexively, whereas specification `addTerm` asserts the root alone. The port uses `SameMeaning`.
- `FDatabase.toDatabase_terms` needs `SubtermClosed`; `WF` no longer guarantees that an arbitrary finite list is closed. Finite closure completeness additionally requires held endpoints.
- Deletion refinement is refuted by `Tests/SemanticCong.absent_delete_not_sameMeaning`: deleting an absent compound row reasserts its children in the spec, but `deleteAtoms` only filters existing finite terms. A general bridge requires those children already held or a change outside this task's scope.
- `Tests/SemanticCong.delete_does_not_preserve_closed` proves that deleting a self-unioned nullary row removes its term but leaves its reflexive pair in `eqs`, violating the equation-endpoint part of `FDatabase.Closed`. Closure-preservation statements therefore need delete-freedom.


## Root imports

- `EgglogSemantics.lean`: replace `Proofs.Counterexamples` with `Proofs.MatchingCounterexamples`, remove `Proofs.Lattice`, and add `Tests.SemanticCong` for the retained semantic regressions.
- `EgglogPaper.lean`: add `import EgglogSemantics.Proofs.OrderFinite` to restore `Term.blt_admissible` / blueprint node `thm:order` to the paper build.
- Other deleted modules are not direct root imports. Out-of-scope legacy proof modules may still import them and need their separate rewrite. The root also imports preexisting deleted out-of-scope tests (`MergeViews`, `AtomStore`); their owner must remove those imports.
- Neither root import list was edited or built as a validation gate.

## Foundation milestone

Successfully built `Congruence`, `SemanticCong`, `Operands`, `SameMeaning`, `Eval`, `Match`, `Query`, `Writes` (`/tmp/proof-port-a-writes.log`). These modules are ready for session B.

- `Eval`: signature parameters and separate atom evaluation disappear; actions now take an explicit environment. `evalAction_eq_some` gains a delete case. Containment of actions/blocks requires delete-freedom; well-formedness remains unconditional (it now only means literal isolation). Removed entry/value/declaration/merge-only sections.
- `Match`/`Query`: use `Expr.eval`; disequality cases included. Global-environment compatibility lemmas removed. `querySubst_of_matches` now uses held terms, like `querySubst_of_matches_terms`.
- `Writes`: sequential/additive equivalences require delete-free actions/rules. `RunErases.eq_empty`, `RunRules.eq_addEqs`, `RunRules.eq_sUnion` require delete-free stored rules. Removed merge/normalization readings and signature/environment projections.
- `SameMeaning`: only rule equality and congruence agreement remain; all signature/environment equality premises removed.
- `Congruence`: removed constructor-value preservation (`StoredCong.isValue_iff`), whose typing predicate no longer exists.

## Second milestone

Building: `Step`, `Closure`, `SourceMeaning`, `SourceModel`, `Completion`, `Result`, `Behavior`, `Scope`, `Divergence`, `FiniteSaturation`, `Bindings`, `EnvTransform`, `ActionMonotone`, `MatchMonotone`, `MatchValues`, `Presentation`, `RuleStore`, `Diagonal`, `DiagonalPreservation`, `Source/Arity`, `Source/Domain`, `Source/RebuildVars`, `Source/FreshBindings`, `Source/FreshEnv`, `Source/Termination`. Logs: `/tmp/proof-port-a-{step,round,scope,small}.log`. All modules needed by session B now build.

## Deletions

`git rm` was attempted but cannot create `index.lock`: the worktree index lives under the read-only main checkout (`/home/oflatt/work/extended-proofs2/.git/worktrees/extended-proofs2-port-A`). Files are removed from this worktree, with deletions left unstaged; no main-checkout metadata was changed.

- `Signature`: executable signature lookup; signatures/declarations no longer exist.
- `SignatureLookup`: mathematical declaration lookup; declarations no longer exist.
- `StoreInvariant`: typed constructor values and function-entry invariants no longer exist.
- `AtomEntries`: function-entry shape/typing and entry-store laws no longer exist.
- `Out`: merge-function output lookup no longer exists.
- `StepMonotone`: value/entry separation across merge steps no longer exists.
- `Lattice`: countermodels about lattice-function merge/lookup semantics no longer apply.
- `Counterexamples`: declaration/merge countermodels are obsolete; surviving matching-domain and non-vacuity witnesses are retained in `MatchingCounterexamples`.

## Further statement changes

- Proof-level definitions drop extinct fields: `Database.Recorded` records equations only; `Database.NoUnions` retains diagonality and union-free heads; `FDatabase.NoUnions` retains its equation/rule invariants; `Database.NoLits` and `Database.CtorsInState` retain terms and rule heads; `Database.Avoids` retains the term census. `Database.FiniteStore` retains finite equations and rules. `Cmd.DeclOrRule` now recognizes only rule registration, and `Action.IsAtomWrite` only `.expr`. `CongListOn` is the existing operand-extended stored congruence-list relation. `EntryRead` denotes a constructor row with held arguments; `FreshEnv` ranges over all finite held terms. These are proof definitions, not changes to the specification or interpreter.
- `Closure.mem_closure_iff`, `mem_closureTotal_iff`: require both endpoints held in `db.terms`; finite closure only enumerates stored terms. Soundness remains unconditional for entries in the computed closure.
- `Step`: removed signature/declaration/merge/current-entry facts. `saturateReach_det`, `CmdStep.det`, `ProgramStep.det` are unconditional. `runRules_eq_self_iff` gains `db.DeleteFree`. `SaturateReach.reach` uses the graph of `RunRules`. WF and rule-store preservation handle general deletes. Fresh-name avoidance drops global-environment fields.
- `SourceMeaning`: all typing/store/signature premises removed. Evaluation and matching transport keep ordering-freedom; head transport additionally requires delete-freedom. The retained `evalLocalActions_transport` now concerns `evalActions` with explicit environments.
- `SourceModel`: firing/round containment and semantic round transport require delete-free stored rules; all obsolete typing premises removed. Completion and saturation results carry the same delete-freedom premise.
- `Scope`: expression evaluation needs only scoped bindings. Action/block progress replaces removed evaluability/width checks with `Action.UnionSafe` (evaluated union operands are nonliterals). Command/program progress drops normalization and typing premises.
- `Divergence`, `FiniteSaturation`: remove merge divergence/normalization. Round termination uses well-founded descent of changing `RunRules`; round totality is now automatic. Bounded-program nondivergence drops constructor hypotheses.
- `Diagonal`, `DiagonalPreservation`: `NoUnions` has only diagonal equations and union-free rules; deletion preserves diagonality, without a delete-free premise.
- `MatchMonotone`: positive-pattern/query (`monotoneB`) premises are needed to exclude disequalities; no signature/environment equality premises remain.
- `ActionMonotone`: explicit common environment, delete-free action/block; conclusion retains containment only.
- `Bindings`: remove signature arguments and `IsValue` premises; no `ite` case.
- `MatchValues`: remove typed-value shape machinery; retain keyed-query definitions and variable-membership facts. `ValidQuerySubst.mem_values` now states held-term membership.
- `Presentation`: remove comparison to obsolete `evaluate`/`evalAtom` and global-environment facts. Singleton writes are the returned set itself.
- `Source/Domain`: global inlining is gone; grounded-at implication includes disequality. `Source/FreshEnv` uses all held `terms` in place of `valueTerms`.
- `Source/Termination`: finite evaluation from `WellFormed` and `NoSaturate`, without declarations or merge termination.

## Source and finiteness milestone

Building: `Finite`, `ActionProgram`, `Setup`, `StatePreservation`, `Source/Execution`, `Source/Ctors`. Logs `/tmp/proof-port-a-{finite,preservation,ctors}.log`.

- `Finite`: finite equations and rules suffice; all deletion/round finiteness theorems include finite erase sets and child reassertions. `FiniteStore` drops signatures and environments.
- `Setup`: retained rule-only prefix/empty-term facts; removed declaration/evaluability setup theorems.
- `StatePreservation`: removed store typing; `reachable_wf_storeOk` now concludes only WF. Added subterm-closed property preservation through sequential actions and simultaneous delete/write rounds.
- `Source/Execution`, `Source/Ctors`: explicit environment and binding-property premises replace `db.env`; constructor signatures/`CtorState`/declaration premises disappear. Literal-freedom and constructor census remain valid with deletes. Action progress uses union-freedom or literal-free operands instead of declaration lookup.

## Executable and regression milestone

Building: `Interp`, `NoUnions`, `Rules`, `Execution`, `Entries`, `Assignments`, `LiveTables`, `DiagonalRound`, `Merge`, `MatchingCounterexamples`, and all four assigned tests. Matcher soundness/completeness, canonical query equivalence, and check-command soundness also build (`/tmp/proof-port-a-finalbridge.log`).

- `LiveTables` is retained only for inactive-ruleset identity and saturation; every live-entry/merge claim is removed.
- `DiagonalRound`: `RunStep.self_of_sameMeaning` becomes `RunRules.self_of_sameMeaning`, with `NoUnions` and delete-freedom; obsolete store-typing/merge premises disappear.
- `NoUnions`: executable invariants retain equations and rules only; general deletes preserve them. Removed merge/rebuild phases; command/program lemmas use `execCmd`/`execProgram` instead of removed `*M` runners.
- `Rules`: surviving registration, rule replacement, and matching facts use the current runner and explicit environments. Removed merge-phase laws.
- `Execution`: term/projection containment requires delete-free stored rules, plus monotone commands for a program; raw equation-list growth is unconditional. Removed global environment and merge-phase facts.
- `Entries`: retained substitution refinement, block concatenation, and constructor-row reads; removed function-entry/key/output operations. Constructor-row self-match now requires subterm closure. `Assignments.EntryRead` is a constructor row with arguments, without a signature or separate output tuple.
- `Interp`: finite closure completeness requires `SubtermClosed` and held endpoints. `toDatabase_addTerm`, `toDatabase_addTerms`, and `toDatabase_addEq` now state `SameMeaning`, not raw equality. Removed signature/env/declaration/old firing-loop statements. Raw-state round/program equality is replaced by semantic refinement as detailed below; general deletion correctness is refuted by the regressions.
- `Interp.patternHolds_iff`, `mem_matchQuery_iff`, `mem_matchQuery_of_validQuerySubst`, `queryHolds_iff_matchQuery`: explicit row-index soundness (`IndexOk`) and completeness (`IndexCurrent`) replace constructor-signature hypotheses; soundness alone requires only `IndexOk`. `execCheck_cmdStep` relates successful checks without requiring index completeness.
- `Merge`: retains generic assertion/congruence transport and `Recorded` laws, with no merge algorithm. `Cong.mono_recorded` now directly transports semantic `Cong` without WF. `RuleResults.mono` and `RunRules.mono` require positive queries and delete-free heads/stores. `Database.addTerm_eq_self` needs the explicit reflexive assertion; `Conservativity.refl_mem_addTerms` needs a listed root, because subterms are no longer asserted explicitly.
- `Tests/Examples`: global actions are empty-query rules plus runs; old declaration/lookup/merge tests are removed. Retained scope, ordering, congruence, matching, swap, nested witness, and transitive-closure cases; added delete/write ordering and disequality.
- `Tests/Checks`: `observe` replaces `observeM`; absent names are well formed, literal unions remain syntactically well scoped but outside `Fragment`, and checks do not export bindings.

## Confirmed semantic limitation

`Tests/SemanticCong.absent_delete_not_sameMeaning` proves the deletion mismatch using the closed empty finite database: deleting `f(a())` reasserts `a()` in `Spec.deleteRows`, whereas `Impl.deleteAtoms` merely filters the empty lists. A general deletion bridge needs a premise that the deleted rows' children are already held, or an out-of-scope change to `Impl.deleteAtoms` to record them. Neither source well-scoping nor absence of signatures solves this by itself. No out-of-scope code has been changed.

## Final interpreter refinement milestone

- `execRunRules_RunRules` is retained with a `SameMeaning` conclusion. It requires `Closed`, `IndexOk`, `IndexCurrent`, and delete-free stored rules. It allows `min` and disequality in that one round; no constructor signature or typing hypotheses remain.
- `execRunRules_iterate` now gives semantic agreement with the same number of specification rounds, adding WF and ordering-free stored rules for transport between different stored spellings.
- `runSaturateF_saturateReach` now gives an existential specification result with the same meaning as the successful finite result, under those same invariants. It handles the difference between semantic stopping and structural `sameData` stopping; the interpreter may take extra redundant rounds.
- `execCmd_cmdStep`, `execProgram_programStep`, and `exec_programStep` are retained as successful-execution soundness with an existential semantic result, replacing raw projection equality. Programs use `Cmd.monotoneB` and `Program.OrderingFree`; these are exactly the relevant `Program.Fragment.monotone` and `.noMin` fields. No scoping or declaration premise is needed for soundness, since stuck firings contribute nothing in both semantics.
- `execCmd_toDatabase` now states success-existence equivalence for nonsaturating commands. New `execProgram_complete` / `exec_complete` restore the converse direction for nonsaturating programs, returning a finite result semantically equivalent to the specified result. Unconditional completeness for saturation is not claimed: the executable has finite fuel.
- `closed_execRunRules`, `closed_iterate`, and `execCmd_closed` survive with delete-freedom. Row-index preservation is proved for recording terms/equations and delete-free rounds.
- The private `InterpReady` structure bundles proof assumptions only; the executable is unchanged. Old witness-driven `runSaturate` / `RunRel` facts are removed because those executable definitions no longer exist. Old `fireInto` / `fireRule` membership decompositions are replaced by write-accumulation proofs for the current runner.
- `Tests/Examples` includes a redundant-spelling saturation example whose successful specification execution is proved with `decide +kernel` and `exec_programStep`. No native decision tactic is used.

## Remaining limits

- No failing scoped module is left. The two deletion discrepancies above are documented semantic issues, not hidden proof obligations.
- Unrestricted delete-containing interpreter refinement is not proved; the absent-child counterexample rules out that statement. A child-existence premise would be necessary, but its sufficiency for a general deletion bridge has not been established here.
- Raw database projection equality is intentionally not asserted where explicit versus implicit subterm assertions differ.
- The aggregate root and paper imports remain for their owners to update. Out-of-scope compiler/session-B modules have not been ported in this worktree.
- `git rm` cannot stage removals because the worktree index is outside the writable sandbox; the eight file deletions are present and unstaged.

## Validation command

The final build discovers every retained file in scope, rather than selecting a subset:

```bash
source /tmp/proof-port-env.sh
python3 - <<'PY'
from pathlib import Path
import subprocess
files = sorted(Path('EgglogSemantics/Proofs').glob('*.lean'))
files += sorted(Path('EgglogSemantics/Proofs/Source').rglob('*.lean'))
files += [Path('EgglogSemantics/Tests') / (name + '.lean')
          for name in ['Examples', 'Checks', 'SemanticCong', 'SubtermExistence']]
modules = [str(p.with_suffix('')).replace('/', '.') for p in files]
raise SystemExit(subprocess.call(['lake', 'build', *modules]))
PY
```

The validated module list exactly matches this discovery (59 modules, no missing or extra targets). The successful combined log is `/tmp/proof-port-a-all.log`; focused final interpreter log is `/tmp/proof-port-a-programbridge.log`.

## Named statement-change inventory

The module-level explanations above describe the semantic changes. This inventory names retained public theorem declarations whose signatures changed, including removed obsolete parameters, new delete/positivity/closure/index premises, and semantic reformulations. Namespace prefix `Egglog` is omitted. Renames from removed runners or relations are described above; obsolete-subject theorem deletions are covered by their module explanations.

- `Proofs/ActionMonotone.lean`: `evalAction_mono`, `evalActions_mono`.
- `Proofs/Assignments.lean`: `mem_matchQuery_of_lookup`, `EntryRead.holds`, `mem_matchQuery_of_entryReads`, `Expr.evalList_canon_query`, `execLocalActions_atom_of_eval`.
- `Proofs/Bindings.lean`: `Expr.evalList_map_var`, `Expr.freeVarsList_map_var_subset`, `Expr.mem_freeVarsList_map_var`, `Expr.lookup_isSome_of_mem_vars`, `Expr.lookup_isSome_of_mem_varsList`, `Expr.evalList_set`, `Expr.getElem?_of_evalList`, `Expr.evalList_singleton`, `Expr.evalList_pair`.
- `Proofs/Closure.lean`: `mem_closure_iff`, `mem_closureTotal_iff`.
- `Proofs/Completion.lean`: `Database.WF.completion`, `SourceMeaning.queryHolds_completion_iff`.
- `Proofs/Database.lean`: `Database.WF.empty`, `Database.WF.addTerm`, `Database.WF.addEq`, `Database.WF.sUnion`.
- `Proofs/DiagonalPreservation.lean`: `evalAction_diag`, `evalActions_diag`, `evalLocalActions_diag`.
- `Proofs/Divergence.lean`: `changingRunStep_iff`, `changingRunReach_runReach`, `not_saturateDiverges_of_wellFounded`, `not_cmdDiverges_of_allConstructors`, `not_programDiverges_of_allConstructors`.
- `Proofs/Entries.lean`: `Expr.eval_of_refines`, `Expr.evalList_of_refines`, `matches_of_patternHolds`, `validQuerySubst_of_mem_matchQuery_diag`, `execActions_append`, `Expr.evalList_append_eq`, `execActions_append_eq`, `mem_zip_self`, `congrKeys_self`, `execAction_atom_of_eval`, `patternHolds_entry_of_mem_rows`.
- `Proofs/Eval.lean`: `Database.terms_setRules`, `Database.WF.congr`, `Expr.eval_lit`, `Expr.eval_var`, `Expr.eval_app_ctor`, `Expr.eval_min`, `Expr.evalList_nil`, `Expr.evalList_cons`, `Expr.evalList_length`, `Expr.lookup_isSome_of_mem_evalList`, `Expr.eval_agree`, `Expr.evalList_agree`, `Expr.eval_agreeOn`, `Expr.evalList_agreeOn`, `Expr.eval_isSome`, `Expr.evalList_isSome`, `Expr.eval_append_env`, `Expr.evalList_append_env`, `evalActions_nil`, `evalActions_cons`, `evalAction_expr_of_eval`, `evalAction_eq_some`, `evalAction_contained`, `evalAction_rules`, `evalAction_wf`, `evalActions_contained`, `evalActions_rules`, `evalActions_wf`, `Expr.evalList_append`.
- `Proofs/Execution.lean`: `FDatabase.execRunRules_terms`, `FDatabase.execRunRules_eqs`.
- `Proofs/Finite.lean`: `evalAction_finite`, `evalActions_finite`, `evalLocalActions_finite`, `evalAction_finiteStore`, `evalActions_finiteStore`, `evalLocalActions_finiteStore`.
- `Proofs/FiniteSaturation.lean`: `saturateReach_exists_of_wellFounded`, `saturateReach_exists_of_measure`.
- `Proofs/Interp.lean`: `mem_closure_iff_of_diag`, `FDatabase.mem_toDatabase_terms`, `FDatabase.toDatabase_consRule`, `FDatabase.Closed.consRule`, `FDatabase.toDatabase_addTerm`, `FDatabase.toDatabase_addTerms`, `FDatabase.toDatabase_addEq`, `FDatabase.coe_termsF`, `FDatabase.mem_closureF_iff`, `FDatabase.WF.addEq`, `FDatabase.empty_wf`, `FDatabase.mem_closureF_addTerm`, `FDatabase.mem_closureF_addTerm₂`, `patternHolds_iff`, `validEnv_canon`, `mem_matchQuery_iff`, `validQuerySubst_of_mem_matchQuery`, `mem_matchQuery_of_validQuerySubst`, `execAction_eq_some`, `execAction_subtermClosed`, `execActions_subtermClosed`, `execAction_closed`, `execAction_rules`, `execActions_closed`, `execAction_toDatabase`, `execActions_toDatabase`, `closed_execRunRules`, `execRunRules_RunRules`, `toDatabase_eq_of_fields`, `closed_iterate`, `execRunRules_iterate`, `runSaturateF_saturateReach`, `queryHolds_iff_matchQuery`, `execCmd_toDatabase`, `execCmd_closed`, `execCmd_cmdStep`, `execProgram_programStep`, `exec_programStep`.
- `Proofs/LiveTables.lean`: `LiveTables.runSaturated_of_no_rules`.
- `Proofs/Match.lean`: `Matches.expr`, `Matches.eq`, `Matches.storedCases`.
- `Proofs/MatchMonotone.lean`: `congOn_mono`, `ValidEnv.mono`, `ValidSubst.mono`, `ValidQuerySubst.mono`.
- `Proofs/MatchValues.lean`: `ValidQuerySubst.mem_values`.
- `Proofs/Merge.lean`: `CongList.append`, `mem_congOn_self`, `Database.addTerms_eqs_of_eqs`, `congOn_setEnvRules`, `Conservativity.mem_addTerms_eqs'`, `Conservativity.refl_mem_addTerms`, `Conservativity.addTerms_eqs_mono`, `Conservativity.terms_subtermClosed`, `Conservativity.withOperands_subtermClosed`, `Conservativity.congOn_elim`, `Cong.mono_recorded`, `CongList.mono_recorded`, `Database.Recorded.of_contained`, `Database.Recorded.setEnvRules`, `Database.Recorded.trans`, `Database.Recorded.trans_contained`, `Database.Recorded.addTerm_mono`, `Database.Recorded.addTerms_mono`, `Database.Recorded.addEq_mono`, `Database.addTerm_eq_self`, `Env.Agree.cons`, `Database.mem_terms_of_eqs`, `Database.Recorded.contained_of_diag`, `RuleResults.mono`, `RunRules.mono`.
- `Proofs/NoUnions.lean`: `FDatabase.NoUnions.union`, `execAction_noUnions`, `execActions_noUnions`.
- `Proofs/Presentation.lean`: `Action.writes_singleton`, `Action.writes_append`.
- `Proofs/Query.lean`: `Matches.expr_iff_cong`, `Matches.eq_iff_cong`, `Matches.expr_iff_infers`, `Matches.eq_iff_infers`, `querySubst_of_matches`, `mem_ruleResults_iff_queryMatches`.
- `Proofs/RuleStore.lean`: `runStep_rules`, `runReach_rules`.
- `Proofs/Rules.lean`: `FDatabase.execAction_setRules`, `FDatabase.execActions_setRules`.
- `Proofs/SameMeaning.lean`: `Database.SameMeaning.of_inferred`.
- `Proofs/Scope.lean`: `Expr.eval_isSome_of_scoped`, `Expr.not_isLit_of_isApp`, `evalAction_isSome_of_scoped`, `evalActions_isSome_of_scoped`, `Query.bind_models`, `evalLocalActions_isSome_of_scoped`, `CmdEval.exists_of_scoped`, `Eval.exists_of_scoped`.
- `Proofs/Setup.lean`: `CmdStep.eqs_empty_of_declOrRule`, `ProgramStep.eqs_empty_of_declOrRule`.
- `Proofs/SourceMeaning.lean`: `SourceMeaning.eval_interpret`, `SourceMeaning.evalList_interpret`, `SourceMeaning.EnvRelated.mono`, `SourceMeaning.eval_congOn`, `SourceMeaning.matches_transport`, `SourceMeaning.validSubst_map`, `SourceMeaning.validQuerySubst_map`, `SourceMeaning.validQuerySubst_transport`, `SourceMeaning.queryHolds_iff`, `SourceMeaning.evalLocalActions_transport`.
- `Proofs/SourceModel.lean`: `SourceMeaning.firing_contained_round`, `SourceMeaning.round_extends`, `SourceMeaning.firing_transport`, `SourceMeaning.round_sameMeaning`, `SourceMeaning.completion_closed`, `SourceMeaning.completion_closed_of_saturated`, `SourceMeaning.saturation_completion_closed`.
- `Proofs/StatePreservation.lean`: `Program.queriesSafe_of_rules`, `reachable_wf_storeOk`.
- `Proofs/Step.lean`: `SaturateReach.reach`, `runRules_eq_self_iff`, `saturateReach_det`, `evalAction_setRules`, `evalActions_setRules`, `Database.Avoids.congr`, `CmdStep.det`, `ProgramStep.det`.
- `Proofs/Syntax.lean`: `Expr.recExpr`.
- `Proofs/Writes.lean`: `evalAction_eq_write`, `evalActions_eq_writes`, `mem_ruleResults_iff_writes`, `RunRules.eq_sUnion`.
- `Proofs/Source/Ctors.lean`: `Expr.eval_ctorsIn`, `Expr.evalList_ctorsIn`, `Database.CtorsIn.lookup`, `evalAction_ctorsIn`, `evalActions_ctorsIn`, `evalLocalActions_ctorsIn`, `Database.empty_ctorsInState`, `cmdStep_ctorsIn`, `programStep_ctorsIn`, `ctorsIn_of_prefixStep`.
- `Proofs/Source/Domain.lean`: `Pattern.Grounded.groundedAt`.
- `Proofs/Source/Execution.lean`: `Program.OrderingFree.of_mem`, `Expr.eval_litFree`, `Expr.evalList_litFree`, `Database.LitFree.lookup`, `evalAction_litFree`, `evalActions_litFree`, `evalLocalActions_litFree`, `Database.empty_noLits`, `cmdStep_noLits`, `programStep_noLits`, `evalAction_isSome_of_builds`, `evalActions_isSome_of_builds`, `evalLocalActions_isSome_of_builds`.
- `Proofs/Source/Termination.lean`: `Program.WellFormed.eval_exists`.
