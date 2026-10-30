# Task D: rule lists, equation-only states, and the final check

## Status and validation

All 70 retained in-scope proof modules, all six scoped test modules, all other
retained root imports, and `EgglogPaper` build together (1,084 jobs). The final
combined gate passed after all edits. Validation uses
`source /tmp/proof-port-env.sh` and `lake build`, without Makefile targets or
network access. Original scoped files are backed up in
`/tmp/proof-port-d-original`; preexisting worktree changes were preserved.

- Foundations, including `OrderFinite`, passed early in
  `/tmp/proof-port-d-foundation.log` (984 jobs).
- Combined retained-root-import and paper gate: `/tmp/proof-port-d-final.log`.
  This includes every retained module in this task's proof scope, including
  the source, provenance, and resugaring proof chains.
- Scoped tests: `Examples`, `SemanticCong`, `SubtermExistence`, `SourceProof`,
  `SourceProofCorrectness`, and `ProofPass` all pass. `SubtermExistence` needed
  no edits. The focused grouped-rule-index regression also passed in
  `/tmp/proof-port-d-rule-index.log`.
- `/tmp/proof-port-d-audit.lean` imports the entire retained root import list
  and checks 33 theorem dependencies with `assert_no_sorry`. It passed; the
  12 main axiom reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`. Output: `/tmp/proof-port-d-audit.log`. The proposed paper
  imports and assertions below also passed as
  `/tmp/proof-port-d-paper-audit.lean` (empty diagnostic log).
- No `sorry`, `axiom`, `native_decide`, or increased heartbeat limit was added.
- Exact `lake build EgglogSemantics EgglogPaper` still fails **only** on the
  two deleted-module imports below. First errors: missing
  `Proofs/RuleStore.lean` and `Proofs/Rules.lean`, followed by bad imports in
  `EgglogSemantics.lean`. Log: `/tmp/proof-port-d-root-final.log`.
- No retained in-scope module remains failing. No out-of-scope file was edited.

## Deleted modules

- `Proofs/Rules.lean`: ruleset registration and stored-rule replacement no longer exist.
- `Proofs/RuleStore.lean`: mathematical states no longer contain a rule store.

`git rm -f` was attempted but could not lock the worktree index, which is inside
the read-only main checkout. Both files are removed locally; their deletions
remain unstaged. Mixed-subject modules (`Setup`, `LiveTables`, `Merge`, and
`Entries`) retain their surviving material.

## Statement changes

The uniform change throughout is that rounds and saturation take `List Rule`,
command-block judgments take `List Cmd`, and whole-program statements refer to
`P.commands`. `SameMeaning` compares congruence alone. Rule membership is in
the explicit command rule list or `P.rules`, never in a database or ruleset.
The following lists the changes beyond those uniform substitutions.

- **Database, Eval, SameMeaning, Completion, Deletes:** remove all rule-store
  projections, updates, equalities, and preservation lemmas. In particular,
  `Database.DeleteFree`, `terms_setRules`, `deleteRows_rules`, and
  `evalAction(s)_rules` are gone. `Action.DeleteFree`, `Actions.DeleteFree`,
  and `Rule.DeleteFree` remain. `SameMeaning.of_inferred` and completion
  constructions no longer take rule equality. `Database.deleteRows_empty`
  proves that deleting the empty set is identity.
- **Writes:** `RunErases.eq_empty`, `RunRules.eq_addEqs`, and
  `RunRules.eq_sUnion` take `∀ r ∈ rs, r.DeleteFree`. Rule results range
  directly over `rs`; `RunRules.rules` and `Database.addEqs_rules` disappear.
- **Step:** remove rule-store and database-delete-freedom preservation, plus
  `evalAction(s)_setRules` and `deleteRows_setRules`. `runRules_eq_self_iff`
  takes delete-freedom of the explicit rule list. WF and determinism retain
  their meaning; program append, inversion, and preservation concern command
  lists.
- **Result:** `Eval.ok_iff` includes both command execution and the final
  `QueryHolds`; `Eval.failed_iff` identifies a completed command execution and
  a false final check. `Eval.append_of_ok`, `append_iff`, and
  `append_of_no_checks` compose a command-list prefix with a program suffix,
  retaining the suffix's final check. `append_of_no_checks` needs no extra
  premise because commands cannot check. `ok_of_no_checks` assumes
  `P.check = []`. Added `Eval.det` for both finite outcomes. Removed the
  `CmdEval` theorems, `Eval.check_cons_iff`, and `Eval.append_of_failed`:
  intermediate checks and failure before a command suffix no longer exist.
- **Scope:** `CmdEval.exists_of_scoped` becomes
  `CmdStep.exists_of_scoped`. Added `ProgramStep.exists_of_noSaturate`;
  `Eval.exists_of_scoped` executes the commands and then decides the final
  check. Nonsaturating commands always produce a database.
- **Setup:** only `Database.terms_empty_of_eqs_empty` remains; `DeclOrRule`
  and all rule-only prefix theorems are removed.
- **StatePreservation, MatchValues:** remove the stored-query invariant
  `Database.RulesSafe` and its `CmdStep.rulesSafe` preservation theorem.
  Retain `Cmd.QueriesSafe` and `Program.QueriesSafe` as static conditions on
  the explicit rule queries; `Program.queriesSafe_of_rules` now takes
  membership in `P.rules`. As before, this condition concerns rule queries,
  not the final check. Round preservation receives conditions on the
  explicit rules. `reachable_wf_storeOk` concerns a command list.
- **Diagonal, DiagonalPreservation:** `Database.NoUnions` contains only
  `diag`; round and saturation preservation take union-freedom of their rule
  lists, and command/program preservation takes the corresponding command
  conditions. **DiagonalRound:** unchanged-round absorption takes both
  delete-freedom and union-freedom of its rule list, with no rule equality.
- **LiveTables:** inactive-ruleset identities become empty-rule-list
  identities (`R = []`). `empty_saturateReach` is specifically for `[]`;
  an arbitrary rule list may build terms from empty.
- **Merge:** retains assertion transport, recorded facts, and positive-rule
  monotonicity. Removes `congOn_setEnvRules` and `Recorded.setEnvRules`.
  `RunRules.mono` uses one explicit delete-free rule list and positive
  queries, with no comparison of stored rules.
- **SourceModel:** firing containment, round extension, round meaning,
  completed fixed points, and saturation closure use delete-freedom and
  ordering-freedom of the same explicit rule list. These conditions are
  independent of the database, so duplicated source/target conditions and
  rule-store equality disappear.
- **Finite:** `RunWrites.finite`, `RunErases.finite`, and
  `RunRules.finite_eqs` need only finite input equations; a rule list is
  already finite. Step/program finiteness concludes finite equations alone.
  `Database.FiniteStore` has only `eqs`. `FiniteStore.of_eqs_rules` retains
  its name but takes only equation finiteness.
- **Divergence, FiniteSaturation, ActionProgram:** rule-list and command-list
  substitutions described above; whole-program nondivergence uses
  `P.commands`. Well-founded saturation progress remains an explicit
  premise, including when rows can be deleted and rebuilt.
- **Source/Arity:** constructor names embed in
  `P.names = P.ctors.map Prod.fst ++ P.vars`. **Source/Domain:**
  `Cmd.ruleUnionFreeB_iff` means union-freedom of all a command's rules;
  added `Rule.deleteFree_of_monotone` and `Cmd.deleteFree_of_monotone`.
- **Source/Execution:** `Database.NoLits` concerns terms only; `Cmd.NoLits`
  concerns heads of every rule it runs. Round preservation takes the head
  condition explicitly. Program constructor membership includes commands
  and the final check. Removed `ruleset_ne_rebuild`, since ruleset names no
  longer exist. **Source/Ctors:** `Database.CtorsInState` concerns terms
  only; round preservation receives head constructor conditions and prefix
  conditions refer to `P.commands`.
- **Execution:** term-growth premises concern the executed rules/commands;
  stored-rule delete-freedom preservation disappears. Raw equation growth
  remains unconditional.
- **Interp:** remove finite rule-store projection and preservation lemmas
  and check-command refinement. `InterpReady` contains state invariants
  only; deletion and ordering restrictions are on the executed rules.
  `execRunRules_eq_fold_of_deleteFree` takes the rule list followed by its
  delete-freedom proof. `execRunRules_induction_ruleset` retains its public
  name but inducts over a rule list. `toDatabase_eq_of_fields` takes terms
  and equations only. `exec_programStep` and `exec_complete` use
  `ProgramStep Database.empty P.commands out`; source hypotheses are
  monotonicity of each command and `P.OrderingFree`. Completeness retains
  `P.NoSaturate` because executable saturation has finite fuel.
- **NoUnions, InterpDeletes:** `FDatabase.NoUnions` means empty raw equations
  only; union-freedom is an explicit round/command premise. One-round
  refinement from empty raw equations still permits arbitrary heads.
  `exec_programStep_noUnions` and `exec_complete_noUnions` use `P.commands`
  and `P.UnionFree`, with no monotonicity, ordering, or scope restrictions.
  Completeness retains `P.NoSaturate`. `execCmd_toDatabase` and
  `execCmd_success_iff_of_noSaturate` now need only `c.NoSaturate`; the old
  matching invariants were needed solely for removed check commands.
  `Congruence.exec_encode_programStep` relates `exec (encode P)` to
  `ProgramStep Database.empty (encode P).commands out`.
- **Final checks:** added `FDatabase.holds_iff_queryHolds` under closure and
  both row-index invariants. `exec_programStep_check` and
  `exec_programStep_check_noUnions` transport that check agreement to the
  simulated specification state. `observe_eq_exec` identifies command
  execution followed by the final check; `observe_eval_of_exec`,
  `observe_eval`, and `observe_eval_noUnions` cover both successful and
  failed checks, preserving `Result.succeeded`.
- **SourceProof/Rules, SourceProof/Soundness, Provenance/Model,
  Provenance/GeneratedClaim, Provenance/GeneratedSoundness,
  Resugar/Soundness:** source rule certificates use `P.rules` membership
  and lookup by rule index. Reached-state premises are
  `ProgramStep Database.empty P.commands db`. Final saturation is
  `∀ c ∈ P.commands, RunSaturated c.rules db`; the source fragment supplies
  deletion and ordering restrictions for each list. `SourceProof.check_infers`,
  `Provenance.extract_checked`, `Resugar.extractAll_infers`, and
  `Resugar.certificates_infers` retain their soundness roles.
  `Resugar.lift_checked` follows `(Congruence.compile P).program` and the
  executable origin lookup.

## Test changes

Programs use `⟨commands, check⟩`, global actions are unconditional one-rule
runs, and certificate indices refer to flattened rule lists. The certificate
correctness tests retain explicit reached states and saturation under every
command's rules. `ProofPass` executes the actual compiler, provenance pass,
extraction, and lifting, and proves that its returned source claims are inferred.

`Examples` observes the final check separately from `exec`, including a
kernel-checked failed disequality followed through `observe_eval` to
`Eval.checkFailed`. `SemanticCong` verifies the final check after deletion,
simultaneous writes, and a stuck head, in addition to command refinement.
`SourceProof` additionally tests two rules in one command preceded by an empty
rule list, so command positions cannot be mistaken for rule indices.

## Semantic findings and limits

No new specification/source defect was established by this port. Existing
`SemanticCong.union_delete_nonheld_argument` still witnesses a mismatch between
arbitrary unions plus deletion and the specification projection;
`delete_does_not_preserve_closed` still witnesses loss of `Closed` after a
self-union and deletion. These explain the preserved delete-free source and
union-free target premises; neither theorem family claims unrestricted
union-plus-delete refinement. The current relational literal-deletion test
agrees with the specification, so the earlier literal-deletion discrepancy
recorded in the previous port is not present in this checkout.

The current executable `FDatabase`, unlike the brief's parenthetical field
list, also has no `rules` field. Its rule-store proof lemmas were removed.

Source-to-compiled-program equivalence remains the preexisting open proof
identified by `Congruence.Correctness` and `EgglogPaper`. The restored
`Congruence.exec_encode_programStep` proves agreement with the compiled
program's own specification, without claiming that open equivalence.

## Required root changes (outside this task's edit scope)

Remove these two imports from `EgglogSemantics.lean`; no additional import
changes are required for the retained library or tests:

```lean
import EgglogSemantics.Proofs.RuleStore
import EgglogSemantics.Proofs.Rules
```

`EgglogPaper.lean` already builds, but its temporary reduced audit can now be
restored. Add these imports alongside its existing `Proofs.OrderFinite` import:

```lean
import EgglogSemantics.Proofs.InterpDeletes
import EgglogSemantics.Proofs.Provenance.GeneratedSoundness
import EgglogSemantics.Proofs.Resugar.Soundness
```

The following main claims passed the dependency audit and can be asserted there
alongside the existing `Egglog.Term.blt_admissible` assertion:

```lean
assert_no_sorry Egglog.queryHolds_iff_validQuerySubst
assert_no_sorry Egglog.RunErases.eq_empty
assert_no_sorry Egglog.RunRules.eq_addEqs
assert_no_sorry Egglog.RunRules.eq_sUnion
assert_no_sorry Egglog.RunRules.wf
assert_no_sorry Egglog.Eval.det
assert_no_sorry Egglog.SourceMeaning.completion_closed_of_saturated
assert_no_sorry Egglog.patternHolds_iff
assert_no_sorry Egglog.FDatabase.holds_iff_queryHolds
assert_no_sorry Egglog.exec_programStep
assert_no_sorry Egglog.exec_complete
assert_no_sorry Egglog.observe_eval
assert_no_sorry Egglog.exec_programStep_noUnions
assert_no_sorry Egglog.exec_complete_noUnions
assert_no_sorry Egglog.observe_eval_noUnions
assert_no_sorry Egglog.Congruence.exec_encode_programStep
assert_no_sorry Egglog.SourceProof.check_infers
assert_no_sorry Egglog.Provenance.extract_checked
assert_no_sorry Egglog.Provenance.Generated.check_uf_infers
assert_no_sorry Egglog.Resugar.extractAll_infers
assert_no_sorry Egglog.Resugar.certificates_infers
```
