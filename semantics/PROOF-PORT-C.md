# Task C: interpreter refinement with deletes

## Completed and building

`lake build EgglogSemantics EgglogPaper difftest` passes (1808 jobs;
`/tmp/proof-port-c-final-gate.log`). No module remains failing.

Files changed by this task:

- `Proofs/Deletes.lean` (new): specification deletion laws on diagonal stores.
- `Proofs/InterpDeletes.lean` (new): deletion, round, iteration, saturation,
  command/program refinement, and nonsaturating completeness.
- `Proofs/Interp.lean`: optional erase-list refinement and general round factoring;
  corrected the header's obsolete claim that the absent-delete regression still
  refutes deletion refinement.
- `Proofs/Writes.lean`: `Action.erase_agree` and `Action.erases_agree`.
- `Tests/SemanticCong.lean`: seven new kernel-checked regression theorems.

No files or theorems were deleted. No existing theorem statement or name changed,
including every theorem asserted by `EgglogPaper.lean`. All preexisting out-of-scope
changes were left intact. Neither root import list was edited.

The extension is separate because `Proofs/NoUnions` already imports
`Proofs/Interp`; putting the `NoUnions` corollaries in `Interp` would create an
import cycle. Generic round factoring remains in `Interp` and reuses its private
matching/write proofs without exposing them.

## New principal statements

All names below are in `Egglog`.

- `Cong.iff_eq_and_mem_of_diag`: on a diagonal database, `Cong db a b` iff
  `a = b` and `a ∈ db.terms`.
- `Database.proper_subterm_mem_deleteRows`: every proper subterm of a pre-state
  term survives deletion. This holds without a diagonality premise, including
  simultaneous deletion of both parent and child.
- `Database.mem_deletedRows_of_diag` and `Database.mem_deleteRows_terms_of_diag`:
  diagonal deletion removes held application rows by identity. Its resulting
  term census consists of old terms which are literals, are not requested for
  deletion, or occur properly inside another old term.
- `Database.SameMeaning.deleteRows_of_diag`: deletion respects `SameMeaning`
  when both pre-states are diagonal, independently of redundant subterm assertions.
- `FDatabase.toDatabase_deleteAtoms`: for **any** subterm-closed finite state with
  reflexive raw equations (`EqsRefl`) and **any** list `X`,
  `(d.deleteAtoms d.closureF X).toDatabase` has the same meaning as
  `d.toDatabase.deleteRows {t | t ∈ X}`. Empty raw equations, `Closed`, index
  invariants, and scoping of targets are not needed for this deletion theorem.
- `FDatabase.SubtermClosed.deleteAtoms`, `IndexOk.deleteAtoms`, and
  `IndexCurrent.deleteAtoms`: these invariants survive deletion for arbitrary
  closure arguments and erase lists. `closed_deleteAtoms_of_eqs_empty` additionally
  preserves `Closed` when the raw equation list is empty.
- `actionDeletes_erase` / `actionsDeletes_erases` and
  `roundDeletes_eq_RunErases`: executable optional erase lists and the complete
  pre-state round erase list denote the specification's erase sets, including
  heads which fail. The round identity uses `Closed`, `IndexOk`, and `IndexCurrent`.
- `execRunRules_deletes_writes`: arbitrary rounds refine the union of writes over
  their executable deletion base, assuming that base is `Closed` and the pre-state
  has the matching invariants. `closed_execRunRules_of_deleteAtoms` and
  `execRunRules_index_of_deleteAtoms` factor preservation through that same base.
- `execRunRules_RunRules_of_eqs_empty`: **one round with arbitrary heads**, including
  unions, refines `RunRules` up to `SameMeaning`, assuming `SubtermClosed`, empty raw
  equations, `IndexOk`, and `IndexCurrent`. A subsequent round needs its own premises.
- `Database.SameMeaning.matches_iff`: patterns transport at the same environment
  under `SameMeaning`, without any syntax restrictions.
  `queryMatches_iff_of_diag`, `queryHolds_iff_of_diag`, and `runRules_of_diag` also
  transport binding domains and rounds between diagonal states. Queries may use
  disequality and `min`; round heads are unrestricted.

The six requested extensions are:

1. `execRunRules_RunRules_noUnions`
2. `execRunRules_iterate_noUnions`
3. `runSaturateF_saturateReach_noUnions`
4. `execCmd_cmdStep_noUnions`
5. `execProgram_programStep_noUnions`
6. `exec_programStep_noUnions`

The arbitrary-initial-state statements require `SubtermClosed`, `IndexOk`,
`IndexCurrent`, and `FDatabase.NoUnions`; programs additionally require
`Program.UnionFree`. The from-empty statement needs **only** `Program.UnionFree`
and successful `exec`. There are no WF, monotonicity, ordering-freedom, scoping,
or arity premises. The command theorem even permits registration of an arbitrary
rule; continued union-free execution requires that registered head to be union-free.
Saturation soundness handles extra structurally redundant rounds after the
specification reaches its semantic fixpoint.

Additional results:

- `execRunRules_index_with_deletes` preserves both index invariants without a
  delete-free premise. `closed_execRunRules_noUnions`, `closed_iterate_noUnions`,
  `execCmd_closed_noUnions`, `execProgram_closed_noUnions`, and
  `exec_closed_noUnions` establish closure throughout union-free execution.
- `execProgram_complete_noUnions` and `exec_complete_noUnions` give executable
  results with the specified meaning for every successful **nonsaturating**
  union-free specification execution.
- `execCmd_success_iff_of_noSaturate` equates executable and specification success
  for nonsaturating commands under only closure/index invariants. This success-only
  statement does not require union-freedom, even in the initial state.
- `Congruence.exec_encode_programStep` specializes soundness to `Congruence.encode P`
  using the existing `Congruence.encode_unionFree P`. Every successful reference
  execution of that compiled program has a specification execution of the compiled
  program with the same meaning. It does **not** assert equivalence to source `P`.

## Regressions and remaining limits

The existing absent-row deletion theorems and `delete_does_not_preserve_closed`
remain unchanged. New `Tests.SemanticCong` theorems are:

- `self_union_delete_sameMeaning`: deletion still refines the specification for a
  reflexive raw union, despite failure of the stronger `Closed` invariant.
- `parent_child_delete`: simultaneous parent/child deletion keeps the child and
  removes the parent in the specification.
- `delete_min_disequality_saturation`: a concrete successful run uses all three
  features, reaches saturation, represents the replacement row, and no longer
  represents the old row in its specification result.
- `simultaneous_deletes_before_writes`: all firings read the pre-state, and writes
  survive deletes, including a write preceding a delete within a syntactic head.
- `stuck_head_no_effect`: an unbound variable makes the whole head contribute neither
  its preceding deletes nor its preceding writes.
- `union_delete_nonheld_argument`: with `a = b` and held `R(f(a))`, the specification
  recognizes `R(f(b))` as the same row, while executable `sameRow` returns false
  because `f(b)` is absent from finite closure. This is a concrete matching mismatch
  outside diagonal states, not a proved unrestricted deletion bridge. Extending
  refinement to arbitrary union states needs a semantic comparison of nonheld
  target spellings (or additional target-argument premises) and a solution to
  dangling reflexive raw equations. `Impl/Interp.lean` was not changed.
- `relational_literal_delete_difference`: the separate
  `Congruence/Relational.lean` runtime removes a lone literal requested for deletion;
  the reference runtime and specification preserve it because literals are not
  application rows. The example is an unscoped literal delete. A general equivalence
  for that runtime must restrict delete targets or change its `deleteAtoms` filter
  to ignore literals. No out-of-scope runtime was changed.

Unproved: unrestricted mixed union/delete program refinement; equivalence of the
separate relational runtime with the reference runtime; source/compiler correctness;
and saturation completeness (the executable has finite fuel). None blocks the six
new union-free reference-interpreter refinement theorems. No new defect in `Spec/`
or `Source/` was found.

## Validation

- Baseline gate passed: `/tmp/proof-port-c-baseline.log`.
- Intermediate full gate passed after round refinement:
  `/tmp/proof-port-c-round-gate.log`.
- Final gate passed: `/tmp/proof-port-c-final-gate.log`.
- `assert_no_sorry` and `#print axioms` audited **57 declarations**, covering every
  public theorem in both new modules, the new core helpers, and all SemanticCong
  regressions. Only `propext`, `Classical.choice`, and `Quot.sound` occur; some
  theorems use no axioms. Audit source/log:
  `/tmp/proof-port-c-audit.lean`, `/tmp/proof-port-c-audit.log`.
- All five touched Lean files pass source/whitespace checks. No `sorry`, `admit`,
  added `axiom`, `native_decide`, or heartbeat override was introduced.
- All computation in the new regression proofs uses `decide +kernel`; no native
  decision tactic is used. No Makefile target or network operation was run.

## Root/paper integration

`EgglogSemantics.lean` already reaches the extension through the updated
`Tests.SemanticCong` import, so the full gate passes without editing it. For explicit
library exports, add:

```lean
import EgglogSemantics.Proofs.Deletes
import EgglogSemantics.Proofs.InterpDeletes
```

`EgglogPaper.lean` should import `EgglogSemantics.Proofs.InterpDeletes` and may add:

```lean
assert_no_sorry Egglog.Database.SameMeaning.deleteRows_of_diag
assert_no_sorry Egglog.FDatabase.toDatabase_deleteAtoms
assert_no_sorry Egglog.execRunRules_RunRules_of_eqs_empty
assert_no_sorry Egglog.execRunRules_RunRules_noUnions
assert_no_sorry Egglog.execRunRules_iterate_noUnions
assert_no_sorry Egglog.runSaturateF_saturateReach_noUnions
assert_no_sorry Egglog.execCmd_cmdStep_noUnions
assert_no_sorry Egglog.execProgram_programStep_noUnions
assert_no_sorry Egglog.exec_programStep_noUnions
assert_no_sorry Egglog.exec_complete_noUnions
assert_no_sorry Egglog.Congruence.exec_encode_programStep
```

No existing import or audit assertion needs removal or renaming.
