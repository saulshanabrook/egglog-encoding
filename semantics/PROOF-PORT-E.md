# Task E: nested schedules

## Status and validation

The full gate `lake build EgglogSemantics EgglogPaper` passes (1,087 jobs), including
all 71 in-scope proof modules and all six scoped test modules. All theorem names
asserted by `EgglogPaper.lean` are retained and pass its `assert_no_sorry` checks.
No module remains failing. The final combined rerun passed after all proof and test
edits, including the nested regressions and review.

Validation uses `source /tmp/proof-port-env.sh` and `lake build`, without network
access or Makefile targets. Existing worktree changes were preserved. Original
scoped files are backed up under `/tmp/proof-port-e-original`.

- Full combined build: `/tmp/proof-port-e-final.log`.
- Nested regression gate: `/tmp/proof-port-e-nested-tests.log`.
- Additional dependency audit: `/tmp/proof-port-e-audit.lean`, importing the complete
  library and paper and checking 24 additional theorem dependencies, passed. Its 11
  axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`.
  Results: `/tmp/proof-port-e-audit.log`.
- All 71 scoped modules are in the root/paper import dependency closure, including
  the new `Proofs/Schedule.lean`. `OrderFinite` and the round-level foundations
  build without changes. `Tests/SubtermExistence.lean` also needed no edits.
- No `sorry`, `axiom`, `native_decide`, or heartbeat-limit change was added.
- `git diff --check` passes for the task's edited tracked files.

## Statement changes

The uniform substitution is `Cmd` → `Schedule`, command/program-list execution →
`Reach db S d`, and `P.commands` → `P.schedule`. A round-list saturation becomes
`Reach db (.saturate (.run rs)) d`. No removed specification judgment or executable
runner is reintroduced.

- **Step, ActionProgram:** `Reach.wf` and `Reach.det` replace the separate command,
  saturation and program preservation/determinism proofs. `saturateReach_det`
  retains its name and accepts an arbitrary schedule body. `Reach.saturate_reach`
  expresses saturation as finitely many body passes. `Reach.seq_inv`, `Reach.append`
  and `Reach.append_inv` compose/split at a `Schedule.seq` boundary. The retained
  `cmdStep_saturate_iff` exposes the first body pass and its fixed-point/repeat
  alternative. List-specific `ProgramStep.nil_inv` disappears; empty-run identity
  remains in `LiveTables`.
- **Result:** `Eval.ok_iff`, `failed_iff`, `ok_of_no_checks` and determinism use
  schedule execution followed by the final check. `Eval.append*` composes a
  schedule prefix with the suffix program using `Schedule.seq`.
- **Scope:** `Reach.exists_of_noSaturate` and `Reach.exists_of_scoped` prove progress
  for saturation-free schedules. Scoping is not needed for schedule progress:
  a round omits stuck heads. `Eval.exists_of_scoped` then decides the final check.
- **Finite, DiagonalPreservation:** finiteness, finite-store preservation and
  `NoUnions` preservation induct on `Reach`; rule conditions pass to each child
  of a sequence. `Reach.finite[_from_empty]`, `Reach.finiteStore[_from_empty]`
  and `Reach.noUnions` replace the corresponding three old judgment families.
- **LiveTables:** `empty_saturateReach` is now
  `Reach empty (.saturate (.run [])) empty`; empty-rule round/saturation identities
  retain their previous premises.
- **FiniteSaturation, SourceModel:** existing well-founded/measure termination
  results and `saturation_completion_closed` retain their rule-list premises and
  names, with `.saturate (.run rs)` as their schedule. They do not assert that each
  constituent run of an arbitrary nested saturation is independently saturated.
- **Divergence:** `InfinitePasses.reachable` replaces the old trace helper;
  `not_infinitePasses_of_wellFounded` excludes infinite changing schedule passes.
  The changing-run lemmas use `Reach db (.run rs) d ∧ Cong db ≠ Cong d` directly.
  `Diverges.append_iff` splits divergence at `Schedule.seq`.
  `not_cmdDiverges_of_allConstructors` and
  `not_programDiverges_of_allConstructors` retain their names and prove that
  `NoSaturate` schedules/programs never diverge. The well-founded round theorem
  excludes `Diverges db (.saturate (.run rs))` by induction at reachable states.
- **StatePreservation:** `Schedule.QueriesSafe` quantifies over `S.rules`;
  `Program.QueriesSafe` is its schedule's condition. `queriesSafe_of_rules` takes
  `P.rules` membership directly. `reachable_wf_storeOk` takes `Reach`.
- **Source/Domain:** `Schedule.ruleUnionFreeB_iff` and
  `Schedule.deleteFree_of_monotone` replace their command counterparts.
- **Source/Execution, Source/Ctors:** `Schedule.NoLits` and `Schedule.CtorsIn`
  quantify over schedule rules. The existing `cmdStep_*`/`programStep_*`
  preservation names now take one `Reach` and the schedule's invariant. Prefix
  theorems admit any schedule with `S.rules ⊆ P.rules`. `mem_program_ctors` uses
  this rule inclusion; `Program.OrderingFree.of_mem` now takes one rule in
  `P.rules`. Literal-free domain lemmas take `P.schedule.litFreeB = true`.
- **Schedule (new):** `Reach.preserves` and `Reach.transport` lift round invariants
  and semantic simulations. `execSchedule_preserves` and `execSchedule_refines`
  cover schedule recursion and induction on the saturation pass counter. If the
  specification reaches a semantic fixed point before the structural runner,
  further successful passes preserve its meaning. `execSchedule_exists` proves
  saturation-free executable progress for any fuel. `execSaturate_run` and
  `execSchedule_saturate_run` relate single-run saturation to `runSaturateF`.
- **Interp:** `execSchedule_reach` proves soundness for arbitrary nested schedules
  with delete-free, ordering-free rules. Existing public `execCmd_*` and
  `execProgram_*` names remain, with schedule arguments and `execSchedule fuel`.
  Program monotonicity hypotheses now read `p.schedule.monotoneB = true` (the
  final check need not be monotone). `exec_programStep`, `exec_complete`, check
  agreement and `observe_eval*` use `p.schedule`. Completeness keeps `NoSaturate`
  and works for any fuel. Round-level iteration/saturation theorems remain.
- **NoUnions, InterpDeletes:** executable union-freedom and closure lift through
  arbitrary nested schedules. `execSchedule_reach_noUnions` and all retained
  `exec*_*noUnions` interfaces preserve deletion, disequality and `min` support
  without extra source-fragment assumptions. Completeness keeps `NoSaturate`.
  `Congruence.exec_encode_programStep` uses the compiled program's schedule.
- **Execution:** term growth uses delete-freedom of schedule rules; raw equation
  growth remains unconditional. The existing program growth and containment
  names take a schedule and `execSchedule fuel`. Append splitting uses `.seq`.
- **SourceProof/Rules, SourceProof/Soundness, Provenance/GeneratedClaim,
  Provenance/GeneratedSoundness, Resugar/Soundness:** reached-state premises are
  `Reach empty P.schedule db`; final saturation is
  `∀ rs ∈ P.runs, RunSaturated rs db`. Rule lookup remains by position in `P.rules`.
  `Schedule.mem_rules_iff`/`Program.mem_rules_iff` locate the enclosing run without
  confusing a rule index with a schedule position. All named certificate soundness
  conclusions are retained.

## Tests

The five edited scoped tests and `Provenance/Counterexamples` construct schedules
with `Schedule.seqAll` or `.seq`, and saturate schedule bodies. Relational execution
uses `Relational.execSchedule runFuel`. The explicit certificate-correctness fixtures
still prove reached states, saturation of every run, and inferred source claims.

Concrete kernel checks rewrite the well-founded mutual runner with its proved
computation equations before `decide +kernel`. There is no native proof shortcut.
The previous redundant-spelling, deletion, simultaneous-write, stuck-head,
failed-check, extraction and lifting regressions still pass.

New regressions cover a sequence inside saturation containing another saturation:
both levels first change and then settle, both interpreter refinement interfaces
produce the same specification result, and zero fuel fails explicitly. The public
`observe` also succeeds. The grouped source-certificate regression now has empty
runs and nested saturation and still checks the same flattened rule indices.

## Deleted modules

None. Namespaced lemmas about removed judgments were replaced by the `Reach`,
`Diverges`, `InfinitePasses` and `Schedule` interfaces described above.

## Semantic issues and blockers

No new semantic defect was established. No out-of-scope edit is needed.
The existing `union_delete_nonheld_argument` and `delete_does_not_preserve_closed`
regressions still witness limits on unrestricted union-plus-delete refinement;
the restored theorems retain their delete-free source/union-free target premises.

The compiler's full source-to-target behavior equivalence remains the preexisting
open statement in `Congruence.Correctness`, outside this proof port.
`Congruence.exec_encode_programStep` proves refinement of the compiled program's
own specification, as before.

## Root import changes

None required. `Proofs/Schedule.lean` is imported by `Proofs/Interp.lean` and hence
already lies in both root dependency closures. `EgglogSemantics.lean` and
`EgglogPaper.lean` were not edited.
