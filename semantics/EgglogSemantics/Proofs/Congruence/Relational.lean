import EgglogSemantics.Congruence.Relational
import EgglogSemantics.Proofs.Congruence.Properties

/-!
# Execution without equality reasoning: equivalence

This target interpreter never computes congruence closure. Its equality relation is the
diagonal of the stored values: testing a pair requires structural identity and existence.
The same finite relation serves query matching and function-key collision detection.
Generated UF and rebuilding rules run as ordinary table rules.

The equivalence proof applies to every union-free program, including merge bodies and
rule heads. Thus compiling away `union` is sufficient to remove the runtime's equality
axioms, rather than merely hiding them behind a different syntax.
-/

namespace Egglog.Relational

theorem matchQuery_eq {d : FDatabase} (h : d.EqsRefl) (q : Query) :
    matchQuery d q = Egglog.matchQuery d q := by
  simp only [matchQuery, Egglog.matchQuery, patternHolds_eq h]

theorem runRules_eq {d : FDatabase} (h : d.EqsRefl) (R : RulesetName) :
    runRules R d = execRunRules R d := by
  have hf : fireRule d = Egglog.fireRule d := by
    funext acc r
    simp only [fireRule, Egglog.fireRule, matchQuery_eq h]
  simp only [runRules, execRunRules, hf]

/-- With structural equality, the runtime's implicit re-keying does nothing. -/
theorem rebuild_diagonal (d : FDatabase) :
    FDatabase.rebuild (diagonal d) d = { d with rows := d.rows.dedup } := by
  have hc (t : Term) : FDatabase.canonOf (diagonal d) d.terms t = t := by
    rcases FDatabase.canonOf_spec (cl := diagonal d) (ts := d.terms) (t := t) with
      h | ⟨_, h | h⟩
    · exact h
    · exact h
    · exact (mem_diagonal.mp h).1.symm
  have hr (r : Row) : d.rebuildRow (diagonal d) r = r := by
    simp only [FDatabase.rebuildRow, FDatabase.canonKeyOf]
    split
    · simp only [List.map_congr_left (g := id) (fun t _ => hc t), List.map_id]
    · rfl
  have hm : (d.rows.map fun r => (d.rebuildRow (diagonal d) r, r)) =
      d.rows.map fun r => (r, r) := List.map_congr_left fun r _ => by rw [hr]
  simp [FDatabase.rebuild, hm, List.filter_map, Function.comp_def]

theorem mergeRound_eq {d : FDatabase} (h : d.EqsRefl) :
    mergeRound d = d.mergeRound := by
  rw [mergeRound, mergeRoundWith_eq, ← rebuild_diagonal d, diagonal_eq_closure h]
  rfl

theorem mergeSaturate_eq (n : Nat) {d : FDatabase} (h : d.NoUnions) :
    mergeSaturate n d = d.mergeSaturateF n := by
  induction n generalizing d with
  | zero =>
    simp only [mergeSaturate, FDatabase.mergeSaturateF, FDatabase.settled,
      mergeRound_eq (eqsRefl_of_noUnions h)]
    rfl
  | succ n ih =>
    simp only [mergeSaturate, FDatabase.mergeSaturateF, FDatabase.settled,
      mergeRound_eq (eqsRefl_of_noUnions h), ih (mergeRound_noUnions h)]
    rfl

theorem runRound_eq {d : FDatabase} (h : d.NoUnions) (R : RulesetName) :
    runRound R d = d.runRoundM R := by
  change mergeSaturate mergeFuel (runRules R d) =
    FDatabase.mergeSaturateF mergeFuel (execRunRules R d)
  exact (congrArg (mergeSaturate mergeFuel) (runRules_eq (eqsRefl_of_noUnions h) R)).trans
    (mergeSaturate_eq mergeFuel (execRunRules_noUnions h))

attribute [local irreducible] runRound FDatabase.runRoundM

theorem runSaturate_eq (R : RulesetName) (n : Nat) {d : FDatabase} (h : d.NoUnions) :
    runSaturate R n d = d.runSaturateM R n := by
  induction n generalizing d with
  | zero =>
    exact congrArg (fun o : Option FDatabase =>
      o.bind fun e => if d.sameData e then some d else none) (runRound_eq h R)
  | succ n ih =>
    change (runRound R d).bind _ = (d.runRoundM R).bind _
    rw [runRound_eq h R]
    apply Option.bind_congr
    intro e he
    by_cases hd : d.sameData e = true
    · simp only [hd, if_true]
    · simp only [hd]
      exact ih (runRoundM_noUnions h he)

theorem execCmd_eq {d : FDatabase} (h : d.NoUnions) {c : Cmd} (hc : c.UnionFree) :
    execCmd d c = d.execCmdM c := by
  cases c with
  | action a =>
    simp only [execCmd, FDatabase.execCmdM]
    apply Option.bind_congr
    intro e he
    exact mergeSaturate_eq mergeFuel (execAction_noUnions hc h he)
  | rule _ | decl _ _ => rfl
  | check q => simp only [execCmd, FDatabase.execCmdM, matchQuery_eq (eqsRefl_of_noUnions h)]
  | run R =>
    simp only [execCmd, FDatabase.execCmdM]
    exact runRound_eq h R
  | saturate R =>
    simp only [execCmd, FDatabase.execCmdM]
    exact runSaturate_eq R runFuel h

theorem execProgram_eq {p : Program} {d : FDatabase}
    (hp : p.UnionFree) (h : d.NoUnions) : execProgram d p = d.execProgramM p := by
  induction p generalizing d with
  | nil => rfl
  | cons c cs ih =>
    simp only [execProgram, FDatabase.execProgramM, execCmd_eq h hp.1]
    apply Option.bind_congr
    intro e he
    exact ih hp.2 (execCmdM_noUnions hp.1 h he)

theorem exec_eq {p : Program} (h : p.UnionFree) : exec p h = execM p :=
  execProgram_eq h empty_noUnions

end Egglog.Relational

namespace Egglog.Congruence

/-- The target's built-in equality remains diagonal; equality is represented by tables. -/
theorem execM_encode_eqsRefl {P : Program} {tgt : FDatabase}
    (h : execM (encode P) = some tgt) : tgt.EqsRefl := by
  intro p hp
  rw [(execM_noUnions (encode_unionFree P) h).eqs] at hp
  simp at hp


/-- The congruence pass needs no equality closure in its target runtime. -/
theorem encode_relational (P : Program) :
    Relational.exec (encode P) (encode_unionFree P) = execM (encode P) :=
  Relational.exec_eq (encode_unionFree P)

/-- No built-in equality between distinct terms can hold after compilation. -/
theorem encode_cong_iff {P : Program} {d : FDatabase}
    (h : execM (encode P) = some d) (a b : Term) :
    Cong d.toDatabase a b ↔ a = b ∧ a ∈ d.terms := by
  rw [← FDatabase.mem_closureF_iff, ← Relational.diagonal_eq_closure (execM_encode_eqsRefl h),
    Relational.mem_diagonal]

end Egglog.Congruence
