import EgglogSemantics.Proofs.Query
import EgglogSemantics.Proofs.InterpSubsume
import EgglogSemantics.Proofs.MatchMonotone
import EgglogSemantics.Congruence.Relational

namespace Egglog.Tests.SemanticCong

private def a : Term := .app "a" []
private def b : Term := .app "b" []
private def f (t : Term) : Term := .app "f" [t]
private def d : Database := (Database.empty.addEq a b).addTerm (f a)

/-- Adding a smaller spelling invalidates the old representative binding. -/
theorem representative_binding_not_monotone :
    let before := Database.empty.addTerm b
    let after := before.addEq a b
    before.Contained after ∧ ValidEnv ["x"] before [("x", b)] ∧
      ¬ ValidEnv ["x"] after [("x", b)] := by
  dsimp only
  refine ⟨Database.Contained.addEq _ _ _, ⟨by simp, ?_⟩, ?_⟩
  · intro binding hb
    obtain rfl := List.mem_singleton.mp hb
    rw [(Database.NoUnions.empty.diag.addTerm b).reps_eq_terms]
    exact Database.mem_addTerm _ _
  · intro h
    have hb := h.mem_reps ("x", b) (by simp)
    exact hb.2 a (StoredCong.direct (Set.mem_insert _ _)).mem_left
      (.direct (Set.mem_insert _ _)) (by decide +kernel)

/-- The positive query still matches after rebinding to a congruent representative. -/
theorem representative_query_transport :
    let before := (Database.empty.addTerm b).addTerm (f b)
    let after := before.addEq a b
    ∃ σ, QueryMatches after [.expr (.app "f" [.var "x"])] σ ∧
      SourceMeaning.EnvRelated after [("x", b)] σ := by
  dsimp only
  let before := (Database.empty.addTerm b).addTerm (f b)
  let after := before.addEq a b
  have hq : QueryMatches before [.expr (.app "f" [.var "x"])] [("x", b)] := by
    refine ⟨⟨by decide, ?_⟩, ?_⟩
    · intro binding hb
      obtain rfl := List.mem_singleton.mp hb
      rw [((Database.NoUnions.empty.diag.addTerm b).addTerm (f b)).reps_eq_terms]
      exact (Database.Contained.addTerm _ _).terms (Database.mem_addTerm _ _)
    · intro p hp
      obtain rfl := List.mem_singleton.mp hp
      exact .atom (Lookup.of_eval rfl (by decide) rfl (.direct (Set.mem_insert _ _))).2
  have hw : after.WF := ((Database.WF.empty.addTerm b).addTerm (f b)).addEq _ _
    (by simp [a, b, Term.isLit])
  have hf : after.eqs.Finite :=
    ((Set.finite_empty.insert (b, b)).insert (f b, f b)).insert (a, b)
  obtain ⟨σ, hσ, hrel⟩ := hq.transport (Database.Contained.addEq _ _ _)
    (fun t ht => ⟨ht.1.mono (Database.Contained.addEq _ _ _), by
      rintro ⟨u, hu, _⟩; exact hu⟩) hw
    (Database.hasReps_of_finite hf) (by decide)
    (by simp [Pattern.monotoneB])
  exact ⟨σ, hσ, hrel⟩

/-- Congruence represents a spelling absent from the stored subterms. -/
theorem alternate_spelling : Cong d (f a) (f b) := by
  apply Cong.congr (.direct (Set.mem_insert _ _))
  exact .cons (.direct (Or.inr (Set.mem_insert _ _))) .nil

theorem alternate_not_stored : f b ∉ d.terms := by
  simp [d, Database.addTerm_terms, Database.addEq_terms, a, b, f, Term.subterms_app]

private def cyclic : Database := Database.empty.addEq a (f a)

/-- A cycle can represent arbitrarily nested spellings without growing the binding domain. -/
theorem nested_represented : Cong cyclic (f (f a)) (f (f a)) := by
  have h : Cong cyclic a (f a) := .direct (Set.mem_insert _ _)
  have hf : Cong cyclic (f a) (f (f a)) := .congr (h.symm.trans h) (.cons h .nil)
  exact hf.symm.trans hf

theorem nested_not_stored : f (f a) ∉ cyclic.terms := by
  simp [cyclic, Database.addEq_terms, a, f, Term.subterms_app]

/-- Mentioning a term alone does not establish its existence. -/
theorem empty_has_no_facts {s t : Term} : ¬ Cong Database.empty s t := by
  intro h
  induction h using Cong.rec (motive_2 := fun _ _ _ => True) with
  | direct h => exact h
  | child _ _ ih => exact ih
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | congr _ _ ih _ => exact ih
  | nil => trivial
  | cons => trivial

/-- A variable lookup alone does not assert that its binding exists. -/
theorem unrepresented_variable_lookup :
    Matches Database.empty (.expr (.var "x")) [("x", a)] :=
  .atom (.var rfl)

/-- Evaluation of `min` can discard an absent operand; matching must read both. -/
theorem min_eval_does_not_imply_lookup :
    let db := Database.empty.addTerm (.lit (.int 0))
    let e := Expr.min (.lit (.int 0)) (.lit (.int 1))
    e.eval [] = some (.lit (.int 0)) ∧ Cong db (.lit (.int 0)) (.lit (.int 0)) ∧
      ¬ (e.eval [] = some (.lit (.int 0)) ∧ Expr.Matches db [] e) := by
  refine ⟨by decide +kernel, .direct (Set.mem_insert _ _), ?_⟩
  intro h
  have hl : Term.lit (.int 1) ∈ (Database.empty.addTerm (.lit (.int 0))).live := by
    cases h.2 with | min _ hb => cases hb with | lit hl => exact hl
  have hm := (Cong.iff_eq_and_mem_of_diag (Database.NoUnions.empty.diag.addTerm _)).mp hl.1
  simpa [Database.addTerm_terms, Term.subterms_lit] using hm.2

/-- Subsuming an absent row asserts it and marks it. -/
theorem absent_subsume_spec :
    (f a, f a) ∈ ((Database.empty.addTerm (f a)).addSubsumed {f a}).eqs ∧
    f a ∈ ((Database.empty.addTerm (f a)).addSubsumed {f a}).subsumed :=
  ⟨Set.mem_insert _ _, Or.inr rfl⟩

theorem absent_subsume_exec :
    f a ∈ (FDatabase.empty.subsume (f a)).terms ∧
    a ∈ (FDatabase.empty.subsume (f a)).terms ∧
    f a ∈ (FDatabase.empty.subsume (f a)).subsumed := by decide +kernel

theorem absent_subsume_sameMeaning :
    (FDatabase.empty.subsume (f a)).toDatabase.SameMeaning
      ((Database.empty.addTerm (f a)).addSubsumed {f a}) := by
  simpa only [FDatabase.toDatabase_empty] using
    FDatabase.toDatabase_subsume FDatabase.empty_closed (f a)

/-- Subsuming even a self-unioned row preserves the closure invariant. -/
theorem subsume_preserves_closed : ((FDatabase.empty.addEq a a).subsume a).Closed :=
  (FDatabase.empty_closed.addEq a a).subsume a

theorem self_union_subsume_sameMeaning :
    ((FDatabase.empty.addEq a a).subsume a).toDatabase.SameMeaning
      (((FDatabase.empty.addEq a a).toDatabase.addTerm a).addSubsumed {a}) :=
  FDatabase.toDatabase_subsume (FDatabase.empty_closed.addEq a a) a

/-- Both parent and child remain held after both are subsumed. -/
theorem parent_child_subsume :
    let d := ((FDatabase.empty.addTerm (f a)).subsume (f a)).subsume a
    a ∈ d.terms ∧ f a ∈ d.terms ∧ a ∈ d.subsumed ∧ f a ∈ d.subsumed := by
  decide +kernel

/-- Reasserting a row never makes it live again. Action order does not matter. -/
theorem writes_subsumes_commute :
    execActions [] FDatabase.empty [.subsume "f" [a.toExpr], .expr (f a).toExpr] =
      execActions [] FDatabase.empty [.expr (f a).toExpr, .subsume "f" [a.toExpr]] := by
  rfl

/-- Matching skips a subsumed row while the final check includes it. -/
theorem subsumed_not_matched_but_checked :
    let d := FDatabase.empty.subsume (f a)
    patternHolds d (.expr (f a).toExpr) [] = false ∧ d.holds [.expr (f a).toExpr] = true := by
  decide +kernel

/-- Congruent children identify one subsumed row, even at an unstored spelling. -/
theorem congruent_subsumed_spelling_not_matched :
    let d := (FDatabase.empty.addEq a b).subsume (f a)
    patternHolds d (.expr (f b).toExpr) [] = false ∧ d.holds [.expr (f b).toExpr] = true := by
  decide +kernel

/-- A round that only changes row liveness is not a semantic fixed point. -/
theorem subsumption_changes_sameMeaning :
    let d := Database.empty.addTerm (f a)
    ¬ d.SameMeaning (d.addSubsumed {f a}) := by
  intro d hm
  have hc : Cong d (f a) (f a) := .direct (Set.mem_insert _ _)
  have hl : f a ∈ d.live := ⟨hc, by rintro ⟨u, hu, _⟩; exact hu⟩
  have hl' := (hm.live _).mp hl
  exact hl'.2 ⟨_, Or.inr rfl,
    Database.SameRow.self_app ((hm.congr _ _).mp hc)⟩

private def replaceRows : Program :=
  ⟨Schedule.seqAll [.run [⟨[], [.expr (.app "R" [.app "b" []]), .expr (.app "a" [])]⟩],
    .saturate (.run [⟨[.expr (.app "R" [.var "x"]), .ne (.var "x") (.app "a" [])],
      [.subsume "R" [.var "x"],
        .expr (.app "R" [.min (.var "x") (.app "a" [])])]⟩])],
    [.expr (.app "R" [.app "a" []]) ]⟩

/-- Saturation replaces live rows while retaining the subsumed historical row. -/
theorem subsume_min_disequality_saturation :
    ∃ out, Reach Database.empty replaceRows.schedule out ∧
      QueryHolds out.forgetSubsumed replaceRows.check ∧
      Cong out (.app "R" [a]) (.app "R" [a]) ∧
      Cong out (.app "R" [b]) (.app "R" [b]) ∧ Term.app "R" [b] ∉ out.live := by
  have hu : replaceRows.UnionFree := by
    simp [replaceRows, Schedule.rules, Schedule.seqAll, Action.UnionFree]
  have hs : (exec replaceRows).any (fun d =>
      d.terms.contains (.app "R" [a]) && d.terms.contains (.app "R" [b]) &&
        d.subsumed.contains (.app "R" [b])) = true := by
    simp only [exec, replaceRows, Schedule.seqAll, execSchedule,
      execSchedule_saturate_run, Option.bind_some]
    decide +kernel
  obtain ⟨e, he, hm⟩ := (Option.any_eq_true _ _).mp hs
  have hterms : (Term.app "R" [a] ∈ e.terms ∧ Term.app "R" [b] ∈ e.terms) ∧
      Term.app "R" [b] ∈ e.subsumed := by simpa using hm
  obtain ⟨out, hout, hmean, hq⟩ := exec_programStep_check_noUnions hu he
  have hcheck : (exec replaceRows).any (fun d => d.holds replaceRows.check) = true := by
    simp only [exec, replaceRows, Schedule.seqAll, execSchedule,
      execSchedule_saturate_run, Option.bind_some]
    decide +kernel
  rw [he] at hcheck
  have hb : Cong e.toDatabase (.app "R" [b]) (.app "R" [b]) :=
    .direct (Or.inl ⟨rfl, hterms.1.2⟩)
  refine ⟨out, hout, hq.mp hcheck,
    (hmean.congr _ _).mp (.direct (Or.inl ⟨rfl, hterms.1.1⟩)),
    (hmean.congr _ _).mp hb, ?_⟩
  intro hl
  exact ((hmean.live _).mpr hl).2 ⟨_, hterms.2, Database.SameRow.self_app hb⟩

private def sameRound : Program :=
  ⟨Schedule.seqAll [.run [⟨[], [.expr (.app "a" [])]⟩],
    .run [⟨[.expr (.app "a" [])], [.subsume "a" []]⟩,
      ⟨[.expr (.app "a" [])], [.expr (.app "a" []), .subsume "a" [],
        .expr (.app "b" [])]⟩]], [.expr (.app "a" []), .expr (.app "b" [])]⟩

/-- All firings see the pre-state; the final check sees their writes and subsumed rows. -/
theorem simultaneous_writes_and_subsumes :
    Eval Database.empty sameRound .ok := by
  have hs : (exec sameRound).isSome = true := by
    simp only [exec, sameRound, Schedule.seqAll, execSchedule, Option.bind_some]
    decide +kernel
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check_noUnions
    (by simp [sameRound, Schedule.rules, Schedule.seqAll, Action.UnionFree]) he
  have hcheck : (exec sameRound).any (fun d => d.holds sameRound.check) = true := by
    simp only [exec, sameRound, Schedule.seqAll, execSchedule, Option.bind_some]
    decide +kernel
  rw [he] at hcheck
  exact .ok hout (hq.mp hcheck)

private def stuckHead : Program :=
  ⟨Schedule.seqAll [.run [⟨[], [.expr (.app "a" [])]⟩],
    .run [⟨[], [.subsume "a" [], .expr (.app "b" []), .expr (.var "unbound")]⟩]],
    [.expr (.app "a" [])]⟩

/-- An undefined head contributes neither its earlier marks nor its earlier writes. -/
theorem stuck_head_no_effect :
    Eval Database.empty stuckHead .ok := by
  have hs : (exec stuckHead).any (fun d => !d.terms.contains b) = true := by
    simp only [exec, stuckHead, Schedule.seqAll, execSchedule, Option.bind_some]
    decide +kernel
  obtain ⟨e, he, _⟩ := (Option.any_eq_true _ _).mp hs
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check_noUnions
    (by simp [stuckHead, Schedule.rules, Schedule.seqAll, Action.UnionFree]) he
  have hcheck : (exec stuckHead).any (fun d => d.holds stuckHead.check) = true := by
    simp only [exec, stuckHead, Schedule.seqAll, execSchedule, Option.bind_some]
    decide +kernel
  rw [he] at hcheck
  exact .ok hout (hq.mp hcheck)


private def unionRows : FDatabase :=
  (FDatabase.empty.addEq a b).addTerm (.app "R" [f a])

/-- Raw finite closure compares held children. The subsume operation first inserts its
target, ensuring that subsequent matching has those children available. -/
theorem sameRow_nonheld_argument :
    unionRows.toDatabase.SameRow (.app "R" [f a]) (.app "R" [f b]) ∧
      FDatabase.sameRow unionRows.closureF (.app "R" [f a]) (.app "R" [f b]) = false := by
  constructor
  · have hab : Cong unionRows.toDatabase a b :=
      .direct (Or.inr ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩)
    have hfa : Cong unionRows.toDatabase (f a) (f a) :=
      .direct (Or.inl ⟨rfl, by decide +kernel⟩)
    exact ⟨"R", [f a], [f b], rfl, rfl, .cons (.congr hfa (.cons hab .nil)) .nil⟩
  · decide +kernel

/-- Arbitrary records with unheld marked children need the stronger index invariant. -/
theorem unheld_mark_breaks_liveWith :
    let db := { unionRows with subsumed := [.app "R" [f b]] }
    db.liveWith db.closureF (.app "R" [f a]) = true ∧
      Term.app "R" [f a] ∉ db.toDatabase.live := by
  dsimp only
  refine ⟨by decide +kernel, ?_⟩
  intro hl
  apply hl.2
  refine ⟨.app "R" [f b], by simp [FDatabase.toDatabase], ?_⟩
  apply (Database.SameRow.iff_of_congr
    (fun s t => Cong.iff_of_eqs_eq (d := unionRows.toDatabase)
      (e := ({ unionRows with subsumed := [.app "R" [f b]] } : FDatabase).toDatabase)
      (a := s) (b := t) rfl)).mp
  exact sameRow_nonheld_argument.1

/-- Literal marks do not hide literals in either matching implementation. -/
theorem relational_literal_subsume_agrees :
    let t := Term.lit (.int 0)
    let d := FDatabase.empty.subsume t
    let e := Expr.lit (.int 0)
    e.eval [] = some t ∧ Relational.exprHolds d [] e = true ∧
      exprHoldsWith d.closureF d [] e = true := by
  decide +kernel

private def nestedProgram : Program :=
  ⟨.seq (.run [⟨[], [.expr (.app "a" [])]⟩])
    (.saturate (.seq
      (.run [⟨[.expr (.app "a" [])], [.expr (.app "b" [])]⟩])
      (.saturate (.run [⟨[.expr (.app "b" [])], [.expr (.app "c" [])]⟩])))),
    [.expr (.app "c" [])]⟩

-- The public runner reaches the result of both levels of saturation.
set_option linter.hashCommand false in
#guard (observe nestedProgram).any ExecutionResult.succeeded

/-- A sequence inside saturation, itself containing saturation, refines through both
interpreter theorems. Each level changes on its first pass and settles on its second. -/
theorem nested_saturation_reaches :
    ∃ out, Reach Database.empty nestedProgram.schedule out ∧
      Cong out (.app "c" []) (.app "c" []) := by
  have hs : (execSchedule 1 FDatabase.empty nestedProgram.schedule).any
      (fun d => d.terms.contains (.app "c" [])) = true := by
    simp only [nestedProgram, execSchedule, execSchedule_saturate_run, execSaturate,
      Option.bind_some]
    decide +kernel
  obtain ⟨e, he, hc⟩ := (Option.any_eq_true _ _).mp hs
  have hi : FDatabase.empty.IndexOk :=
    ⟨by simp [FDatabase.empty], by simp [FDatabase.empty]⟩
  have hj : FDatabase.empty.IndexCurrent := by
    simp [FDatabase.IndexCurrent, FDatabase.empty]
  have hd : ∀ r ∈ nestedProgram.schedule.rules, r.SubsumeFree := by
    simp [nestedProgram, Schedule.rules, Rule.SubsumeFree, Actions.SubsumeFree,
      Action.SubsumeFree, Action.monotoneB]
  obtain ⟨out, hr, _⟩ := execSchedule_reach FDatabase.empty_closed hi hj
    FDatabase.empty_wf hd (by decide) he
  obtain ⟨out', hr', hm'⟩ := execSchedule_reach_noUnions
    FDatabase.empty_closed.subterms hi hj .empty (by
      simp [nestedProgram, Schedule.rules, Action.UnionFree]) he
  have hout : out' = out := hr'.det hr
  have hmean := hout ▸ hm'
  refine ⟨out, by simpa only [FDatabase.toDatabase_empty] using hr,
    (hmean.congr _ _).mp ?_⟩
  exact .direct (Or.inl ⟨rfl, by simpa using hc⟩)

/-- Zero pass budget cannot complete the changing inner saturation. -/
theorem nested_saturation_exhausts :
    execSchedule 0 FDatabase.empty nestedProgram.schedule = none := by
  simp only [nestedProgram, execSchedule, execSchedule_saturate_run, execSaturate,
    Option.bind_some]
  decide +kernel

private def representativeSaturation : Program :=
  ⟨.seq (.run [⟨[], [.union (.app "a" []) (.app "b" []),
      .union (.app "a" []) (.app "g" [.app "b" []]),
      .expr (.app "f" [.app "a" []])]⟩])
    (.saturate (.run [⟨[.expr (.app "f" [.var "x"])],
      [.expr (.app "g" [.var "x"])]⟩])),
    [.expr (.app "g" [.app "a" []])]⟩

/-- Binding all held class members would keep building `g (g ...)`. Binding the
least spelling builds `g a` once and reaches a structural fixed point. -/
theorem representative_saturation_exec :
    (exec representativeSaturation).any (fun d => d.holds representativeSaturation.check &&
      !d.terms.contains (.app "g" [.app "g" [b]])) = true := by
  simp only [exec, representativeSaturation, execSchedule, execSchedule_saturate_run,
    Option.bind_some]
  decide +kernel

/-- The terminating representative-based execution proves specification success. -/
theorem representative_saturation_succeeds :
    Eval Database.empty representativeSaturation .ok := by
  obtain ⟨e, he, hcheck⟩ := (Option.any_eq_true _ _).mp representative_saturation_exec
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check (by decide) (by decide) he
  exact .ok hout (hq.mp (Bool.and_eq_true_iff.mp hcheck).1)

end Egglog.Tests.SemanticCong
