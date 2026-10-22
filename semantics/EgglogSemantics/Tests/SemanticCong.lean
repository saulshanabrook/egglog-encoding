import EgglogSemantics.Proofs.Query
import EgglogSemantics.Proofs.InterpDeletes
import EgglogSemantics.Congruence.Relational

namespace Egglog.Tests.SemanticCong

private def a : Term := .app "a" []
private def b : Term := .app "b" []
private def f (t : Term) : Term := .app "f" [t]
private def d : Database := (Database.empty.addEq a b).addTerm (f a)

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
  | subterm _ _ ih => exact ih
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | congr _ _ ih _ => exact ih
  | nil => trivial
  | cons => trivial

/-- Deleting an absent row changes nothing in the specification. -/
theorem absent_delete_spec : Database.empty.deleteRows {f a} = Database.empty := by
  apply Database.ext <;> try rfl
  ext p
  simp [Database.deleteRows, Database.deletedRows, Database.empty]

/-- The executable deletion only filters terms, and hence leaves an empty store empty. -/
theorem absent_delete_exec :
    FDatabase.empty.deleteAtoms FDatabase.empty.closureF [f a] = FDatabase.empty := rfl

/-- Deleting an absent row agrees between the executable store and the specification. -/
theorem absent_delete_sameMeaning :
    (FDatabase.empty.deleteAtoms FDatabase.empty.closureF [f a]).toDatabase.SameMeaning
      (Database.empty.deleteRows {f a}) := by
  rw [absent_delete_exec, FDatabase.toDatabase_empty, absent_delete_spec]
  exact Database.SameMeaning.refl _

/-- Deleting a self-unioned row leaves a filtered-out reflexive equation in the finite list.
`Closed` therefore needs a delete-free premise, even though the projection is sound here. -/
theorem delete_does_not_preserve_closed :
    ¬ ((FDatabase.empty.addEq a a).deleteAtoms
      (FDatabase.empty.addEq a a).closureF [a]).Closed := by
  intro hc
  have hp : (a,a) ∈ ((FDatabase.empty.addEq a a).deleteAtoms
      (FDatabase.empty.addEq a a).closureF [a]).eqs := by decide
  have ht : ((FDatabase.empty.addEq a a).deleteAtoms
      (FDatabase.empty.addEq a a).closureF [a]).terms = [] := rfl
  have hm := (hc.eqs (a,a) hp).1
  rw [ht] at hm
  cases hm


/-- The bridge still holds for a self-union, although deletion breaks `Closed`. -/
theorem self_union_delete_sameMeaning :
    ((FDatabase.empty.addEq a a).deleteAtoms
      (FDatabase.empty.addEq a a).closureF [a]).toDatabase.SameMeaning
      ((FDatabase.empty.addEq a a).toDatabase.deleteRows {a}) := by
  simpa using FDatabase.toDatabase_deleteAtoms
    ((FDatabase.empty_closed.addEq a a).subterms)
    (by
      intro p hp
      have hp : p = (a, a) := by simpa [FDatabase.addEq, FDatabase.empty] using hp
      cases hp
      rfl) [a]

/-- Simultaneously deleting a parent and its child keeps the child and removes the parent. -/
theorem parent_child_delete :
    a ∈ (((FDatabase.empty.addTerm (f a)).toDatabase).deleteRows {f a, a}).terms ∧
      f a ∉ (((FDatabase.empty.addTerm (f a)).toDatabase).deleteRows {f a, a}).terms := by
  let d := FDatabase.empty.addTerm (f a)
  have hc : d.SubtermClosed := FDatabase.empty_closed.subterms.addTerm _
  have hd : d.EqsRefl := by simp [d, FDatabase.EqsRefl, FDatabase.addTerm, FDatabase.empty]
  have hmean := FDatabase.toDatabase_deleteAtoms hc hd [f a, a]
  have hdiag : (d.deleteAtoms d.closureF [f a, a]).EqsRefl := by
    simp [FDatabase.EqsRefl, FDatabase.deleteAtoms, d, FDatabase.addTerm, FDatabase.empty]
  have ht := hmean.terms_eq_of_diag hdiag.toDatabase (hd.toDatabase.deleteRows _)
  have hX : {t | t ∈ [f a, a]} = ({f a, a} : Set Term) := by ext t; simp
  rw [hX, FDatabase.toDatabase_terms (hc.deleteAtoms _ _)] at ht
  change a ∈ (d.toDatabase.deleteRows {f a, a}).terms ∧
    f a ∉ (d.toDatabase.deleteRows {f a, a}).terms
  rw [← ht]
  decide +kernel

private def replaceRows : Program :=
  ⟨[.run [⟨[], [.expr (.app "R" [.app "b" []]), .expr (.app "a" [])]⟩],
    .saturate [⟨[.expr (.app "R" [.var "x"]), .ne (.var "x") (.app "a" [])],
      [.delete (.app "R" [.var "x"]),
        .expr (.app "R" [.min (.var "x") (.app "a" [])])]⟩]],
    [.expr (.app "R" [.app "a" []]) ]⟩

/-- A checked execution actually replaces a row using deletion, disequality and `min`,
then semantically saturates. The old row is absent in the specification result. -/
theorem delete_min_disequality_saturation :
    ∃ out, ProgramStep Database.empty replaceRows.commands out ∧ QueryHolds out replaceRows.check ∧
      Cong out (.app "R" [a]) (.app "R" [a]) ∧
      ¬ Cong out (.app "R" [b]) (.app "R" [b]) := by
  have hu : replaceRows.UnionFree := by simp [replaceRows, Cmd.rules, Action.UnionFree]
  have hs : (exec replaceRows).any (fun d =>
      d.terms.contains (.app "R" [a]) && !d.terms.contains (.app "R" [b])) = true := by
    decide +kernel
  obtain ⟨e, he, hm⟩ := (Option.any_eq_true _ _).mp hs
  have hterms : Term.app "R" [a] ∈ e.terms ∧ Term.app "R" [b] ∉ e.terms := by
    simpa using hm
  obtain ⟨out, hout, hmean, hq⟩ := exec_programStep_check_noUnions hu he
  have hcheck : (exec replaceRows).any (fun d => d.holds replaceRows.check) = true := by
    decide +kernel
  rw [he] at hcheck
  have hn := exec_noUnions hu he
  refine ⟨out, hout, hq.mp hcheck, (hmean.congr _ _).mp (.direct (Or.inl ⟨rfl, hterms.1⟩)), ?_⟩
  intro hc
  have hc := (Cong.iff_eq_and_mem_of_diag hn.toDatabase.diag).mp
    ((hmean.congr _ _).mpr hc)
  exact hterms.2 ((FDatabase.mem_toDatabase_terms
    (exec_closed_noUnions hu he).subterms).mp hc.2)

private def sameRound : Program :=
  ⟨[.run [⟨[], [.expr (.app "a" [])]⟩],
    .run [⟨[.expr (.app "a" [])], [.delete (.app "a" [])]⟩,
      ⟨[.expr (.app "a" [])], [.expr (.app "a" []), .delete (.app "a" []),
        .expr (.app "b" [])]⟩]], [.expr (.app "a" []), .expr (.app "b" [])]⟩

/-- All firings see the pre-state, and all writes follow all deletes, including an
expression written before a delete in the same syntactic head. -/
theorem simultaneous_deletes_before_writes :
    Eval Database.empty sameRound .ok := by
  have hs : (exec sameRound).isSome = true := by decide +kernel
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check_noUnions
    (by simp [sameRound, Cmd.rules, Action.UnionFree]) he
  have hcheck : (exec sameRound).any (fun d => d.holds sameRound.check) = true := by
    decide +kernel
  rw [he] at hcheck
  exact .ok hout (hq.mp hcheck)

private def stuckHead : Program :=
  ⟨[.run [⟨[], [.expr (.app "a" [])]⟩],
    .run [⟨[], [.delete (.app "a" []), .expr (.app "b" []), .expr (.var "unbound")]⟩]],
    [.expr (.app "a" [])]⟩

/-- An undefined head contributes neither its earlier deletes nor its earlier writes. -/
theorem stuck_head_no_effect :
    Eval Database.empty stuckHead .ok := by
  have hs : (exec stuckHead).any (fun d => !d.terms.contains b) = true := by decide +kernel
  obtain ⟨e, he, _⟩ := (Option.any_eq_true _ _).mp hs
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check_noUnions
    (by simp [stuckHead, Cmd.rules, Action.UnionFree]) he
  have hcheck : (exec stuckHead).any (fun d => d.holds stuckHead.check) = true := by
    decide +kernel
  rw [he] at hcheck
  exact .ok hout (hq.mp hcheck)


private def unionRows : FDatabase :=
  (FDatabase.empty.addEq a b).addTerm (.app "R" [f a])

/-- Outside diagonal states, a delete target can use a congruent spelling absent from
finite closure. This is an obstacle to unrestricted union/delete refinement. -/
theorem union_delete_nonheld_argument :
    unionRows.toDatabase.SameRow (.app "R" [f a]) (.app "R" [f b]) ∧
      FDatabase.sameRow unionRows.closureF (.app "R" [f a]) (.app "R" [f b]) = false := by
  constructor
  · have hab : Cong unionRows.toDatabase a b :=
      .direct (Or.inr ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩)
    have hfa : Cong unionRows.toDatabase (f a) (f a) :=
      .direct (Or.inl ⟨rfl, by decide +kernel⟩)
    exact ⟨"R", [f a], [f b], rfl, rfl, .cons (.congr hfa (.cons hab .nil)) .nil⟩
  · decide +kernel

/-- A literal is not a row: naming one for deletion changes nothing, in the specification,
in the reference runtime, and in the relational runtime. -/
theorem relational_literal_delete_agrees :
    let t := Term.lit (.int 0)
    let d := FDatabase.empty.addTerm t
    (Relational.deleteAtoms [t] d).terms = [t] ∧
      (d.deleteAtoms d.closureF [t]).terms = [t] := by
  decide +kernel

end Egglog.Tests.SemanticCong
