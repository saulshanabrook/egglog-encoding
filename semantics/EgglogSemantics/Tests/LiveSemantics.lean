import EgglogSemantics.Proofs.SameMeaning

/-! A cyclic constructor equality has infinitely many inferred spellings. Recording
another spelling can change the raw store while preserving the stopping criterion. -/

namespace Egglog.Tests.LiveSemantics

private def c : Term := .app "C" []
private def f (t : Term) : Term := .app "F" [t]
private def cyclic : Database := Database.empty.addEq c (f c)

private theorem cycle : Cong cyclic c (f c) := .direct (Set.mem_insert _ _)

/-- `F(F(C))` is represented by the existing class of `F(C)`. -/
theorem nested_inferred : cyclic.Infers (f (f c)) (f (f c)) := by
  have grow := Database.Contained.addTerms [f (f c), f (f c)] cyclic
  have hc : CongOn cyclic [f (f c), f (f c)] (f c) (f (f c)) :=
    .congr (cycle.mem_of.2.mono grow) (Database.mem_addTerms (by simp [f]))
      (.cons (cycle.mono grow) .nil)
  exact ⟨f c, cycle.mem_of.2, hc, hc.mem_of.2⟩

/-- Its exact spelling is nevertheless absent from the finite store. -/
theorem nested_not_recorded : f (f c) ∉ cyclic.terms := by
  simp [cyclic, Database.addEq_terms, c, f, Term.subterms_app]

/-- The new semantic stopping comparison absorbs this redundant construction. -/
theorem redundant_write_sameMeaning :
    cyclic.SameMeaning (cyclic.addTerm (f (f c))) := by
  apply InferredFacts.sameMeaning_addTerm _ nested_inferred
  exact Database.WF.empty.addEq c (f c) (by simp [c, f, Term.isLit])

end Egglog.Tests.LiveSemantics
