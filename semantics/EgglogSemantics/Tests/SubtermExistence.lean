import EgglogSemantics.Proofs.SameMeaning
import EgglogSemantics.Proofs.Diagonal

/-! Implicit existence does not materialize child assertions or invert congruence. -/

namespace Egglog.Tests.SubtermExistence

private def child : Term := .lit (.int 0)
private def parent : Term := .app "f" [child]
private def stored : Database := Database.empty.addTerm parent

example : stored.eqs = {(parent, parent)} := by
  simp [stored, Database.addTerm, Database.empty]

example : (child, child) ∉ stored.eqs := by
  simp [stored, Database.addTerm, Database.empty, child, parent]

theorem child_exists : child ∈ stored.terms :=
  stored.subtermClosed parent (Database.mem_addTerm parent Database.empty)
    (Term.arg_subterms (by simp) child.self_mem_subterms)

example : (Database.empty.addEq parent child).eqs = {(parent, child)} := by
  simp [Database.addEq, Database.empty]

example : child ∈ (Database.empty.addEq parent child).terms :=
  (StoredCong.direct (Set.mem_insert _ _)).mem_right

private def other : Term := .lit (.int 1)
private def parentsEqual : Database :=
  Database.empty.addEq parent (.app "f" [other])

example : ¬ Cong parentsEqual child other := by
  intro hc
  have hl : parentsEqual.LitsIsolated := by
    rintro p (rfl | hp)
    · simp [parent, Term.isLit]
    · exact (Set.notMem_empty p hp).elim
  have he := InferredFacts.infers_eq_of_isLit ⟨hl⟩ (InferredFacts.congr_iff_infers.mp hc) (Or.inl (by trivial))
  cases he

/-- Saturation ignores a redundant explicit child assertion. -/
example : stored.SameMeaning (stored.addTerm child) :=
  InferredFacts.sameMeaning_addTerm (Database.WF.empty.addTerm parent)
    (InferredFacts.infers_of_held child_exists)

example : stored ≠ stored.addTerm child := by
  intro he
  have hc : (child, child) ∈ stored.eqs := he ▸ Set.mem_insert _ _
  simp [stored, Database.addTerm, Database.empty, child, parent] at hc

end Egglog.Tests.SubtermExistence
