import EgglogSemantics.Proofs.SourceProof.Support

/-! One stored `Table(A)` row and `A = B` can justify the spelling `Table(B)`.
The second spelling need not occur as an explicit assertion. -/

namespace Egglog.SourceProof.Counterexamples

set_option linter.hashCommand false

private def a : Term := .app "A" []
private def b : Term := .app "B" []
private def c : Term := .app "C" []
private def row (x : Term) : Term := .app "Table" [x]

private def seedActions : List Action :=
  [.expr (row a).toExpr, .union a.toExpr b.toExpr, .expr c.toExpr]

-- An empty-query firing supplies both anchors.
#guard (actionsFacts [] seedActions).any fun fs =>
  decide ((⟨row a, row a⟩ : Claim) ∈ fs ∧ (⟨a, b⟩ : Claim) ∈ fs)

private def snapshot : Database :=
  { Database.empty with eqs := {(row a, row a), (a, b), (c, c)} }

private def isC : Term → Bool
  | .lit _ => false
  | .app f _ => f == "C"

private theorem same_isC {s t : Term} (h : Cong snapshot s t) : isC s = isC t := by
  induction h using Cong.rec (motive_2 := fun _ _ _ => True) with
  | direct hp =>
      simp only [snapshot, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hp | hp | hp <;> cases hp <;> rfl
  | child => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr => rfl
  | nil | cons => trivial

private theorem unrelated_equality_absent : ¬ Cong snapshot a c := by
  intro h
  have he := same_isC h
  change false = true at he
  contradiction

private theorem second_row_absent : (row b, row b) ∉ snapshot.eqs := by
  simp [snapshot, row, a, b, c]

/-- Congruence establishes a spelling even without a second explicit row. -/
private theorem second_spelling {db : Database} (hw : db.WF)
    (hrow : Cong db (row a) (row a)) (hab : Cong db a b) :
    Claim.Supported db ⟨row b, row b⟩ := by
  have base := Claim.Supported.of_completion (c := ⟨row a, row a⟩) hw
    (.direct (InferredFacts.congr_infers hrow))
  have child := Claim.Supported.of_completion (c := ⟨a, b⟩) hw
    (.direct (InferredFacts.congr_infers hab))
  have rewritten := base.congr (i := 0) child rfl
  exact rewritten.symm.trans rewritten

end Egglog.SourceProof.Counterexamples
