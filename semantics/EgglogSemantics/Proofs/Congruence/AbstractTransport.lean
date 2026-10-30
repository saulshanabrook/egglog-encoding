import EgglogSemantics.Proofs.Operands
import EgglogSemantics.Proofs.Congruence.AbstractRebuild

/-! Source congruence transports canonical readings, including temporary query operands. -/

namespace Egglog.Congruence.Abstract

/-- Terms have the same canonical readings, even when neither has a reading yet. -/
def CanonicalEq {d : Database} (h : Rebuilt d) (a b : Term) : Prop :=
  ∀ r, ViewRepr d a (h.root r) ↔ ViewRepr d b (h.root r)

theorem CanonicalEq.refl {d : Database} (h : Rebuilt d) (a : Term) : CanonicalEq h a a :=
  fun _ => Iff.rfl

theorem CanonicalEq.symm {d : Database} {h : Rebuilt d} {a b : Term}
    (hab : CanonicalEq h a b) : CanonicalEq h b a := fun r => (hab r).symm

theorem CanonicalEq.trans {d : Database} {h : Rebuilt d} {a b c : Term}
    (hab : CanonicalEq h a b) (hbc : CanonicalEq h b c) : CanonicalEq h a c :=
  fun r => (hab r).trans (hbc r)

section Transport

variable {d : Database} {src : Database}
variable (h : Rebuilt d) (hs : EdgesSound d src) (hw : src.WF)
include h hs hw

/-- Pointwise equivalent children can use the normalized keys of an existing tuple reading. -/
theorem canonicalEq_readList {as bs : List Term} (hab : List.Forall₂ (CanonicalEq h) as bs)
    {es : List Term} (ha : ViewReprList d as es) :
    ViewReprList d bs (es.map h.root) := by
  induction hab generalizing es with
  | nil => cases ha; exact .nil
  | @cons a b as bs hab _ ih =>
      cases ha with
      | @cons _ e _ es hae has =>
          exact .cons ((hab e).mp (h.normalize_view hs hw a hae)) (ih has)

/-- Existing parent entries answer congruent children without inventing parent existence. -/
theorem canonicalEq_read_app {f : FnName} {as bs : List Term}
    (hab : List.Forall₂ (CanonicalEq h) as bs) {r : Term}
    (ha : ViewRepr d (.app f as) (h.root r)) :
    ViewRepr d (.app f bs) (h.root r) := by
  cases ha with
  | app hl ho =>
      refine .app (canonicalEq_readList h hs hw hab hl) ?_
      simpa only [h.root_idem] using
        h.out_normalized ho

/-- Canonical reading equivalence is a congruence relation on constructor applications. -/
theorem canonicalEq_congr {f : FnName} {as bs : List Term}
    (hab : List.Forall₂ (CanonicalEq h) as bs) : CanonicalEq h (.app f as) (.app f bs) := by
  intro r
  refine ⟨canonicalEq_read_app h hs hw hab, ?_⟩
  have hba : List.Forall₂ (CanonicalEq h) bs as :=
    hab.flip.imp fun _ _ h => CanonicalEq.symm h
  exact canonicalEq_read_app h hs hw hba

/-- A shared view id makes all canonical readings agree, by uniqueness of rebuilt readings. -/
theorem canonicalEq_of_sameClass {a b : Term} (hab : SameClass d a b) :
    CanonicalEq h a b := by
  obtain ⟨e, hae, hbe⟩ := hab
  intro r
  constructor
  · intro har
    have heq := h.unique_view a har hae
    rw [h.root_idem] at heq
    rw [heq]
    exact h.normalize_view hs hw b hbe
  · intro hbr
    have heq := h.unique_view b hbr hbe
    rw [h.root_idem] at heq
    rw [heq]
    exact h.normalize_view hs hw a hae

/-- Adding query operands introduces only reflexive assertions. Thus source congruence
still preserves canonical target readings at these temporary terms. -/
theorem canonicalEq_of_congOn {querySrc : Database} (hun : UnionsRead d querySrc)
    {ts : List Term} {a b : Term} (hab : StoredCongOn querySrc ts a b) : CanonicalEq h a b := by
  refine StoredCong.le (R := CanonicalEq h) ?_ (fun _ _ => CanonicalEq.symm)
    (fun _ _ _ => CanonicalEq.trans)
    (fun _ _ _ _ _ hl => canonicalEq_congr h hs hw hl)
    (fun _ s _ _ => CanonicalEq.refl h s) hab
  intro x y hxy
  rcases Conservativity.mem_addTerms_eqs ts querySrc (x, y) hxy with hxy | hxy
  · by_cases heq : x = y
    · subst y; exact .refl h x
    · exact canonicalEq_of_sameClass h hs hw (hun x y hxy heq)
  · obtain rfl : x = y := hxy
    exact .refl h x

/-- The existence witness in a source match supplies the reading of its queried operand.
Congruence transports that witness; it does not create existence on its own. -/
theorem view_of_congOn {querySrc : Database} (hun : UnionsRead d querySrc)
    {ts : List Term} {a b e : Term}
    (hab : StoredCongOn querySrc ts a b) (ha : ViewRepr d a e) :
    ViewRepr d b (h.root e) :=
  (canonicalEq_of_congOn h hs hw hun hab e).mp
    (h.normalize_view hs hw a ha)

/-- A source expression match yields a represented instance using its held witness. -/
theorem view_of_matches_expr {querySrc : Database} (hun : UnionsRead d querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d t e)
    {e : Expr} {σ : Env} (hm : Matches querySrc (.expr e) σ) :
    ∃ t i, e.evalAtom querySrc.sig σ = some t ∧ ViewRepr d t (h.root i) := by
  cases hm using Matches.storedCases with
  | expr hwit he hcng =>
      obtain ⟨i, hi⟩ := hex _ hwit
      exact ⟨_, i, he, view_of_congOn h hs hw hun hcng hi⟩

/-- Both equality operands read to the same canonical id, justified by the original
match's existence witness and its two source congruence proofs. -/
theorem views_of_matches_eq {querySrc : Database} (hun : UnionsRead d querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d t e)
    {a b : Expr} {σ : Env} (hm : Matches querySrc (.eq a b) σ) :
    ∃ ta tb i, a.eval querySrc.sig σ = some ta ∧ b.eval querySrc.sig σ = some tb ∧
      ViewRepr d ta (h.root i) ∧ ViewRepr d tb (h.root i) := by
  cases hm using Matches.storedCases with
  | eq hwit ha hb' hwa hab =>
      obtain ⟨i, hi⟩ := hex _ hwit
      have hia := view_of_congOn h hs hw hun hwa hi
      have hib := view_of_congOn h hs hw hun hab hia
      exact ⟨_, _, i, ha, hb', hia, by simpa only [h.root_idem] using hib⟩

end Transport

end Egglog.Congruence.Abstract
