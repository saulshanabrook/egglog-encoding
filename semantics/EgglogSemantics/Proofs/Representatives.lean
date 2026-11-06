import EgglogSemantics.Proofs.Match
import EgglogSemantics.Proofs.Order
import Mathlib.Order.WellFoundedSet

/-! Representative existence is explicit for arbitrary stores. Finite stores always
have representatives; the global term order need not be well founded. -/

namespace Egglog

/-- Every represented class has a least held spelling. -/
def Database.HasReps (d : Database) : Prop :=
  ∀ t, Cong d t t → ∃ r ∈ d.reps, Cong d t r

theorem Database.hasReps_of_finite_terms {d : Database} (hf : d.terms.Finite) :
    d.HasReps := by
  letI : IsStrictOrder Term (fun s t => Term.blt s t = true) :=
    { irrefl := fun t => by simp
      trans := fun a b c => Term.blt_trans a b c }
  intro t ht
  obtain ⟨w, hw, hwt, _⟩ := InferredFacts.congr_iff_infers.mp ht
  have htw : Cong d t w :=
    (InferredFacts.congr_iff_infers.mpr
      (InferredFacts.infers_of_congOn_core (InferredFacts.infers_of_held hw) hwt)).symm
  let S : Set Term := {s | s ∈ d.terms ∧ Cong d t s}
  have hS : S.Finite := hf.subset fun _ h => h.1
  obtain ⟨r, hr, hmin⟩ := (Set.wellFoundedOn_iff.mp
    (hS.wellFoundedOn (r := fun s t => Term.blt s t = true))).has_min
    S ⟨w, hw, htw⟩
  refine ⟨r, ⟨hr.1, ?_⟩, hr.2⟩
  intro s hs hsr
  have hs' : s ∈ S := ⟨hs, hr.2.trans hsr.symm⟩
  exact fun hlt => hmin s hs' ⟨hlt, hs', hr⟩

/-- Representatives in one class are unique. -/
theorem Database.reps_eq_of_cong {d : Database} {s t : Term}
    (hs : s ∈ d.reps) (ht : t ∈ d.reps) (hc : Cong d s t) : s = t := by
  by_contra hne
  exact (Term.blt_total s t hne).elim (ht.2 s hs.1 hc) (hs.2 t ht.1 hc.symm)

end Egglog
