import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import EgglogSemantics.Spec.Sequential
import EgglogSemantics.Proofs.Writes

/-! Existence of finite normalization and saturation requires actual progress.

A finite equation universe supplies a maximal reachable equation set, but deleting
and rebuilding rows can cycle within that universe. The execution theorems below
therefore require well-founded progress at reachable states. -/

namespace Egglog

/-- Among states reachable within one finite equation universe, choose a state whose
equations cannot grow further. No finiteness assumption on the state type is needed. -/
theorem exists_reachable_maximal_eqs (step : Database → Database → Prop) (d : Database)
    {bound : Set (Term × Term)} (hf : bound.Finite)
    (hb : ∀ e, Relation.ReflTransGen step d e → e.eqs ⊆ bound) :
    ∃ e, Relation.ReflTransGen step d e ∧
      ∀ e', Relation.ReflTransGen step d e' → e.eqs ⊆ e'.eqs → e'.eqs = e.eqs := by
  let stores : Set (Set (Term × Term)) :=
    {s | ∃ e, Relation.ReflTransGen step d e ∧ s = e.eqs}
  have hfin : stores.Finite := hf.finite_subsets.subset (by
    rintro s ⟨e, he, rfl⟩
    exact hb e he)
  obtain ⟨s, ⟨e, he, rfl⟩, hmax⟩ :=
    Set.exists_max_image stores Set.ncard hfin ⟨d.eqs, d, .refl, rfl⟩
  refine ⟨e, he, fun e' he' hsub => ?_⟩
  exact (Set.eq_of_subset_of_ncard_le hsub
    (hmax e'.eqs ⟨e', he', rfl⟩) (hf.subset (hb e' he'))).symm

/-- A reachable state with no outgoing work exists when every unfinished state has
an actual successor decreasing a well-founded relation. Only the chosen successor needs
to decrease; arbitrary scheduling is not asserted to terminate. -/
theorem exists_reachable_normal_of_wellFounded {α : Type*}
    (step : α → α → Prop) (normal : α → Prop) (d : α)
    (lt : α → α → Prop) (hwf : WellFounded lt)
    (hprogress : ∀ e, Relation.ReflTransGen step d e → ¬ normal e →
      ∃ e', step e e' ∧ lt e' e) :
    ∃ e, Relation.ReflTransGen step d e ∧ normal e := by
  classical
  have aux : ∀ e, Relation.ReflTransGen step d e →
      ∃ e', Relation.ReflTransGen step e e' ∧ normal e' := by
    intro e
    induction e using hwf.induction with
    | h e ih =>
      intro he
      by_cases hn : normal e
      · exact ⟨e, .refl, hn⟩
      · obtain ⟨mid, hs, hlt⟩ := hprogress e he hn
        obtain ⟨last, hreach, hlast⟩ := ih mid hlt (he.tail hs)
        exact ⟨last, (Relation.ReflTransGen.single hs).trans hreach, hlast⟩
  exact aux d .refl

/-- Saturation terminates when every changing round decreases a well-founded relation. -/
theorem saturateReach_exists_of_wellFounded (R : List Rule) (d : Database)
    (lt : Database → Database → Prop) (hwf : WellFounded lt)
    (hprogress : ∀ e, Relation.ReflTransGen (fun a b => b = RunRules R a) d e →
      Cong e ≠ Cong (RunRules R e) → lt (RunRules R e) e) :
    ∃ e, SaturateReach R d e := by
  classical
  have aux : ∀ e, Relation.ReflTransGen (fun a b => b = RunRules R a) d e →
      ∃ e', SaturateReach R e e' := by
    intro e
    induction e using hwf.induction with
    | h e ih =>
      intro he
      by_cases hm : Cong e = Cong (RunRules R e)
      · exact ⟨_, .fixpoint hm⟩
      · obtain ⟨last, hlast⟩ := ih _ (hprogress e he hm) (he.tail rfl)
        exact ⟨last, .again hm hlast⟩
  exact aux d .refl

theorem saturateReach_exists_of_measure (R : List Rule) (d : Database)
    (rank : Database → Nat)
    (hprogress : ∀ e, Relation.ReflTransGen (fun a b => b = RunRules R a) d e →
      Cong e ≠ Cong (RunRules R e) → rank (RunRules R e) < rank e) :
    ∃ e, SaturateReach R d e :=
  saturateReach_exists_of_wellFounded R d (fun e' e => rank e' < rank e)
    (measure rank).wf hprogress

end Egglog
