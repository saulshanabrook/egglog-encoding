import EgglogSemantics.Proofs.DiagonalPreservation

/-! An unchanged diagonal, subsume-free round absorbs its redundant assertions. -/

namespace Egglog

theorem Matches.sameMeaning {d e : Database} (h : d.SameMeaning e) {p : Pattern} {σ : Env}
    (hm : Matches d p σ) : Matches e p σ := by
  cases hm with
  | atom hl =>
    obtain ⟨t, hv⟩ := hl.eval_exists
    exact .atom (Lookup.mono_live (fun _ ht => (h.live _).mp ht) ⟨hv, hl⟩).2
  | equal hl₁ hl₂ hv hw hc =>
    exact .equal (Lookup.mono_live (fun _ ht => (h.live _).mp ht) ⟨hv, hl₁⟩).2
      (Lookup.mono_live (fun _ ht => (h.live _).mp ht) ⟨hw, hl₂⟩).2
      hv hw ((h.congr _ _).mp hc)
  | unequal hl₁ hl₂ hv hw hn =>
    exact .unequal (Lookup.mono_live (fun _ ht => (h.live _).mp ht) ⟨hv, hl₁⟩).2
      (Lookup.mono_live (fun _ ht => (h.live _).mp ht) ⟨hw, hl₂⟩).2 hv hw
      (fun hc => hn ((h.congr _ _).mpr hc))

theorem QueryMatches.sameMeaning {d e : Database} (h : d.SameMeaning e) (ht : d.terms = e.terms)
    {q : Query} {σ : Env} (hm : QueryMatches d q σ) : QueryMatches e q σ :=
  ⟨⟨hm.1.1, fun b hb => h.reps_eq ht ▸ hm.1.2 b hb⟩,
    fun p hp => Matches.sameMeaning h (hm.2 p hp)⟩

/-- With unchanged congruence and held terms, the same substitutions write the same pairs. -/
theorem RunWrites.eq_of_sameMeaning_terms {d e : Database} (h : d.SameMeaning e)
    (ht : d.terms = e.terms) (R : List Rule) : RunWrites R d = RunWrites R e := by
  ext p
  constructor
  · rintro ⟨W, ⟨r, hr, σ, hσ, hw⟩, hp⟩
    exact ⟨W, ⟨r, hr, σ, QueryMatches.sameMeaning h ht hσ, hw⟩, hp⟩
  · rintro ⟨W, ⟨r, hr, σ, hσ, hw⟩, hp⟩
    exact ⟨W, ⟨r, hr, σ, QueryMatches.sameMeaning h.symm ht.symm hσ, hw⟩, hp⟩

theorem RunMarks.eq_of_sameMeaning_terms {d e : Database} (h : d.SameMeaning e)
    (ht : d.terms = e.terms) (R : List Rule) : RunMarks R d = RunMarks R e := by
  ext t
  constructor
  · rintro ⟨X, ⟨r, hr, σ, hσ, hx⟩, htX⟩
    exact ⟨X, ⟨r, hr, σ, QueryMatches.sameMeaning h ht hσ, hx⟩, htX⟩
  · rintro ⟨X, ⟨r, hr, σ, hσ, hx⟩, htX⟩
    exact ⟨X, ⟨r, hr, σ, QueryMatches.sameMeaning h.symm ht.symm hσ, hx⟩, htX⟩

/-- After a semantically unchanged diagonal round, the next round changes no assertions. -/
theorem RunRules.self_of_sameMeaning {d e : Database} {R : List Rule}
    (hn : d.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) (hdf : ∀ r ∈ R, r.SubsumeFree)
    (hr : e = RunRules R d)
    (heq : d.SameMeaning e) : RunRules R e = e := by
  subst e
  have ht := heq.terms_eq_of_diag hn.diag (RunRules.noUnions hn hu).diag
  have hw := RunWrites.eq_of_sameMeaning_terms heq ht R
  rw [RunRules.eq_addEqs hdf, ← hw, RunRules.eq_addEqs hdf]
  apply Database.ext
  · simp [Database.addEqs, Set.union_assoc]
  · rfl

end Egglog
