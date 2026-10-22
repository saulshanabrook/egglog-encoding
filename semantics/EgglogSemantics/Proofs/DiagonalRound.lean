import EgglogSemantics.Proofs.DiagonalPreservation

/-! An unchanged diagonal, delete-free round absorbs its redundant assertions. -/

namespace Egglog

private theorem matches_same {d e : Database} (h : d.SameMeaning e) {p : Pattern} {σ : Env}
    (hm : Matches d p σ) : Matches e p σ := by
  cases hm with
  | atom hv hc => exact .atom hv ((h.congr _ _).mp hc)
  | equal hv hw hc => exact .equal hv hw ((h.congr _ _).mp hc)
  | unequal hv hw ha hb hn =>
    exact .unequal hv hw ((h.congr _ _).mp ha)
      ((h.congr _ _).mp hb) (fun hc => hn ((h.congr _ _).mpr hc))

private theorem query_same {d e : Database} (h : d.SameMeaning e) (ht : d.terms = e.terms)
    {q : Query} {σ : Env} (hm : QueryMatches d q σ) : QueryMatches e q σ :=
  ⟨⟨hm.1.1, fun b hb => ht ▸ hm.1.2 b hb⟩, fun p hp => matches_same h (hm.2 p hp)⟩

/-- With unchanged congruence and held terms, the same substitutions write the same pairs. -/
theorem RunWrites.eq_of_sameMeaning_terms {d e : Database} (h : d.SameMeaning e)
    (ht : d.terms = e.terms) (R : List Rule) : RunWrites R d = RunWrites R e := by
  ext p
  constructor
  · rintro ⟨W, ⟨r, hr, σ, hσ, hw⟩, hp⟩
    exact ⟨W, ⟨r, hr, σ, query_same h ht hσ, hw⟩, hp⟩
  · rintro ⟨W, ⟨r, hr, σ, hσ, hw⟩, hp⟩
    exact ⟨W, ⟨r, hr, σ, query_same h.symm ht.symm hσ, hw⟩, hp⟩

/-- After a semantically unchanged diagonal round, the next round changes no assertions. -/
theorem RunRules.self_of_sameMeaning {d e : Database} {R : List Rule}
    (hn : d.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) (hdf : ∀ r ∈ R, r.DeleteFree)
    (hr : e = RunRules R d)
    (heq : d.SameMeaning e) : RunRules R e = e := by
  subst e
  have ht := heq.terms_eq_of_diag hn.diag (RunRules.noUnions hn hu).diag
  have hw := RunWrites.eq_of_sameMeaning_terms heq ht R
  rw [RunRules.eq_addEqs hdf, ← hw, RunRules.eq_addEqs hdf]
  apply Database.ext
  · simp [Database.addEqs, Set.union_assoc]

end Egglog
