import EgglogSemantics.Provenance.Log

/-! The proofs read off the log are checked. This holds whatever log is supplied. -/

namespace Egglog.Provenance

/-- Every row's proof in `rowProofs` has been checked against it. -/
theorem rowProofs_checked {P : Program} {terms : List Term} {t : Term} {pf : Proof}
    (h : (t, some pf) ∈ rowProofs P terms) : check P pf = some t := by
  obtain ⟨row, _, hrow⟩ := List.mem_map.mp h
  have hpair := Prod.mk.inj hrow
  obtain rfl := hpair.1
  obtain ⟨fp, _, hp⟩ := Option.bind_eq_some_iff.mp hpair.2
  split at hp
  · rename_i hc
    cases Option.some.inj hp
    exact beq_iff_eq.mp hc
  · contradiction

/-- Every proof `proofs` returns is checked against its row. -/
theorem proofs_checked {P : Program} {terms : List Term} {facts : Facts}
    (h : proofs P terms = some facts) :
    ∀ tp ∈ facts, check P tp.2 = some tp.1 := by
  unfold proofs at h
  split at h
  · contradiction
  · have aux : ∀ (xs : List (Term × Option Proof)) (ys : Facts),
        xs.mapM (fun tp => tp.2.map (tp.1, ·)) = some ys →
        ∀ tp ∈ ys, (tp.1, some tp.2) ∈ xs := by
      intro xs
      induction xs with
      | nil => intro ys he tp hm; simp at he; subst ys; simp at hm
      | cons x xs ih =>
        intro ys he tp hm
        simp only [List.mapM_cons, Option.bind_eq_bind] at he
        obtain ⟨y, hy, he⟩ := Option.bind_eq_some_iff.mp he
        obtain ⟨ys', hys, he⟩ := Option.bind_eq_some_iff.mp he
        cases Option.some.inj he
        obtain ⟨pf, hpf, rfl⟩ := Option.map_eq_some_iff.mp hy
        rcases List.mem_cons.mp hm with rfl | hm
        · exact List.mem_cons.mpr (Or.inl (by cases x; simp_all))
        · exact List.mem_cons_of_mem _ (ih _ hys _ hm)
    exact fun tp ht => rowProofs_checked (aux _ _ h tp ht)

end Egglog.Provenance
