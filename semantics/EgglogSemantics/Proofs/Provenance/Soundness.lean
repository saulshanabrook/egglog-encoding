import EgglogSemantics.Provenance.Extract
import EgglogSemantics.Proofs.Provenance.Model

/-! Extraction returns only certificates accepted by the relational checker. This
statement is independent of the origin of the supplied firing log. -/

namespace Egglog.Provenance

/-- Every successful entry of `extractEach` has been checked against its row. -/
theorem extractEach_checked {P : Program} {terms : List Term} {t : Term} {pf : Proof}
    (h : (t, some pf) ∈ extractEach P terms) : check P pf = some t := by
  obtain ⟨row, _, hrow⟩ := List.mem_map.mp h
  have hpair := Prod.mk.inj hrow
  obtain rfl := hpair.1
  obtain ⟨fp, _, hp⟩ := Option.bind_eq_some_iff.mp hpair.2
  split at hp
  · rename_i hc
    cases Option.some.inj hp
    exact beq_iff_eq.mp hc
  · contradiction

/-- Successful extraction checks every returned proof against the associated term. -/
theorem extract_checked {P : Program} {terms : List Term} {facts : Facts}
    (h : extract P terms = some facts) :
    ∀ tp ∈ facts, check P tp.2 = some tp.1 := by
  unfold extract at h
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
    exact fun tp ht => extractEach_checked (aux _ _ h tp ht)

/-- Extraction is sound in any interpretation closed under the checker rules. -/
theorem extract_sound {P : Program} {terms : List Term} {facts : Facts} {H : Term → Prop}
    (model : Model P H) (h : extract P terms = some facts) : ∀ tp ∈ facts, H tp.1 :=
  fun tp ht => check_sound_in_model model (extract_checked h tp ht)

end Egglog.Provenance
