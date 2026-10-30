import EgglogSemantics.Provenance.Checker

namespace Egglog.Provenance

/-- An interpretation closed under the checker's rule and subterm certificates.
It need not describe rows still present after deletion. -/
structure Model (P : Program) (H : Term → Prop) : Prop where
  ruleFacts : ∀ {r : Rule} {σ : Env} {premises fs : List Term},
    r ∈ P.rules → (∀ t ∈ premises, H t) →
      Egglog.Provenance.ruleFacts r σ premises = some fs → ∀ t ∈ fs, H t
  subterms : ∀ {parent : Term}, H parent → ∀ t ∈ parent.subtermList, H t

private theorem option_true {b : Option Bool} (h : b.getD false = true) : b = some true := by
  cases b with
  | none => simp at h
  | some b => simpa using h

/-- Each accepted node preserves the chosen model. -/
theorem checkNode_sound_in_model {P : Program} {H : Term → Prop}
    (model : Model P H) {pf : Proof}
    (hp : ∀ q ∈ pf.subproofs, H q.fact)
    (h : checkReason P pf = true) : H pf.fact := by
  cases pf with
  | rule t i σ ps =>
      simp only [checkReason] at h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp (option_true h)
      obtain ⟨fs, hfs, h⟩ := Option.bind_eq_some_iff.mp h
      refine model.ruleFacts (List.mem_of_getElem? hr) ?_ hfs t (by simpa using h)
      intro u hu
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      exact hp q hq
  | subterm t parent =>
      simp only [checkReason, decide_eq_true_eq] at h
      exact model.subterms (hp parent (by simp [Proof.subproofs])) t h

mutual

theorem valid_sound_in_model {P : Program} {H : Term → Prop}
    (model : Model P H) : (pf : Proof) → valid P pf = true → H pf.fact
  | .rule t i σ ps, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      exact checkNode_sound_in_model model (allValid_sound_in_model model ps h.1) h.2
  | .subterm t p, h => by
      simp only [valid, Bool.and_eq_true_iff] at h
      have ih := valid_sound_in_model model p h.1
      refine checkNode_sound_in_model model ?_ h.2
      intro q hq
      simp only [Proof.subproofs, List.mem_singleton] at hq
      subst hq
      exact ih
termination_by structural pf => pf

theorem allValid_sound_in_model {P : Program} {H : Term → Prop}
    (model : Model P H) : (ps : List Proof) → allValid P ps = true →
      ∀ q ∈ ps, H q.fact
  | [], _, _, hq => by simp at hq
  | p :: ps, h, q, hq => by
      simp only [allValid, Bool.and_eq_true_iff] at h
      rcases List.mem_cons.mp hq with hqp | hq
      · rw [hqp]
        exact valid_sound_in_model model p h.1
      · exact allValid_sound_in_model model ps h.2 q hq
termination_by structural ps => ps

end

/-- Checker soundness relative to an explicitly supplied semantic model. -/
theorem check_sound_in_model {P : Program} {H : Term → Prop} {pf : Proof} {t : Term}
    (model : Model P H) (h : check P pf = some t) : H t := by
  unfold check at h
  split at h
  · contradiction
  · split at h
    · rename_i hv
      cases Option.some.inj h
      exact valid_sound_in_model model pf hv
    · contradiction

end Egglog.Provenance
