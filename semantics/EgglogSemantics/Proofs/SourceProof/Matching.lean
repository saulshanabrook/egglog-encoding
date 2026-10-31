import EgglogSemantics.SourceProof.Checker
import EgglogSemantics.Proofs.SourceProof.Actions
import EgglogSemantics.Proofs.Query

namespace Egglog.SourceProof

theorem premiseMatches_sound {db : Database} {σ : Env} {p : Pattern} {c : Claim}
    (hX : db.subsumed = ∅) (ho : p.OrderingFree)
    (hc : c.Holds db) (h : premiseMatches σ p c = true) : Matches db p σ := by
  cases p with
  | expr e =>
      simp only [premiseMatches, beq_iff_eq] at h
      exact .atom (Lookup.of_eval hX ho h (hc.symm.trans hc).toCong).2
  | eq a b =>
      simp only [premiseMatches, Bool.and_eq_true_iff, beq_iff_eq] at h
      exact .equal (Lookup.of_eval hX ho.1 h.1 (hc.trans hc.symm).toCong).2
        (Lookup.of_eval hX ho.2 h.2 (hc.symm.trans hc).toCong).2 h.1 h.2 hc.toCong
  | ne _ _ => simp [premiseMatches] at h

theorem premisesMatch_sound {db : Database} {σ : Env} {q : Query} {cs : List Claim}
    (hX : db.subsumed = ∅) (ho : ∀ p ∈ q, p.OrderingFree)
    (hc : ∀ c ∈ cs, c.Holds db) (h : premisesMatch σ q cs = true) :
    ∀ p ∈ q, Matches db p σ := by
  induction q generalizing cs with
  | nil => simp
  | cons p ps ih =>
      cases cs with
      | nil => simp [premisesMatch] at h
      | cons c cs =>
          simp only [premisesMatch, Bool.and_eq_true_iff] at h
          intro p' hp'
          rcases List.mem_cons.mp hp' with rfl | hp'
          · exact premiseMatches_sound hX (ho p' (by simp)) (hc c (by simp)) h.1
          · exact ih (fun p hp => ho p (by simp [hp])) (fun c hc' => hc c (by simp [hc'])) h.2 p' hp'

theorem supportedValue_sound {db : Database} (hw : db.WF) {cs : List Claim}
    (hc : ∀ c ∈ cs, c.Holds db) {t : Term} (ht : supportedValue cs t = true) :
    t ∈ db.terms := by
  simp only [supportedValue, List.any_eq_true, decide_eq_true_eq] at ht
  obtain ⟨c, hcm, hsub⟩ := ht
  rcases hsub with hl | hr
  · exact hw.subtermClosed _ (eqsInTerms_free (hc c hcm)).1
      ((Term.mem_subtermList _).mp hl)
  · exact hw.subtermClosed _ (eqsInTerms_free (hc c hcm)).2
      ((Term.mem_subtermList _).mp hr)

theorem querySubst_of_matches {db : Database} {q : Query} {σ : Env}
    (hdom : (Env.dom σ).Perm q.vars) (hval : ∀ b ∈ σ, b.2 ∈ db.reps)
    (hm : ∀ p ∈ q, Matches db p σ) :
    ∃ τ, ValidQuerySubst db q τ ∧ Env.Agree τ σ :=
  Egglog.querySubst_of_matches_terms hdom hval hm

end Egglog.SourceProof
