import EgglogSemantics.Proofs.Congruence.Diverge
import EgglogSemantics.Proofs.Congruence.Check

/-! The exact simulation for schedules without saturation: every compiled run follows the
source run at the source state itself, not at a partner of the same meaning. This is what
lets a rule take the minimum of two query variables. A minimum compares representatives,
and the partner of a settled source state, which the extra compiled passes of a
saturation refire the rules at, need not share them. -/

namespace Egglog.Congruence

variable {P : Program}

/-- The compiled schedule reaches a canonical state related to the source result itself. -/
theorem sim_exact_fwd (hP : P.Fragment) : ∀ (S : Schedule), S.NoSaturate → S.rules ⊆ P.rules →
    ∀ {x d e : Database}, SrcInv P x → Rel (!P.schedule.subsumeFreeB) x d → Canon d → Reach x S e →
      ∃ d', Reach d (encS P S) d' ∧ Rel (!P.schedule.subsumeFreeB) e d' ∧ Canon d'
  | .run R, _, hS, x, d, e, hx, hd, hc, hr => by
      cases hr
      exact sim_run hP (fun r hr => hS hr) hx hd hc
  | .saturate _, hn, _, _, _, _, _, _, _, _ => hn.elim
  | .seq S₁ S₂, hn, hS, x, d, e, hx, hd, hc, hr => by
      have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
      have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
      obtain ⟨mid, h₁, h₂⟩ := Reach.seq_inv hr
      obtain ⟨d₁, hd₁, hrel₁, hc₁⟩ := sim_exact_fwd hP S₁ hn.1 hS₁ hx hd hc h₁
      obtain ⟨d₂, hd₂, hrel₂, hc₂⟩ :=
        sim_exact_fwd hP S₂ hn.2 hS₂ (hx.reach hP hS₁ h₁) hrel₁ hc₁ h₂
      exact ⟨d₂, .seq hd₁ hd₂, hrel₂, hc₂⟩

/-- Every compiled execution of the schedule follows a source execution exactly. -/
theorem sim_exact_bwd (hP : P.Fragment) : ∀ (S : Schedule), S.NoSaturate → S.rules ⊆ P.rules →
    ∀ {x d d' : Database}, SrcInv P x → Rel (!P.schedule.subsumeFreeB) x d → Canon d → Reach d (encS P S) d' →
      ∃ e, Reach x S e ∧ Rel (!P.schedule.subsumeFreeB) e d' ∧ Canon d'
  | .run R, _, hS, x, d, d', hx, hd, hc, hr => by
      obtain ⟨hrel', hc'⟩ := sim_run_bwd hP (fun r hr => hS hr) hx hd hc hr
      exact ⟨RunRules R x, .run, hrel', hc'⟩
  | .saturate _, hn, _, _, _, _, _, _, _, _ => hn.elim
  | .seq S₁ S₂, hn, hS, x, d, d', hx, hd, hc, hr => by
      have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
      have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
      obtain ⟨mid, h₁, h₂⟩ := Reach.seq_inv hr
      obtain ⟨e₁, he₁, hrel₁, hc₁⟩ := sim_exact_bwd hP S₁ hn.1 hS₁ hx hd hc h₁
      obtain ⟨e₂, he₂, hrel₂, hc₂⟩ :=
        sim_exact_bwd hP S₂ hn.2 hS₂ (hx.reach hP hS₁ he₁) hrel₁ hc₁ h₂
      exact ⟨e₂, .seq he₁ he₂, hrel₂, hc₂⟩

/-- The compilation of a schedule without saturation does not diverge: every rebuild
saturation terminates. -/
theorem encS_not_diverges (hP : P.Fragment) : ∀ (S : Schedule), S.NoSaturate →
    S.rules ⊆ P.rules → ∀ {x d : Database}, SrcInv P x → Rel (!P.schedule.subsumeFreeB) x d → Canon d →
      ¬ Diverges d (encS P S)
  | .run R, _, hS, x, _, hx, hd, hc =>
      run_not_diverges hP (fun r hr => hS hr) ⟨x, hx, Database.SameMeaning.refl x, hd, hc⟩
  | .saturate _, hn, _, _, _, _, _, _ => hn.elim
  | .seq S₁ S₂, hn, hS, x, d, hx, hd, hc => by
      have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
      have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
      intro hdiv
      change Diverges d (.seq (encS P S₁) (encS P S₂)) at hdiv
      rcases Diverges.append_iff.mp hdiv with h | ⟨mid, hmid, h⟩
      · exact encS_not_diverges hP S₁ hn.1 hS₁ hx hd hc h
      · obtain ⟨e, he, hrel, hc'⟩ := sim_exact_bwd hP S₁ hn.1 hS₁ hx hd hc hmid
        exact encS_not_diverges hP S₂ hn.2 hS₂ (hx.reach hP hS₁ he) hrel hc' h

/-- Compiler correctness for a program without saturation, by the exact simulation. -/
theorem encode_correct_noSaturate (hP : P.Fragment) (hn : P.NoSaturate) :
    (∀ o : Result, Eval Database.empty (encode P) o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty (encode P).schedule ↔ Diverges Database.empty P.schedule) := by
  have hinv : SrcInv P Database.empty := SrcInv.empty P
  have hS : P.schedule.rules ⊆ P.rules := fun _ hr => hr
  -- Related final states agree on the check.
  have hcheck : ∀ {e d : Database}, SrcInv P e → Rel (!P.schedule.subsumeFreeB) e d → Canon d →
      (QueryHolds e P.check ↔ QueryHolds d (encode P).check) := by
    intro e d he hd hc
    rw [encode_check]
    exact check_corr hP he hd hc
  refine ⟨fun o => ?_, ?_⟩
  · cases o with
    | ok =>
      rw [Eval.ok_iff, Eval.ok_iff, encode_schedule]
      constructor
      · rintro ⟨d, hd, hq⟩
        obtain ⟨e, he, hrel, hc⟩ :=
          sim_exact_bwd hP P.schedule hn hS hinv rel_empty canon_empty hd
        exact ⟨e, he, (hcheck (hinv.reach hP hS he) hrel hc).mpr hq⟩
      · rintro ⟨e, he, hq⟩
        obtain ⟨d, hd, hrel, hc⟩ :=
          sim_exact_fwd hP P.schedule hn hS hinv rel_empty canon_empty he
        exact ⟨d, hd, (hcheck (hinv.reach hP hS he) hrel hc).mp hq⟩
    | checkFailed =>
      rw [Eval.failed_iff, Eval.failed_iff, encode_schedule]
      constructor
      · rintro ⟨d, hd, hq⟩
        obtain ⟨e, he, hrel, hc⟩ :=
          sim_exact_bwd hP P.schedule hn hS hinv rel_empty canon_empty hd
        exact ⟨e, he, fun h => hq ((hcheck (hinv.reach hP hS he) hrel hc).mp h)⟩
      · rintro ⟨e, he, hq⟩
        obtain ⟨d, hd, hrel, hc⟩ :=
          sim_exact_fwd hP P.schedule hn hS hinv rel_empty canon_empty he
        exact ⟨d, hd, fun h => hq ((hcheck (hinv.reach hP hS he) hrel hc).mpr h)⟩
  · rw [encode_schedule]
    exact ⟨fun h => (encS_not_diverges hP P.schedule hn hS hinv rel_empty canon_empty h).elim,
      fun h => (not_cmdDiverges_of_allConstructors hn h).elim⟩

end Egglog.Congruence
