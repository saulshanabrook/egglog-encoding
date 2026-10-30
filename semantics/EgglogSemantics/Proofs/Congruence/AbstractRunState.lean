import EgglogSemantics.Proofs.Congruence.AbstractMaintenanceDescent
import EgglogSemantics.Proofs.Congruence.AbstractRuntime

/-! Soundness through actual mathematical rounds and finite rebuilding executions. -/

namespace Egglog.Congruence.Abstract

/-- Runtime structure comes from the live store and checked row declarations. -/
abbrev Runtime (d : Database) : Prop := Live.Runtime d

theorem Descending.sUnion {d : Database} {S : Set Database} (h : Descending d)
    (hs : ∀ e ∈ S, Descending e) : Descending (d.sUnion S) := by
  intro a b hm
  simp only [Database.sUnion_terms, Set.mem_union, Set.mem_iUnion, exists_prop] at hm
  rcases hm with hm | ⟨e, he, hm⟩
  · exact h a b hm
  · exact hs e he a b hm

/-- Unioning all successful firings preserves each of their row invariants. -/
theorem runRules_preserves {src d : Database} {R : RulesetName}
    (hs : SoundTerms d src) (hd : Descending d)
    (hfire : ∀ r ∈ d.rules, r.ruleset = R → ∀ σ post,
      ValidQuerySubst d r.query σ → evalLocalActions d r.actions σ = some post →
        SoundTerms post src ∧ Descending post) :
    SoundTerms (RunRules R d) src ∧ Descending (RunRules R d) := by
  rw [RunRules.eq_sUnion]
  constructor
  · apply hs.sUnion
    rintro e ⟨r, hr, hR, σ, hσ, hf⟩
    exact (hfire r hr hR σ e hσ hf).1
  · apply hd.sUnion
    rintro e ⟨r, hr, hR, σ, hσ, hf⟩
    exact (hfire r hr hR σ e hσ hf).2

/-- A whole round includes every successful firing and any finite merge schedule. -/
theorem runStep_preserves {src d e : Database} {R : RulesetName} (h : Runtime d)
    (hshape : MergeShape d.sig) (hs : SoundTerms d src) (hd : Descending d)
    (hfire : ∀ r ∈ d.rules, r.ruleset = R → ∀ σ post,
      ValidQuerySubst d r.query σ → evalLocalActions d r.actions σ = some post →
        SoundTerms post src ∧ Descending post) (hr : RunStep R d e) :
    SoundTerms e src ∧ Descending e := by
  obtain ⟨hs', hd'⟩ := runRules_preserves hs hd hfire
  have h' := h.runRules R
  exact ⟨mergeClosure_soundTerms (d := RunRules R d) hshape
    h'.noUnions.diag h'.wf h'.storeOk h'.state.uf hs' hr.1,
    mergeClosure_descending (d := RunRules R d) hshape
      h'.noUnions.diag h'.wf h'.storeOk h'.state.uf hd' hr.1⟩

/-- Induction over the given finite derivation, without any assumption about the number
of rounds taken by the source. The callback handles a single actual firing. -/
theorem runReach_preserves {src d e : Database} {R : RulesetName} (h : Runtime d)
    (hshape : MergeShape d.sig) (hs : SoundTerms d src) (hd : Descending d)
    (hfire : ∀ mid, Runtime mid → mid.sig = d.sig → mid.rules = d.rules → mid.env = d.env →
      SoundTerms mid src → Descending mid → ∀ r ∈ mid.rules, r.ruleset = R → ∀ σ post,
      ValidQuerySubst mid r.query σ → evalLocalActions mid r.actions σ = some post →
        SoundTerms post src ∧ Descending post)
    (hr : Relation.ReflTransGen (RunStep R) d e) : SoundTerms e src ∧ Descending e := by
  have hi : Runtime e ∧ e.sig = d.sig ∧ e.rules = d.rules ∧ e.env = d.env ∧
      SoundTerms e src ∧ Descending e := by
    apply RunReach.induction (P := fun mid => Runtime mid ∧ mid.sig = d.sig ∧
      mid.rules = d.rules ∧ mid.env = d.env ∧ SoundTerms mid src ∧ Descending mid) _ hr
      ⟨h, rfl, rfl, rfl, hs, hd⟩
    rintro mid post ⟨hm, hsig, hrules, henv, hsound, hdesc⟩ hstep
    have hpostrules : post.rules = d.rules := by
      rw [(MergeClosure.envRules hstep.1).2]
      exact hrules
    exact ⟨hm.runStep hstep, (RunStep.sig hstep).trans hsig, hpostrules,
      (RunStep.env hstep).trans henv,
      runStep_preserves hm (by rw [hsig]; exact hshape) hsound hdesc
        (hfire mid hm hsig hrules henv hsound hdesc) hstep⟩
  exact hi.2.2.2.2

/-- A dedicated rebuilding run only fires maintenance; all such firings are sound. -/
theorem rebuild_preserves {P : Program} {src d e : Database} (h : Runtime d)
    (hshape : MergeShape d.sig) (hs : SoundTerms d src) (hd : Descending d)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (hr : Relation.ReflTransGen (RunStep rebuildRuleset) d e) :
    SoundTerms e src ∧ Descending e := by
  apply runReach_preserves h hshape hs hd _ hr
  intro mid hm _ hrules _ hsound hdesc r hr hR σ post hσ hf
  obtain ⟨c, hc, hcr⟩ := honly r (hrules ▸ hr) hR
  exact ⟨maintenance_soundTerms hc hcr hm.noUnions.diag hm.wf hsound hσ hf,
    maintenance_descending hc hcr hm.noUnions.diag hm.wf hdesc hσ hf⟩

/-- The mathematical `saturate @rebuild` command preserves the row invariants. -/
theorem rebuild_cmd_preserves {P : Program} {src d e : Database} (h : Runtime d)
    (hshape : MergeShape d.sig) (hs : SoundTerms d src) (hd : Descending d)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (hr : CmdStep d (.saturate rebuildRuleset) e) : SoundTerms e src ∧ Descending e :=
  rebuild_preserves h hshape hs hd honly (cmdStep_saturate_iff.mp hr).reach

end Egglog.Congruence.Abstract
