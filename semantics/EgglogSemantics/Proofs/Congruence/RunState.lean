import EgglogSemantics.Proofs.Congruence.Maintenance
import EgglogSemantics.Proofs.Congruence.MaintenanceDescent
import EgglogSemantics.Proofs.Congruence.Execution
import EgglogSemantics.Proofs.Congruence.Rebuilt

/-! Composition of entry soundness, retained-row history, and UF descent through rounds. -/

namespace Egglog.Congruence

/-- Data invariants required between rounds, before rebuilding has reached a fixed point. -/
structure RunState (src : Database) (d : FDatabase) : Prop where
  inv : d.Inv
  noUnions : d.NoUnions
  shape : MergeShape d.sig
  uf : d.sig ufName = some (tableDecl 1)
  sound : SoundTerms d src
  history : EntryRowsUF d
  descend : UFTermsDescend d

theorem RunState.merge {src : Database} {d e : FDatabase} (h : RunState src d)
    {n : Nat} (run : Egglog.FDatabase.mergeSaturateF n d = some e) : RunState src e := by
  have hsig := (Egglog.FDatabase.mergeSaturateF_fields run).1
  exact ⟨h.inv.mergeSaturateF h.shape.mergesLegal run, mergeSaturateF_noUnions n h.noUnions run,
    hsig ▸ h.shape, hsig ▸ h.uf,
    mergeSaturateF_soundTerms n h.shape h.inv h.noUnions h.sound run,
    mergeSaturateF_entryRowsUF n h.shape h.inv h.noUnions h.history run,
    mergeSaturateF_ufTermsDescend n h.shape h.inv h.noUnions h.descend run⟩

/-- Each selected firing preserves the historical invariants; unioning all its results
preserves them as well. The ruleset premise excludes unrelated registered source rules. -/
theorem RunState.rules {src : Database} {d : FDatabase} {R : RulesetName}
    (h : RunState src d)
    (hf : ∀ r ∈ d.rules, r.ruleset = R → ∀ σ e, σ ∈ matchQuery d r.query → Fired d r σ e →
      SoundTerms e src ∧ EntryRowsUF e ∧ UFTermsDescend e) : RunState src (execRunRules R d) := by
  have hist : (SoundTerms (execRunRules R d) src ∧ EntryRowsUF (execRunRules R d) ∧
      UFTermsDescend (execRunRules R d)) ∧ (execRunRules R d).sig = d.sig := by
    apply Egglog.FDatabase.execRunRules_induction_ruleset
      (P := fun e => (SoundTerms e src ∧ EntryRowsUF e ∧ UFTermsDescend e) ∧ e.sig = d.sig)
      ⟨⟨h.sound, h.history, h.descend⟩, rfl⟩
    intro acc e r σ hacc hr hR hσ he
    have hfire : Fired d r σ { e with env := d.env, rules := d.rules } := by
      change (execActions { d with env := σ ++ d.env } r.actions).map _ = _
      rw [he]; rfl
    have hpost := hf r hr hR σ _ hσ hfire
    have hsig : e.sig = acc.sig := (Egglog.FDatabase.execActions_sig he).trans hacc.2.symm
    exact ⟨⟨hacc.1.1.union hpost.1, hacc.1.2.1.union hpost.2.1 hsig,
      hacc.1.2.2.union hpost.2.2⟩, hacc.2⟩
  have hsig := Egglog.FDatabase.execRunRules_fields (R := R) (d := d)
  exact ⟨h.inv.execRunRules (fun r _ => actions_writeLegal r.actions d.sig),
    execRunRules_noUnions h.noUnions, hsig.1 ▸ h.shape, hsig.1 ▸ h.uf,
    hist.1.1, hist.1.2.1, hist.1.2.2⟩

theorem RunState.round {src : Database} {d e : FDatabase} {R : RulesetName}
    (h : RunState src d)
    (hf : ∀ r ∈ d.rules, r.ruleset = R → ∀ σ e, σ ∈ matchQuery d r.query → Fired d r σ e →
      SoundTerms e src ∧ EntryRowsUF e ∧ UFTermsDescend e)
    (run : d.runRoundM R = some e) : RunState src e := (h.rules hf).merge run

/-- Closing a sequence of rounds preserves the same source justification reference. -/
theorem RunState.saturate {src : Database} {R : RulesetName} {rules : List Rule}
    {sig : Signature}
    (hf : ∀ d, RunState src d → d.sig = sig → d.rules = rules →
      ∀ r ∈ rules, r.ruleset = R → ∀ σ e, σ ∈ matchQuery d r.query → Fired d r σ e →
        SoundTerms e src ∧ EntryRowsUF e ∧ UFTermsDescend e) :
    ∀ n {d e : FDatabase}, RunState src d → d.sig = sig → d.rules = rules →
      d.runSaturateM R n = some e → RunState src e := by
  intro n
  induction n with
  | zero =>
      intro d e h hs hr run
      rw [Egglog.FDatabase.runSaturateM] at run
      obtain ⟨m, _, run⟩ := Option.bind_eq_some_iff.mp run
      split at run
      · obtain rfl := Option.some.inj run; exact h
      · cases run
  | succ n ih =>
      intro d e h hs hr run
      rw [Egglog.FDatabase.runSaturateM] at run
      obtain ⟨m, hm, run⟩ := Option.bind_eq_some_iff.mp run
      split at run
      · obtain rfl := Option.some.inj run; exact h
      · exact ih (h.round (fun r hmem => hf d h hs hr r (hr ▸ hmem)) hm)
          ((Egglog.FDatabase.runRoundM_fields hm).1.trans hs)
          ((Egglog.FDatabase.runRoundM_fields hm).2.2.trans hr) run

/-- Generated maintenance rules discharge all three historical preservation obligations. -/
theorem RunState.maintenance_firing {src : Database} {d e : FDatabase} (h : RunState src d)
    {P : Program} {c : Command} (hc : c ∈ allMaintenanceRules P) {r : Rule}
    (hr : c.command = .rule r) {σ : Env} (hm : σ ∈ matchQuery d r.query)
    (hf : Fired d r σ e) : SoundTerms e src ∧ EntryRowsUF e ∧ UFTermsDescend e :=
  ⟨maintenance_soundTerms hc hr h.noUnions.eqsRefl h.inv.index
      (Egglog.FDatabase.SubtermClosed.of_wf h.inv.wf) h.sound hm hf,
    maintenance_entryRowsUF hc hr h.inv h.shape h.history hm hf,
    maintenance_ufTermsDescend hc hr h.inv h.noUnions h.descend hm hf⟩

/-- An actual maintenance saturation preserves the invariants needed for rebuilding. -/
theorem RunState.maintenance {src : Database} {P : Program} {d e : FDatabase}
    {R : RulesetName} {n : Nat} (h : RunState src d)
    (hr : ∀ r ∈ d.rules, r.ruleset = R →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (run : d.runSaturateM R n = some e) : RunState src e := by
  apply RunState.saturate (rules := d.rules) (sig := d.sig) _ n h rfl rfl run
  intro m hm _ _ r hmem hR σ e hσ hf
  obtain ⟨c, hc, hcr⟩ := hr r hmem hR
  exact hm.maintenance_firing hc hcr hσ hf

/-- Dedicated maintenance saturation establishes the actual rebuilt-state predicate. -/
theorem RunState.rebuilt {src : Database} {P : Program} {d e : FDatabase} {n : Nat}
    (h : RunState src d)
    (hr : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (run : d.runSaturateM rebuildRuleset n = some e) : Rebuilt e ∧ SoundTerms e src := by
  have he := h.maintenance hr run
  exact ⟨⟨he.inv, he.noUnions, he.shape, he.uf, he.descend, he.history,
    Egglog.FDatabase.runSaturateM_mergeSettled run,
    Egglog.FDatabase.runSaturateM_roundClosed run⟩, he.sound⟩

end Egglog.Congruence
