import EgglogSemantics.Proofs.Congruence.AbstractSoundHead
import EgglogSemantics.Proofs.Congruence.AbstractRunState

/-! Actual target rounds preserve soundness in the source's inferred-fact completion. -/

namespace Egglog.Congruence.Abstract

/-- A completed source firing may be re-expressed using recorded source values. -/
theorem completion_firing_contained_round {src out post : Database} {r : Rule}
    {R : RulesetName} (hw : src.WF) (hs : src.StoreOk) (hc : src.sig.AllConstructors)
    (hn : r.OrderingFree)
    (hr : r ∈ src.rules) (hR : r.ruleset = R)
    (hout : out ∈ RuleResults src.completion r) (hstep : RunStep R src post) :
    out.Contained post.completion := by
  obtain ⟨out', ho', hh⟩ := SourceMeaning.firing_transport hw.completion hw hs hc
    (src.sameMeaning_completion hw).symm hn hout
  obtain rfl := hstep.eq_of_allConstructors hc
  constructor
  intro p hp
  exact InferredFacts.infers_mono (SourceMeaning.firing_contained_round hr hR ho')
    ((hh.inferred _ _).mp (InferredFacts.infers_of_cong (.direct hp)))

theorem completion_mono {src post : Database} (h : src.Contained post) :
    src.completion.Contained post.completion :=
  ⟨fun _ hp => InferredFacts.infers_mono h hp⟩

/-- The upper source model contains every firing reconstructed at current target leaders. -/
theorem source_firing_preserves {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ rest) {src ref d post : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Live.Runtime d)
    (hs : SoundTerms d src.completion) (hd : Descending d) (hsig : d.sig = encodeSig P)
    {r : Rule} (hr : r ∈ src.rules)
    (hupper : ∀ out ∈ RuleResults src.completion r, out.Contained ref) {σ : Env}
    (hm : ValidQuerySubst d (encodeRule r).query σ)
    (hf : evalLocalActions d (encodeRule r).actions σ = some post) :
    SoundTerms post ref ∧ Descending post := by
  have hmem : Cmd.rule r ∈ P := by
    rw [hP]
    apply List.mem_append_left
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr
  obtain ⟨τ, out, hτ, hout, hs', hd'⟩ := encodedRule_firing_of_programStep hp hP hpre
    hmem hr h hs hd hsig hm hf
  exact ⟨hs'.mono_src (hupper out ⟨τ, hτ, hout⟩).eqs, hd'⟩

/-- A source round justifies every actual compiled firing and destructive merge. -/
theorem source_round_preserves {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Live.Runtime d)
    (hs : SoundTerms d src.completion) (hd : Descending d) (hsig : d.sig = encodeSig P)
    (hrules : ∀ r ∈ d.rules,
      (∃ c ∈ allMaintenanceRules P, c.command = .rule r) ∨
      ∃ s ∈ src.rules, r = encodeRule s) {R : RulesetName}
    (hsource : RunStep R src post) (htarget : RunStep R d e) :
    SoundTerms e post.completion ∧ Descending e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hc := hpre.ctorState Database.CtorState.empty (fun c hm => hp.ctorsOnly c (hsub c hm))
  have hcontains : src.Contained post := by
    rw [hsource.eq_of_allConstructors hc.sig]
    exact SourceMeaning.round_extends src R
  have hbase := hs.mono_src (completion_mono hcontains).eqs
  apply runStep_preserves h (hsig ▸ encodeSig_mergeShape P) hbase hd _ htarget
  intro r hr hR σ out hm hf
  rcases hrules r hr with ⟨c, hc', hcr⟩ | ⟨s, hs', rfl⟩
  · exact ⟨maintenance_soundTerms hc' hcr h.noUnions.diag h.wf hbase hm hf,
      maintenance_descending hc' hcr h.noUnions.diag h.wf hd hm hf⟩
  · apply source_firing_preserves hp hP hpre h hs hd hsig hs' ?_ hm hf
    intro result hresult
    have hmem : Cmd.rule s ∈ P := hsub _ (by
      simpa [Database.empty] using (hpre.mem_rules_iff s).mp hs')
    exact completion_firing_contained_round hc.wf
      (storeOk_of_sourceTerms hc.wf
        (termsBuild_of_programStep (fun c hm => hp.ctorsOnly c (hsub c hm)) hpre) hc.sig)
      hc.sig (Program.OrderingFree.of_mem hp.noMin hmem) hs' hR hresult hsource

/-- A closed completed source model justifies arbitrarily many actual target rounds. -/
theorem source_saturation_preserves {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ rest) {src d e : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Live.Runtime d)
    (hs : SoundTerms d src.completion) (hd : Descending d) (hsig : d.sig = encodeSig P)
    (hrules : ∀ r ∈ d.rules,
      (∃ c ∈ allMaintenanceRules P, c.command = .rule r) ∨
      ∃ s ∈ src.rules, r = encodeRule s) {R : RulesetName}
    (hfixed : RunRules R src.completion = src.completion)
    (htarget : Relation.ReflTransGen (RunStep R) d e) :
    SoundTerms e src.completion ∧ Descending e := by
  apply runReach_preserves h (hsig ▸ encodeSig_mergeShape P) hs hd _ htarget
  intro mid hm hmSig hmRules _ hsound hdesc r hr hR σ out hσ hf
  rcases hrules r (hmRules ▸ hr) with ⟨c, hc, hcr⟩ | ⟨s, hs', rfl⟩
  · exact ⟨maintenance_soundTerms hc hcr hm.noUnions.diag hm.wf hsound hσ hf,
      maintenance_descending hc hcr hm.noUnions.diag hm.wf hdesc hσ hf⟩
  · exact source_firing_preserves hp hP hpre hm hsound hdesc (hmSig.trans hsig) hs'
      ((runRules_eq_self_iff R src.completion).mp hfixed s hs' hR) hσ hf

end Egglog.Congruence.Abstract
