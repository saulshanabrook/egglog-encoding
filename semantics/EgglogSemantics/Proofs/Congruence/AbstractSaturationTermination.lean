import EgglogSemantics.Proofs.Congruence.AbstractTermination
import EgglogSemantics.Proofs.Congruence.AbstractRowWrites
import EgglogSemantics.Proofs.Congruence.AbstractComplete

/-! A finite saturated source state bounds all generated values and rows. This supplies
finite target saturation executions independently of conditional outcome agreement. -/

namespace Egglog.Congruence.Abstract

/-- Source rule heads can construct new values, but their source justifications bound
those values by the fixed source state throughout any finite target execution. -/
theorem source_saturation_termBound {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ rest) {src d e : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d) (hsig : d.sig = encodeSig P)
    (hrules : RulesEncoded P src d) {R : RulesetName} (hsat : RunSaturated R src)
    (hr : Relation.ReflTransGen (RunStep R) d e) :
    e.terms ⊆ d.terms ∪ (src.terms ∪ SoundRows src) := by
  induction hr with
  | refl => exact Set.subset_union_left
  | @tail mid post hreach hstep ih =>
      have hm := h.runReach hreach
      obtain ⟨hsm, hdm⟩ :=
        source_saturation_preserves hp hP hpre h hs hd hsig hrules hsat hreach
      have hfire : ∀ r ∈ mid.rules, r.ruleset = R → ∀ out ∈ RuleResults mid r,
          SoundTerms out src ∧ out.terms ⊆ mid.terms ∪ (src.terms ∪ SoundRows src) := by
        rintro r hr hR out ⟨σ, hσ, hf⟩
        rcases (hrules r).mp ((runReach_rules hreach) ▸ hr) with
          ⟨c, hc, hcr⟩ | ⟨s, hs', rfl⟩
        · refine ⟨maintenance_soundTerms hc hcr hm.noUnions.diag hm.wf hsm hσ hf, ?_⟩
          intro t ht
          exact (maintenance_newTerms hc hcr hm.noUnions.diag hm.wf hsm hσ hf ht).elim
            Or.inl (fun ht => Or.inr (Or.inr ht))
        · have hout := source_firing_preserves hp hP hpre hm hsm hdm
            ((RunReach.sig hreach).trans hsig) hs'
            ((runRules_eq_self_iff R src).mp hsat.1 s hs' hR) hσ hf
          exact ⟨hout.1, evalLocalActions_rows_newTerms (hpre.wf Database.WF.empty)
            hout.1 (encodeActions_rowActions s.actions) hf⟩
      have hsound : SoundTerms (RunRules R mid) src := by
        apply hsm.sUnion
        rintro out ⟨r, hr, hR, hout⟩
        exact (hfire r hr hR out hout).1
      have hbound : (RunRules R mid).terms ⊆ d.terms ∪ (src.terms ∪ SoundRows src) := by
        intro t ht
        simp only [RunRules, Database.sUnion_terms, Set.mem_union, Set.mem_iUnion,
          exists_prop] at ht
        rcases ht with ht | ⟨out, ⟨r, hr, hR, hout⟩, ht⟩
        · exact ih ht
        · exact ((hfire r hr hR out hout).2 ht).elim (fun ht => ih ht) Or.inr
      intro t ht
      exact (mergeClosure_newTerms (hm.runRules R) hsound hstep ht).elim
        (fun ht => hbound ht) (fun ht => Or.inr (Or.inr ht))

/-- A finite source fixed point guarantees existence of a finite compiled saturation.
The target may take a different number of rounds from the source. -/
theorem source_saturate_exists {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ rest) {src d : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d) (hsig : d.sig = encodeSig P)
    (hrules : RulesEncoded P src d) {R : RulesetName} (hsat : RunSaturated R src)
    (hf : d.eqs.Finite) : ∃ e, SaturateReach R d e := by
  have hsrc := Database.finite_terms hpre.finite_from_empty.1
  have hbound := (Database.finite_terms hf).union (hsrc.union (SoundRows.finite hsrc))
  apply Egglog.saturateReach_exists_of_finite_bound R d (hbound.prod hbound)
  intro e he p hp'
  have hm := eqsInTerms_free (Cong.direct hp')
  have ht := source_saturation_termBound hp hP hpre h hs hd hsig hrules hsat he
  exact ⟨ht hm.1, ht hm.2⟩

/-- The whole compiled block for a terminating source saturation has a finite execution,
including the trailing dedicated rebuilding command. -/
theorem saturate_command_exists {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ Cmd.saturate R :: rest) {src post d : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hsource : CmdStep src (.saturate R) post) :
    ∃ e, ProgramStep d ((encodeCmd pre.length (.saturate R)).map Command.command) e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hrt := prefix_runtime hp hsub htpre
  have hm := metadata_of_prefix hpre htpre
  have hnext := hpre.append (ProgramStep.cons hsource .nil)
  have hP' : P = (pre ++ [.saturate R]) ++ rest := by
    simpa only [List.append_assoc, List.singleton_append] using hP
  have hsub' : ∀ c ∈ pre ++ [Cmd.saturate R], c ∈ P :=
    fun c hc => hP' ▸ List.mem_append_left _ hc
  have hsat := cmdStep_saturate_iff.mp hsource
  have hsound : SoundTerms d post := h.sound.mono_src hsource.contained.eqs
  have hrules : RulesEncoded P post d := by
    intro r
    simpa only [cmdStep_rules_of_saturate hsource] using hm.rules r
  obtain ⟨mid, hmid⟩ := source_saturate_exists hp hP' hnext hrt hsound h.descend
    hm.sig hrules hsat.2 htpre.finite_from_empty.1
  have hfirst : CmdStep d (.saturate R) mid := CmdStep.of_reach hmid
  have hmidExec := htpre.append (ProgramStep.cons hfirst .nil)
  have hmidRuntime := hrt.runReach hmid.1
  have hmidSound := (source_saturation_preserves hp hP' hnext hrt hsound h.descend
    hm.sig hrules hsat.2 hmid.1).1
  have hmidRules : RulesEncoded P post mid := by
    intro r
    simpa only [runReach_rules hmid.1] using hrules r
  obtain ⟨last, hlast⟩ := rebuild_cmd_exists hmidRuntime hmidSound
    hmidExec.finite_from_empty.1 (Database.finite_terms hnext.finite_from_empty.1)
    (hmidRules.rebuild_only hp hnext hsub')
  exact ⟨last, .cons hfirst (.cons hlast .nil)⟩

end Egglog.Congruence.Abstract
