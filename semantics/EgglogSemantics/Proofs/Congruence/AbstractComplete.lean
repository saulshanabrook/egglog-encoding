import EgglogSemantics.Proofs.Congruence.AbstractSetup
import EgglogSemantics.Proofs.Congruence.AbstractRounds
import EgglogSemantics.Proofs.Congruence.LiveGlobal
import EgglogSemantics.Proofs.Congruence.LiveMetadata
import EgglogSemantics.Proofs.Congruence.LiveCorrespond
import EgglogSemantics.Proofs.Congruence.Observation
import EgglogSemantics.Proofs.ActionProgram

/-! Composition of live mathematical compilation at original command boundaries. -/

namespace Egglog.Congruence.Abstract

open Live

private theorem maintenance_only {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src d : Database}
    (hpre : ProgramStep Database.empty pre src) (hrules : Live.RulesEncoded P src d) :
    ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
  intro r hr hR
  rcases (hrules r).mp hr with hm | ⟨s, hs, rfl⟩
  · exact hm
  · have hm : Cmd.rule s ∈ P := hsub _ (by
      simpa [Database.empty] using (hpre.mem_rules_iff s).mp hs)
    exact (ruleset_ne_rebuild hp hm hR).elim

private theorem source_reach_contained {d e : Database} (hc : d.sig.AllConstructors)
    {R : RulesetName} (hr : Relation.ReflTransGen (RunStep R) d e) : d.Contained e := by
  induction hr with
  | refl => exact .refl _
  | @tail mid post hr hs ih =>
      apply ih.trans
      rw [hs.eq_of_allConstructors (by rw [RunReach.sig hr]; exact hc)]
      exact SourceMeaning.round_extends mid R

theorem boundary_of_rebuild {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src d e : Database}
    (hpre : ProgramStep Database.empty pre src) (h : Runtime d)
    (hsig : d.sig = encodeSig P)
    (hs : SoundTerms d src.completion) (hd : Descending d)
    (hrules : Live.RulesEncoded P src d) (hreads : Reads d src) (hu : UFTotal d)
    (ht : CmdStep d (.saturate rebuildRuleset) e) : Boundary src e := by
  have honly := maintenance_only hp hsub hpre hrules
  have hreach := cmdStep_saturate_iff.mp ht
  have he := h.runReach hreach.reach
  obtain ⟨hs', hd'⟩ := rebuild_cmd_preserves h (hsig ▸ encodeSig_mergeShape P) hs hd honly ht
  have herules : Live.RulesEncoded P src e := by
    intro r
    rw [runReach_rules hreach.reach]
    exact hrules r
  exact ⟨hs', hd', (Covers.runReach h hreach.reach).reads hreads,
    rebuilt_of_metadata he hp ((RunReach.sig hreach.reach).trans hsig) herules
      (Or.inl rfl) (Database.finite_terms he.state.finite.eqs)
      (saturated_endpoint h hreach) hd', hu.rebuild hp h hsig honly hreach.reach⟩

theorem compiled_prefix_step {P pre : Program} {d e : Database} {c : Cmd}
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (hc : ProgramStep d ((encodeCmd pre.length c).map Command.command) e) :
    ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds (pre ++ [c]) 0).map Command.command) e := by
  have hex : encodeCmds (pre ++ [c]) 0 = encodeCmds pre 0 ++ encodeCmd pre.length c := by
    rw [encodeCmds_append]
    simp only [Nat.zero_add, encodeCmds, List.append_nil]
  simpa only [hex, List.append_assoc, List.map_append] using ht.append hc

theorem Boundary.run {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ Cmd.run R :: rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hrt : Runtime d) (hsource : CmdStep src (.run R) post)
    (htarget : ProgramStep d ((encodeCmd pre.length (.run R)).map Command.command) e) :
    Boundary post e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hnext := hpre.append (ProgramStep.cons hsource .nil)
  have hP' : P = (pre ++ [.run R]) ++ rest := by simpa [List.append_assoc] using hP
  have hsub' : ∀ c ∈ pre ++ [Cmd.run R], c ∈ P :=
    fun c hc => hP' ▸ List.mem_append_left _ hc
  have hsig := Live.prefix_sig htpre
  have hrules := Live.rulesEncoded_of_prefix hpre htpre
  have hs : RunStep R src post := hsource
  obtain ⟨mid, hfirst, hrest⟩ := htarget.cons_inv
  obtain ⟨last, hlast, hnil⟩ := hrest.cons_inv
  obtain rfl := hnil.nil_inv
  have ht : RunStep R d mid := hfirst
  obtain ⟨hsound, hdesc⟩ := source_round_preserves hp hP hpre hrt
    h.sound h.descend hsig (fun r hr => (hrules r).mp hr) hs ht
  have hreads := round_reads hp hsub hpre hs h.rebuilt hrt h.sound h.total
    hsig hrules h.reads ht
  have hu := target_runReach_ufTotal hp hsub hpre hrt hsig hrules h.total (.single ht)
  have hrules' : Live.RulesEncoded P post mid := by
    intro r
    simpa only [cmdStep_rules_of_run hsource, cmdStep_rules_of_run hfirst] using hrules r
  exact boundary_of_rebuild hp hsub' hnext (hrt.runStep ht) (ht.sig.trans hsig)
    hsound hdesc hrules' hreads hu hlast

theorem Boundary.saturate {P pre rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ Cmd.saturate R :: rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hrt : Runtime d) (hsource : CmdStep src (.saturate R) post)
    (htarget : ProgramStep d ((encodeCmd pre.length (.saturate R)).map Command.command) e) :
    Boundary post e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hnext := hpre.append (ProgramStep.cons hsource .nil)
  have hP' : P = (pre ++ [.saturate R]) ++ rest := by simpa [List.append_assoc] using hP
  have hsub' : ∀ c ∈ pre ++ [Cmd.saturate R], c ∈ P :=
    fun c hc => hP' ▸ List.mem_append_left _ hc
  have hR : R ∈ P.saturateRulesets := by rw [hP]; simp [Program.saturateRulesets]
  have hsig := Live.prefix_sig htpre
  have hrules := Live.rulesEncoded_of_prefix hpre htpre
  have hs := cmdStep_saturate_iff.mp hsource
  obtain ⟨mid, hfirst, hrest⟩ := htarget.cons_inv
  obtain ⟨last, hlast, hnil⟩ := hrest.cons_inv
  obtain rfl := hnil.nil_inv
  have ht := cmdStep_saturate_iff.mp hfirst
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))
  have hstore := storeOk_of_sourceTerms hcs.wf
    (termsBuild_of_programStep (fun c hc => hp.ctorsOnly c (hsub c hc)) hpre) hcs.sig
  have hfixed := SourceMeaning.saturation_completion_closed hcs.wf hstore hcs.sig
    (fun r hr _ => Program.OrderingFree.of_mem hp.noMin (hsub (.rule r) (by
      simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr))) hs
  have hrulesPost : Live.RulesEncoded P post d := by
    intro r
    simpa only [cmdStep_rules_of_saturate hsource] using hrules r
  obtain ⟨hsound, hdesc⟩ := source_saturation_preserves hp hP' hnext hrt
    (h.sound.mono_src (completion_mono (source_reach_contained hcs.sig hs.reach)).eqs)
    h.descend hsig (fun r hr => (hrulesPost r).mp hr) hfixed ht.reach
  have hmid := hrt.runReach ht.reach
  have hmsig := (RunReach.sig ht.reach).trans hsig
  have hrules' : Live.RulesEncoded P post mid := by
    intro r
    rw [runReach_rules ht.reach]
    exact hrulesPost r
  have hu := target_runReach_ufTotal hp hsub hpre hrt hsig hrules h.total ht.reach
  have hrebuild := rebuilt_of_metadata hmid hp hmsig hrules' (Or.inr hR)
    (Database.finite_terms hmid.state.finite.eqs) (saturated_endpoint hrt ht) hdesc
  have hreads := saturation_reads hp hsub' hnext hs hrt ht hrebuild
    hsound hu hmsig hrules' h.reads
  exact boundary_of_rebuild hp hsub' hnext hmid hmsig hsound hdesc hrules' hreads hu hlast

theorem Boundary.step {P pre rest : Program} (hp : P.Fragment) {c : Cmd}
    (hP : P = pre ++ c :: rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hs : CmdStep src c post)
    (ht : ProgramStep d ((encodeCmd pre.length c).map Command.command) e) :
    Boundary post e := by
  have hsub : ∀ cmd ∈ pre, cmd ∈ P := fun cmd hm => hP ▸ List.mem_append_left _ hm
  have hmem : c ∈ P := hP ▸ List.mem_append_right _ List.mem_cons_self
  have hcs := (hpre.ctorState Database.CtorState.empty
    (fun cmd hm => hp.ctorsOnly cmd (hsub cmd hm))).sig
  have hrt := Live.prefix_runtime hp hsub htpre
  cases c with
  | decl f dc => exact h.decl hcs (hp.ctorsOnly _ hmem) hs ht
  | rule r =>
      exact h.rule hcs
        (Congruence.prefix_mergeNormal htpre) hs ht
  | check q => exact h.check hs ht
  | run R => exact h.run hp hP hpre htpre hrt hs ht
  | saturate R => exact h.saturate hp hP hpre htpre hrt hs ht
/-- Compose command preservation without requiring either execution to determine the other. -/
theorem Boundary.program {P pre todo rest : Program} (hp : P.Fragment)
    (hP : P = pre ++ todo ++ rest) {src post d e : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hs : ProgramStep src todo post)
    (ht : ProgramStep d ((encodeCmds todo pre.length).map Command.command) e) :
    Boundary post e := by
  induction todo generalizing pre src d with
  | nil =>
      obtain rfl := hs.nil_inv
      obtain rfl := ht.nil_inv
      exact h
  | cons c cs ih =>
      obtain ⟨mid, hc, hcs⟩ := hs.cons_inv
      have ht' : ProgramStep d ((encodeCmd pre.length c).map Command.command ++
          (encodeCmds cs (pre.length + 1)).map Command.command) e := by
        simpa only [encodeCmds, List.map_append] using ht
      obtain ⟨targetMid, htc, htcs⟩ := ht'.append_inv
      have hPstep : P = pre ++ c :: (cs ++ rest) := by
        simpa only [List.append_assoc, List.cons_append] using hP
      have hnext := h.step hp hPstep hpre htpre hc htc
      apply ih (pre := pre ++ [c]) ?_ (hpre.append (.cons hc .nil))
        (compiled_prefix_step htpre htc) hnext hcs
      · simpa only [List.length_append, List.length_singleton] using htcs
      · simpa only [List.append_assoc, List.singleton_append, List.cons_append,
          List.nil_append] using hP

/-- The relation holds at every pair of corresponding successful mathematical prefixes. -/
theorem boundary_prefix {P pre rest : Program} (hp : P.Fragment) (hP : P = pre ++ rest)
    {src d : Database} (hs : ProgramStep Database.empty pre src)
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d) : Boundary src d := by
  have ht' : ProgramStep Database.empty
      ((encodePrelude P).map Command.command ++ (encodeCmds pre 0).map Command.command) d := by
    simpa only [List.map_append] using ht
  obtain ⟨initial, hi, hr⟩ := ht'.append_inv
  apply Boundary.program (pre := []) hp (by simpa using hP) ProgramStep.nil
    (by simpa [encodeCmds] using hi) (prelude_boundary hp hi) hs hr

/-- Every observation premise is derived from the two actual command prefixes. -/
theorem checkAgreement {P : Program} (hp : P.Fragment) : CheckAgreement P := by
  intro pre q rest src d hP hs ht
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hmem : Cmd.check q ∈ P := hP ▸ List.mem_append_right _ List.mem_cons_self
  have h := boundary_prefix hp hP hs ht
  have hrt := Live.prefix_runtime hp hsub ht
  have hsig := Live.prefix_sig ht
  have hcs := hs.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))
  have hstore := storeOk_of_sourceTerms hcs.wf
    (termsBuild_of_programStep (fun c hc => hp.ctorsOnly c (hsub c hc)) hs) hcs.sig
  apply Live.queryHolds_iff h.rebuilt hrt.noUnions.diag hrt.storeOk
    (viewTables_of_signature hp hsig) (viewDeclared_of_signature hp hrt.noUnions.diag hsig)
    h.sound h.reads hcs.wf hstore hcs.sig (Program.OrderingFree.of_mem hp.noMin hmem)
    (fun p hpat => ((hp.queryEncodable _ hmem).1 p hpat).1)
    (hp.queryEncodable _ hmem).2 ?_ 0
  intro v hv
  apply hp.noAt v
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  exact ⟨Cmd.check q, hmem, hv⟩

end Egglog.Congruence.Abstract

namespace Egglog.Congruence

/-- Terminating mathematical executions agree on success versus failed checks. -/
theorem preservesObservations : PreservesObservations := by
  intro P _hw hp source target hs ht
  exact observations_of_checkAgreement (Abstract.checkAgreement hp) hs ht

end Egglog.Congruence
