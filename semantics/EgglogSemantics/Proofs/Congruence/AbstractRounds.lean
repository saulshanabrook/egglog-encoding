import EgglogSemantics.Proofs.Congruence.AbstractHead
import EgglogSemantics.Proofs.Congruence.AbstractSoundHead
import EgglogSemantics.Proofs.Congruence.LiveRunRead
import EgglogSemantics.Proofs.Congruence.LiveMetadata

/-! Completed target fixed points represent every finite source round sequence. -/

namespace Egglog.Congruence.Abstract

open Live

theorem encodedRule_firing_reads_of_programStep {P pre : Program}
    (hp : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    {src querySrc post : Database} (hpre : ProgramStep Database.empty pre src)
    (hqsig : querySrc.sig = src.sig)
    {d : Database} (h : Rebuilt d) (hrt : Live.Runtime d)
    (hs : SoundTerms d src.completion) (htotal : UFTotal d)
    (hsig : d.sig = encodeSig P) (hreads : Reads d querySrc)
    {r : Rule} (hr : Cmd.rule r ∈ P) {σ : Env}
    (hm : ValidQuerySubst querySrc r.query σ)
    (hf : evalLocalActions querySrc r.actions σ = some post) :
    ∃ ρ d', ValidQuerySubst d (encodeRule r).query ρ ∧
      evalLocalActions d (encodeRule r).actions ρ = some d' ∧ Reads d' post := by
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))
  have hhead : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, fk ∈ P.ctors := by
    intro a ha e he fk hk
    apply mem_program_ctors hr
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, actionExprs_ctors he hk⟩)
  apply encodedRule_firing_reads h hrt.noUnions.diag hrt.storeOk
    (viewDeclared_of_signature hp hrt.noUnions.diag hsig) (hs.edgesSound hrt.noUnions.diag)
    hcs.wf.completion htotal (by rw [hqsig]; exact hcs.sig) hreads
    ?_ (hp.queryEncodable _ hr).2
    (fun p hm => ((hp.queryEncodable _ hr).1 p hm).1) ?_ ?_ ?_ ?_ ?_ hm hf
  · exact (Program.OrderingFree.of_mem hp.noMin hr).1
  · intro v hv
    apply hp.noAt v
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_dedup.mpr
    apply List.mem_flatMap.mpr
    exact ⟨Cmd.rule r, hr, List.mem_union_iff.mpr (Or.inl hv)⟩
  · exact orderingFree_actionExprs (Program.OrderingFree.of_mem hp.noMin hr).2
  · intro _ _ _ _ f _ hctor
    exact sourceConstructors_of_programStep hp hsub hpre hsig f (hqsig ▸ hctor)
  · exact hsig ▸ encodeSig_ufName hp
  · intro a ha e he fk hk
    exact hsig ▸ (encodeSig_tables hp (hhead a ha e he fk hk)).2

theorem reads_round_of_closed {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src querySrc : Database}
    (hpre : ProgramStep Database.empty pre src)
    (hqsig : querySrc.sig = src.sig)
    {d : Database} (h : Rebuilt d) (hrt : Live.Runtime d)
    (hs : SoundTerms d src.completion) (htotal : UFTotal d)
    (hsig : d.sig = encodeSig P) (hreads : Reads d querySrc)
    (hrules : ∀ r ∈ querySrc.rules, Cmd.rule r ∈ P ∧ encodeRule r ∈ d.rules)
    {R : RulesetName} (hclosed : RunSaturated R d) : Reads d (RunRules R querySrc) := by
  apply hreads.round
  intro r hr hR post hpost
  obtain ⟨σ, hm, hf⟩ := hpost
  obtain ⟨ρ, d', hmatch, hfire, hreads'⟩ := encodedRule_firing_reads_of_programStep
    hp hsub hpre hqsig h hrt hs htotal hsig hreads (hrules r hr).1 hm hf
  exact (Covers.firing hrt hclosed (hrules r hr).2 hR ⟨ρ, hmatch, hfire⟩).reads hreads'

theorem reads_reach_of_closed {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src start post : Database}
    (hpre : ProgramStep Database.empty pre src)
    (hssig : start.sig = src.sig)
    {d : Database} (h : Rebuilt d) (hrt : Live.Runtime d)
    (hs : SoundTerms d src.completion) (htotal : UFTotal d)
    (hsig : d.sig = encodeSig P) (hreads : Reads d start)
    (hrules : ∀ r ∈ start.rules, Cmd.rule r ∈ P ∧ encodeRule r ∈ d.rules)
    {R : RulesetName} (hclosed : RunSaturated R d)
    (hreach : Relation.ReflTransGen (RunStep R) start post) : Reads d post := by
  have hctor := (hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))).sig
  have go : Reads d post ∧ post.sig = src.sig ∧ post.rules = start.rules := by
    induction hreach with
    | refl => exact ⟨hreads, hssig, rfl⟩
    | @tail m e hreach hstep ih =>
        have hresult := reads_round_of_closed hp hsub hpre ih.2.1 h hrt hs
          htotal hsig ih.1 (fun r hr => hrules r (ih.2.2 ▸ hr)) hclosed
        refine ⟨?_, hstep.sig.trans ih.2.1, hstep.1.envRules.2.trans ih.2.2⟩
        rw [hstep.eq_of_allConstructors (by rw [ih.2.1]; exact hctor)]
        exact hresult
  exact go.1

theorem round_reads {P pre : Program} (hp : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    {src post : Database} (hpre : ProgramStep Database.empty pre src)
    {R : RulesetName} (hsource : RunStep R src post) {d e : Database}
    (h : Rebuilt d) (hrt : Live.Runtime d) (hs : SoundTerms d src.completion)
    (htotal : UFTotal d) (hsig : d.sig = encodeSig P) (hrules : Live.RulesEncoded P src d)
    (hreads : Reads d src) (htarget : RunStep R d e) : Reads e post := by
  have hcs := (hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))).sig
  rw [hsource.eq_of_allConstructors hcs]
  apply ((Covers.runStep hrt htarget).reads hreads).round
  intro r hr hR out hout
  obtain ⟨σ, hm, hf⟩ := hout
  have hmem : Cmd.rule r ∈ P := hsub _ (by
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr)
  obtain ⟨ρ, d', hmatch, hfire, hreads'⟩ := encodedRule_firing_reads_of_programStep
    hp hsub hpre rfl h hrt hs htotal hsig hreads hmem hm hf
  apply (Covers.mergeClosure (hrt.runRules R).state
    (hrt.runRules R).noUnions.diag htarget.1).reads
  apply hreads'.mono
  exact fun _ he => ruleResult_row ((hrules _).mpr (Or.inr ⟨r, hr, rfl⟩))
    hR ⟨ρ, hmatch, hfire⟩ he

theorem saturation_reads {P pre : Program} (hp : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src start : Database}
    (hpre : ProgramStep Database.empty pre src) {R : RulesetName}
    (hsource : SaturateReach R start src)
    {initial d : Database} (hi : Live.Runtime initial) (htarget : SaturateReach R initial d)
    (h : Rebuilt d) (hs : SoundTerms d src.completion) (htotal : UFTotal d)
    (hsig : d.sig = encodeSig P) (hrules : Live.RulesEncoded P src d)
    (hreads : Reads initial start) : Reads d src := by
  apply reads_reach_of_closed hp hsub hpre (RunReach.sig hsource.reach).symm
    h (hi.runReach htarget.reach) hs htotal hsig
    ((Covers.runReach hi htarget.reach).reads hreads) ?_
    (saturated_endpoint hi htarget) hsource.reach
  intro r hr
  have hr' : r ∈ src.rules := runReach_rules hsource.reach ▸ hr
  have hmem : Cmd.rule r ∈ P := hsub _ (by
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr')
  exact ⟨hmem, (hrules _).mpr (Or.inr ⟨r, hr', rfl⟩)⟩

end Egglog.Congruence.Abstract
