import EgglogSemantics.Proofs.Execution
import EgglogSemantics.Proofs.Congruence.AbstractRounds
import EgglogSemantics.Proofs.Congruence.ForwardHead
import EgglogSemantics.Proofs.Congruence.RuleStore
import EgglogSemantics.Proofs.Congruence.RunState
import EgglogSemantics.Proofs.Congruence.Head

/-! Forward source-round simulation and preservation of target invariants across source runs. -/

namespace Egglog.Congruence

/-- The agreed source domain supplies the syntactic and declaration premises for
forward rule firing at any represented source prefix. -/
theorem encodedRule_firing_reads_of_programStep {P pre : Program}
    (hdom : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    {src querySrc post : Database}
    (hpre : ProgramStep Database.empty pre src)
    (hqsig : querySrc.sig = src.sig) (hqenv : querySrc.env = [])
    {d : FDatabase} (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hsig : d.sig = encodeSig P)
    (hreads : SourceReads d.toDatabase querySrc) {r : Rule} (hr : Cmd.rule r ∈ P) {σ : Env}
    (hm : ValidQuerySubst querySrc r.query σ)
    (hf : evalLocalActions querySrc r.actions σ = some post) :
    ∃ ρ d', ρ ∈ matchQuery d (encodeRule r).query ∧ Fired d (encodeRule r) ρ d' ∧
      SourceReads d'.toDatabase post := by
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hdom.ctorsOnly c (hsub c hc))
  have hhead : ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, fk ∈ P.ctors := by
    intro a ha e he fk hk
    apply mem_program_ctors hr
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, actionExprs_ctors he hk⟩)
  apply encodedRule_firing_reads h htables hs
    (termsBuild_of_programStep (fun c hc => hdom.ctorsOnly c (hsub c hc)) hpre)
    (ctorsIn_of_prefixStep hdom hsub hpre)
    (sourceConstructors_of_programStep hdom hsub hpre hsig) (hpre.wf Database.WF.empty)
    (by rw [hqsig]; exact hcs.sig) hreads hqenv ?_ (hdom.queryEncodable _ hr).2
    (fun p hp => ((hdom.queryEncodable _ hr).1 p hp).1) ?_ ?_ ?_ ?_ hm hf
  · exact (Program.OrderingFree.of_mem hdom.noMin hr).1
  · intro v hv
    apply hdom.noAt v
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_dedup.mpr
    apply List.mem_flatMap.mpr
    exact ⟨Cmd.rule r, hr, List.mem_union_iff.mpr (Or.inl hv)⟩
  · exact orderingFree_actionExprs (Program.OrderingFree.of_mem hdom.noMin hr).2
  · intro _ _ _ _ f _ hctor
    exact sourceConstructors_of_programStep hdom hsub hpre hsig f (hqsig ▸ hctor)
  · intro a ha e he fk hk
    simp [htables.view fk.1 fk.2 (hhead a ha e he fk hk)]

/-- A compiled fixed point represents every original source firing from the source
facts it already represents. Rebuilding supplies the unflattened query's canonical ids. -/
theorem SourceReads.round_of_closed {P pre : Program} (hdom : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src querySrc : Database}
    (hpre : ProgramStep Database.empty pre src)
    (hqsig : querySrc.sig = src.sig) (hqenv : querySrc.env = [])
    {d : FDatabase} (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hsig : d.sig = encodeSig P)
    (hreads : SourceReads d.toDatabase querySrc)
    (hrules : ∀ r ∈ querySrc.rules, Cmd.rule r ∈ P ∧ encodeRule r ∈ d.rules)
    {R : RulesetName} (hclosed : d.RoundClosed R) :
    SourceReads d.toDatabase (RunRules R querySrc) := by
  apply hreads.runRules
  intro r hr hR post hp
  obtain ⟨σ, hm, hf⟩ := hp
  obtain ⟨ρ, d', hmatch, hfire, hpost⟩ := encodedRule_firing_reads_of_programStep
    hdom hsub hpre hqsig hqenv h htables hs hsig hreads (hrules r hr).1 hm hf
  apply hpost.mono
  apply Egglog.FDatabase.toDatabase_contained_of_lists
  · exact fun t ht => hclosed.fired (hrules r hr).2 hR hmatch hfire ht
  · have hn := execLocalActions_noUnions (encodeActions_unionFree r.actions) h.noUnions hfire
    rw [hn.eqs]
    simp

/-- A compiled fixed point contains every finite sequence of corresponding source rounds.
The target may justify its entries using the final source state throughout this induction. -/
theorem SourceReads.reach_of_closed {P pre : Program} (hdom : P.Fragment)
    (hsub : ∀ c ∈ pre, c ∈ P) {src start post : Database}
    (hpre : ProgramStep Database.empty pre src)
    (hssig : start.sig = src.sig) (hsenv : start.env = [])
    {d : FDatabase} (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hsig : d.sig = encodeSig P)
    (hreads : SourceReads d.toDatabase start)
    (hrules : ∀ r ∈ start.rules, Cmd.rule r ∈ P ∧ encodeRule r ∈ d.rules)
    {R : RulesetName} (hclosed : d.RoundClosed R)
    (hreach : Relation.ReflTransGen (RunStep R) start post) :
    SourceReads d.toDatabase post := by
  have hctor := (hpre.ctorState Database.CtorState.empty
    (fun c hc => hdom.ctorsOnly c (hsub c hc))).sig
  have go : SourceReads d.toDatabase post ∧ post.sig = src.sig ∧ post.env = [] ∧
      post.rules = start.rules := by
    induction hreach with
    | refl => exact ⟨hreads, hssig, hsenv, rfl⟩
    | @tail m e hreach hstep ih =>
        have hresult := ih.1.round_of_closed hdom hsub hpre ih.2.1 ih.2.2.1 h htables hs hsig
          (fun r hr => hrules r (ih.2.2.2 ▸ hr)) hclosed
        refine ⟨?_, hstep.sig.trans ih.2.1, hstep.env.trans ih.2.2.1,
          hstep.envRules.2.trans ih.2.2.2⟩
        rw [hstep.eq_of_allConstructors (by rw [ih.2.1]; exact hctor)]
        exact hresult
  exact go.1


theorem RunState.mono_src {src src' : Database} {d : FDatabase} (h : RunState src d)
    (hc : src.Contained src') : RunState src' d :=
  ⟨h.inv, h.noUnions, h.shape, h.uf, h.sound.mono_src hc.eqs, h.history, h.descend⟩

/-- Readback of one compiled source firing preserves its historical invariants and is
sound in any source state containing that original firing's result. -/
theorem RunState.source_firing {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src ref : Database}
    (hpre : ProgramStep Database.empty pre src) {d d' : FDatabase} (h : RunState src d)
    (hsig : d.sig = encodeSig P) {r : Rule} (hr : r ∈ src.rules)
    (hupper : ∀ post ∈ RuleResults src r, post.Contained ref)
    {σ : Env} (hm : σ ∈ matchQuery d (encodeRule r).query)
    (hf : Fired d (encodeRule r) σ d') :
    SoundTerms d' ref ∧ EntryRowsUF d' ∧ UFTermsDescend d' := by
  have hmem : Cmd.rule r ∈ P := by
    rw [hP]
    apply List.mem_append_left
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr
  obtain ⟨τ, post, hτ, hp, hs, hh, hd⟩ := encodedRule_firing_of_programStep hdom hP hpre
    hmem hr h.inv h.noUnions h.sound hsig hm hf
  exact ⟨hs.mono_src (hupper post ⟨τ, hτ, hp⟩).eqs, hh h.shape h.history, hd h.descend⟩

/-- An aligned source round justifies every firing and merge in the compiled round. -/
theorem RunState.source_round {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) {d e : FDatabase} (h : RunState src d)
    (hsig : d.sig = encodeSig P) (hrules : RulesEncoded P src d)
    {R : RulesetName} (hstep : RunStep R src post) (run : d.runRoundM R = some e) :
    RunState post e := by
  apply (h.mono_src hstep.contained).round _ run
  intro r hr hR σ d' hm hf
  rcases (hrules r).mp hr with ⟨c, hc, hcr⟩ | ⟨s, hs, rfl⟩
  · obtain ⟨hs, hh, hd⟩ := h.maintenance_firing hc hcr hm hf
    exact ⟨hs.mono_src hstep.contained.eqs, hh, hd⟩
  · apply h.source_firing hdom hP hpre hsig hs _ hm hf
    intro out hl
    refine Database.Contained.trans ?_ (MergeClosure.contained hstep)
    -- The firing contributes directly to the rule phase of this source round.
    exact ⟨fun p hp => Or.inr (Set.mem_iUnion₂.mpr ⟨out, ⟨s, hs, hR, hl⟩, hp⟩)⟩

/-- A saturated source state justifies all rounds of its compiled saturation, including
source rules and the maintenance copies registered in that ruleset. -/
theorem RunState.source_saturate {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src : Database} (hpre : ProgramStep Database.empty pre src)
    {d e : FDatabase} (h : RunState src d) (hsig : d.sig = encodeSig P)
    (hrules : RulesEncoded P src d) {R : RulesetName} (hsat : RunSaturated R src)
    {n : Nat} (run : d.runSaturateM R n = some e) : RunState src e := by
  apply RunState.saturate (rules := d.rules) (sig := d.sig) _ n h rfl rfl run
  intro m hstate hmSig hmRules r hr hR σ e hσ hf
  rcases (hrules r).mp hr with ⟨c, hc, hcr⟩ | ⟨s, hs, rfl⟩
  · exact hstate.maintenance_firing hc hcr hσ hf
  · exact hstate.source_firing hdom hP hpre (hmSig.trans hsig) hs
      ((runRules_eq_self_iff R src).mp hsat.1 s hs hR) hσ hf

/-- Before the final dedicated rebuilding command, a successful compiled saturation
already represents all source facts at its source fixed point. -/
theorem saturation_simulation {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src start : Database}
    (hpre : ProgramStep Database.empty pre src) {R : RulesetName}
    (hreach : SaturateReach R start src) (henv : start.env = [])
    {d e : FDatabase} (h : RunState src d) (htables : RebuildTables P d)
    (hsig : d.sig = encodeSig P) (hrules : RulesEncoded P src d)
    (hreads : SourceReads d.toDatabase start) (hR : R ∈ P.saturateRulesets)
    {n : Nat} (run : d.runSaturateM R n = some e) :
    RunState src e ∧ Rebuilt e ∧ SourceReads e.toDatabase src := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left rest hc
  have he := h.source_saturate hdom hP hpre hsig hrules hreach.2 run
  have hfields := Egglog.FDatabase.runSaturateM_fields n run
  have hstore : RulesEncoded P src e := by
    intro r
    rw [hfields.2.2]
    exact hrules r
  have hclosed := Egglog.FDatabase.runSaturateM_roundClosed run
  have hrb : Rebuilt e := ⟨he.inv, he.noUnions, he.shape, he.uf, he.descend, he.history,
    Egglog.FDatabase.runSaturateM_mergeSettled run,
    hstore.rebuild_closed hdom hpre hsub hR hclosed⟩
  have ht : RebuildTables P e := ⟨fun f k hk => hfields.1 ▸ htables.view f k hk,
    fun f k hk => hfields.2.2 ▸ htables.output f k hk,
    fun f k hk i hi => hfields.2.2 ▸ htables.child f k hk i hi⟩
  have hsrcrules := runReach_rules hreach.1
  refine ⟨he, hrb, SourceReads.reach_of_closed hdom hsub hpre
    (RunReach.sig hreach.1).symm henv hrb ht he.sound (hfields.1.trans hsig)
    (hreads.mono (Egglog.FDatabase.runSaturateM_toDatabase_contained run)) ?_ hclosed hreach.1⟩
  intro r hr
  have hr' : r ∈ src.rules := hsrcrules ▸ hr
  have hmem : Cmd.rule r ∈ P := hsub _ (by
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr')
  exact ⟨hmem, (hstore _).mpr (Or.inr ⟨r, hr', rfl⟩)⟩

/-- One executable target round represents every result of the corresponding source
round, while retaining source justifications for all of its compiled entries. -/
theorem round_simulation {P pre rest : Program} (hdom : P.Fragment)
    (hP : P = pre ++ rest) {src post : Database}
    (hpre : ProgramStep Database.empty pre src) {R : RulesetName}
    (hstep : RunStep R src post) {d e : FDatabase} (h : Rebuilt d)
    (htables : RebuildTables P d) (hs : SoundTerms d src) (hsig : d.sig = encodeSig P)
    (hrules : RulesEncoded P src d) (hreads : SourceReads d.toDatabase src)
    (run : d.runRoundM R = some e) : RunState post e ∧ SourceReads e.toDatabase post := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left rest hc
  have hstate : RunState src d :=
    ⟨h.inv, h.noUnions, h.shape, h.uf, hs, h.history, h.descend⟩
  refine ⟨hstate.source_round hdom hP hpre hsig hrules hstep run, ?_⟩
  have hcs := (hpre.ctorState Database.CtorState.empty
    (fun c hc => hdom.ctorsOnly c (hsub c hc))).sig
  rw [hstep.eq_of_allConstructors hcs]
  apply (hreads.mono (Egglog.FDatabase.runRoundM_toDatabase_contained run)).runRules
  intro r hr hR out hp
  obtain ⟨σ, hm, hf⟩ := hp
  have hmem : Cmd.rule r ∈ P := hsub _ (by
    simpa [Database.empty] using (hpre.mem_rules_iff r).mp hr)
  obtain ⟨ρ, d', hmatch, hfire, hout⟩ := encodedRule_firing_reads_of_programStep
    hdom hsub hpre rfl hpre.env h htables hs hsig hreads hmem hm hf
  apply hout.mono
  apply Egglog.FDatabase.toDatabase_contained_of_lists
  · intro t ht
    apply Egglog.FDatabase.mergeSaturateF_terms run
    exact mem_terms_execRunRules.mpr (Or.inr
      ⟨encodeRule r, (hrules _).mpr (Or.inr ⟨r, hr, rfl⟩), hR, ρ, hmatch, d', hfire, ht⟩)
  · have hn := execLocalActions_noUnions (encodeActions_unionFree r.actions) h.noUnions hfire
    rw [hn.eqs]
    simp

end Egglog.Congruence
