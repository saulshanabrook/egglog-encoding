import EgglogSemantics.Proofs.Congruence.AbstractRunState
import EgglogSemantics.Proofs.Congruence.AbstractWrites
import EgglogSemantics.Proofs.RuleStore
import EgglogSemantics.Proofs.Congruence.AbstractBuild
import EgglogSemantics.Proofs.Congruence.AbstractWidths
import EgglogSemantics.Proofs.Congruence.HeadMatch

/-! Compiled global writes remain sound when each command performs arbitrary merges. -/

namespace Egglog.Congruence.Abstract

/-- A legal union-free action preserves the structural target invariants. -/
theorem Runtime.action {d e : Database} {a : Action} (h : Runtime d)
    (hu : a.UnionFree) (hw : a.WidthOk d.sig) (he : evalAction d a = some e) :
    Runtime e where
  wf := evalAction_wf h.wf he
  noUnions := ⟨evalAction_diag hu h.noUnions.diag he,
    by rw [evalAction_sig he]; exact h.noUnions.sig,
    by rw [evalAction_rules he]; exact h.noUnions.rules⟩
  declared := evalAction_declaredTerms h.wf h.declared hw he
  rulesOk := by
    intro r hr
    rw [evalAction_sig he]
    exact h.rulesOk r (evalAction_rules he ▸ hr)
  shape := by rw [evalAction_sig he]; exact h.shape
  uf := by rw [evalAction_sig he]; exact h.uf

/-- Compiled writes retain their source justification across every command-level merge.
Their evaluations only read the unchanged signature and surrounding environment. -/
theorem sourceWrites_program_preserves {src d e : Database} {as : List Action}
    (hw : src.WF) (hsafe : SourceSafe src) (h : Runtime d)
    (hs : SoundTerms d src) (hd : Descending d)
    (hwrites : SourceWrites src d.sig d.env as) (hwidth : Actions.WidthOk as d.sig)
    (hr : ProgramStep d (as.map Cmd.action) e) :
    Runtime e ∧ SoundTerms e src ∧ Descending e := by
  induction as generalizing d with
  | nil => obtain rfl := hr.nil_inv; exact ⟨h, hs, hd⟩
  | cons a as ih =>
      obtain ⟨ea, t, rfl, hev, ht⟩ := hwrites a List.mem_cons_self
      obtain ⟨mid, hcmd, hrest⟩ := hr.cons_inv
      obtain ⟨raw, hraw, hm⟩ := hcmd
      have heval : evalAction d (.expr ea) = some (d.addTerm t) := by
        simp [evalAction, hev]
      obtain rfl : raw = d.addTerm t := Option.some.inj (hraw.symm.trans heval)
      have hrawstate := h.action (by trivial) hwidth.1 heval
      obtain ⟨hsraw, hdraw⟩ := sourceAtom_preserves hw hsafe hs hd ht
      have hmid := hrawstate.merge hm
      have hsmid := mergeClosure_soundTerms hrawstate.shape hrawstate.noUnions.diag
        hrawstate.wf hrawstate.declared hrawstate.uf hsraw hm
      have hdmid := mergeClosure_descending hrawstate.shape hrawstate.noUnions.diag
        hrawstate.wf hrawstate.declared hrawstate.uf hdraw hm
      have hsig : mid.sig = d.sig := hm.sig
      have henv : mid.env = d.env := hm.envRules.1
      apply ih hmid hsmid hdmid _ _ hrest
      · rw [hsig, henv]
        exact fun a ha => hwrites a (List.mem_cons_of_mem _ ha)
      · rw [hsig]
        exact hwidth.2

/-- The emitted commands for a successful source action, including their interleaved
merge phases, preserve soundness and descending links. -/
theorem encodeAction_program_preserves {src post d e : Database} {a : Action}
    (hw : src.WF) (hsafe : SourceSafe post) (hcs : src.sig.AllConstructors)
    (h : Runtime d) (hs : SoundTerms d src) (hdesc : Descending d)
    (hp : ∀ x ∈ actionExprs a, x.OrderingFree)
    (hviews : ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      (d.sig (viewName fk.1)).isSome = true)
    (heval : ∀ x ∈ actionExprs a, ∀ t,
      x.eval src.sig src.env = some t → x.eval d.sig d.env = some t)
    (hwidth : Actions.WidthOk (encodeAction a) d.sig)
    (hsrc : evalAction src a = some post)
    (htgt : ProgramStep d ((encodeAction a).map Cmd.action) e) :
    Runtime e ∧ SoundTerms e post ∧ Descending e :=
  sourceWrites_program_preserves (evalAction_wf hw hsrc) hsafe h
    (hs.mono_src (evalAction_contained hsrc).eqs) hdesc
    (encodeAction_sourceWrites (evalAction_wf hw hsrc) hcs hp hviews
      (by rw [h.uf]; rfl) heval hsrc) hwidth htgt

private theorem programStep_append_inv {p q : Program} {d e : Database}
    (hr : ProgramStep d (p ++ q) e) : ∃ mid, ProgramStep d p mid ∧ ProgramStep mid q e := by
  induction p generalizing d with
  | nil => exact ⟨d, .nil, hr⟩
  | cons c cs ih =>
      obtain ⟨mid, hc, hrest⟩ := hr.cons_inv
      obtain ⟨post, hp, hq⟩ := ih hrest
      exact ⟨post, .cons hc hp, hq⟩

/-- A complete compiled global-action block also performs its trailing dedicated rebuild. -/
theorem encodeAction_command_preserves {P : Program} {src post d e : Database}
    {a : Action} {i : Nat} (hw : src.WF) (hsafe : SourceSafe post)
    (hcs : src.sig.AllConstructors) (h : Runtime d)
    (hs : SoundTerms d src) (hdesc : Descending d)
    (hp : ∀ x ∈ actionExprs a, x.OrderingFree)
    (hviews : ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      (d.sig (viewName fk.1)).isSome = true)
    (heval : ∀ x ∈ actionExprs a, ∀ t,
      x.eval src.sig src.env = some t → x.eval d.sig d.env = some t)
    (hwidth : Actions.WidthOk (encodeAction a) d.sig)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (hsrc : evalAction src a = some post)
    (htgt : ProgramStep d ((encodeCmd i (.action a)).map Command.command) e) :
    Runtime e ∧ SoundTerms e post ∧ Descending e := by
  have hprog : ProgramStep d
      ((encodeAction a).map Cmd.action ++ [.saturate rebuildRuleset]) e := by
    simpa only [encodeCmd, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def] using htgt
  obtain ⟨mid, hacts, hrest⟩ := programStep_append_inv hprog
  obtain ⟨e', hrebuild, hnil⟩ := hrest.cons_inv
  obtain rfl := hnil.nil_inv
  obtain ⟨hm, hsound, hdown⟩ := encodeAction_program_preserves hw hsafe hcs h hs hdesc hp
    hviews heval hwidth hsrc hacts
  have hrules : mid.rules = d.rules := by
    apply Set.ext
    intro r
    rw [hacts.mem_rules_iff r]
    constructor
    · rintro (hr | hr)
      · exact hr
      · obtain ⟨a', _, ha'⟩ := List.mem_map.mp hr
        cases ha'
    · exact Or.inl
  exact ⟨hm.runReach (cmdStep_saturate_iff.mp hrebuild).1,
    rebuild_cmd_preserves hm hsound hdown
      (fun r hr hR => honly r (hrules ▸ hr) hR) hrebuild⟩

/-- At an actual source prefix, the supported fragment supplies every premise of global
simulation. The complete compiled block retains source readings and ends rebuilt. -/
theorem encodeAction_command_preserves_of_programStep {P pre : Program}
    (hp : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    {src post : Database} (hpre : ProgramStep Database.empty pre src)
    {a : Action} (ha : Cmd.action a ∈ P) (hsrc : CmdStep src (.action a) post)
    {d e : Database} (h : Runtime d) (hm : Metadata P src d)
    (hsound : SoundTerms d src) (hdesc : Descending d) (hreads : SourceReads d src)
    {i : Nat} (htgt : ProgramStep d ((encodeCmd i (.action a)).map Command.command) e) :
    Runtime e ∧ SoundTerms e post ∧ Descending e ∧ SourceReads e post ∧
      RunSaturated rebuildRuleset e := by
  have hcs := hpre.ctorState Database.CtorState.empty
    (fun c hc => hp.ctorsOnly c (hsub c hc))
  have hnext : ProgramStep Database.empty (pre ++ [.action a]) post :=
    hpre.append (.cons hsrc .nil)
  have hsub' : ∀ c ∈ pre ++ [Cmd.action a], c ∈ P := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hsub c hc
    · exact List.mem_singleton.mp hc ▸ ha
  have hctor := sourceConstructors_of_programStep hp hsub hpre hm.sig
  have hhead : ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors, fk ∈ P.ctors := by
    intro x hx fk hk
    exact mem_program_ctors ha (actionExprs_ctors hx hk)
  have hviews : ∀ x ∈ actionExprs a, ∀ fk ∈ x.ctors,
      (d.sig (viewName fk.1)).isSome = true := by
    intro x hx fk hk
    rw [hm.sig, (encodeSig_tables hp (hhead x hx fk hk)).2]
    rfl
  have hsenv : src.env = [] := hpre.env
  have hact : evalAction src a = some post := by
    obtain ⟨mid, hmid, hmerge⟩ := hsrc
    have hmid' : evalAction src a = some mid := hmid
    have heq : post = mid := hmerge.eq_of_allConstructors (by
      rw [evalAction_sig hmid']; exact hcs.sig)
    exact heq.symm ▸ hmid'
  have hof := Action.orderingFree_exprs (Program.OrderingFree.of_mem hp.noMin ha)
  have heval : ∀ x ∈ actionExprs a, ∀ t,
      x.eval src.sig src.env = some t → x.eval d.sig d.env = some t := by
    intro x _ t ht
    exact eval_transport x (fun f _ => hctor f)
      (fun v _ => by rw [hsenv, hm.env]) ht
  have hwidth : Actions.WidthOk (encodeAction a) d.sig := by
    rw [hm.sig]
    exact encodeAction_width hp a (fun fk hk => mem_program_ctors ha hk)
  obtain ⟨he, hs, hd⟩ := encodeAction_command_preserves hcs.wf
    (sourceSafe_of_programStep hp hsub' hnext) hcs.sig h hsound hdesc hof hviews heval hwidth
    (hm.rules.rebuild_only hp hpre hsub) hact htgt
  have hprog : ProgramStep d
      ((encodeAction a).map Cmd.action ++ [.saturate rebuildRuleset]) e := by
    simpa only [encodeCmd, List.map_append, List.map_map, List.map_cons, List.map_nil,
      Function.comp_def] using htgt
  obtain ⟨mid, hacts, hrest⟩ := programStep_append_inv hprog
  obtain ⟨e', hrebuild, hnil⟩ := hrest.cons_inv
  obtain rfl := hnil.nil_inv
  have hρ : Env.Reads d src.env d.env := by
    intro v t hv
    simp [hsenv] at hv
  have hmidreads := encodeAction_program_reads hcs.sig hof
    (fun _ _ f _ => hctor f) hviews (by rw [hm.uf hp]; rfl) hρ hreads hact hacts
  exact ⟨he, hs, hd, hmidreads.mono (CmdStep.contained hrebuild),
    (cmdStep_saturate_iff.mp hrebuild).2⟩

end Egglog.Congruence.Abstract
