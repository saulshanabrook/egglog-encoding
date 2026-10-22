import EgglogSemantics.Proofs.Congruence.LiveRebuildStrongTermination
import EgglogSemantics.Proofs.Congruence.AbstractBoundary
import EgglogSemantics.Proofs.Divergence

/-! Every schedule of a compiled bounded source program avoids divergence. -/

namespace Egglog.Congruence.Live

theorem State.not_mergeDiverges {d : Database} (h : State d) (hd : d.Diag) : ¬ MergeDiverges d :=
  not_infiniteTrace_of_wellFounded (merge_wellFounded h hd)

theorem not_rebuildDiverges {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hn : MergeNormal d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) :
    ¬ SaturateDiverges rebuildRuleset d := by
  rintro (ht | ⟨mid, hr, hm⟩)
  · obtain ⟨trace, hstart, hstep⟩ := ht
    obtain ⟨n, hn⟩ := rebuild_trace_stops hp h hn hsig honly trace hstart
      (fun n => (hstep n).1)
    exact (hstep n).2 ((hstep n).1.sameMeaning_iff.mp hn)
  · have hreach := changingRunReach_runReach hr
    exact ((h.runReach hreach).runRules rebuildRuleset).state.not_mergeDiverges
      ((h.runReach hreach).runRules rebuildRuleset).noUnions.diag hm

private theorem noDecl_sigBind {c : Cmd} (hc : NoDecl c) (sig : Signature) :
    c.sigBind sig = sig := by
  cases c <;> first | rfl | contradiction

theorem not_cmdDiverges {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hn : MergeNormal d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    {c : Cmd} (hnd : NoDecl c) (hu : c.UnionFree)
    (hsat : ∀ R, c = .saturate R → R = rebuildRuleset) : ¬ CmdDiverges d c := by
  intro hd
  cases hd with
  | saturate hd =>
      have he := hsat _ rfl
      subst he
      exact not_rebuildDiverges hp h hn hsig honly hd
  | run hm => exact (h.runRules _).state.not_mergeDiverges (h.runRules _).noUnions.diag hm

theorem not_programDiverges {P : Program} (hp : P.Fragment) {p : Program}
    (hnd : ∀ c ∈ p, NoDecl c) (hu : p.UnionFree) (hqs : p.QueriesSafe)
    (hsat : ∀ R, Cmd.saturate R ∈ p → R = rebuildRuleset)
    (hrules : ∀ r, Cmd.rule r ∈ p → r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    {d : Database} (h : Runtime d) (hn : MergeNormal d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) :
    ¬ ProgramDiverges d p := by
  induction p generalizing d with
  | nil => intro hd; cases hd
  | cons c cs ih =>
      intro hd
      cases hd with
      | head hc =>
          exact not_cmdDiverges hp h hn hsig honly (hnd _ List.mem_cons_self) hu.1
            (fun R he => hsat R (he ▸ List.mem_cons_self)) hc
      | tail hc hd =>
          apply ih (fun c hm => hnd c (List.mem_cons_of_mem _ hm)) hu.2 hqs.2
            (fun R hm => hsat R (List.mem_cons_of_mem _ hm))
            (fun r hm => hrules r (List.mem_cons_of_mem _ hm))
            (h.cmd (hnd _ List.mem_cons_self) hu.1 hqs.1 hc)
            (hc.mergeNormal hn (hnd _ List.mem_cons_self))
            ((hc.sig.trans (noDecl_sigBind (hnd _ List.mem_cons_self) _)).trans hsig) ?_ hd
          intro r hr hR
          rcases (hc.mem_rules_iff r).mp hr with hr | hr
          · exact honly r hr hR
          · exact hrules r (hr ▸ List.mem_cons_self) hR

private theorem cmds_onlySaturate {p : Program} (hn : p.NoSaturate) (i : Nat) :
    ∀ R, Cmd.saturate R ∈ (encodeCmds p i).map Command.command → R = rebuildRuleset := by
  induction p generalizing i with
  | nil => simp [encodeCmds]
  | cons c cs ih =>
      intro R hR
      rw [encodeCmds, List.map_append, List.mem_append] at hR
      rcases hR with hR | hR
      · have hc := hn c List.mem_cons_self
        cases c <;> simp_all [encodeCmd, taggedRule, Function.comp_def, Cmd.NoSaturate]
      · exact ih (fun c hm => hn c (List.mem_cons_of_mem _ hm)) (i + 1) R hR

private theorem unionFree_append_right {p q : Program} (h : (p ++ q).UnionFree) :
    q.UnionFree := by
  induction p with
  | nil => exact h
  | cons _ _ ih => exact ih h.2

theorem encoded_commands_not_diverge {P : Program} (hp : P.Fragment) (hn : P.NoSaturate)
    {d : Database} (hpre : ProgramStep Database.empty
      ((encodePrelude P).map Command.command) d) :
    ¬ ProgramDiverges d ((encodeCmds P 0).map Command.command) := by
  have hempty := (prelude_empty hpre).1
  have hnormal : MergeNormal d := by
    intro row hr
    exact (hempty ▸ hr.2).elim
  apply not_programDiverges hp (cmds_noDecl P 0) ?_
    (Program.queriesSafe_of_rules _ (encodeCmds_querySafe hp.noMin 0))
    (cmds_onlySaturate hn 0) ?_
    (prelude_runtime hp hpre) hnormal hpre.sig ?_
  · apply unionFree_append_right (p := (encodePrelude P).map Command.command)
    simpa only [List.map_append] using encodePrefix_unionFree P P 0
  · intro r hr hR
    obtain ⟨s, hs, rfl⟩ := (rule_mem_encodeCmds P 0 r).mp hr
    exact (ruleset_ne_rebuild hp hs hR).elim
  · intro r hr _
    apply (rule_mem_prelude P r).mp
    simpa only [Database.empty, Set.mem_empty_iff_false, false_or] using
      (hpre.mem_rules_iff r).mp hr

private theorem not_mergeDiverges_empty {d : Database} (he : d.eqs = ∅) :
    ¬ MergeDiverges d := by
  rintro ⟨trace, hstart, hs⟩
  exact (hs 0).not_of_empty_eqs (hstart ▸ he)

private theorem setup_not_diverge {p : Program} (hp : ∀ c ∈ p, c.DeclOrRule)
    {d : Database} (he : d.eqs = ∅) : ¬ ProgramDiverges d p := by
  induction p generalizing d with
  | nil => intro hd; cases hd
  | cons c cs ih =>
      intro hd
      cases hd with
      | head hd =>
          have hc := hp c List.mem_cons_self
          cases hd with
          | saturate => contradiction
          | run => contradiction
      | tail hs hd =>
          exact ih (fun c hm => hp c (List.mem_cons_of_mem _ hm))
            (hs.eqs_empty_of_declOrRule (hp _ List.mem_cons_self) he) hd

/-- Generated saturation and destructive merging cannot diverge on any target schedule. -/
theorem encode_not_diverge {P : Program} (hp : P.Fragment) (hn : P.NoSaturate) :
    ¬ ProgramDiverges Database.empty (encode P) := by
  rw [encode, compile, List.map_append, ProgramDiverges.append_iff]
  rintro (hd | ⟨d, hpre, hd⟩)
  · exact setup_not_diverge (prelude_setup P) rfl hd
  · exact encoded_commands_not_diverge hp hn hpre hd

end Egglog.Congruence.Live

namespace Egglog.Congruence

theorem not_encode_diverges {P : Program} (hp : P.Fragment) (hn : P.NoSaturate) :
    ¬ ProgramDiverges Database.empty (encode P) := Live.encode_not_diverge hp hn

end Egglog.Congruence
