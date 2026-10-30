import EgglogSemantics.Proofs.Congruence.AbstractComplete
import EgglogSemantics.Proofs.Congruence.LiveRebuildTermination

/-! Finite compiled blocks for source commands with bounded rounds. -/

namespace Egglog.Congruence.Abstract

private theorem empty_normal {d : Database} (he : d.eqs = ∅) : MergeNormal d := by
  intro row hr
  exact (he ▸ hr.2).elim

/-- Declarations and rule registrations cannot introduce merge collisions into empty data. -/
theorem prelude_exists (P : Program) :
    ∃ d, ProgramStep Database.empty ((encodePrelude P).map Command.command) d := by
  have go : ∀ (p : Program), (∀ c ∈ p, c.DeclOrRule) → ∀ d, d.eqs = ∅ →
      ∃ e, ProgramStep d p e := by
    intro p
    induction p with
    | nil => exact fun _ d _ => ⟨d, .nil⟩
    | cons c cs ih =>
        intro hall d hd
        have hc := hall c List.mem_cons_self
        have hs := fun c hc => hall c (List.mem_cons_of_mem _ hc)
        cases c with
        | decl f dc =>
            obtain ⟨e, he⟩ := ih hs {d with sig := Function.update d.sig f (some dc)} hd
            exact ⟨e, .cons (CmdStep.of_reach rfl (empty_normal hd)) he⟩
        | rule r =>
            obtain ⟨e, he⟩ := ih hs {d with rules := insert r d.rules} hd
            exact ⟨e, .cons (CmdStep.of_reach rfl (empty_normal hd)) he⟩
        | _ => contradiction
  exact go _ (prelude_setup P) Database.empty rfl

/-- Every finite generated store admits one rule round and a completed rebuild. -/
theorem Boundary.run_exists {P pre rest : Program} (hp : P.Fragment) {R : RulesetName}
    (hP : P = pre ++ Cmd.run R :: rest) {src post d : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (_h : Boundary src d) (_hsrc : CmdStep src (.run R) post) :
    ∃ e, ProgramStep d ((encodeCmd pre.length (.run R)).map Command.command) e := by
  have hsub : ∀ c ∈ pre, c ∈ P := fun c hc => hP ▸ List.mem_append_left _ hc
  have hrt := Live.prefix_runtime hp hsub htpre
  have hsig := Live.prefix_sig htpre
  have honly := (Live.rulesEncoded_of_prefix hpre htpre).rebuild_only hp hpre hsub
  obtain ⟨mid, hm⟩ := hrt.state.runStep_exists hrt.generated hrt.storeOk hrt.rulesSafe hrt.noUnions R
  obtain ⟨e, he⟩ := Live.rebuild_exists hp (hrt.runStep hm) hm.normal (hm.sig.trans hsig)
    (fun r hr hR => honly r (hm.1.envRules.2 ▸ hr) hR)
  exact ⟨e, .cons hm (.cons (cmdStep_saturate_iff.mpr he) .nil)⟩

/-- Ordinary source commands have finite compiled blocks at corresponding prefixes. -/
theorem Boundary.nonSaturate_exists {P pre rest : Program} (hp : P.Fragment) {c : Cmd}
    (hP : P = pre ++ c :: rest) {src post d : Database}
    (hpre : ProgramStep Database.empty pre src)
    (htpre : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d)
    (h : Boundary src d) (hsrc : CmdStep src c post) (hn : c.NoSaturate) :
    ∃ e, ProgramStep d ((encodeCmd pre.length c).map Command.command) e := by
  cases c with
  | run R => exact h.run_exists hp hP hpre htpre hsrc
  | decl f dc => exact ⟨d, .nil⟩
  | rule r =>
      have hd := Congruence.prefix_mergeNormal htpre
      exact ⟨_, .cons (CmdStep.of_reach rfl (hd.setRules _)) .nil⟩
  | check q =>
      exact ⟨d, .cons ⟨(checkAgreement hp pre q rest src d hP hpre htpre).mp hsrc.1, rfl⟩
        .nil⟩
  | saturate R => exact hn.elim

/-- A local existence obligation for successful source commands. Failed checks are
handled separately, without requiring a run of their unreachable suffix. -/
def CommandsTerminate (P : Program) : Prop :=
  ∀ pre rest c src post d, P = pre ++ c :: rest →
    ProgramStep Database.empty pre src →
    ProgramStep Database.empty ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d →
    CmdStep src c post →
    ∃ e, ProgramStep d ((encodeCmd pre.length c).map Command.command) e

private theorem eval_exists_from_prefix {P : Program} (hp : P.Fragment)
    (hcmd : CommandsTerminate P) :
    ∀ rest pre src d source,
      P = pre ++ rest → ProgramStep Database.empty pre src →
      ProgramStep Database.empty
        ((encodePrelude P ++ encodeCmds pre 0).map Command.command) d →
      Eval src rest source →
      ∃ target, Eval d ((encodeCmds rest pre.length).map Command.command) target := by
  intro rest
  induction rest with
  | nil =>
      intro pre src d source _ _ _ _
      exact ⟨.ok d, .nil⟩
  | cons c cs ih =>
      intro pre src d source hP hpre htpre hs
      cases hs with
      | cons hc hs =>
          have hsc := CmdEval.ok_iff.mp hc
          obtain ⟨e, he⟩ := hcmd pre cs c src _ d hP hpre htpre hsc
          obtain ⟨target, ht⟩ := ih (pre ++ [c]) _ e source
            (by simpa only [List.append_assoc, List.singleton_append] using hP)
            (hpre.append (.cons hsc .nil)) (compiled_prefix_step htpre he) hs
          refine ⟨target, ?_⟩
          simpa only [encodeCmds, List.map_append, List.length_append, List.length_singleton]
            using Eval.append_of_ok he ht
      | fail hc =>
          cases hc with
          | checkFailed hq =>
              rename_i q
              have hqt : ¬ QueryHolds d (encodeQuery q 0).1 := by
                intro ht
                exact hq ((checkAgreement hp pre _ cs src d hP hpre htpre).mpr ht)
              exact ⟨.checkFailed, .fail (.checkFailed hqt)⟩

/-- Command existence and the established query correspondence compose to finite
evaluation existence, including failed checks and their unexecuted suffixes. -/
theorem termination_of_commands {P : Program} (hp : P.Fragment)
    (hc : CommandsTerminate P) {source : Result} (hs : Eval Database.empty P source) :
    ∃ target, Eval Database.empty (encode P) target := by
  obtain ⟨d, hd⟩ := prelude_exists P
  obtain ⟨target, ht⟩ := eval_exists_from_prefix hp hc P [] Database.empty d source
    (by simp) .nil (by simpa [encodeCmds] using hd) hs
  refine ⟨target, ?_⟩
  simpa only [encode, compile, List.map_append, List.length_nil] using Eval.append_of_ok hd ht

end Egglog.Congruence.Abstract
