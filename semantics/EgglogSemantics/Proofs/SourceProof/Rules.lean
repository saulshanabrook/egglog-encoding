import EgglogSemantics.Proofs.SourceProof.Matching
import EgglogSemantics.Proofs.SourceProof.Support
import EgglogSemantics.Proofs.SourceModel
import EgglogSemantics.Proofs.Source.Domain

namespace Egglog.SourceProof

/-- `sourceOk` is `Program.Fragment`, decided. -/
theorem sourceOk_fragment {P : Program} (h : sourceOk P = true) : P.Fragment :=
  of_decide_eq_true h

/-- The fragment computes with no `min`, so neither does any of its rules. -/
theorem sourceOk_rule {P : Program} (h : sourceOk P = true) {r : Rule}
    (hr : r ∈ P.rules) : r.OrderingFree := by
  obtain ⟨c, hc, hr⟩ := List.mem_flatMap.mp hr
  exact (sourceOk_fragment h).noMin.1 c hc r hr

/-- A checked head fact follows from a valid source rule firing, up to supported terms. -/
theorem ruleFacts_supported {P : Program} {db : Database}
    (hs : ProgramStep Database.empty P.commands db) (hw : db.WF)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules db) (hok : sourceOk P = true) {r : Rule}
    (hr : r ∈ P.rules) {σ : Env} {premises fs : List Claim}
    (hp : ∀ c ∈ premises, c.Supported db) (hf : ruleFacts r σ premises = some fs) :
    ∀ c ∈ fs, c.Supported db := by
  obtain ⟨cmd, hcmd, hr⟩ := List.mem_flatMap.mp hr
  have hdf : ∀ r ∈ cmd.rules, r.DeleteFree := Cmd.deleteFree_of_monotone
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (sourceOk_fragment hok).monotone).1 cmd hcmd)
  have hmodel : RunRules cmd.rules db.completion = db.completion :=
    SourceMeaning.completion_closed_of_saturated hw hdf
      ((sourceOk_fragment hok).noMin.1 cmd hcmd) (hclosed cmd hcmd)
  unfold ruleFacts at hf
  split at hf
  · rename_i hchecks
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq, List.all_eq_true] at hchecks
    have hh : ∀ c ∈ premises, c.Holds db.completion :=
      fun c hc => (hp c hc).completion hw
    have hval : ∀ b ∈ σ, b.2 ∈ db.completion.terms := fun b hb =>
      supportedValue_sound hw.completion hh (hchecks.1.2 b hb)
    obtain ⟨τ, hτ, hag⟩ := querySubst_of_matches hchecks.1.1 hval
      (premisesMatch_sound hh hchecks.2)
    obtain ⟨d, hd, hfacts⟩ := actionsFacts_sound (db := db.completion) hf
    have hresult : d ∈ RuleResults db.completion r :=
      ⟨τ, hτ, by rw [evalActions_agree hag]; exact hd⟩
    have hpost : d.Contained db.completion :=
      (runRules_eq_self_iff cmd.rules db.completion hdf).mp hmodel r hr d hresult
    exact fun c hc => Claim.Supported.of_completion hw ((hfacts c hc).mono hpost)
  · contradiction

end Egglog.SourceProof
