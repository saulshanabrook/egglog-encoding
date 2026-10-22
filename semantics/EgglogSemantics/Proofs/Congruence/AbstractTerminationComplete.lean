import EgglogSemantics.Proofs.Congruence.AbstractTerminationCommands
import EgglogSemantics.Proofs.Congruence.LiveRebuildStrongTermination
import EgglogSemantics.Proofs.Source.Termination

/-! Termination and observation preservation for bounded source schedules. -/

namespace Egglog.Congruence.Abstract

/-- Source commands are bounded; generated rebuilding has its own termination proof. -/
theorem commandsTerminate {P : Program} (hp : P.Fragment) (hn : P.NoSaturate) :
    CommandsTerminate P := by
  intro pre rest c src post d hP hpre htpre hsrc
  have h := boundary_prefix hp hP hpre htpre
  exact h.nonSaturate_exists hp hP hpre htpre hsrc
    (hn c (hP ▸ List.mem_append_right _ List.mem_cons_self))

end Egglog.Congruence.Abstract

namespace Egglog.Congruence

/-- Finite source executions compile to finite executions, including failed checks. -/
theorem preservesTermination : PreservesTermination := by
  intro P _hw hp hn source hs
  exact Abstract.termination_of_commands hp (Abstract.commandsTerminate hp hn) hs

/-- Target termination and the same success/failure observation are conclusions. -/
theorem preservesFiniteObservations (P : Program) (hw : P.WellFormed) (hp : P.Fragment)
    (hn : P.NoSaturate) (source : Result) (hs : Eval Database.empty P source) :
    ∃ target, Eval Database.empty (encode P) target ∧
      source.succeeded = target.succeeded := by
  obtain ⟨target, ht⟩ := preservesTermination P hw hp hn source hs
  exact ⟨target, ht, preservesObservations P hw hp source target hs ht⟩

/-- Both sides have finite evaluations; every pair agrees by `preservesObservations`. -/
theorem evaluations_exist (P : Program) (hw : P.WellFormed) (hp : P.Fragment)
    (hn : P.NoSaturate) :
    ∃ source target, Eval Database.empty P source ∧
      Eval Database.empty (encode P) target ∧ source.succeeded = target.succeeded := by
  obtain ⟨source, hs⟩ := hw.eval_exists hn hp.ctorsOnly
  obtain ⟨target, ht, he⟩ := preservesFiniteObservations P hw hp hn source hs
  exact ⟨source, target, hs, ht, he⟩

/-- Compilation preserves exactly the possible success/failure observations. -/
theorem observations_iff (P : Program) (hw : P.WellFormed) (hp : P.Fragment)
    (hn : P.NoSaturate) (b : Bool) :
    (∃ target, Eval Database.empty (encode P) target ∧ target.succeeded = b) ↔
      ∃ source, Eval Database.empty P source ∧ source.succeeded = b := by
  constructor
  · rintro ⟨target, ht, hb⟩
    obtain ⟨source, hs⟩ := hw.eval_exists hn hp.ctorsOnly
    exact ⟨source, hs, (preservesObservations P hw hp source target hs ht).trans hb⟩
  · rintro ⟨source, hs, hb⟩
    obtain ⟨target, ht, he⟩ := preservesFiniteObservations P hw hp hn source hs
    exact ⟨target, ht, he.symm.trans hb⟩

end Egglog.Congruence
