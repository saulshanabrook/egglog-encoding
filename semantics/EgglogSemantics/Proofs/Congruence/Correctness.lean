import EgglogSemantics.Proofs.Congruence.AbstractTerminationComplete
import EgglogSemantics.Proofs.Congruence.LiveProgramTermination
import EgglogSemantics.Proofs.Behavior

/-! Top-level congruence compiler correctness: success, check failure, and divergence.
`correctness` is the form the paper states. -/

namespace Egglog.Congruence

/-- All success, failure, and divergence behaviors agree, without evaluation premises. -/
theorem preservesBehaviors : PreservesBehaviors := by
  intro P hw hp hn behavior
  cases behavior with
  | success =>
      rw [behaves_success_iff, behaves_success_iff]
      exact observations_iff P hw hp hn true
  | checkFailed =>
      rw [behaves_failure_iff, behaves_failure_iff]
      exact observations_iff P hw hp hn false
  | diverges =>
      exact ⟨fun h => (not_encode_diverges hp hn h).elim,
        fun h => (not_programDiverges_of_allConstructors
          Database.CtorState.empty.sig hp.ctorsOnly hn h).elim⟩

/-- Bounded source schedules and every compiled merge/rebuild schedule are nondivergent. -/
theorem neither_diverges {P : Program} (hp : P.Fragment) (hn : P.NoSaturate) :
    ¬ ProgramDiverges Database.empty P ∧ ¬ ProgramDiverges Database.empty (encode P) :=
  ⟨not_programDiverges_of_allConstructors Database.CtorState.empty.sig hp.ctorsOnly hn,
    not_encode_diverges hp hn⟩

/-- The paper's statement of `preservesBehaviors`: the finite outcomes agree, and neither
program diverges, so the divergence case needs no rules of its own. -/
@[blueprint "thm:congruence"
  (title := /-- Congruence compiler correctness -/)
  (statement := /-- Let $P$ be a well-formed program in the constructor source fragment
  without $\kw{saturate}$. Then
  \[\begin{gathered}
    (\exists D.\ \langle\operatorname{encode}(P),\varnothing\rangle\Downarrow D)
      \iff(\exists D.\ \langle P,\varnothing\rangle\Downarrow D)\\
    \langle\operatorname{encode}(P),\varnothing\rangle\Downarrow\kw{error}
      \iff\langle P,\varnothing\rangle\Downarrow\kw{error}
  \end{gathered}\]
  and neither $P$ nor $\operatorname{encode}(P)$ has a nonterminating execution: no run
  has an infinite sequence of merge steps, and no saturation repeats forever. -/)
  (hasProof := false) (latexEnv := "theorem")]
theorem correctness {P : Program} (hw : P.WellFormed) (hp : P.Fragment) (hn : P.NoSaturate) :
    ((∃ d, Eval Database.empty (encode P) (.ok d)) ↔ ∃ d, Eval Database.empty P (.ok d)) ∧
    (Eval Database.empty (encode P) .checkFailed ↔ Eval Database.empty P .checkFailed) ∧
    ¬ ProgramDiverges Database.empty P ∧ ¬ ProgramDiverges Database.empty (encode P) :=
  ⟨preservesBehaviors P hw hp hn .success, preservesBehaviors P hw hp hn .checkFailed,
    neither_diverges hp hn⟩

end Egglog.Congruence
