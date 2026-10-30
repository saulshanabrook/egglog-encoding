import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Spec.Behavior
import Architect

/-! The paper's compiler-correctness obligation. Both evaluations use mathematical
`Database` states. No executable interpreter or fuel bound occurs in the statement.
The paper's source programs use bounded rounds; only compiled rebuilding uses saturation.
The proof for the constructor-and-delete encoding is pending; the executable gates in
`DiffTest.lean` check the statement on the corpus. -/

namespace Egglog.Congruence

/-- Compilation preserves success, failed checks, and divergence. Neither side's
termination is a premise; source schedules use bounded rounds. -/
def PreservesBehaviors : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → P.NoSaturate → ∀ behavior : Behavior,
    Behaves Database.empty (encode P) behavior ↔ Behaves Database.empty P behavior

/-- For a well-formed supported source program, every pair of finite evaluations agrees
on success versus check failure. This does not assert either evaluation exists. -/
def PreservesObservations : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ source target : Result,
    Eval Database.empty P source → Eval Database.empty (encode P) target →
      source.succeeded = target.succeeded

/-- The paper's statement: the outcomes agree, and neither program diverges. -/
@[blueprint "thm:congruence"
  (title := /-- Congruence pass correctness -/)
  (statement := /-- Let $P$ be a well-formed program in the source fragment without
  $\kw{saturate}$. Then, for every outcome $o$,
  \[
    \langle\operatorname{encode}(P),\varnothing\rangle\Downarrow o
      \iff\langle P,\varnothing\rangle\Downarrow o,
  \]
  and neither $P$ nor $\operatorname{encode}(P)$ has a nonterminating execution: no
  saturation repeats forever. -/)
  (hasProof := false) (latexEnv := "theorem")]
def Correctness : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → P.NoSaturate →
    (∀ o : Result, Eval Database.empty (encode P) o ↔ Eval Database.empty P o) ∧
    ¬ ProgramDiverges Database.empty P.commands ∧
    ¬ ProgramDiverges Database.empty (encode P).commands

/-- Bounded source schedules have finite compiled evaluations. Generated rebuilding
may saturate; this asserts existence, not termination of every schedule. -/
def PreservesTermination : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → P.NoSaturate → ∀ source : Result,
    Eval Database.empty P source → ∃ target, Eval Database.empty (encode P) target

end Egglog.Congruence
