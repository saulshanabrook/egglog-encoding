import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Spec.Behavior
import Architect

/-! The paper's compiler-correctness obligation. Both evaluations use mathematical
`Database` states. No executable interpreter or fuel bound occurs in the statement.
The proof for the view-free union-find encoding is pending; the executable gates in
`DiffTest.lean` check the statement on the corpus. -/

namespace Egglog.Congruence

/-- Compilation preserves success, failed checks, and divergence. Neither side's
termination is a premise. -/
def PreservesBehaviors : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ behavior : Behavior,
    Behaves Database.empty (encode P) behavior ↔ Behaves Database.empty P behavior

/-- For a well-formed supported source program, every pair of finite evaluations agrees
on success versus check failure. This does not assert either evaluation exists. -/
def PreservesObservations : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ source target : Result,
    Eval Database.empty P source → Eval Database.empty (encode P) target →
      source.succeeded = target.succeeded

/-- The paper's statement: the outcomes agree, and so does divergence. -/
@[blueprint "thm:congruence"
  (title := /-- Congruence pass correctness -/)
  (statement := /-- Let $P$ be a well-formed program in the source fragment. Then, for
  every outcome $o$,
  \[
    \langle\operatorname{encode}(P),\varnothing\rangle\Downarrow o
      \iff\langle P,\varnothing\rangle\Downarrow o,
  \]
  and $\operatorname{encode}(P)$ has a nonterminating execution, a saturation that
  repeats forever, if and only if $P$ has one. -/)
  (hasProof := false) (latexEnv := "theorem")]
def Correctness : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment →
    (∀ o : Result, Eval Database.empty (encode P) o ↔ Eval Database.empty P o) ∧
    (Diverges Database.empty (encode P).schedule ↔ Diverges Database.empty P.schedule)

/-- Every source evaluation has a compiled evaluation. -/
def PreservesTermination : Prop :=
  ∀ P : Program, P.WellFormed → P.Fragment → ∀ source : Result,
    Eval Database.empty P source → ∃ target, Eval Database.empty (encode P) target

end Egglog.Congruence
