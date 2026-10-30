import EgglogSemantics.Proofs.Scope
import EgglogSemantics.Source.WellFormed

namespace Egglog

/-- Well-formed programs with bounded rounds have a finite result. -/
theorem Program.WellFormed.eval_exists {P : Program} (hw : P.WellFormed)
    (hn : P.NoSaturate) : ∃ r, Eval Database.empty P r :=
  Eval.exists_of_scoped hn hw.1

end Egglog
