import EgglogSemantics.Spec.Divergence

namespace Egglog

/-- The three observable outcomes of a program. -/
inductive Behavior where
  | success
  | checkFailed
  | diverges

/-- Finite outcomes and infinite execution, observed without exposing the final store. -/
def Behaves (db : Database) (P : Program) : Behavior → Prop
  | .success => Eval db P .ok
  | .checkFailed => Eval db P .checkFailed
  | .diverges => Diverges db P.schedule

end Egglog
