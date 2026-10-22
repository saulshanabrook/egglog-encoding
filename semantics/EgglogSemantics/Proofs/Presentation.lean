import EgglogSemantics.Spec.Behavior
import EgglogSemantics.Proofs.Query
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Proofs.Step

namespace Egglog

/-- The paper treats one action as a singleton sequence of actions. -/
theorem Action.writes_singleton (σ : Env) (a : Action) :
    Action.writes σ [a] = a.write σ := by
  cases h : a.write σ <;> simp [Action.writes, h]

/-- Concatenating action sequences unions their writes. -/
theorem Action.writes_append (σ : Env) (as bs : List Action) :
    Action.writes σ (as ++ bs) =
      (Action.writes σ as).bind fun A =>
        (Action.writes σ bs).map fun B => A ∪ B := by
  induction as with
  | nil => simp [Action.writes]
  | cons a as ih =>
    simp only [List.cons_append, Action.writes, ih]
    cases a.write σ <;>
      cases Action.writes σ as <;>
      cases Action.writes σ bs <;>
      simp [Set.union_assoc]

end Egglog
