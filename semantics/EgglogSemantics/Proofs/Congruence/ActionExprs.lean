import EgglogSemantics.Proofs.Congruence.IdOrder
import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.Source.Domain

/-! Source action expressions and evaluation of generated minimum ids. -/

namespace Egglog.Congruence

/-- The value expressions evaluated by a source action. -/
def actionExprs : Action → List Expr
  | .expr e => [e]
  | .union a b => [a, b]

/-- `Action.OrderingFree`, at the expressions the action evaluates. -/
theorem Action.orderingFree_exprs {a : Action} (h : a.OrderingFree) :
    ∀ e ∈ actionExprs a, e.OrderingFree := by
  cases a with
  | expr x =>
      intro e he
      obtain rfl := List.mem_singleton.mp he
      exact h
  | union x y =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h.1
      · obtain rfl := List.mem_singleton.mp he
        exact h.2

/-- `Actions.OrderingFree`, at the expressions the actions evaluate. -/
theorem orderingFree_actionExprs {as : List Action} (h : Actions.OrderingFree as) :
    ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree := by
  induction as with
  | nil => simp
  | cons a as ih =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Action.orderingFree_exprs h.1
      · exact ih h.2 b hb

/-- The compiled union's `min` column picks the smaller of the two ids. -/
theorem eval_min_ids {sig : Signature} {ρ : Env} {a b : Expr} {ta tb : Term}
    (ha : a.eval sig ρ = some ta) (hb : b.eval sig ρ = some tb) :
    (Expr.min a b).eval sig ρ = some (lowerId ta tb) := by
  rw [Expr.eval_min, ha, Option.bind_some, hb, Option.map_some]
  rfl

theorem actionExprs_ctors {a : Action} {e : Expr} (he : e ∈ actionExprs a)
    {fk : FnName × Nat} (hk : fk ∈ e.ctors) : fk ∈ a.ctors := by
  cases a with
  | expr x => obtain rfl := List.mem_singleton.mp he; exact hk
  | union x y =>
      rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_append_left _ hk
      · obtain rfl := List.mem_singleton.mp he
        exact List.mem_append_right _ hk

end Egglog.Congruence
