import EgglogSemantics.Proofs.Congruence.ActionExprs

/-! Leader binding changes variable names, preserving the constructor syntax. -/

namespace Egglog.Congruence

@[simp] theorem leaderArgs_length (es : List Expr) : (leaderArgs es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [leaderArgs] using ih

@[simp] theorem leaderExpr_ctors (e : Expr) : (leaderExpr e).ctors = e.ctors := by
  induction e using Expr.rec
      (motive_2 := fun es => Expr.ctorsList (leaderArgs es) = Expr.ctorsList es) <;>
    simp_all [leaderExpr, leaderArgs, Expr.ctors, Expr.ctorsList]

@[simp] theorem leaderExpr_fns (e : Expr) : (leaderExpr e).fns = e.fns := by
  induction e using Expr.rec
      (motive_2 := fun es => Expr.fnsList (leaderArgs es) = Expr.fnsList es) <;>
    simp_all [leaderExpr, leaderArgs, Expr.fns, Expr.fnsList]

@[simp] theorem leaderExpr_hasMin (e : Expr) : (leaderExpr e).hasMin = e.hasMin := by
  induction e using Expr.rec
      (motive_2 := fun es => Expr.hasMinList (leaderArgs es) = Expr.hasMinList es) <;>
    simp_all [leaderExpr, leaderArgs, Expr.hasMin, Expr.hasMinList]

@[simp] theorem leaderExpr_orderingFree (e : Expr) :
    (leaderExpr e).OrderingFree ↔ e.OrderingFree := by simp [Expr.OrderingFree]

theorem leaderAction_exprs (a : Action) :
    actionExprs (leaderAction a) = (actionExprs a).map leaderExpr := by
  cases a <;> rfl

end Egglog.Congruence
