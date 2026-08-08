import Mathlib.Data.List.Basic
import EgglogSemantics.Spec.Syntax

namespace Egglog
namespace Expr
@[simp] theorem vars_lit {l : Lit} : (Expr.lit l).vars = [] := rfl

@[simp] theorem vars_var {v : Var} : (Expr.var v).vars = [v] := rfl

@[simp] theorem vars_app {f : FnName} {args : List Expr} :
    (Expr.app f args).vars = Expr.varsList args := rfl

@[simp] theorem varsList_nil : Expr.varsList ([] : List Expr) = [] := rfl

@[simp] theorem varsList_cons {e : Expr} {es : List Expr} :
    Expr.varsList (e :: es) = e.vars ∪ Expr.varsList es := rfl

/-- A variable of an argument list is a variable of one of its arguments. -/
theorem mem_varsList {v : Var} {es : List Expr} (h : v ∈ Expr.varsList es) :
    ∃ e ∈ es, v ∈ e.vars := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    rw [varsList_cons, List.mem_union_iff] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', hv⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', hv⟩

end Expr
@[simp] theorem Query.vars_nil : Query.vars [] = [] := rfl

@[simp] theorem Query.vars_cons {p : Pattern} {ps : Query} :
    Query.vars (p :: ps) = p.vars ∪ Query.vars ps := rfl

end Egglog
