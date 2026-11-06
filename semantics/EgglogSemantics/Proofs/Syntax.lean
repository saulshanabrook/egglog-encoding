import Mathlib.Data.List.Basic
import EgglogSemantics.Spec.Syntax

namespace Egglog
namespace Expr
/-- Structural induction over `Expr`, with the induction hypothesis given for every element
of an application's argument list. `Term.recTerm`'s twin. -/
@[elab_as_elim]
theorem recExpr {motive : Expr → Prop} (lit : ∀ l, motive (.lit l)) (var : ∀ v, motive (.var v))
    (app : ∀ f args, (∀ a ∈ args, motive a) → motive (.app f args))
    (min : ∀ a b, motive a → motive b → motive (.min a b))
    (e : Expr) : motive e :=
  Expr.rec (motive_1 := motive) (motive_2 := fun args => ∀ a ∈ args, motive a) lit var
    (fun f args ih => app f args ih) (fun a b iha ihb => min a b iha ihb)
    (fun a ha => by simp at ha)
    (fun _ _ iht ihts a ha => (List.mem_cons.mp ha).elim (fun h => h ▸ iht) (ihts a)) e

@[simp] theorem vars_lit {l : Lit} : (Expr.lit l).vars = [] := rfl

@[simp] theorem vars_var {v : Var} : (Expr.var v).vars = [v] := rfl

@[simp] theorem vars_min {a b : Expr} : (Expr.min a b).vars = a.vars ∪ b.vars := rfl

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

@[simp] theorem fns_lit {l : Lit} : (Expr.lit l).fns = [] := rfl

@[simp] theorem fns_var {v : Var} : (Expr.var v).fns = [] := rfl

@[simp] theorem fns_min {a b : Expr} : (Expr.min a b).fns = a.fns ∪ b.fns := rfl

@[simp] theorem fns_app {f : FnName} {args : List Expr} :
    (Expr.app f args).fns = f :: Expr.fnsList args := rfl

@[simp] theorem fnsList_nil : Expr.fnsList ([] : List Expr) = [] := rfl

@[simp] theorem fnsList_cons {e : Expr} {es : List Expr} :
    Expr.fnsList (e :: es) = e.fns ∪ Expr.fnsList es := rfl

/-- An argument's own function names are among the list's: `mem_fnsList`'s converse, and the
direction a hypothesis about the whole application is consumed in. -/
theorem fns_subset_fnsList {e : Expr} : ∀ {es : List Expr}, e ∈ es → e.fns ⊆ Expr.fnsList es
  | x :: xs, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact fun _ hx => List.mem_union_iff.mpr (Or.inl hx)
    · exact fun _ hx => List.mem_union_iff.mpr (Or.inr (fns_subset_fnsList h' hx))

/-- A function name of an argument list is a function name of one of its arguments. -/
theorem mem_fnsList {f : FnName} {es : List Expr} (h : f ∈ Expr.fnsList es) :
    ∃ e ∈ es, f ∈ e.fns := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    rw [fnsList_cons, List.mem_union_iff] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', hv⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', hv⟩

end Expr
@[simp] theorem Query.vars_nil : Query.vars [] = [] := rfl

@[simp] theorem Query.vars_cons {p : Pattern} {ps : Query} :
    Query.vars (p :: ps) = p.vars ∪ Query.vars ps := rfl

/-- A rule occurs in a schedule exactly when it occurs in one of its runs. -/
theorem Schedule.mem_rules_iff {S : Schedule} {r : Rule} :
    r ∈ S.rules ↔ ∃ rs ∈ S.runs, r ∈ rs := by
  induction S with
  | run rs => simp [Schedule.rules, Schedule.runs]
  | saturate S ih => exact ih
  | seq S₁ S₂ ih₁ ih₂ =>
    simp only [Schedule.rules, Schedule.runs, List.mem_append, ih₁, ih₂]
    constructor
    · rintro (⟨rs, hrs, hr⟩ | ⟨rs, hrs, hr⟩)
      · exact ⟨rs, Or.inl hrs, hr⟩
      · exact ⟨rs, Or.inr hrs, hr⟩
    · rintro ⟨rs, hrs | hrs, hr⟩
      · exact Or.inl ⟨rs, hrs, hr⟩
      · exact Or.inr ⟨rs, hrs, hr⟩

theorem Program.mem_rules_iff {P : Program} {r : Rule} :
    r ∈ P.rules ↔ ∃ rs ∈ P.runs, r ∈ rs := Schedule.mem_rules_iff

end Egglog
