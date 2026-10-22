import Mathlib.Logic.Function.Basic
import EgglogSemantics.Spec.Term

/-!
# The front end's static checks

`Scoped` — every variable used is bound, and a fact or build is an application;
`UnionLegal` — no `union` operand is a literal; `UnionFree` — no `union` at all;
`OrderingFree` — no `min`. The untyped language has no declarations to check against.
-/

namespace Egglog

/-! ### Scope -/

/-- The variables in scope. -/
abbrev Scope := List Var

/-- Every variable of `e` is in scope. -/
def Expr.Scoped (e : Expr) (Γ : Scope) : Prop := ∀ v ∈ e.vars, v ∈ Γ

/-- `e` is an application. Query facts and `expr` actions are restricted to applications;
an equality or disequality fact is not. -/
def Expr.IsApp : Expr → Prop
  | .app _ _ => True
  | _ => False

/-- Query facts must be applications; equality and disequality patterns have no shape
restriction. -/
def Pattern.Scoped : Pattern → Prop
  | .expr e => e.IsApp
  | .eq _ _ => True
  | .ne _ _ => True

/-- An action scopes when each expression it evaluates does, plus the application
restriction on a bare `expr` and on a delete. -/
def Action.Scoped : Action → Scope → Prop
  | .expr e, Γ => e.IsApp ∧ e.Scoped Γ
  | .union e₁ e₂, Γ => e₁.Scoped Γ ∧ e₂.Scoped Γ
  | .delete e, Γ => e.IsApp ∧ e.Scoped Γ

/-- The scope a query's patterns bind. -/
def Query.bind (q : Query) (Γ : Scope) : Scope := Γ ∪ Query.vars q

/-- Every action in the same scope. -/
@[simp] def Actions.Scoped : List Action → Scope → Prop
  | [], _ => True
  | a :: as, Γ => a.Scoped Γ ∧ Actions.Scoped as Γ

/-- Its facts, then its head in the scope the query binds. -/
@[simp] def Rule.Scoped (r : Rule) (Γ : Scope) : Prop :=
  (∀ p ∈ r.query, p.Scoped) ∧ Actions.Scoped r.actions (Query.bind r.query Γ)

/-- Every rule the command fires. -/
@[simp] def Cmd.Scoped (c : Cmd) (Γ : Scope) : Prop := ∀ r ∈ c.rules, r.Scoped Γ

/-- Every command in the same initial scope, and the final check's facts. -/
@[simp] def Program.Scoped (P : Program) (Γ : Scope) : Prop :=
  (∀ c ∈ P.commands, c.Scoped Γ) ∧ ∀ p ∈ P.check, p.Scoped

/-- A program with no free variables: `Program.Scoped` from the empty scope. -/
def WellScoped (P : Program) : Prop := Program.Scoped P []

/-! ### `union` legality

egglog rejects a `union` on a sort that is not an eq sort statically, where
`Spec/Eval.lean`'s `Action.write` only gets stuck on it. This is its syntactic half: an
operand is not a literal *expression*. -/

/-- Neither operand of a `union` is a literal. -/
def Action.UnionLegal : Action → Prop
  | .union e₁ e₂ => (∀ l, e₁ ≠ .lit l) ∧ ∀ l, e₂ ≠ .lit l
  | _ => True

@[simp] def Actions.UnionLegal : List Action → Prop
  | [] => True
  | a :: as => a.UnionLegal ∧ Actions.UnionLegal as

@[simp] def Cmd.UnionLegal (c : Cmd) : Prop := ∀ r ∈ c.rules, Actions.UnionLegal r.actions

@[simp] def Program.UnionLegal (P : Program) : Prop := ∀ c ∈ P.commands, c.UnionLegal

/-! ### Union-freedom

Where a program may assert an equation. `Action.union` is the only action that asserts
one between distinct terms — every other write records a reflexive pair — so a program
with none keeps every state it reaches **diagonal**, and on a diagonal state nothing is
congruent to anything but itself. The compiled target is union-free. -/

/-- The action that asserts an equation between distinct terms, ruled out. -/
def Action.UnionFree : Action → Prop
  | .union _ _ => False
  | _ => True

@[simp] def Actions.UnionFree : List Action → Prop
  | [] => True
  | a :: as => a.UnionFree ∧ Actions.UnionFree as

@[simp] def Rule.UnionFree (r : Rule) : Prop := Actions.UnionFree r.actions

@[simp] def Cmd.UnionFree (c : Cmd) : Prop := ∀ r ∈ c.rules, r.UnionFree

@[simp] def Program.UnionFree (P : Program) : Prop := ∀ c ∈ P.commands, c.UnionFree

/-! ### Ordering-freedom

Where a program may apply `min`. It compares two terms by `Term.blt`, a structural order,
where egglog compares by e-class id. It is therefore not stable under congruence, and the
source fragment excludes it; the compiled rebuilding is where it is used. -/

mutual

/-- Whether `min` occurs anywhere in `e`. -/
def Expr.hasMin : Expr → Bool
  | .lit _ => false
  | .var _ => false
  | .app _ args => Expr.hasMinList args
  | .min _ _ => true

def Expr.hasMinList : List Expr → Bool
  | [] => false
  | e :: es => e.hasMin || Expr.hasMinList es

end

/-- No order-sensitive minimum in `e`. -/
def Expr.OrderingFree (e : Expr) : Prop := e.hasMin = false

/-- `Expr.OrderingFree` over an argument list. -/
def Expr.OrderingFreeList (es : List Expr) : Prop := Expr.hasMinList es = false

/-- A query pattern is evaluated, so it carries the condition too. -/
def Pattern.OrderingFree : Pattern → Prop
  | .expr e => e.OrderingFree
  | .eq e₁ e₂ => e₁.OrderingFree ∧ e₂.OrderingFree
  | .ne e₁ e₂ => e₁.OrderingFree ∧ e₂.OrderingFree

def Action.OrderingFree : Action → Prop
  | .expr e => e.OrderingFree
  | .union e₁ e₂ => e₁.OrderingFree ∧ e₂.OrderingFree
  | .delete e => e.OrderingFree

@[simp] def Actions.OrderingFree : List Action → Prop
  | [] => True
  | a :: as => a.OrderingFree ∧ Actions.OrderingFree as

/-- Both halves: a query pattern is evaluated against the database, a head action against
the substitution. -/
@[simp] def Rule.OrderingFree (r : Rule) : Prop :=
  (∀ p ∈ r.query, p.OrderingFree) ∧ Actions.OrderingFree r.actions

@[simp] def Cmd.OrderingFree (c : Cmd) : Prop := ∀ r ∈ c.rules, r.OrderingFree

/-- Every rule, and the final check. -/
@[simp] def Program.OrderingFree (P : Program) : Prop :=
  (∀ c ∈ P.commands, c.OrderingFree) ∧ ∀ p ∈ P.check, p.OrderingFree

instance (e : Expr) : Decidable e.OrderingFree := inferInstanceAs (Decidable (_ = false))
instance (es : List Expr) : Decidable (Expr.OrderingFreeList es) :=
  inferInstanceAs (Decidable (_ = false))
instance : ∀ p : Pattern, Decidable p.OrderingFree
  | .expr e => inferInstanceAs (Decidable e.OrderingFree)
  | .eq a b => inferInstanceAs (Decidable (a.OrderingFree ∧ b.OrderingFree))
  | .ne a b => inferInstanceAs (Decidable (a.OrderingFree ∧ b.OrderingFree))
instance : ∀ a : Action, Decidable a.OrderingFree
  | .expr e => inferInstanceAs (Decidable e.OrderingFree)
  | .union a b => inferInstanceAs (Decidable (a.OrderingFree ∧ b.OrderingFree))
  | .delete e => inferInstanceAs (Decidable e.OrderingFree)
instance instDecidableActionsOrderingFree : ∀ as : List Action, Decidable (Actions.OrderingFree as)
  | [] => inferInstanceAs (Decidable True)
  | a :: as => @instDecidableAnd _ _ inferInstance (instDecidableActionsOrderingFree as)
instance (r : Rule) : Decidable r.OrderingFree :=
  inferInstanceAs (Decidable ((∀ p ∈ r.query, p.OrderingFree) ∧ Actions.OrderingFree r.actions))
instance (c : Cmd) : Decidable c.OrderingFree :=
  inferInstanceAs (Decidable (∀ r ∈ c.rules, r.OrderingFree))
instance (P : Program) : Decidable (Program.OrderingFree P) :=
  inferInstanceAs (Decidable ((∀ c ∈ P.commands, c.OrderingFree) ∧ ∀ p ∈ P.check, p.OrderingFree))

/-! ### Keyed variables -/

mutual

/-- The variable occurs as an **argument of an application**: a key column of one of the view
reads `encodeQueryExpr` emits. -/
def Expr.ArgVar (v : Var) : Expr → Prop
  | .lit _ => False
  | .var _ => False
  | .app _ args => Expr.var v ∈ args ∨ Expr.ArgVarList v args
  | .min a b => Expr.ArgVar v a ∨ Expr.ArgVar v b

/-- `Expr.ArgVar` over an argument list. -/
def Expr.ArgVarList (v : Var) : List Expr → Prop
  | [] => False
  | e :: es => Expr.ArgVar v e ∨ Expr.ArgVarList v es

end

@[inherit_doc Expr.ArgVar]
def Pattern.ArgVar (v : Var) : Pattern → Prop
  | .expr e => Expr.ArgVar v e
  | .eq e₁ e₂ => Expr.ArgVar v e₁ ∨ Expr.ArgVar v e₂
  | .ne e₁ e₂ => Expr.ArgVar v e₁ ∨ Expr.ArgVar v e₂

def Query.VarsKeyed (q : Query) : Prop := ∀ v ∈ Query.vars q, ∃ p ∈ q, Pattern.ArgVar v p

end Egglog
