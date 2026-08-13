import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import EgglogSemantics.Spec.Eval

/-!
# E-matching

Which variables a pattern leaves for the matcher to assign, how the substitutions of
several patterns are joined, when one is well formed against a database, and the matching
relation itself. What a match *does* is `Spec/Step.lean`'s `RuleResults`.
-/

namespace Egglog
mutual

/-- The variables of `e` not already bound in `σ`. A pattern variable that *is* bound in
`σ` is not a match variable: it denotes its value. -/
def Expr.freeVars : Expr → Env → List Var
  | .lit _, _ => []
  | .var v, σ => if (Env.lookup v σ).isSome then [] else [v]
  | .app _ args, σ => Expr.freeVarsList args σ

/-- `Expr.freeVars` over an argument list, deduplicated. -/
def Expr.freeVarsList : List Expr → Env → List Var
  | [], _ => []
  | e :: es, σ => e.freeVars σ ∪ Expr.freeVarsList es σ

end

def Pattern.freeVars : Pattern → Env → List Var
  | .expr e, σ => e.freeVars σ
  | .eq e₁ e₂, σ => e₁.freeVars σ ∪ e₂.freeVars σ
  | .values vs _ as, σ => Expr.freeVarsList vs σ ∪ Expr.freeVarsList as σ

namespace Env
/-- Append, requiring the two to agree wherever both bind. The result may bind a variable
twice, always to the same term. -/
def Union2 (σ₁ σ₂ σ : Env) : Prop :=
  (∀ b ∈ σ₁, ∀ t, lookup b.1 σ₂ = some t → b.2 = t) ∧ σ = σ₁ ++ σ₂

/-- The left fold of `Union2`, which fails if any step does. -/
inductive UnionAll : List Env → Env → Prop where
  | nil : UnionAll [] []
  | single (σ : Env) : UnionAll [σ] σ
  | step {σ₁ σ₂ σr σ : Env} {σs : List Env} :
      Union2 σ₁ σ₂ σr → UnionAll (σr :: σs) σ → UnionAll (σ₁ :: σ₂ :: σs) σ

end Env
/-! ### Well-formed substitutions -/
/-- `σ` binds exactly `vars`, each to a term the database holds. `Perm` rather than
equality, so the order `Expr.freeVars` produces does not matter. -/
def ValidEnv (vars : List Var) (db : Database) (σ : Env) : Prop :=
  (Env.dom σ).Perm vars ∧ ∀ b ∈ σ, b.2 ∈ db.terms

/-! ### Matching -/
/-- A pattern **matches** under `σ` when its instance is congruent to a term the database
holds. The **witness** `w` is drawn from the *original* terms: without one, the reflexive
equation `withOperands` adds for the instance would match everything. -/
inductive Matches (db : Database) : Pattern → Env → Prop where
  | expr {e : Expr} {σ : Env} {w t : Term} :
      w ∈ db.terms → e.eval db.sig (db.env ++ σ) = some t → CongOn db [t] w t →
      Matches db (.expr e) σ
  | eq {e₁ e₂ : Expr} {σ : Env} {w t₁ t₂ : Term} :
      w ∈ db.terms →
      e₁.eval db.sig (db.env ++ σ) = some t₁ → e₂.eval db.sig (db.env ++ σ) = some t₂ →
      CongOn db [t₁, t₂] w t₁ → CongOn db [t₁, t₂] t₁ t₂ →
      Matches db (.eq e₁ e₂) σ
  /-- The entry atom: `f`'s entry at a key class congruent to `as`, with value columns
  congruent to `vs`, whose instance is the term `f(as…, vs…)`. **The only read.** -/
  | values {vs : List Expr} {f : FnName} {as : List Expr} {σ : Env}
      {us ts : List Term} {w : Term} :
      w ∈ db.terms →
      Expr.evalList db.sig as (db.env ++ σ) = some ts →
      Expr.evalList db.sig vs (db.env ++ σ) = some us →
      CongOn db [.app f (ts ++ us)] w (.app f (ts ++ us)) →
      Matches db (.values vs f as) σ

/-- The substitutions one query pattern admits: `σ` binds exactly the pattern's free
variables, and the pattern matches under it. -/
def ValidSubst (db : Database) (p : Pattern) (σ : Env) : Prop :=
  ValidEnv (p.freeVars db.env) db σ ∧ Matches db p σ

/-- The substitutions a whole query admits: one per pattern, unioned. -/
def ValidQuerySubst (db : Database) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (ValidSubst db) q σs ∧ Env.UnionAll σs σ

end Egglog
