import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import EgglogSemantics.Spec.Eval

/-!
# E-matching

Which variables a pattern leaves for the matcher to assign, how the substitutions of
several patterns are joined, when one is well formed against a database, and the matching
relation itself. What a match *does* is `Spec/Step.lean`'s `RunRules`.
-/

namespace Egglog
mutual

/-- The variables of `e` not already bound in `σ`. A pattern variable that *is* bound in
`σ` is not a match variable: it denotes its value. -/
def Expr.freeVars : Expr → Env → List Var
  | .lit _, _ => []
  | .var v, σ => if (Env.lookup v σ).isSome then [] else [v]
  | .app _ args, σ => Expr.freeVarsList args σ
  | .min a b, σ => a.freeVars σ ∪ b.freeVars σ

/-- `Expr.freeVars` over an argument list, deduplicated. -/
def Expr.freeVarsList : List Expr → Env → List Var
  | [], _ => []
  | e :: es, σ => e.freeVars σ ∪ Expr.freeVarsList es σ

end

def Pattern.freeVars : Pattern → Env → List Var
  | .expr e, σ => e.freeVars σ
  | .eq e₁ e₂, σ => e₁.freeVars σ ∪ e₂.freeVars σ
  | .ne e₁ e₂, σ => e₁.freeVars σ ∪ e₂.freeVars σ

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
/-- Match evaluated terms through semantic congruence. Bindings remain local to the query.
A disequality holds when both sides exist and are not congruent. -/
inductive Matches (db : Database) : Pattern → Env → Prop where
  | atom {e : Expr} {σ : Env} {t : Term} :
      e.eval σ = some t → Cong db t t → Matches db (.expr e) σ
  | equal {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term} :
      e₁.eval σ = some t₁ → e₂.eval σ = some t₂ →
      Cong db t₁ t₂ → Matches db (.eq e₁ e₂) σ
  | unequal {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term} :
      e₁.eval σ = some t₁ → e₂.eval σ = some t₂ →
      Cong db t₁ t₁ → Cong db t₂ t₂ → ¬ Cong db t₁ t₂ → Matches db (.ne e₁ e₂) σ

/-- One substitution binds the query's variables to held terms and satisfies every conjunct. -/
@[blueprint "def:query"
  (statement := /--
\[
  \ir{Atom}{\eval e=t\\t\sim_E t}{E,\sigma\models e}\quad
  \ir{Equal}{\eval{e_1}=s\\\eval{e_2}=t\\s\sim_E t}
    {E,\sigma\models e_1=e_2}\quad
  \ir{Unequal}{\eval{e_1}=s\\\eval{e_2}=t\\s\sim_E s\\t\sim_E t\\s\not\sim_E t}
    {E,\sigma\models e_1\ne e_2}
  \]
  \[
  \ir{Query}{\sigma:\operatorname{FV}(Q)\to\operatorname{terms}(E)\\\\
    \forall p\in Q.\ E,\sigma\models p}
    {E,\sigma\models Q}
  \]
  -/)
  (latexEnv := "paperfragment")]
def QueryMatches (db : Database) (q : Query) (σ : Env) : Prop :=
  ValidEnv q.vars db σ ∧ ∀ p ∈ q, Matches db p σ

/-- A substitution binds exactly the pattern's variables and makes the pattern match.
Every query variable is local to the match. -/
def ValidSubst (db : Database) (p : Pattern) (σ : Env) : Prop :=
  ValidEnv (p.freeVars []) db σ ∧ Matches db p σ

/-- Join representation of a query match; `Proofs/Query.lean` relates it to `QueryMatches`. -/
def ValidQuerySubst (db : Database) (q : Query) (σ : Env) : Prop :=
  ∃ σs : List Env, List.Forall₂ (ValidSubst db) q σs ∧ Env.UnionAll σs σ

/-- Some substitution satisfies the query. Check variables are existential and local to
the query; evaluating a check exports no bindings and builds no terms. -/
def QueryHolds (db : Database) (q : Query) : Prop := ∃ σ, QueryMatches db q σ

end Egglog
