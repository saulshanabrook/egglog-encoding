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
/-! ### Representatives and well-formed substitutions -/
/-- The canonical representative of each class: the stored spelling that is least in the
term order among the stored spellings congruent to it. A query variable is bound to a
representative, one value per class, as egglog binds a variable to an e-class. -/
@[blueprint "def:representatives"
  (statement := /--
  \[
  \operatorname{reps}(E)\triangleq
    \{\,t\in\operatorname{terms}(E)\mid
      \forall s\in\operatorname{terms}(E).\ s\sim_E t\Rightarrow t\preceq s\,\}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Database.reps (db : Database) : Set Term :=
  {t | t ∈ db.terms ∧ ∀ s ∈ db.terms, Cong db s t → ¬ Term.blt s t}

/-- `σ` binds exactly `vars`, each to a representative. `Perm` rather than equality, so
the order `Expr.freeVars` produces does not matter. -/
def ValidEnv (vars : List Var) (db : Database) (σ : Env) : Prop :=
  (Env.dom σ).Perm vars ∧ ∀ b ∈ σ, b.2 ∈ db.reps

/-! ### Matching -/
mutual

/-- `G,σ ⊨ e`: the expression evaluates and every application it reads is live. A query
looks rows up and builds nothing. -/
inductive Expr.Matches (db : Database) (σ : Env) : Expr → Prop where
  | lit {l : Lit} : Term.lit l ∈ db.live → Expr.Matches db σ (.lit l)
  | var {v : Var} {t : Term} : Env.lookup v σ = some t → Expr.Matches db σ (.var v)
  | app {f : FnName} {args : List Expr} {ts : List Term} :
      Expr.MatchesList db σ args → Expr.evalList args σ = some ts →
      Term.app f ts ∈ db.live → Expr.Matches db σ (.app f args)
  | min {a b : Expr} : Expr.Matches db σ a → Expr.Matches db σ b → Expr.Matches db σ (.min a b)

/-- `Expr.Matches` over an argument list. -/
inductive Expr.MatchesList (db : Database) (σ : Env) : List Expr → Prop where
  | nil : Expr.MatchesList db σ []
  | cons {e : Expr} {es : List Expr} :
      Expr.Matches db σ e → Expr.MatchesList db σ es → Expr.MatchesList db σ (e :: es)

end

/-- `G,σ ⊨ p`: a pattern that is an expression matches as that expression; an equality or
disequality needs both sides to match and compares them through congruence. -/
inductive Matches (db : Database) : Pattern → Env → Prop where
  | atom {e : Expr} {σ : Env} : Expr.Matches db σ e → Matches db (.expr e) σ
  | equal {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term} :
      Expr.Matches db σ e₁ → Expr.Matches db σ e₂ →
      e₁.eval σ = some t₁ → e₂.eval σ = some t₂ → Cong db t₁ t₂ → Matches db (.eq e₁ e₂) σ
  | unequal {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term} :
      Expr.Matches db σ e₁ → Expr.Matches db σ e₂ →
      e₁.eval σ = some t₁ → e₂.eval σ = some t₂ → ¬ Cong db t₁ t₂ → Matches db (.ne e₁ e₂) σ

/-- One substitution binds the query's variables to representatives and satisfies every
conjunct. -/
@[blueprint "def:query"
  (statement := /--
  \begin{mathpar}
  \ir{Var}{x\in\operatorname{dom}(\sigma)}{G,\sigma\models x}
  \and
  \ir{App}{G,\sigma\models e_i\ (\forall i)\\
    \eval{f(e_1,\ldots,e_n)}\in\operatorname{live}(G)}
    {G,\sigma\models f(e_1,\ldots,e_n)}
  \and
  \ir{Min}{G,\sigma\models e_1\\G,\sigma\models e_2}{G,\sigma\models\min(e_1,e_2)}
  \and
  \ir{Equal}{G,\sigma\models e_1\\G,\sigma\models e_2\\\eval{e_1}\sim_E\eval{e_2}}
    {G,\sigma\models e_1=e_2}
  \and
  \ir{Unequal}{G,\sigma\models e_1\\G,\sigma\models e_2\\\eval{e_1}\not\sim_E\eval{e_2}}
    {G,\sigma\models e_1\ne e_2}
  \and
  \ir{Query}{\sigma:\operatorname{FV}(Q)\to\operatorname{reps}(E)\\
    \forall p\in Q.\ G,\sigma\models p}
    {G,\sigma\models Q}
  \end{mathpar}
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
