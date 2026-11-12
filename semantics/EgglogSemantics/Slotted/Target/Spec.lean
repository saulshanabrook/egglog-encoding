import EgglogSemantics.Spec.Step
import EgglogSemantics.Spec.Divergence
import EgglogSemantics.Slotted.Target.Prim

/-!
# The target semantics: the plain semantics with the primitive step

The compiled program is a plain `Program` whose rules apply the reserved primitive heads of
`Prim.lean`. Its semantics is the plain one with one change in matching: an expression
evaluates by `Expr.eval` followed by the primitive step (`evalExpr`), a primitive
application computes on evaluated operands (including unstored slot constants), a table application is a
live row of its reduced instance, an equality compares reduced values, equal when identical or
congruent, and the membership pattern `@mem(x, e)` binds `x` to an element of the value of
`e`. A query's **computed variables**, those defined by `v = @op(…)` or `@mem(v, …)`, are
bound by their defining pattern instead of ranging over representatives. Actions contain no
primitive application, so `evalActions` and the state, congruence, representatives, live rows
and the meaning of a state are the plain definitions; rounds, schedules, outcomes and
divergence repeat the plain definitions over the target match.
-/

namespace Egglog.Slotted.Target

/-- `Expr.eval` followed by the primitive step. -/
def evalExpr (e : Expr) (σ : Env) : Option Term := (e.eval σ).bind Prim.norm?

/-- `evalExpr` over an argument list. -/
def evalList (es : List Expr) (σ : Env) : Option (List Term) :=
  (Expr.evalList es σ).bind Prim.normList?

/-- The head of the membership pattern. -/
def memName : FnName := "@mem"

/-- Whether an expression is a membership pattern. -/
def isMemExpr : Expr → Bool
  | .app f [.var _, _] => f = memName
  | _ => false

mutual

/-- `G,σ ⊨ e` with primitives: a literal or a non-primitive application is a live row of the
reduced instance; a primitive evaluates its operands and has a defined value. In particular,
the names used as keys of `fresh` need not occur in the database. -/
inductive TExpr.Matches (db : Database) (σ : Env) : Expr → Prop where
  | lit {l : Lit} : Term.lit l ∈ db.live → TExpr.Matches db σ (.lit l)
  | var {v : Var} {t : Term} : Env.lookup v σ = some t → TExpr.Matches db σ (.var v)
  | app {f : FnName} {args : List Expr} {ts : List Term} :
      isPrimName f = false → TExpr.MatchesList db σ args → evalList args σ = some ts →
      Term.app f ts ∈ db.live → TExpr.Matches db σ (.app f args)
  | prim {f : FnName} {args : List Expr} {ts : List Term} {v : Term} :
      isPrimName f = true → evalList args σ = some ts →
      Prim.eval f ts = some v → TExpr.Matches db σ (.app f args)
  | min {a b : Expr} :
      TExpr.Matches db σ a → TExpr.Matches db σ b → TExpr.Matches db σ (.min a b)

inductive TExpr.MatchesList (db : Database) (σ : Env) : List Expr → Prop where
  | nil : TExpr.MatchesList db σ []
  | cons {e : Expr} {es : List Expr} :
      TExpr.Matches db σ e → TExpr.MatchesList db σ es → TExpr.MatchesList db σ (e :: es)

end

/-- Two reduced values agree: they are the same term, or congruent in the state. Values are
never unioned with anything, so a computed value that is not stored compares syntactically. -/
def Agree (db : Database) (t₁ t₂ : Term) : Prop := t₁ = t₂ ∨ Cong db t₁ t₂

/-- `G,σ ⊨ p` with primitives. -/
inductive TMatches (db : Database) : Pattern → Env → Prop where
  | atom {e : Expr} {σ : Env} :
      isMemExpr e = false → TExpr.Matches db σ e → TMatches db (.expr e) σ
  /-- `@mem(x, e)`: `x` is bound to an element of the set-valued `e`. -/
  | mem {x : Var} {e : Expr} {σ : Env} {t v : Term} {vs : List Term} :
      Env.lookup x σ = some t → TExpr.Matches db σ e → evalExpr e σ = some v →
      Prim.elements v = some vs → t ∈ vs → TMatches db (.expr (.app memName [.var x, e])) σ
  | equal {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term} :
      TExpr.Matches db σ e₁ → TExpr.Matches db σ e₂ →
      evalExpr e₁ σ = some t₁ → evalExpr e₂ σ = some t₂ → Agree db t₁ t₂ →
      TMatches db (.eq e₁ e₂) σ
  | unequal {e₁ e₂ : Expr} {σ : Env} {t₁ t₂ : Term} :
      TExpr.Matches db σ e₁ → TExpr.Matches db σ e₂ →
      evalExpr e₁ σ = some t₁ → evalExpr e₂ σ = some t₂ → ¬ Agree db t₁ t₂ →
      TMatches db (.ne e₁ e₂) σ

/-- The variables a pattern computes: the left side of `v = @op(…)` and the element variable
of `@mem(x, e)`. -/
def patternComputed : Pattern → List Var
  | .eq (.var v) (.app f _) => if isPrimName f then [v] else []
  | .expr (.app f [.var x, _]) => if f = memName then [x] else []
  | _ => []

/-- The computed variables of a query. -/
def computedVars (q : Query) : List Var := q.flatMap patternComputed

/-- `σ` binds exactly the query's variables; every match variable to a representative. The
computed variables are bound by their defining patterns. -/
def TValidEnv (q : Query) (db : Database) (σ : Env) : Prop :=
  (Env.dom σ).Perm q.vars ∧ ∀ b ∈ σ, b.1 ∉ computedVars q → b.2 ∈ db.reps

/-- `G,σ ⊨ Q` with primitives. -/
def TQueryMatches (db : Database) (q : Query) (σ : Env) : Prop :=
  TValidEnv q db σ ∧ ∀ p ∈ q, TMatches db p σ

def TQueryHolds (db : Database) (q : Query) : Prop := ∃ σ, TQueryMatches db q σ

/-- The round: every rule fires on every target match. -/
def TRunRules (rs : List Rule) (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ rs, ∃ σ, TQueryMatches db r.query σ ∧ evalActions σ db r.actions = some d}

/-- `⟨S, G⟩ ⇓ G'` over target rounds. -/
inductive TReach : Database → Schedule → Database → Prop where
  | run {db : Database} {rs : List Rule} : TReach db (.run rs) (TRunRules rs db)
  | seq {db d d' : Database} {S₁ S₂ : Schedule} :
      TReach db S₁ d → TReach d S₂ d' → TReach db (.seq S₁ S₂) d'
  | fixpoint {db d : Database} {S : Schedule} :
      TReach db S d → db.SameMeaning d → TReach db (.saturate S) d
  | again {db d d' : Database} {S : Schedule} :
      TReach db S d → ¬ db.SameMeaning d → TReach d (.saturate S) d' →
      TReach db (.saturate S) d'

/-- Program evaluation: the schedule, then the check as a target query. -/
inductive Eval : Database → Program → Result → Prop where
  | ok {db d : Database} {P : Program} :
      TReach db P.schedule d → TQueryHolds d P.check → Eval db P .ok
  | checkFailed {db d : Database} {P : Program} :
      TReach db P.schedule d → ¬ TQueryHolds d P.check → Eval db P .checkFailed

/-- Passes of `S` that each change the meaning of the state, forever. -/
def InfinitePasses (S : Schedule) (d : Database) : Prop :=
  ∃ trace : Nat → Database, trace 0 = d ∧
    ∀ n, TReach (trace n) S (trace (n + 1)) ∧ ¬ (trace n).SameMeaning (trace (n + 1))

/-- Divergence of a target schedule, as `Egglog.Diverges`. -/
inductive Diverges : Database → Schedule → Prop where
  | seqLeft {d : Database} {S₁ S₂ : Schedule} : Diverges d S₁ → Diverges d (.seq S₁ S₂)
  | seqRight {d d' : Database} {S₁ S₂ : Schedule} :
      TReach d S₁ d' → Diverges d' S₂ → Diverges d (.seq S₁ S₂)
  | body {d : Database} {S : Schedule} : Diverges d S → Diverges d (.saturate S)
  | later {d d₁ : Database} {S : Schedule} :
      TReach d S d₁ → ¬ d.SameMeaning d₁ → Diverges d₁ (.saturate S) → Diverges d (.saturate S)
  | forever {d : Database} {S : Schedule} : InfinitePasses S d → Diverges d (.saturate S)

end Egglog.Slotted.Target
