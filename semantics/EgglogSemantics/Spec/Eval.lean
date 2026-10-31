import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

Evaluation builds terms without consulting the database: every application builds.
-/

namespace Egglog
mutual

/-- Evaluate an expression under a substitution. -/
@[blueprint "def:evaluation"
  (statement := /--
  \[
  \begin{gathered}
  \sigma:\mathit{Var}\rightharpoonup\mathit{Term}\qquad
  \eval x=\sigma(x)\qquad
  \eval{f(e_1,\ldots,e_n)}=f(\eval{e_1},\ldots,\eval{e_n})\\
  \eval{\min(e_1,e_2)}=\min_{\prec}(\eval{e_1},\eval{e_2})
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Expr.eval : Expr → Env → Option Term
  | .lit l, _ => some (.lit l)
  | .var v, σ => Env.lookup v σ
  | .app f args, σ => (Expr.evalList args σ).map (Term.app f)
  | .min a b, σ => (a.eval σ).bind fun x => (b.eval σ).map (Term.least x)

/-- `Expr.eval` over an argument list, failing if any argument does. -/
def Expr.evalList : List Expr → Env → Option (List Term)
  | [], _ => some []
  | e :: es, σ => (e.eval σ).bind fun t => (Expr.evalList es σ).map (t :: ·)

end

/-- `G ⊕_σ h`: the e-graph after one action under a substitution. Actions read only the
bindings, never the store, and every action adds, so the actions of a head commute. A
subsume asserts the row it marks, as egglog inserts a missing row it subsumes.

A `union` on a literal is stuck. egglog rejects it in its type checker — `union` wants an
eq-sort and `i64` is not one (`TypeError::NonEqsortUnion`) — and this untyped model cannot
see it until the operands are values. Asserting it instead would cost
`Database.LitsIsolated`. -/
@[blueprint "def:actions"
  (statement := /--
  \[
  \begin{gathered}
  \begin{aligned}
  (E,X)\oplus_\sigma\kw{union}(e_1,e_2)&=(E\cup\{(\eval{e_1},\eval{e_2})\},\ X)\\
  (E,X)\oplus_\sigma\kw{subsume}(f(e_1,\ldots,e_n))&=(E\cup\{(t,t)\},\ X\cup\{t\})
    \quad\text{where }t=\eval{f(e_1,\ldots,e_n)}\\
  G\oplus_\sigma\{h_1,\ldots,h_n\}&=G\oplus_\sigma h_1\oplus_\sigma\cdots\oplus_\sigma h_n
  \end{aligned}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def evalAction (σ : Env) (db : Database) : Action → Option Database
  | .expr e => (e.eval σ).map fun t => db.addTerm t
  | .union e₁ e₂ =>
      (e₁.eval σ).bind fun t₁ =>
        (e₂.eval σ).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some (db.addEq t₁ t₂)
  | .subsume f es =>
      (Expr.evalList es σ).map fun ts => (db.addTerm (.app f ts)).addSubsumed {.app f ts}

/-- `G ⊕_σ H`: the actions of a head in turn, and `none` if one is stuck. The order does not
matter, since every action only adds. -/
def evalActions (σ : Env) (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction σ db a).bind fun db' => evalActions σ db' as

end Egglog
