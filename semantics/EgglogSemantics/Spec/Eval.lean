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
  \sigma:\mathit{Var}\rightharpoonup\mathit{Term}\qquad
  \eval x=\sigma(x)\qquad
  \eval{f(e_1,\ldots,e_n)}=f(\eval{e_1},\ldots,\eval{e_n})\qquad
  \eval{\min(e_1,e_2)}=\min_{\prec}(\eval{e_1},\eval{e_2})
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

/-- The equations an action asserts. Actions read only the bindings, never the store, so
an action sequence denotes a set of equations to add and a set of rows to remove. A
delete asserts no equation, but its term must evaluate.

A `union` on a literal is stuck. egglog rejects it in its type checker — `union` wants an
eq-sort and `i64` is not one (`TypeError::NonEqsortUnion`) — and this untyped model cannot
see it until the operands are values. Asserting it instead would cost
`Database.LitsIsolated`. -/
def Action.write (σ : Env) : Action → Option (Set (Term × Term))
  | .expr e => (e.eval σ).map fun t => {(t, t)}
  | .union e₁ e₂ =>
      (e₁.eval σ).bind fun t₁ =>
        (e₂.eval σ).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some {(t₁, t₂)}
  | .delete e => (e.eval σ).map fun _ => ∅

/-- The rows an action removes: the term of a delete, and nothing for the others. -/
def Action.erase (σ : Env) : Action → Option (Set Term)
  | .delete e => (e.eval σ).map fun t => {t}
  | a => (a.write σ).map fun _ => ∅

/-- The equations asserted by an action sequence, defined when every action's is. -/
@[blueprint "def:actions"
  (statement := /--
\[
  \begin{gathered}
  \writes e=\{(\eval e,\eval e)\}\qquad
  \writes{\kw{union}(e_1,e_2)}=\{(\eval{e_1},\eval{e_2})\}\qquad
  \writes{\kw{delete}(e)}=\emptyset\\
  \erases{\kw{delete}(e)}=\{\eval e\}\qquad
  \erases{e}=\erases{\kw{union}(e_1,e_2)}=\emptyset\\
  \writes{h_1;\ldots;h_n}=\bigcup_{i=1}^n\writes{h_i}\qquad
  \erases{h_1;\ldots;h_n}=\bigcup_{i=1}^n\erases{h_i}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Action.writes (σ : Env) : List Action → Option (Set (Term × Term))
  | [] => some ∅
  | a :: as => (a.write σ).bind fun W => (Action.writes σ as).map (W ∪ ·)

/-- The rows removed by an action sequence, defined exactly when its writes are. -/
def Action.erases (σ : Env) : List Action → Option (Set Term)
  | [] => some ∅
  | a :: as => (a.erase σ).bind fun X => (Action.erases σ as).map (X ∪ ·)

end Egglog
