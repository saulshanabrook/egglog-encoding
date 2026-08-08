import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

Ports the Redex `Eval-Expr`, `Eval-Action`, `Eval-Global-Actions` and
`Eval-Local-Actions`.

Evaluation is partial: `Eval-Expr` has no rule for an unbound variable, so it gets
stuck. Here that is `none`, and `Scope.lean` shows a well-scoped program never
produces it.

Actions only ever add terms and equalities, which is `evalAction_contained` — the
fact the Redex documentation appeals to when it says the order of actions does not
matter.
-/

namespace Egglog
mutual

/-- The Redex `Eval-Expr`: build the ground term an expression denotes. -/
def Expr.eval : Expr → Env → Option Term
  | .lit l, _ => some (.lit l)
  | .var v, σ => Env.lookup v σ
  | .app f args, σ => (Expr.evalList args σ).map (Term.app f)

/-- `Expr.eval` over an argument list, failing if any argument does. -/
def Expr.evalList : List Expr → Env → Option (List Term)
  | [], _ => some []
  | e :: es, σ => (e.eval σ).bind fun t => (Expr.evalList es σ).map (t :: ·)

end

/-- The Redex `Eval-Action`.

A `let` binds in the environment the database carries, so at top level it adds a
global and inside a rule it adds a rule-local binding; `evalLocalActions` is what
makes the second case local by restoring the caller's environment afterwards. -/
def evalAction (db : Database) : Action → Option Database
  | .expr e => (e.eval db.env).map fun t => db.addTerm t
  | .letBind v e => (e.eval db.env).map fun t =>
      { db.addTerm t with env := (v, t) :: db.env }
  | .union e₁ e₂ =>
      (e₁.eval db.env).bind fun t₁ => (e₂.eval db.env).map fun t₂ => db.addEq t₁ t₂
  | .set f args out =>
      (Expr.evalList args db.env).bind fun as =>
        (Expr.evalList out db.env).map fun vs => db.addRow f as vs

/-- The Redex `Eval-Global-Actions`: run the actions in order. -/
def evalActions (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction db a).bind fun db' => evalActions db' as

/-- The Redex `Eval-Local-Actions`: run a rule's actions with `σ` in scope, then
forget the resulting environment.

`σ` is appended *after* the globals, matching `Env-Union Env_1 Env_local`, so a
globally bound variable shadows a substitution for the same name. That never
happens in practice because a pattern's free variables exclude the globals
(`Expr.freeVars`), but the order is the Redex's. -/
def evalLocalActions (db : Database) (as : List Action) (σ : Env) : Option Database :=
  (evalActions { db with env := db.env ++ σ } as).map fun db' =>
    { db' with env := db.env, rules := db.rules }

end Egglog
