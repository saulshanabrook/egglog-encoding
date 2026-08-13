import EgglogSemantics.Spec.Congruence

/-!
# Evaluating expressions and actions

An expression denotes a ground term; an action turns a database into a database. This file
is `Option`-valued: what a command computes, deterministically. The nondeterminism —
merge closure, rule firing — is `Spec/Step.lean`. Evaluation is partial in five ways, all
`none`: an unbound variable, an **undeclared** name, a declared merge function — which is a
*lookup*, and so the query atom `Pattern.values` rather than an expression — a
primitive given operands of the wrong sort, and a `union` on a literal. Actions only ever
add equations.
-/

namespace Egglog
mutual

/-- Build the ground term an expression denotes. The signature is read for one thing only —
whether a name **builds, computes, reads, or means nothing** — and the primitive table is
consulted first, so a reserved name shadows a user function. -/
def Expr.eval (sig : Signature) : Expr → Env → Option Term
  | .lit l, _ => some (.lit l)
  | .var v, σ => Env.lookup v σ
  | .app f args, σ =>
      match Prim.ofName f with
      | some p => (Expr.evalList sig args σ).bind p.apply
      | none =>
          if sig.IsCtor f then (Expr.evalList sig args σ).map (Term.app f) else none

/-- `Expr.eval` over an argument list, failing if any argument does. -/
def Expr.evalList (sig : Signature) : List Expr → Env → Option (List Term)
  | [], _ => some []
  | e :: es, σ => (e.eval sig σ).bind fun t => (Expr.evalList sig es σ).map (t :: ·)

end

/-- Run one action against the database. A `let` binds in the environment the database
carries, a global at top level and a rule-local binding inside a rule. A `set` only
*records* its entry; a collision on a congruent key is resolved by `MergeStep`.

A `union` on a literal is stuck. egglog rejects it in its type checker — `union` wants an
eq-sort and `i64` is not one (`TypeError::NonEqsortUnion`) — and this untyped model cannot
see it until the operands are values. Asserting it instead would cost
`Database.LitsIsolated`. -/
def evalAction (db : Database) : Action → Option Database
  | .expr e => (e.eval db.sig db.env).map fun t => db.addTerm t
  | .letBind v e => (e.eval db.sig db.env).map fun t =>
      { db.addTerm t with env := (v, t) :: db.env }
  | .union e₁ e₂ =>
      (e₁.eval db.sig db.env).bind fun t₁ =>
        (e₂.eval db.sig db.env).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some (db.addEq t₁ t₂)
  | .set f args out =>
      (Expr.evalList db.sig args db.env).bind fun as =>
        (Expr.evalList db.sig out db.env).map fun vs => db.addTerm (.app f (as ++ vs))

/-- Run the actions in order, threading the database through. -/
def evalActions (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction db a).bind fun db' => evalActions db' as

/-- Run a rule's actions with `σ` in scope, then forget the resulting environment. `σ` is
appended *after* the globals, so a global shadows a substitution for the same name. -/
def evalLocalActions (db : Database) (as : List Action) (σ : Env) : Option Database :=
  (evalActions { db with env := db.env ++ σ } as).map fun db' =>
    { db' with env := db.env, rules := db.rules }

end Egglog
