import EgglogSemantics.Spec.Step

/-!
# Scope checking

Ports the Redex `typed-expr`, `typed-query-expr`, `typed-action`, `typed-pattern`,
`typed-query`, `typed-actions`, `typed-rule` and `typed-program`.

The Redex has a single type, `no-type`, so its `TypeEnv` is a list of variables and
its judgments check nothing but scope. `Scope` is that list of variables with the
type erased; real sorts arrive with `:merge` functions, which need base-sorted
outputs (`PLAN.md`, M9).

Two things the Redex's judgments make relational are functions here:

* `typed-query-expr` always succeeds — its variable rule adds an unbound variable
  rather than rejecting it — so what it computes is just the scope extended with
  the pattern's variables. `Query.bind` is that.
* `typed-action`'s `let` rule carries the side condition
  `(not (member (TypeBinding ...) (TypeBinding ...)))`, which asks whether a *list*
  of bindings occurs as an *element* of itself. That is never true, so the negation
  always holds and the condition is vacuous; a `let` may shadow.

The payoff is `runProgram_isSome`: a well-scoped program never gets stuck.
`runRules` cannot get stuck either way — it drops firings whose actions fail — so
the corresponding statement about rules is
`evalLocalActions_isSome_of_scoped`: a well-scoped rule contributes on every
substitution its query admits.
-/

namespace Egglog
/-- The variables in scope. The Redex `TypeEnv`, with its one type erased. -/
abbrev Scope := List Var

/-- The scope describes the environment's domain exactly. Maintained across a run by
`runProgram_isSome`. -/
def Scope.Models (Γ : Scope) (σ : Env) : Prop := ∀ v, v ∈ Γ ↔ v ∈ Env.dom σ

/-- The Redex `typed-expr`: every variable of `e` is in scope. -/
def Expr.Scoped (e : Expr) (Γ : Scope) : Prop := ∀ v ∈ e.vars, v ∈ Γ

/-- `e` is a constructor application.

Query facts and `expr` actions are required to be applications, which the Redex does not
require: there a bare variable is a legal fact, matching any term, and a legal action,
adding one already present. egglog's grammar admits neither, so allowing them would leave
every later phase handling a case the real system cannot express. This is the one place
`WellScoped` is deliberately stricter than the Redex `typed-program`. -/
def Expr.IsApp : Expr → Prop
  | .app _ _ => True
  | _ => False

instance (e : Expr) : Decidable e.IsApp := by cases e <;> simp only [Expr.IsApp] <;>
  infer_instance

/-- The scope a query's patterns bind, i.e. what the Redex `typed-query` returns. -/
def Query.bind (q : Query) (Γ : Scope) : Scope := Γ ∪ Query.vars q

/-- A query fact. Only the application restriction; the Redex `typed-query` never fails,
and what it computes is `Query.bind`. -/
def Pattern.Scoped : Pattern → Prop
  | .expr e => e.IsApp
  | .eq _ _ => True
  | .values _ _ _ => True

/-- The Redex `typed-action`, minus its vacuous side condition and plus the application
restriction on a bare `expr`. -/
def Action.Scoped : Action → Scope → Prop
  | .expr e, Γ => e.IsApp ∧ e.Scoped Γ
  | .letBind _ e, Γ => e.Scoped Γ
  | .union e₁ e₂, Γ => e₁.Scoped Γ ∧ e₂.Scoped Γ
  | .set _ args out, Γ => (∀ e ∈ args, e.Scoped Γ) ∧ ∀ e ∈ out, e.Scoped Γ

/-- The scope after an action: only a `let` extends it. -/
def Action.bind : Action → Scope → Scope
  | .expr _, Γ => Γ
  | .letBind v _, Γ => v :: Γ
  | .union _ _, Γ => Γ
  | .set _ _ _, Γ => Γ

/-- The Redex `typed-actions`: each action is scoped in what the earlier ones bind. -/
def Actions.Scoped : List Action → Scope → Prop
  | [], _ => True
  | a :: as, Γ => a.Scoped Γ ∧ Actions.Scoped as (a.bind Γ)

/-- The scope after a sequence of actions. -/
def Actions.bind : List Action → Scope → Scope
  | [], Γ => Γ
  | a :: as, Γ => Actions.bind as (a.bind Γ)

/-- The Redex `typed-rule`: the actions are scoped in the query's bindings. -/
def Rule.Scoped (r : Rule) (Γ : Scope) : Prop :=
  (∀ p ∈ r.query, p.Scoped) ∧ Actions.Scoped r.actions (Query.bind r.query Γ)

/-- The Redex `typed-program`, one command at a time. -/
def Cmd.Scoped : Cmd → Scope → Prop
  | .action a, Γ => a.Scoped Γ
  | .rule r, Γ => r.Scoped Γ
  | .run, _ => True
  | .decl _ _, _ => True

/-- The scope after a command: only a top-level `let` extends it. -/
def Cmd.bind : Cmd → Scope → Scope
  | .action a, Γ => a.bind Γ
  | .rule _, Γ => Γ
  | .run, Γ => Γ
  | .decl _ _, Γ => Γ

/-- The Redex `typed-program`. -/
def Program.Scoped : Program → Scope → Prop
  | [], _ => True
  | c :: cs, Γ => c.Scoped Γ ∧ Program.Scoped cs (c.bind Γ)

/-- The scope after a program. -/
def Program.bind : Program → Scope → Scope
  | [], Γ => Γ
  | c :: cs, Γ => Program.bind cs (c.bind Γ)

/-- A program with no free variables: the Redex `(typed-program Program TypeEnv)`
starting from the empty environment. -/
def WellScoped (p : Program) : Prop := Program.Scoped p []

/-! ### `set` legality

A second static check, additive and deliberately kept apart from `Scoped`. Both are
things a real front end rejects in one pass, and folding this into `Action.Scoped` is
where it eventually belongs.

It is separate for now because of the parameter. `Scoped` relates an `Action` to a
`Scope`; this relates it to a `Signature`. Threading a signature through
`Actions.Scoped`, `Rule.Scoped`, `Cmd.Scoped` and `Program.Scoped` would put a signature
argument on every lemma in `Proofs/Scope.lean` and a new hypothesis on
`exec_toDatabase`, none of which the scope theorems have any use for. Fold the two
together once `Program.Scoped` needs the signature for its own sake — M9's sort
discipline (`PLAN.md`, M9 point 4) is that reason, since a merge function's output has a
base sort. Until then the pair to carry is `WellScoped p ∧ p.SetLegal sig`.
-/
/-- `(set (f …) …)` is legal only when `f` is not a constructor.

egglog rejects a `set` on a constructor while type-checking (`egglog/src/constraint.rs`,
"Check that we're not trying to set a constructor"), and constructors are exactly the
functions whose merge is `.union` — `Signature.mergeOf` sends an undeclared name there
too, so this covers the undeclared case as well.

It is what keeps `Database.CtorRows` an invariant. A `set` writes the row
`⟨f, as, [v]⟩` for whatever `v` its out expression denotes, and `Database.ctorRowsOf`
holds no such row unless `v` is `.app f as`. -/
def Action.SetLegal : Action → Signature → Prop
  | .expr _, _ => True
  | .letBind _ _, _ => True
  | .union _ _, _ => True
  | .set f _ _, sig => sig.mergeOf f ≠ MergeSpec.union

/-! A `Pattern.values` destructure has the same discipline and does not yet carry it:
egglog recognizes `(= (values v…) (f a…))` only when `f` is tuple-output, so a
destructure on a constructor is a type error there and meaningless here. Adding it means
extending `Rule.SetLegal` to the *query*, which currently reads only the head; the reason
to wait is that `Proofs/Step.lean`'s `CtorRows` chain is stated over the head alone and a
destructure writes nothing, so nothing is unsound in the meantime. -/
/-- Every action in the list is a legal `set`. Unlike `Actions.Scoped` this needs no
threading: no action changes the signature. -/
def Actions.SetLegal : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.SetLegal sig ∧ Actions.SetLegal as sig

/-- A rule is legal when its head is; a query writes nothing. -/
def Rule.SetLegal (r : Rule) (sig : Signature) : Prop := Actions.SetLegal r.actions sig

/-- The signature a command leaves behind. `Cmd.bind` for signatures instead of scopes,
and exactly what `stepCmd`'s `.decl` case does. -/
def Cmd.sigBind : Cmd → Signature → Signature
  | .decl f d, sig => Function.update sig f (some d)
  | _, sig => sig

/-- `Cmd.Scoped`'s companion for `set`. -/
def Cmd.SetLegal : Cmd → Signature → Prop
  | .action a, sig => a.SetLegal sig
  | .rule r, sig => r.SetLegal sig
  | .run, _ => True
  | .decl _ _, _ => True

/-- `Program.Scoped`'s companion for `set`: each command is checked against the
signature the earlier ones leave, as `Program.Scoped` checks against the scope they
leave. -/
def Program.SetLegal : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.SetLegal sig ∧ Program.SetLegal cs (c.sigBind sig)

/-- `c` declares only constructors.

Separate from `SetLegal` because it constrains a different thing: `SetLegal` says what a
head may write, this says what the signature may become. `Database.CtorRows` needs both
— declaring a `:merge` function makes rows *already present* a `MergeStep` collision,
whose combined row need not be a constructor row, and no `set` is involved. -/
def Cmd.CtorDecl : Cmd → Prop
  | .decl _ d => d.merge = MergeSpec.union
  | _ => True

/-- Every declaration in the program declares a constructor. -/
def Program.CtorDecls (p : Program) : Prop := ∀ c ∈ p, c.CtorDecl

end Egglog
