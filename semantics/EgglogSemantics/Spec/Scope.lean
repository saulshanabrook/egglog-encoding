import Mathlib.Logic.Function.Basic
import EgglogSemantics.Spec.Term

/-!
# The front end's static checks

Six checks: `Scoped` — every variable used is bound; `Evaluable` — every applied name is a
declared constructor; `SetLegal` — no `set` writes a constructor; `WidthOk` — every
application carries its declaration's column counts; `DeclsFresh` — no name is declared
twice; `MergeDeclared` — every name a `:merge` applies is declared or a primitive.
`Scoped` threads a `Scope`, extended by a `let` and by a query; the other five thread a
`Signature`, moved only by `Cmd.sigBind`.
-/

namespace Egglog

/-! ### Scope -/

/-- The variables in scope. -/
abbrev Scope := List Var

/-- Every variable of `e` is in scope. -/
def Expr.Scoped (e : Expr) (Γ : Scope) : Prop := ∀ v ∈ e.vars, v ∈ Γ

/-- `e` is an application. Query facts and `expr` actions are restricted to applications;
an `.eq` fact is not. -/
def Expr.IsApp : Expr → Prop
  | .app _ _ => True
  | _ => False

/-- A query fact carries the application restriction and nothing else: a fact never fails
to scope, and what it binds is `Query.bind`. A `.values` head is unconstrained. -/
def Pattern.Scoped : Pattern → Prop
  | .expr e => e.IsApp
  | .eq _ _ => True
  | .values _ _ _ => True

/-- An action scopes when each expression it evaluates does, plus the application
restriction on a bare `expr`. -/
def Action.Scoped : Action → Scope → Prop
  | .expr e, Γ => e.IsApp ∧ e.Scoped Γ
  | .letBind _ e, Γ => e.Scoped Γ
  | .union e₁ e₂, Γ => e₁.Scoped Γ ∧ e₂.Scoped Γ
  | .set _ args out, Γ => (∀ e ∈ args, e.Scoped Γ) ∧ ∀ e ∈ out, e.Scoped Γ

/-- The scope after an action: only a `let` extends it, and it may shadow. -/
def Action.bind : Action → Scope → Scope
  | .letBind v _, Γ => v :: Γ
  | _, Γ => Γ

/-- The scope a query's patterns bind. -/
def Query.bind (q : Query) (Γ : Scope) : Scope := Γ ∪ Query.vars q

/-- The scope after a command: only a top-level `let` extends it. -/
def Cmd.bind : Cmd → Scope → Scope
  | .action a, Γ => a.bind Γ
  | _, Γ => Γ

/-- Each action in the scope the earlier ones leave. -/
@[simp] def Actions.Scoped : List Action → Scope → Prop
  | [], _ => True
  | a :: as, Γ => a.Scoped Γ ∧ Actions.Scoped as (a.bind Γ)

/-- Its facts, then its head in the scope the query binds. -/
@[simp] def Rule.Scoped (r : Rule) (Γ : Scope) : Prop :=
  (∀ p ∈ r.query, p.Scoped) ∧ Actions.Scoped r.actions (Query.bind r.query Γ)

/-- A `:merge` body is walked into by `MergeDeclared` alone: it runs in the environment
`mergeEnv` builds rather than in the ambient context, so `Scoped`, `Evaluable` and
`SetLegal` all say nothing about one. -/
@[simp] def Cmd.Scoped : Cmd → Scope → Prop
  | .action a, Γ => a.Scoped Γ
  | .rule r, Γ => r.Scoped Γ
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl _ _, _ => True

/-- Each command in the scope the earlier ones leave. -/
@[simp] def Program.Scoped : Program → Scope → Prop
  | [], _ => True
  | c :: cs, Γ => c.Scoped Γ ∧ Program.Scoped cs (c.bind Γ)

/-- A program with no free variables: `Program.Scoped` from the empty scope. -/
def WellScoped (p : Program) : Prop := Program.Scoped p []

/-! ### Evaluability

`Scoped` is not enough for `Expr.eval` to return a term: an application may be a *lookup*
or a *primitive*. `Evaluable` rules both out. -/

/-- The signature after a command: only a declaration writes it, as in `CmdStep`. -/
def Cmd.sigBind : Cmd → Signature → Signature
  | .decl f d, sig => Function.update sig f (some d)
  | _, sig => sig

/-- Every application in `e` **builds**: its head is a declared constructor and not a
primitive, so evaluating `e` cannot get stuck on it. -/
def Expr.Evaluable (e : Expr) (sig : Signature) : Prop :=
  ∀ f ∈ e.fns, Prim.ofName f = none ∧ sig.IsCtor f

/-- `Action.Scoped`'s companion: every expression the action evaluates builds, and a
`union` operand is an application — the strongest sound stand-in for egglog's eq-sort
requirement, which `evalAction` refuses dynamically. A variable operand may hold a literal,
since a query binds one under a literal argument, so no check reading the expression alone
admits it. -/
def Action.Evaluable : Action → Signature → Prop
  | .expr e, sig => e.Evaluable sig
  | .letBind _ e, sig => e.Evaluable sig
  | .union e₁ e₂, sig => (e₁.IsApp ∧ e₁.Evaluable sig) ∧ e₂.IsApp ∧ e₂.Evaluable sig
  | .set _ args out, sig => (∀ e ∈ args, e.Evaluable sig) ∧ ∀ e ∈ out, e.Evaluable sig

@[simp] def Actions.Evaluable : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Evaluable sig ∧ Actions.Evaluable as sig

/-- Nothing is asked of a query fact, which is matched rather than evaluated. -/
@[simp] def Rule.Evaluable (r : Rule) (sig : Signature) : Prop :=
  Actions.Evaluable r.actions sig

@[simp] def Cmd.Evaluable : Cmd → Signature → Prop
  | .action a, sig => a.Evaluable sig
  | .rule r, sig => r.Evaluable sig
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl _ _, _ => True

/-- Each command in the signature the earlier ones leave. -/
@[simp] def Program.Evaluable : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.Evaluable sig ∧ Program.Evaluable cs (c.sigBind sig)

/-! ### `set` legality -/

/-- `(set (f …) …)` is legal only when `f` is a declared `:merge` or `:no-merge` function.
This decides *which* width an entry is held to; `Action.WidthOk` supplies the column
counts, and only the two together keep every entry the width `FnDecl.entryWidth` gives
it. Alone, this says nothing about an entry no `set` wrote. -/
def Action.SetLegal : Action → Signature → Prop
  | .set f _ _, sig => sig.mergeOf f ≠ none
  | _, _ => True

@[simp] def Actions.SetLegal : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.SetLegal sig ∧ Actions.SetLegal as sig

@[simp] def Rule.SetLegal (r : Rule) (sig : Signature) : Prop :=
  Actions.SetLegal r.actions sig

@[simp] def Cmd.SetLegal : Cmd → Signature → Prop
  | .action a, sig => a.SetLegal sig
  | .rule r, sig => r.SetLegal sig
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl _ _, _ => True

@[simp] def Program.SetLegal : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.SetLegal sig ∧ Program.SetLegal cs (c.sigBind sig)

/-! ### Column widths

egglog fixes a function's column counts at its declaration and checks every use against
them: `constraint.rs`'s `get_atom_application_constraints`, raised as `TypeError::Arity` by
the same pass, on the same node, that raises `SetConstructorDisallowed`. So it belongs
beside `SetLegal` rather than inside `Evaluable`, which structurally could not say it —
`Evaluable` quantifies over `Expr.fns`, a list of *names* that has lost the application
structure. -/

mutual

/-- Every application in `e` carries the argument count its declaration fixes. A name with
no entry has nothing to disagree with; that a program declares what it applies is
`Evaluable`'s business. -/
def Expr.WidthOk : Expr → Signature → Prop
  | .lit _, _ => True
  | .var _, _ => True
  | .app f args, sig =>
      (∀ d, sig f = some d → args.length = d.arity) ∧ Expr.WidthOkList args sig

/-- `Expr.WidthOk` over an argument list. -/
def Expr.WidthOkList : List Expr → Signature → Prop
  | [], _ => True
  | e :: es, sig => Expr.WidthOk e sig ∧ Expr.WidthOkList es sig

end

/-- `Action.SetLegal`'s companion: a `set` fills the declared key and value columns, so the
entry it records is `FnDecl.entryWidth` wide. -/
def Action.WidthOk : Action → Signature → Prop
  | .expr e, sig => e.WidthOk sig
  | .letBind _ e, sig => e.WidthOk sig
  | .union e₁ e₂, sig => e₁.WidthOk sig ∧ e₂.WidthOk sig
  | .set f args out, sig =>
      (∀ d, sig f = some d → args.length = d.arity ∧ out.length = d.outArity) ∧
        Expr.WidthOkList args sig ∧ Expr.WidthOkList out sig

@[simp] def Actions.WidthOk : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.WidthOk sig ∧ Actions.WidthOk as sig

/-- Nothing is asked of a query fact, which is matched rather than evaluated. -/
@[simp] def Rule.WidthOk (r : Rule) (sig : Signature) : Prop :=
  Actions.WidthOk r.actions sig

/-- One result expression per value column: `res` is what `MergeStep` writes into them.
This is the one check besides `MergeDeclared` that walks into a `:merge`, for the reason
`MergeDeclared`'s own heading gives — the body and `res` are where a merge writes. -/
@[simp] def MergeSpec.WidthOk : MergeSpec → Nat → Signature → Prop
  | .merge body res, n, sig =>
      res.length = n ∧ Actions.WidthOk body sig ∧ Expr.WidthOkList res sig
  | .noMerge, _, _ => True

/-- Asked of the signature the declaration **installs**, as `Cmd.MergeDeclared` and unlike
`Cmd.DeclFresh`, so a `:merge` may name the function it resolves. -/
@[simp] def Cmd.WidthOk : Cmd → Signature → Prop
  | .action a, sig => a.WidthOk sig
  | .rule r, sig => r.WidthOk sig
  | .run _, _ => True
  | .saturate _, _ => True
  | .decl f d, sig => ∀ ms ∈ d.merge, ms.WidthOk d.outArity ((Cmd.decl f d).sigBind sig)

/-- Each command in the signature the earlier ones leave, as `Program.SetLegal`. -/
@[simp] def Program.WidthOk : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.WidthOk sig ∧ Program.WidthOk cs (c.sigBind sig)

/-! ### Freshness of a declaration

A redeclaration changes what the signature says of a name the state already has terms of,
breaking `Database.DeclaredTerms`. -/

@[simp] def Cmd.DeclFresh : Cmd → Signature → Prop
  | .decl f _, sig => sig f = none
  | .action _, _ => True
  | .rule _, _ => True
  | .run _, _ => True
  | .saturate _, _ => True

/-- Each command is asked **before** `Cmd.sigBind` installs its declaration; asked after,
the check would read back `Function.update`'s own entry and always fail. -/
@[simp] def Program.DeclsFresh : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.DeclFresh sig ∧ Program.DeclsFresh cs (c.sigBind sig)

/-! ### Declaredness of a `:merge`

The one check that walks into a `:merge`. `Evaluable` is the wrong demand there: a merge
body is where primitives are legal, and it may `set` another merge function. -/

/-- Every name applied in `e` is a primitive or a declared function, of any kind. -/
def Expr.Declared (e : Expr) (sig : Signature) : Prop :=
  ∀ f ∈ e.fns, Prim.ofName f ≠ none ∨ sig f ≠ none

/-- A `set` head must be declared outright: a primitive has no table. -/
def Action.Declared : Action → Signature → Prop
  | .expr e, sig => e.Declared sig
  | .letBind _ e, sig => e.Declared sig
  | .union e₁ e₂, sig => e₁.Declared sig ∧ e₂.Declared sig
  | .set f args out, sig =>
      sig f ≠ none ∧ (∀ e ∈ args, e.Declared sig) ∧ ∀ e ∈ out, e.Declared sig

@[simp] def Actions.Declared : List Action → Signature → Prop
  | [], _ => True
  | a :: as, sig => a.Declared sig ∧ Actions.Declared as sig

/-- `.noMerge` runs nothing. -/
@[simp] def MergeSpec.Declared : MergeSpec → Signature → Prop
  | .merge body res, sig => Actions.Declared body sig ∧ ∀ e ∈ res, e.Declared sig
  | .noMerge, _ => True

/-- Asked of the signature the declaration **installs**, so a `:merge` may name the function
it resolves. The opposite of `Cmd.DeclFresh`, which is asked before. -/
@[simp] def Cmd.MergeDeclared : Cmd → Signature → Prop
  | .decl f d, sig => ∀ ms ∈ d.merge, ms.Declared ((Cmd.decl f d).sigBind sig)
  | .action _, _ => True
  | .rule _, _ => True
  | .run _, _ => True
  | .saturate _, _ => True

@[simp] def Program.MergeDeclared : Program → Signature → Prop
  | [], _ => True
  | c :: cs, sig => c.MergeDeclared sig ∧ Program.MergeDeclared cs (c.sigBind sig)

/-! ### Union-freedom

The one check that reads no signature, because it is about *positions* rather than names:
where a program may assert an equation. `Action.union` is the only action that asserts one
between distinct terms — every other write goes through `Database.addTerm`, which records
reflexive pairs alone — so a program with none keeps every state it reaches **diagonal**,
and on a diagonal state nothing is congruent to anything but itself. That is what makes
`Database.Recorded` and `Database.Contained` agree there, which is one of the two things
`Proofs/Merge.lean`'s two `Recorded` transports can be given; `Database.Diag` is the
state-level reading and `Proofs/Merge.lean` carries it. The other is `OrderingFree` below,
and neither condition implies the other.

It walks into a rule and into a `:merge`, since a `union` runs in either. -/

/-- The action that asserts an equation between distinct terms, ruled out. -/
def Action.UnionFree : Action → Prop
  | .union _ _ => False
  | _ => True

@[simp] def Actions.UnionFree : List Action → Prop
  | [] => True
  | a :: as => a.UnionFree ∧ Actions.UnionFree as

@[simp] def Rule.UnionFree (r : Rule) : Prop := Actions.UnionFree r.actions

/-- `.noMerge` runs nothing, and `res` is evaluated rather than run. -/
@[simp] def MergeSpec.UnionFree : MergeSpec → Prop
  | .merge body _ => Actions.UnionFree body
  | .noMerge => True

/-- A declaration is union-free when its `:merge` body is: the body is what a collision
runs. -/
def FnDecl.UnionFree (d : FnDecl) : Prop := ∀ ms ∈ d.merge, ms.UnionFree

/-- Every declared function's `:merge` body is union-free. Read of a *signature* because a
`MergeStep` reads the body it runs from one. -/
def Signature.UnionFree (sig : Signature) : Prop := ∀ f d, sig f = some d → d.UnionFree

@[simp] def Cmd.UnionFree : Cmd → Prop
  | .action a => a.UnionFree
  | .rule r => r.UnionFree
  | .run _ => True
  | .saturate _ => True
  | .decl _ d => d.UnionFree

/-- No signature threading: which actions a command carries does not depend on what is
declared. -/
@[simp] def Program.UnionFree : Program → Prop
  | [] => True
  | c :: cs => c.UnionFree ∧ Program.UnionFree cs

/-! ### Ordering-freedom

The second condition on *positions* rather than names, and the alternative to union-freedom:
where a program may apply a **choice** primitive. `ordering-min`/`ordering-max` pick between
two terms by `Term.blt`, a structural order, where egglog picks by e-class id, so they are
the one part of `Expr.eval` that is not stable under congruence — `union (f 1) (g 1)` sends
`ordering-min (f 1) (f 2)` to `f 1` and `ordering-min (g 1) (f 2)` to `f 2`, which are not
congruent. `min`/`max` are **not** excluded: they answer only on literals, and
`Cong.eq_of_isLit` makes a literal's class a singleton, so `Prim.apply_cong` is stability
for them.

It walks into a rule — both its query, which evaluates its patterns, and its head — and
into a `:merge`, since a body and its result are evaluated too. -/

/-- No application in `e` names a choice primitive. -/
def Expr.OrderingFree (e : Expr) : Prop :=
  ∀ f ∈ e.fns, Prim.ofName f ≠ some .orderingMin ∧ Prim.ofName f ≠ some .orderingMax

/-- `Expr.OrderingFree` over an argument list. Stated on `Expr.fnsList` rather than
pointwise because that is what the evaluation induction reads. -/
def Expr.OrderingFreeList (es : List Expr) : Prop :=
  ∀ f ∈ Expr.fnsList es, Prim.ofName f ≠ some .orderingMin ∧ Prim.ofName f ≠ some .orderingMax

/-- A query pattern is evaluated, so it carries the condition too. -/
def Pattern.OrderingFree : Pattern → Prop
  | .expr e => e.OrderingFree
  | .eq e₁ e₂ => e₁.OrderingFree ∧ e₂.OrderingFree
  | .values vs _ as => Expr.OrderingFreeList vs ∧ Expr.OrderingFreeList as

def Action.OrderingFree : Action → Prop
  | .expr e => e.OrderingFree
  | .letBind _ e => e.OrderingFree
  | .union e₁ e₂ => e₁.OrderingFree ∧ e₂.OrderingFree
  | .set _ args out => Expr.OrderingFreeList args ∧ Expr.OrderingFreeList out

@[simp] def Actions.OrderingFree : List Action → Prop
  | [] => True
  | a :: as => a.OrderingFree ∧ Actions.OrderingFree as

/-- Both halves: a query pattern is evaluated against the database, a head action against
the substitution. -/
@[simp] def Rule.OrderingFree (r : Rule) : Prop :=
  (∀ p ∈ r.query, p.OrderingFree) ∧ Actions.OrderingFree r.actions

/-- `.noMerge` runs nothing; a `:merge` evaluates both its body and its result. -/
@[simp] def MergeSpec.OrderingFree : MergeSpec → Prop
  | .merge body res => Actions.OrderingFree body ∧ Expr.OrderingFreeList res
  | .noMerge => True

def FnDecl.OrderingFree (d : FnDecl) : Prop := ∀ ms ∈ d.merge, ms.OrderingFree

/-- Read of a *signature*, because a `MergeStep` reads the body it runs from one, as
`Signature.UnionFree`. -/
def Signature.OrderingFree (sig : Signature) : Prop :=
  ∀ f d, sig f = some d → d.OrderingFree

@[simp] def Cmd.OrderingFree : Cmd → Prop
  | .action a => a.OrderingFree
  | .rule r => r.OrderingFree
  | .run _ => True
  | .saturate _ => True
  | .decl _ d => d.OrderingFree

/-- No signature threading, as `Program.UnionFree`. -/
@[simp] def Program.OrderingFree : Program → Prop
  | [] => True
  | c :: cs => c.OrderingFree ∧ Program.OrderingFree cs

end Egglog
