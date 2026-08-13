import EgglogSemantics.Spec.Scope

/-!
# The front end's static checks

Two checks a real egglog front end runs before a program means anything, transcribed from
`constraint.rs` and `typechecking.rs`. They are here rather than in `Spec/` because they
say what egglog *rejects*, not what a program *means*: nothing in the semantics consumes
them, and their consumers are the differential test (`DiffTest.lean`'s `writeCase`,
`Tests/Egg.lean`, `Tests/Examples.lean`) plus the counterexamples that show they are not
redundant with `Spec/Scope.lean`'s `SetLegal`.

Both are `Bool`, unlike `Scoped` and `SetLegal`, so that the difftest's check and the
statement a proof would use are the same definition rather than two that can drift.
-/

namespace Egglog
/-! ### Arity

egglog fixes a function's column counts when it is declared and checks every use against
them: an expression or a query fact appends one fresh output variable, so it needs
`outArity f = 1`; a `set` appends its value list; the row atom `Pattern.values` appends
the values it reads. A declaration is checked too — a `:merge` result has one expression
per value column, and a constructor has exactly one value column.

A name with no entry has no declared column counts, so nothing here constrains it. That a
program must *have* declared what it applies is `Program.Evaluable`'s business.

`PLAN.md`, "Arity checking", is the derivation from egglog's single lowered-atom equation,
what it deliberately leaves out, and the one place this is stricter than egglog.
-/

mutual

/-- Every application of a declared function inside `e` has its declared key arity and one
value column. A name with no entry has nothing to disagree with. -/
def Expr.arityOk : Expr → Signature → Bool
  | .lit _, _ => true
  | .var _, _ => true
  | .app f args, sig =>
      (match sig f with
       | none => true
       | some d => args.length == d.arity && d.outArity == 1) && Expr.arityOkList args sig

/-- `Expr.arityOk` over an argument list. -/
def Expr.arityOkList : List Expr → Signature → Bool
  | [], _ => true
  | e :: es, sig => Expr.arityOk e sig && Expr.arityOkList es sig

end

/-- A query fact. `.expr` and `.eq` hold ordinary expressions, which egglog lowers with a
single fresh output variable; the row atom names a declared function and its two column
counts directly. -/
def Pattern.arityOk : Pattern → Signature → Bool
  | .expr e, sig => e.arityOk sig
  | .eq e₁ e₂, sig => e₁.arityOk sig && e₂.arityOk sig
  | .values vs f as, sig =>
      (match sig f with
       | none => false
       | some d => as.length == d.arity && as.length + vs.length == d.entryWidth)
        && Expr.arityOkList vs sig && Expr.arityOkList as sig

/-- An action. A `set`'s key and value counts are checked together; a `set` on a name with
no entry needs no case here, `Action.SetLegal` already rejects it. -/
def Action.arityOk : Action → Signature → Bool
  | .expr e, sig => e.arityOk sig
  | .letBind _ e, sig => e.arityOk sig
  | .union e₁ e₂, sig => e₁.arityOk sig && e₂.arityOk sig
  | .set f args out, sig =>
      (match sig f with
       | none => true
       | some d => args.length == d.arity && out.length == d.outArity)
        && Expr.arityOkList args sig && Expr.arityOkList out sig

/-- Every action in the list. Like `Actions.SetLegal`, no threading: no action changes the
signature. -/
def Actions.arityOk (as : List Action) (sig : Signature) : Bool :=
  as.all (Action.arityOk · sig)

/-- A rule's query and head. -/
def Rule.arityOk (r : Rule) (sig : Signature) : Bool :=
  r.query.all (Pattern.arityOk · sig) && Actions.arityOk r.actions sig

/-- A merge specification, against the declaration's `outArity` value columns. `.noMerge`
has no result to check. -/
def MergeSpec.arityOk : MergeSpec → Nat → Signature → Bool
  | .noMerge, _, _ => true
  | .merge body res, outArity, sig =>
      res.length == outArity && Actions.arityOk body sig && res.all (Expr.arityOk · sig)

/-- A declaration's own value columns: a constructor has exactly one, which is egglog
forbidding it a tuple output; a merge function is checked against its result. -/
def FnDecl.arityOk (d : FnDecl) (sig : Signature) : Bool :=
  match d.merge with
  | none => d.outArity == 1
  | some m => m.arityOk d.outArity sig

/-- A command. A declaration's merge body sees the signature the declaration itself
installs, so it may write the function's own table. -/
def Cmd.arityOk : Cmd → Signature → Bool
  | .action a, sig => a.arityOk sig
  | .rule r, sig => r.arityOk sig
  | .run _, _ => true
  | .saturate _, _ => true
  | .decl f d, sig => d.arityOk ((Cmd.decl f d).sigBind sig)

/-- `Program.SetLegal`'s shape: each command against the signature the earlier ones
leave. -/
def Program.arityOk : Program → Signature → Bool
  | [], _ => true
  | c :: cs, sig => c.arityOk sig && Program.arityOk cs (c.sigBind sig)

/-- `Program.arityOk` as a proposition, to sit beside `Program.SetLegal`. -/
def Program.ArityOk (p : Program) (sig : Signature) : Prop := p.arityOk sig = true

/-- The arity check from the empty signature, as `WellScoped` is the scope check from the
empty scope. -/
def WellArity (p : Program) : Prop := Program.ArityOk p (fun _ => none)

/-! ### Reading in an action

**All reading happens in the query; all writing happens in the actions.** An application
of a non-constructor is a *lookup* — it reads a recorded row rather than building a term —
and this section says no expression anywhere in a program contains one. The single place
a program may read is then the query atom `Pattern.values`, whose function name is not an
expression position at all.

A lookup is an application of a declared merge function. A **primitive** needs a case of
its own: egglog resolves one out of a table that is already populated, so it is never
declared, and `Signature.IsCtor` — which requires declaration — would otherwise reject
`(min old new)`. This is `Expr.eval`'s own order, primitives first.

An **undeclared** name fails this check too, which is a second thing it now says: it is not
a read, it is a name that means nothing. `Spec/Scope.lean`'s `Evaluable` rejects it for the
same reason.

`Spec/Scope.lean`'s `Evaluable` is the semantics-side half of this: it constrains only
the positions `Expr.eval` reaches, and it also excludes primitives, which this check
deliberately admits.

What it buys is the thing the whole relational layer was paying for: with nothing able to
read but a query atom, `Expr.eval` needs no `lookup` constructor, is deterministic, and
consults the database only for its signature.

`Rule.noLookup`'s action half is egglog's own `check_no_function_lookups_in_actions` and
everything else is ours. `PLAN.md`, "Reading is a query atom", lists the three positions
egglog allows a read and this does not, and what the restriction already caught in
`Encoding/Encode.lean`.
-/

mutual

/-- No application inside `e` reads a row: every function it names is a declared
constructor or a primitive. -/
def Expr.noLookup : Expr → Signature → Bool
  | .lit _, _ => true
  | .var _, _ => true
  | .app f args, sig =>
      ((Prim.ofName f).isSome || decide (sig.IsCtor f)) && Expr.noLookupList args sig

/-- `Expr.noLookup` over an argument list. -/
def Expr.noLookupList : List Expr → Signature → Bool
  | [], _ => true
  | e :: es, sig => Expr.noLookup e sig && Expr.noLookupList es sig

end

/-- An action, in every expression position egglog's check walks. -/
def Action.noLookup : Action → Signature → Bool
  | .expr e, sig => e.noLookup sig
  | .letBind _ e, sig => e.noLookup sig
  | .union e₁ e₂, sig => e₁.noLookup sig && e₂.noLookup sig
  | .set _ args out, sig => Expr.noLookupList args sig && Expr.noLookupList out sig

/-- Every action in the list. No threading: no action changes the signature. -/
def Actions.noLookup (as : List Action) (sig : Signature) : Bool :=
  as.all (Action.noLookup · sig)

/-- A `:merge` body and its result columns. `.noMerge` has no body. -/
def MergeSpec.noLookup : MergeSpec → Signature → Bool
  | .noMerge, _ => true
  | .merge body res, sig => Actions.noLookup body sig && res.all (Expr.noLookup · sig)

/-- A query fact. `.values` is the read, so only its *operands* are checked; `.expr` and
`.eq` are evaluated, so they must name constructors throughout. -/
def Pattern.noLookup : Pattern → Signature → Bool
  | .expr e, sig => e.noLookup sig
  | .eq e₁ e₂, sig => e₁.noLookup sig && e₂.noLookup sig
  | .values vs _ as, sig => Expr.noLookupList vs sig && Expr.noLookupList as sig

/-- A rule's query and head. The head half is exactly
`check_no_function_lookups_in_actions`; the query half is this model's, and says a read is
an atom rather than something nested inside an expression egglog would flatten. -/
def Rule.noLookup (r : Rule) (sig : Signature) : Bool :=
  r.query.all (Pattern.noLookup · sig) && Actions.noLookup r.actions sig

/-- A command. A declaration's merge body sees the signature the declaration installs, as
in `Cmd.arityOk`, so a body may `set` its own table — a write — while reading it is a
lookup like any other. -/
def Cmd.noLookup : Cmd → Signature → Bool
  | .action a, sig => a.noLookup sig
  | .rule r, sig => r.noLookup sig
  | .run _, _ => true
  | .saturate _, _ => true
  | .decl f d, sig =>
      match d.merge with
      | none => true
      | some m => m.noLookup ((Cmd.decl f d).sigBind sig)

/-- Each command against the signature the earlier ones leave, as `Program.arityOk`. -/
def Program.noLookup : Program → Signature → Bool
  | [], _ => true
  | c :: cs, sig => c.noLookup sig && Program.noLookup cs (c.sigBind sig)

/-- `Program.noLookup` as a proposition, to sit beside `Program.SetLegal`. -/
def Program.NoLookup (p : Program) (sig : Signature) : Prop := p.noLookup sig = true

/-- The read check from the empty signature: every read is a `Pattern.values` atom. What a
front end demands in full is `WellArity p` and `ReadsAreAtoms p` together with
`Spec/Scope.lean`'s four: `WellScoped p`, `p.Evaluable sig`, `p.SetLegal sig` and
`p.DeclsFresh sig`. -/
def ReadsAreAtoms (p : Program) : Prop := Program.NoLookup p (fun _ => none)

end Egglog
