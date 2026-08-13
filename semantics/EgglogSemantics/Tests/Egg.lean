import EgglogSemantics.Impl.Check
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Spec.Scope

/-!
# Emitting egglog source

Renders a `Program` as a `.egg` file so that the same program can be run by the Rust
implementation and the results compared (`PLAN.md`, "Differential testing"). The oracle
is `(print-size)`, which prints one row count per function — the same quantity
`FDatabase.rowCount` computes and `egglog/tests/files.rs` snapshots.

Two mismatches to keep in mind when generating programs.

The model is untyped, so the emitter invents a single sort `Math` and declares every
constructor it sees at the arity it is used with. A program that uses one name at two
arities is not expressible in egglog and must not be generated.

`Term.lit` is the same sort as an application here, while egglog's `i64` is a distinct
primitive sort — `1` and `(Num 1)` are interchangeable for us and not for egglog. Literals
are therefore emitted as-is and generated programs should avoid them, using nullary
constructors instead; the fragment loses nothing by it.
-/

namespace Egglog

/-! ### Rendering -/

mutual

/-- An expression as egglog source. -/
def Expr.toEgg : Expr → String
  | .lit (.int n) => toString n
  | .var v => v
  | .app f args => "(" ++ f ++ Expr.toEggArgs args ++ ")"

/-- `Expr.toEgg` over an argument list, each preceded by a space. -/
def Expr.toEggArgs : List Expr → String
  | [] => ""
  | e :: es => " " ++ e.toEgg ++ Expr.toEggArgs es

end

/-- One expression per value column, written as egglog's tuple form `(values e₀ e₁ …)`
when there is more than one and bare when there is exactly one. `Spec/Syntax.lean` takes
the list the tuple denotes, in `Action.set`, `MergeSpec.merge` and `Pattern.values`; this
is where the two notations meet. -/
def Expr.valuesToEgg : List Expr → String
  | [e] => e.toEgg
  | res => "(values " ++ String.intercalate " " (res.map Expr.toEgg) ++ ")"

/-- A query fact. `Pattern.values` is egglog's row atom, whose surface form depends on the
width: `(= v (f a…))` at one value column and `(= (values v…) (f a…))` at more, since
`values` is not a function name and egglog answers "Unbound function values" if the tuple
form is used on a one-column function. -/
def Pattern.toEgg : Pattern → String
  | .expr e => e.toEgg
  | .eq e₁ e₂ => "(= " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"
  | .values vs f as =>
      "(= " ++ Expr.valuesToEgg vs ++ " (" ++ f ++ Expr.toEggArgs as ++ "))"

def Action.toEgg : Action → String
  | .expr e => e.toEgg
  | .letBind v e => "(let " ++ v ++ " " ++ e.toEgg ++ ")"
  | .union e₁ e₂ => "(union " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"
  | .set f args out =>
      "(set (" ++ f ++ Expr.toEggArgs args ++ ") " ++ Expr.valuesToEgg out ++ ")"

/-- `:ruleset` is emitted only for a named ruleset: egglog's unnamed one is what a rule with
no `:ruleset` joins, so the empty name renders as nothing and the existing cases are
unchanged. -/
def Rule.toEgg (r : Rule) : String :=
  "(rule (" ++ String.intercalate " " (r.query.map Pattern.toEgg) ++ ") ("
    ++ String.intercalate " " (r.actions.map Action.toEgg) ++ ")"
    ++ (if r.ruleset = "" then "" else " :ruleset " ++ r.ruleset) ++ ")"

/-- The merged value, in egglog's tuple notation. Shared with `Action.set`. -/
abbrev MergeSpec.resultToEgg : List Expr → String := Expr.valuesToEgg

/-- A merge specification as egglog source. `.noMerge` is `:no-merge`; a constructor has
no merge specification and so never reaches here.

The block form is `:merge (<action>* <result>)` — the actions and the result are
*siblings* in one list, not two nested ones (`egglog/src/ast/parse.rs:531-569`, and
`egglog/tests/merge-action-block.egg`). The parse is disambiguated by whether the first
element is itself a list, which is why an empty body has to emit the bare result: an
expression always has an atom head, so `:merge (min old new)` reads as a result and
`:merge ((let s …) s)` as a block. -/
def MergeSpec.toEgg : MergeSpec → String
  | .noMerge => " :no-merge"
  | .merge [] res => " :merge " ++ MergeSpec.resultToEgg res
  | .merge body res =>
      " :merge (" ++ String.intercalate " " (body.map Action.toEgg) ++ " "
        ++ MergeSpec.resultToEgg res ++ ")"

/-- A `:merge` function's declaration.

**Sorts finally bite** (M9): egglog typechecks a `(function …)`, so a merge function
needs a real output sort. Keys are the one eq-sort `Math`; the output is `i64`, as
`tests/interval.egg` and `tests/merge-during-rebuild.egg` do. An eq-sorted output would
dodge the base sort, but then `ordering-min` has to render — and `Term.blt` is
*structural* where egglog's `ordering-min` is by insertion order, so the two would pick
different representatives. Row counts are per key class and would survive that; nothing
else would. Keeping keys eq-sorted also keeps `Term.lit` out of constructor arguments,
so this file's standing literal mismatch stays out of the way.

A multi-column output is a parenthesized sort list, `(i64 i64)`, as
`egglog/tests/tuple-output.egg` writes it. egglog accepts `(i64)` for one column too,
but the bare form is what every existing case renders and is left alone. -/
def FnDecl.toEgg (f : FnName) (d : FnDecl) (m : MergeSpec) : String :=
  let out := match d.outArity with
    | 1 => "i64"
    | _ => "(" ++ String.intercalate " " (List.replicate d.outArity "i64") ++ ")"
  "(function " ++ f ++ " (" ++ String.intercalate " " (List.replicate d.arity "Math")
    ++ ") " ++ out ++ m.toEgg ++ ")"

/-- A command as egglog source. A run of the *unnamed* ruleset is `(run 1)`, which is what
egglog's bare form means (`egglog/src/ast/parse.rs:834-864`); a named one carries its name.
A constructor declaration is folded into the `datatype` header and produces nothing; a
`:merge` declaration is its own command. -/
def Cmd.toEgg : Cmd → String
  | .action a => a.toEgg
  | .rule r => r.toEgg
  | .run R => if R = "" then "(run 1)" else "(run " ++ R ++ " 1)"
  | .saturate R => "(run-schedule (saturate " ++ (if R = "" then "(run)" else R) ++ "))"
  | .decl f d => match d.merge with
    | none => ""
    | some m => FnDecl.toEgg f d m

/-! ### Collecting the signature

The header has to declare every constructor, so the arities are read off the program's
uses rather than from `Signature`. That is also where `Program.ctorDecls` gets the model
side's declarations, so the two descriptions of a program's constructors cannot drift.

Two names must be kept out of the result, and for opposite reasons. A **declared `:merge`
function** has its own `function` command, and `Program.ctorArities` filters it. A
**primitive** has no declaration at all: `min`, `max`, `ordering-min` and `ordering-max`
are resolved by `Prim.ofName` before the signature is consulted, and egglog resolves them
out of a table that is already populated, so a `datatype` entry for one is rejected with
`Primitive min already declared.` `Program.fnArities` filters those, which also keeps them
out of `Program.fnNames` — a primitive is not a table and `(print-size)` never reports one.
-/

mutual

def Expr.fnArities : Expr → List (FnName × Nat)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args.length) :: Expr.fnAritiesL args

def Expr.fnAritiesL : List Expr → List (FnName × Nat)
  | [] => []
  | e :: es => e.fnArities ++ Expr.fnAritiesL es

end

def Pattern.fnArities : Pattern → List (FnName × Nat)
  | .expr e => e.fnArities
  | .eq e₁ e₂ => e₁.fnArities ++ e₂.fnArities
  | .values vs f as => (f, as.length) :: Expr.fnAritiesL vs ++ Expr.fnAritiesL as

def Action.fnArities : Action → List (FnName × Nat)
  | .expr e => e.fnArities
  | .letBind _ e => e.fnArities
  | .union e₁ e₂ => e₁.fnArities ++ e₂.fnArities
  | .set f args out => (f, args.length) :: Expr.fnAritiesL args ++ Expr.fnAritiesL out

/-- The names a merge specification applies. A `:merge` body is an expression position like
any other, so a constructor mentioned *only* there — `(set (Log (A)) old)` — still has to
reach the `datatype` header, and the function it `set`s still has to be a name the emitter
knows. -/
def MergeSpec.fnArities : MergeSpec → List (FnName × Nat)
  | .noMerge => []
  | .merge body res => body.flatMap Action.fnArities ++ Expr.fnAritiesL res

def Cmd.fnArities : Cmd → List (FnName × Nat)
  | .action a => a.fnArities
  | .rule r => (r.query.flatMap Pattern.fnArities) ++ (r.actions.flatMap Action.fnArities)
  | .run _ => []
  | .saturate _ => []
  | .decl f d => (f, d.arity) :: (d.merge.map MergeSpec.fnArities).getD []

/-- Every function the program uses, with its arity, deduplicated — **primitives
excluded**. A primitive is not a function of the program's signature: egglog has already
declared it, so emitting a `datatype` entry for one is an error and `(print-size)` never
reports a row count for one. -/
def Program.fnArities (p : Program) : List (FnName × Nat) :=
  ((p.flatMap Cmd.fnArities).filter fun fa => (Prim.ofName fa.1).isNone).dedup

/-- The names the program declares as merge functions. These get their own `function`
command and must be kept out of the `datatype`. -/
def Program.mergeNames (p : Program) : List FnName :=
  p.filterMap fun c => match c with
    | .decl f d => if d.merge.isSome then some f else none
    | _ => none

/-- The constructors: everything used that is not a declared `:merge` function. -/
def Program.ctorArities (p : Program) : List (FnName × Nat) :=
  p.fnArities.filter fun fa => fa.1 ∉ p.mergeNames

/-- Every name the program declares, whatever it declares it as. -/
def Program.declaredNames (p : Program) : List FnName :=
  p.filterMap fun c => match c with
    | .decl f _ => some f
    | _ => none

/-- A `(constructor …)` for every constructor the program applies and does not declare.

**Declaration is required** (`Signature.IsCtor`), so a program that applies a name nobody
declared gets stuck in `Expr.eval` and `execM` returns `none`. Generated programs are
written against the `datatype` header — which this file reads off the *uses* — so the model
side needs the same information as commands. This is that, and it is why the two sides
still agree: a constructor declaration renders as nothing (`Cmd.toEgg`), being folded into
the header the header check already emits. -/
def Program.ctorDecls (p : Program) : Program :=
  (p.ctorArities.filter fun fa => fa.1 ∉ p.declaredNames).map fun fa =>
    .decl fa.1 { arity := fa.2, outArity := 1, merge := none }

/-- The program with its constructors declared up front. What the difftest actually runs
and emits. -/
def Program.declared (p : Program) : Program := p.ctorDecls ++ p

/-! ### Which `set`s egglog will accept

`(set (f args…) v)` is legal only when `f` is a **function** — declared with `:merge` or
`:no-merge`. On a constructor it is a *type* error, raised while the command is
constraint-solved and so before that command or any later one runs
(`egglog/src/constraint.rs:862`, `TypeError::SetConstructorDisallowed`):

```
Cannot set constructor Wrap. Use `union` instead or declare Wrap as a function.
```

A `relation` is a constructor for this purpose and gives the same message. Checked here
rather than trusted, because a generator that grows a `set` action would otherwise start
emitting programs egglog throws out wholesale — the failure mode that once cost 34 of 60
random cases when the fragment allowed bare variables. -/

def Action.setTargets : Action → List FnName
  | .set f _ _ => [f]
  | _ => []

def MergeSpec.setTargets : MergeSpec → List FnName
  | .merge body _ => body.flatMap Action.setTargets
  | _ => []

def Cmd.setTargets : Cmd → List FnName
  | .action a => a.setTargets
  | .rule r => r.actions.flatMap Action.setTargets
  | .run _ => []
  | .saturate _ => []
  | .decl _ d => (d.merge.map MergeSpec.setTargets).getD []

/-- The names the program `set`s that egglog would refuse: everything not declared as a
merge function. Empty is the only acceptable value for a case the difftest emits. -/
def Program.illegalSets (p : Program) : List FnName :=
  (p.flatMap Cmd.setTargets).dedup.filter (· ∉ p.mergeNames)

/-! ### Which arities egglog will accept

Two halves, because the model declares only its `:merge` functions.

For a *declared* function, `Impl/Check.lean`'s `Cmd.arityOk` is the check — this only
walks the program threading `Cmd.sigBind` and renders the commands that fail, so the two
cannot drift the way `illegalSets` and `Action.SetLegal` can.

For an *undeclared* one there is no declaration to check against, and the constraint comes
from this file instead: `eggHeader` invents a `datatype` entry per `(name, arity)` pair, so
a name used at two arities emits two entries and egglog answers "Function already bound
{name}". -/

def Program.arityErrorsFrom : Program → Signature → List String
  | [], _ => []
  | c :: cs, sig =>
      (if c.arityOk sig then [] else [c.toEgg]) ++ Program.arityErrorsFrom cs (c.sigBind sig)

/-- The commands whose column counts egglog's typechecker would reject, rendered. Empty is
the only acceptable value for a case the difftest emits. -/
def Program.arityErrors (p : Program) : List String :=
  p.arityErrorsFrom (fun _ => none)

/-! ### Where a program may read

`Impl/Check.lean`'s "Reading in an action": no expression may apply a non-constructor,
because that is a *lookup*, and the only read is the query atom `Pattern.values`. Walked the
same way `arityErrorsFrom` walks the arity check, so the difftest and the specification
share one definition. -/

def Program.illegalReadsFrom : Program → Signature → List String
  | [], _ => []
  | c :: cs, sig =>
      (if c.noLookup sig then [] else [c.toEgg])
        ++ Program.illegalReadsFrom cs (c.sigBind sig)

/-- The commands containing a read that is not a `Pattern.values` atom, rendered. Empty is
the only acceptable value for a case the difftest emits. egglog rejects this in a rule head
only; the other positions are ours, and `Spec/Scope.lean` says why. -/
def Program.illegalReads (p : Program) : List String :=
  p.illegalReadsFrom (fun _ => none)

/-- The names the program uses at more than one key arity. `fnArities` is deduplicated on
the *pair*, so such a name is exactly one occurring twice in it. -/
def Program.arityConflicts (p : Program) : List FnName :=
  ((p.fnArities.map Prod.fst).filter fun f =>
      1 < (p.fnArities.filter fun fa => fa.1 == f).length).dedup

/-- Every function `(print-size)` reports, in a stable order. Deduplicated by *name*:
`fnArities` keys on the pair, so a name used at two arities would appear twice — which
egglog cannot express anyway, but which would silently double a line here. -/
def Program.fnNames (p : Program) : List FnName := (p.fnArities.map Prod.fst).dedup

/-! ### The file -/

/-- The single-sort `datatype` declaration the untyped model needs. -/
def Program.eggHeader (p : Program) : String :=
  "(datatype Math " ++ String.intercalate " "
    (p.ctorArities.map fun fa =>
      "(" ++ fa.1 ++ String.join (List.replicate fa.2 " Math") ++ ")") ++ ")"

/-- A `(ruleset <name>)` for every named ruleset the program mentions. egglog requires the
declaration before a rule may join one or a schedule may run one; the unnamed ruleset is
declared already, so a program that uses only that one emits nothing here. -/
def Program.rulesetDecls (p : Program) : List String :=
  ((p.filterMap fun c => match c with
    | .rule r => some r.ruleset
    | .run R => some R
    | .saturate R => some R
    | _ => none).filter (· ≠ "")).dedup.map fun R => "(ruleset " ++ R ++ ")"

/-- The program as a complete `.egg` file, ending in the `(print-size)` that the
comparison reads. -/
def Program.toEgg (p : Program) : String :=
  String.intercalate "\n"
    (p.eggHeader :: p.rulesetDecls ++ (p.map Cmd.toEgg).filter (· ≠ "")
      ++ ["(print-size)", ""])

/-- The row counts the interpreter predicts, one `name count` line per constructor, for
diffing against egglog's `(print-size)`. `STUCK` if the program does not run, which for a
well-scoped program with no failing lookup and no diverging merge it always does.

This is `Impl/Merge.lean`'s **M9** interpreter, not `Impl/Interp.lean`'s `exec`. `exec`
evaluates with `Expr.eval` and never runs a merge phase, so while it was what this read,
`mergeOne`, `mergeRound`, `execActions`, `patternHolds`'s row scan and the whole
`:merge` implementation had **no** differential coverage — the suite's pass count said
nothing about them. The two agree on the constructor fragment (see `execM`), so the 70
constructor cases are unaffected. -/
def Program.expectedSizes (p : Program) : String :=
  match execM p with
  | none => "STUCK\n"
  | some d =>
    String.intercalate "\n" (p.fnNames.map fun f => f ++ " " ++ toString (d.keyRowCount f))
      ++ "\n"

end Egglog
