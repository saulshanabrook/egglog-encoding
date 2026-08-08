import EgglogSemantics.Impl.Merge

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

def Pattern.toEgg : Pattern → String
  | .expr e => e.toEgg
  | .eq e₁ e₂ => "(= " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"
  | .values vs f as =>
      "(= (values " ++ String.intercalate " " (vs.map Expr.toEgg) ++ ") ("
        ++ f ++ Expr.toEggArgs as ++ "))"

/-- One expression per value column, written as egglog's tuple form `(values e₀ e₁ …)`
when there is more than one and bare when there is exactly one. `Spec/Syntax.lean` takes
the list the tuple denotes, in both `Action.set` and `MergeSpec.merge`; this is where the
two notations meet. -/
def Expr.valuesToEgg : List Expr → String
  | [e] => e.toEgg
  | res => "(values " ++ String.intercalate " " (res.map Expr.toEgg) ++ ")"

def Action.toEgg : Action → String
  | .expr e => e.toEgg
  | .letBind v e => "(let " ++ v ++ " " ++ e.toEgg ++ ")"
  | .union e₁ e₂ => "(union " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"
  | .set f args out =>
      "(set (" ++ f ++ Expr.toEggArgs args ++ ") " ++ Expr.valuesToEgg out ++ ")"

def Rule.toEgg (r : Rule) : String :=
  "(rule (" ++ String.intercalate " " (r.query.map Pattern.toEgg) ++ ") ("
    ++ String.intercalate " " (r.actions.map Action.toEgg) ++ "))"

/-- The merged value, in egglog's tuple notation. Shared with `Action.set`. -/
abbrev MergeSpec.resultToEgg : List Expr → String := Expr.valuesToEgg

/-- A merge specification as egglog source. `.union` is a constructor and never reaches
here; `.noMerge` is `:no-merge`.

The block form is `:merge (<action>* <result>)` — the actions and the result are
*siblings* in one list, not two nested ones (`egglog/src/ast/parse.rs:531-569`, and
`egglog/tests/merge-action-block.egg`). The parse is disambiguated by whether the first
element is itself a list, which is why an empty body has to emit the bare result: an
expression always has an atom head, so `:merge (min old new)` reads as a result and
`:merge ((let s …) s)` as a block. -/
def MergeSpec.toEgg : MergeSpec → String
  | .union => ""
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
def FnDecl.toEgg (f : FnName) (d : FnDecl) : String :=
  let out := match d.outArity with
    | 1 => "i64"
    | _ => "(" ++ String.intercalate " " (List.replicate d.outArity "i64") ++ ")"
  "(function " ++ f ++ " (" ++ String.intercalate " " (List.replicate d.arity "Math")
    ++ ") " ++ out ++ d.merge.toEgg ++ ")"

/-- A command as egglog source. `Cmd.run` is one round, so it emits `(run 1)`.
A constructor declaration is folded into the `datatype` header and produces nothing; a
`:merge` declaration is its own command. -/
def Cmd.toEgg : Cmd → String
  | .action a => a.toEgg
  | .rule r => r.toEgg
  | .run => "(run 1)"
  | .decl f d => match d.merge with
    | .union => ""
    | _ => FnDecl.toEgg f d

/-! ### Collecting the signature

The header has to declare every constructor, so the arities are read off the program's
uses rather than from `Signature` — generated programs need not declare anything. -/

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

def Cmd.fnArities : Cmd → List (FnName × Nat)
  | .action a => a.fnArities
  | .rule r => (r.query.flatMap Pattern.fnArities) ++ (r.actions.flatMap Action.fnArities)
  | .run => []
  | .decl f d => [(f, d.arity)]

/-- Every function the program uses, with its arity, deduplicated. -/
def Program.fnArities (p : Program) : List (FnName × Nat) :=
  (p.flatMap Cmd.fnArities).dedup

/-- The names the program declares with a non-`union` merge. These get their own
`function` command and must be kept out of the `datatype`. -/
def Program.mergeNames (p : Program) : List FnName :=
  p.filterMap fun c => match c with
    | .decl f d => match d.merge with
      | .union => none
      | _ => some f
    | _ => none

/-- The constructors: everything used that is not a declared `:merge` function. -/
def Program.ctorArities (p : Program) : List (FnName × Nat) :=
  p.fnArities.filter fun fa => fa.1 ∉ p.mergeNames

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
  | .run => []
  | .decl _ d => d.merge.setTargets

/-- The names the program `set`s that egglog would refuse: everything not declared with a
non-`union` merge. Empty is the only acceptable value for a case the difftest emits. -/
def Program.illegalSets (p : Program) : List FnName :=
  (p.flatMap Cmd.setTargets).dedup.filter (· ∉ p.mergeNames)

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

/-- The program as a complete `.egg` file, ending in the `(print-size)` that the
comparison reads. -/
def Program.toEgg (p : Program) : String :=
  String.intercalate "\n"
    (p.eggHeader :: (p.map Cmd.toEgg).filter (· ≠ "") ++ ["(print-size)", ""])

/-- The row counts the interpreter predicts, one `name count` line per constructor, for
diffing against egglog's `(print-size)`. `STUCK` if the program does not run, which for a
well-scoped program with no failing lookup and no diverging merge it always does.

This is `Impl/Merge.lean`'s **M9** interpreter, not `Impl/Interp.lean`'s `exec`. `exec`
evaluates with `Expr.eval` and never runs a merge phase, so while it was what this read,
`mergeOne`, `mergeRound`, `execActions`, `execExpr`'s lookup branch and the whole
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
