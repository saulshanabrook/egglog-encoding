import EgglogSemantics.Impl.Interp
import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.Names

/-!
# Emitting egglog source

Renders a `Program` as a `.egg` file so that the same program can be run by the Rust
implementation and the results compared by `DiffTest.lean`. The oracle is `(print-size)`,
which prints one row count per function — the same quantity `FDatabase.rowCount` computes.

The model is untyped and has no declarations, so the emitter invents a single sort `Math`
and declares every name at the arity it is applied with: a generated table as a `relation`,
since its rows are never nested, and every other name as a `constructor`. A program that
uses one name at two arities is not expressible in egglog and must not be generated.

`Term.lit` is the same sort as an application here, while egglog's `i64` is a distinct
primitive sort, so literals are emitted as-is and generated programs avoid them, using
nullary constructors instead; the fragment loses nothing by it.
-/

namespace Egglog

/-! ### Rendering -/

mutual

/-- Render an expression with the chosen surface spelling of its variables. -/
def Expr.toEggWith (name : Var → String) : Expr → String
  | .lit (.int n) => toString n
  | .var v => name v
  | .app f args => "(" ++ f ++ Expr.toEggArgsWith name args ++ ")"
  | .min a b => "(min " ++ a.toEggWith name ++ " " ++ b.toEggWith name ++ ")"

/-- `Expr.toEggWith` over an argument list, each preceded by a space. -/
def Expr.toEggArgsWith (name : Var → String) : List Expr → String
  | [] => ""
  | e :: es => " " ++ e.toEggWith name ++ Expr.toEggArgsWith name es

end

/-- An expression as egglog source, preserving variable names. -/
def Expr.toEgg (e : Expr) : String := e.toEggWith id

def Pattern.toEgg : Pattern → String
  | .expr e => e.toEgg
  | .eq e₁ e₂ => "(= " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"
  | .ne e₁ e₂ => "(!= " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"

def Action.toEgg : Action → String
  | .expr e => e.toEgg
  | .union e₁ e₂ => "(union " ++ e₁.toEgg ++ " " ++ e₂.toEgg ++ ")"
  | .delete e => "(delete " ++ e.toEgg ++ ")"

/-- A rule as egglog source, joining the ruleset `R` and carrying `name` if given. -/
def Rule.toEggIn (R : String) (name : Option String) (r : Rule) : String :=
  "(rule (" ++ String.intercalate " " (r.query.map Pattern.toEgg) ++ ") ("
    ++ String.intercalate " " (r.actions.map Action.toEgg) ++ ")"
    ++ (match name with | some n => " :name \"" ++ n ++ "\"" | none => "")
    ++ " :ruleset " ++ R ++ ")"

/-- A rule as egglog source, outside any ruleset. -/
def Rule.toEgg (r : Rule) : String :=
  "(rule (" ++ String.intercalate " " (r.query.map Pattern.toEgg) ++ ") ("
    ++ String.intercalate " " (r.actions.map Action.toEgg) ++ "))"

/-- The ruleset the `i`th command's rules join: egglog fires rules by ruleset, so every
command gets one of its own, named by position. -/
def commandRuleset (i : Nat) : String := "r" ++ toString i

/-- A command as egglog source: its rules registered in the command's ruleset, then one
run of it, `(run r<i> 1)`, or its saturation, `(run-schedule (saturate r<i>))`. Rules are
named by `name` from their position in `Program.rules`, starting at `k`. -/
def Cmd.toEggAt (name : Nat → Option String) (i k : Nat) : Cmd → List String
  | .run rs => (rs.zipIdx.map fun rj => rj.1.toEggIn (commandRuleset i) (name (k + rj.2))) ++
      ["(run " ++ commandRuleset i ++ " 1)"]
  | .saturate rs => (rs.zipIdx.map fun rj => rj.1.toEggIn (commandRuleset i) (name (k + rj.2))) ++
      ["(run-schedule (saturate " ++ commandRuleset i ++ "))"]

/-- The final check as egglog source; the empty check is left out. -/
def Query.checkToEgg (q : Query) : List String :=
  if q.isEmpty then [] else ["(check" ++ String.join (q.map fun p => " " ++ p.toEgg) ++ ")"]

/-! ### Declarations

Every name has to be declared before egglog runs the program, so the arities are read off
the program's uses (`Program.ctors`). -/

/-- Every generated table, the union-find, the views and the provenance log, is a relation
in egglog: its rows are never nested, so they need no id. Source names never start with
`@`. -/
def isRelationName (f : FnName) : Bool := "@".isPrefixOf f

/-- The names the program uses at more than one arity, which egglog rejects with
"Function already bound". -/
def Program.arityConflicts (p : Program) : List FnName :=
  ((p.ctors.map Prod.fst).filter fun f =>
      1 < (p.ctors.filter fun fa => fa.1 == f).length).dedup

/-- Every function `(print-size)` reports, in a stable order. -/
def Program.fnNames (p : Program) : List FnName := (p.ctors.map Prod.fst).dedup

/-- A `relation` or `constructor` declaration for every name the program applies. -/
def Program.declsToEgg (p : Program) : List String :=
  p.ctors.map fun fa =>
    let sorts := "(" ++ String.intercalate " " (List.replicate fa.2 "Math") ++ ")"
    if isRelationName fa.1 then "(relation " ++ fa.1 ++ " " ++ sorts ++ ")"
    else "(constructor " ++ fa.1 ++ " " ++ sorts ++ " Math)"

/-! ### The file -/

/-- The single sort the untyped model needs. -/
def Program.eggHeader (_ : Program) : String := "(sort Math)"

/-- A `(ruleset r<i>)` for every command with rules. egglog requires the declaration before
a rule may join one or a schedule may run one. -/
def Program.rulesetDecls (p : Program) : List String :=
  p.commands.zipIdx.map fun ci => "(ruleset " ++ commandRuleset ci.2 ++ ")"

/-- The commands as egglog source, with rules named by `name` from their position in
`Program.rules`. -/
def Program.commandsToEgg (p : Program) (name : Nat → Option String) : List String :=
  (p.commands.foldl (fun (acc : List String × Nat × Nat) c =>
    (acc.1 ++ c.toEggAt name acc.2.1 acc.2.2, acc.2.1 + 1, acc.2.2 + c.rules.length))
    ([], 0, 0)).1

/-- The program as egglog source: the sort, the ruleset and function declarations, the
commands, and the check. -/
def Program.renderWith (p : Program) (name : Nat → Option String) : String :=
  String.intercalate "\n"
    (p.eggHeader :: p.rulesetDecls ++ p.declsToEgg ++ p.commandsToEgg name ++
      p.check.checkToEgg) ++ "\n"

@[inherit_doc Program.renderWith]
def Program.render (p : Program) : String := p.renderWith fun _ => none

/-- The program as a complete `.egg` file for the row-count comparison: the commands, then
the `(print-size)` the comparison reads. The check is left out, since a failing one would
stop egglog before it prints. -/
def Program.toEgg (p : Program) : String :=
  String.intercalate "\n"
    (p.eggHeader :: p.rulesetDecls ++ p.declsToEgg ++ p.commandsToEgg (fun _ => none) ++
      ["(print-size)"]) ++ "\n"

/-- The row counts the interpreter predicts, one `name count` line per function, for
diffing against egglog's `(print-size)`. `STUCK` if the program does not run. -/
def Program.expectedSizes (p : Program) : String :=
  match exec p with
  | none => "STUCK\n"
  | some d =>
    String.intercalate "\n" (p.fnNames.map fun f => f ++ " " ++ toString (d.rowCount f))
      ++ "\n"

end Egglog
