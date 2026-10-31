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
  | .lit (.str s) => "\"" ++ s ++ "\""
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
  | .subsume f es => "(subsume " ++ (Expr.app f es).toEgg ++ ")"

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

/-- The ruleset the rules of the `i`th run join: egglog fires rules by ruleset, so every
run gets one of its own, numbered by position. -/
def runRuleset (i : Nat) : String := "r" ++ toString i

/-- A schedule as the body of `run-schedule`, registering each run's rules in a ruleset of
its own. Runs are numbered from `leaf` and rules, by `name`, from `k`; the result is the
registrations, the schedule text, and the next run and rule numbers. -/
def Schedule.toEggAt (name : Nat → Option String) :
    Schedule → Nat → Nat → List String × String × Nat × Nat
  | .run rs, leaf, k =>
      (rs.zipIdx.map fun rj => rj.1.toEggIn (runRuleset leaf) (name (k + rj.2)),
        "(run " ++ runRuleset leaf ++ ")", leaf + 1, k + rs.length)
  | .saturate S, leaf, k =>
      let (regs, text, leaf', k') := S.toEggAt name leaf k
      (regs, "(saturate " ++ text ++ ")", leaf', k')
  | .seq S₁ S₂, leaf, k =>
      let (r₁, t₁, l₁, k₁) := S₁.toEggAt name leaf k
      let (r₂, t₂, l₂, k₂) := S₂.toEggAt name l₁ k₁
      (r₁ ++ r₂, "(seq " ++ t₁ ++ " " ++ t₂ ++ ")", l₂, k₂)

/-- A top-level schedule: its registrations, then `(run r<i> 1)` for a bare run and
`(run-schedule …)` otherwise. -/
def Schedule.toEggLines (name : Nat → Option String) (S : Schedule) (leaf k : Nat) :
    List String × Nat × Nat :=
  let (regs, text, leaf', k') := S.toEggAt name leaf k
  match S with
  | .run _ => (regs ++ ["(run " ++ runRuleset leaf ++ " 1)"], leaf', k')
  | _ => (regs ++ ["(run-schedule " ++ text ++ ")"], leaf', k')

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

/-- A `(ruleset r<i>)` for every run. egglog requires the declaration before a rule may
join one or a schedule may run one. -/
def Program.rulesetDecls (p : Program) : List String :=
  (List.range p.runs.length).map fun i => "(ruleset " ++ runRuleset i ++ ")"

/-- The top-level commands of a schedule: the operands of its outermost sequence, as
`Schedule.seqAll` nests them. -/
def Schedule.topLevel : Schedule → List Schedule
  | .seq S₁ S₂ => S₁ :: S₂.topLevel
  | S => [S]

/-- The schedule as egglog source, one command per top-level operand, with rules named by
`name` from their position in `Program.rules`. -/
def Program.commandsToEgg (p : Program) (name : Nat → Option String) : List String :=
  (p.schedule.topLevel.foldl (fun (acc : List String × Nat × Nat) S =>
    let (lines, leaf, k) := S.toEggLines name acc.2.1 acc.2.2
    (acc.1 ++ lines, leaf, k)) ([], 0, 0)).1

/-- The program as egglog source: the sort, the ruleset and function declarations, the
schedules, and the check. -/
def Program.renderWith (p : Program) (name : Nat → Option String) : String :=
  String.intercalate "\n"
    (p.eggHeader :: p.rulesetDecls ++ p.declsToEgg ++ p.commandsToEgg name ++
      p.check.checkToEgg) ++ "\n"

@[inherit_doc Program.renderWith]
def Program.render (p : Program) : String := p.renderWith fun _ => none

/-! ### The census of the compiled tables

egglog's `(print-size)` counts subsumed rows, and which spellings a run builds depends on
which representative each engine picked, so a compiled program is compared through a
census of canonical e-nodes: a final ruleset joins every application of a source
constructor with the live union-find edges of its children and records the tuple of
parents in the constructor's `:live` relation, whose size is the number of canonical
e-nodes on both sides. Source programs have no union-find and no census. -/

/-- The census relation of a source constructor. -/
def liveName (f : FnName) : FnName := f ++ ":live"

/-- The child variables of a census rule, and their parents. -/
def censusVars (n : Nat) : List Expr := (List.range n).map fun i => .var ("@v" ++ toString i)
def censusParents (n : Nat) : List Expr := (List.range n).map fun i => .var ("@r" ++ toString i)

/-- Whether the program has a union-find, which is what gets a census. -/
def Program.compiledB (p : Program) : Bool := p.ctors.any fun fa => fa.1 == ufName

/-- The source constructors of a compiled program: every name that is not a generated table. -/
def Program.constructors (p : Program) : List (FnName × Nat) :=
  p.ctors.filter fun fa => !isRelationName fa.1

/-- The census atoms of a constructor: its application over the child variables, and one
union-find edge from each child to its parent. -/
def censusQuery (f : FnName) (n : Nat) : Query :=
  .expr (.app f (censusVars n)) ::
    ((censusVars n).zip (censusParents n)).map fun vr => .expr (.app ufName [vr.1, vr.2])

/-- The census declarations and rules, and the command that runs them. -/
def Program.censusToEgg (p : Program) : List String × List String :=
  if !p.compiledB then ([], []) else
  let decls := p.constructors.map fun fa =>
    "(relation " ++ liveName fa.1 ++ " (" ++ String.intercalate " " (List.replicate fa.2 "Math")
      ++ "))"
  let rules := p.constructors.map fun fa =>
    "(rule (" ++ String.intercalate " " ((censusQuery fa.1 fa.2).map Pattern.toEgg) ++ ") ("
      ++ (Expr.app (liveName fa.1) (censusParents fa.2)).toEgg ++ ") :ruleset census)"
  ("(ruleset census)" :: decls ++ rules, ["(run census 1)"])

/-- The program as a complete `.egg` file for the row-count comparison: the schedules, the
census, then the `(print-size)` the comparison reads. The check is left out, since a
failing one would stop egglog before it prints. -/
def Program.toEgg (p : Program) : String :=
  let (census, run) := p.censusToEgg
  String.intercalate "\n"
    (p.eggHeader :: p.rulesetDecls ++ p.declsToEgg ++ census ++ p.commandsToEgg (fun _ => none)
      ++ run ++ ["(print-size)"]) ++ "\n"

/-- The row counts the interpreter predicts, one `name count` line per function and one
per census relation, for diffing against egglog's `(print-size)`. The census count is the
number of distinct parent tuples the census query finds: one per canonical e-node. `STUCK`
if the program does not run. -/
def Program.expectedSizes (p : Program) : String :=
  match exec p with
  | none => "STUCK\n"
  | some d =>
    let raw := p.fnNames.map fun f => f ++ " " ++ toString (d.rowCount f)
    let live := if !p.compiledB then [] else p.constructors.map fun fa =>
      let tuples := (matchQuery d (censusQuery fa.1 fa.2)).map fun σ =>
        (censusParents fa.2).map fun r => r.eval σ
      liveName fa.1 ++ " " ++ toString tuples.dedup.length
    String.intercalate "\n" (raw ++ live) ++ "\n"

end Egglog
