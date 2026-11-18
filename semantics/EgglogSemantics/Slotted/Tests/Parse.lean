import EgglogSemantics.Tests.Parse
import EgglogSemantics.Slotted.Spec.Step

/-!
# Parsing the slotted `.egg` subset

Reads the slotted source language of `egglog-experimental --slotted` into slotted programs.
A file holds several checks; each `(check …)` or `(fail (check …))` becomes one case: the
commands before it as the schedule, the check as the query, and the outcome the file asserts.

Declarations carry the binder signature: `(constructor f (sorts…) out :binder j…)` and the
variants of `(datatype …)` record, for each binder column `j` among the non-payload columns,
the pair `(j, i)` with `i` the term child the binders precede. `(let x e)` builds `e` and
substitutes it for later uses of `x`; a `let` of a slot binds the concrete slot. Slots written
in ground commands are concrete slot terms; slots written in a rewrite, a `rule`, a `:when`
fact or a check use `Expr.var`; the query fixes these slot identifiers to their own names,
while identifiers used only in actions receive fresh names. `(run N)` is `N` rounds of the
rewrites registered so far. `(push)` and `(pop)` save and restore the whole state.

Unsupported forms make the whole file fail with the form's name: `subst` (a representative
choice outside the semantics), `extract` (output rather than a check), `include`,
`__internal-*` checks, `function`, `relation`, `run-schedule`, `datatype*`, and `:ruleset`.
-/

namespace Egglog.Slotted.Parse

open Egglog.Sexp

/-- Sorts that carry no slots; they do not count for `:binder` positions. -/
def payloadSorts : List String := ["i64", "f64", "String", "bool", "Unit", "Rational", "BigInt"]

/-- One check of a file: the program up to it and the outcome the file asserts. -/
structure Case where
  /-- The position of the check among the file's checks, from 0. -/
  index : Nat
  program : Slotted.Program
  expected : Result

/-- The state `(push)` saves and `(pop)` restores. -/
structure Frame where
  binders : List (FnName × List (Nat × Nat)) := []
  globals : List (String × Expr) := []
  rules : List Rule := []
  commands : Array Schedule := #[]

structure State where
  frame : Frame := {}
  stack : List Frame := []
  cases : Array Case := #[]

/-- The binder pairs of a constructor with the given column sorts and `:binder` indices: each
index names a non-payload column, and all of them bind in the non-payload column after the
last of them. -/
def binderPairs (sorts : List String) (idx : List Nat) : Except String (List (Nat × Nat)) := do
  if idx.isEmpty then return []
  let np := (sorts.zipIdx.filter fun si => si.1 ∉ payloadSorts).map Prod.snd
  let last := idx.foldl max 0
  let some child := np[last + 1]? | throw "a binder column must precede the child it binds"
  idx.mapM fun b => match np[b]? with
    | some col => pure (col, child)
    | none => throw "a `:binder` index names no column"

/-- The `:binder` indices among a declaration's options, and whether any other option appears. -/
partial def binderOption : List Sexp → Except String (List Nat)
  | [] => .ok []
  | .atom ":binder" :: rest =>
    let idx := rest.takeWhile fun s => match s with | .atom a => !a.startsWith ":" | _ => false
    let rest := rest.drop idx.length
    do
      let ns ← idx.mapM fun s => match s with
        | .atom a => match a.toNat? with
          | some n => pure n
          | none => throw "`:binder` takes column indices"
        | _ => throw "`:binder` takes column indices"
      pure (ns ++ (← binderOption rest))
  | .atom k :: _ =>
    if k.startsWith ":" then .error s!"constructor option {k}"
    else .error "unexpected constructor option"
  | _ => .error "unexpected constructor option"

/-- The sort names of a column list. -/
def sortNames : List Sexp → Except String (List String)
  | [] => .ok []
  | .atom s :: rest => do pure (s :: (← sortNames rest))
  | _ => .error "a column is a sort name"

/-- A ground expression (`ground`), where a slot is the concrete slot term, or a query or
action expression, where a slot uses `Expr.var` (fixed in a query, fresh only in actions)
and a free identifier is a variable. Globals
are substituted in both. -/
partial def expr (globals : List (String × Expr)) (ground : Bool) : Sexp → Except String Expr
  | .atom s =>
    match s.toInt? with
    | some n => .ok (.lit (.int n))
    | none =>
      if s.startsWith "$" then .ok (if ground then .app s [] else .var s)
      else match globals.lookup s with
        | some e => .ok e
        | none => if ground then .error s!"unbound global {s}" else .ok (.var s)
  | .str s => .ok (.lit (.str s))
  | .list (.atom "subst" :: _) => .error "subst"
  | .list (.atom f :: args) =>
    if f.startsWith "__internal" then .error f
    else do pure (.app f (← args.mapM (expr globals ground)))
  | .list _ => .error "an application starts with a name"

/-- A query fact. Equality and disequality are patterns; everything else, including the
built-in predicates, is an expression pattern. -/
def fact (globals : List (String × Expr)) : Sexp → Except String Pattern
  | .list [.atom "=", a, b] => do pure (.eq (← expr globals false a) (← expr globals false b))
  | .list [.atom "!=", a, b] => do pure (.ne (← expr globals false a) (← expr globals false b))
  | s => do pure (.expr (← expr globals false s))

/-- A rule action. -/
def action (globals : List (String × Expr)) : Sexp → Except String Action
  | .list [.atom "union", a, b] => do
      pure (.union (← expr globals false a) (← expr globals false b))
  | .list (.atom "subsume" :: _) => .error "subsume"
  | .list (.atom "set" :: _) => .error "set"
  | .list (.atom "delete" :: _) => .error "delete"
  | s => do pure (.expr (← expr globals false s))

/-- The options of a `rewrite`: `:name` is ignored, `:when` supplies facts, anything else is
unsupported. -/
partial def rewriteOptions (globals : List (String × Expr)) : List Sexp → Except String Query
  | [] => .ok []
  | .atom ":name" :: _ :: rest => rewriteOptions globals rest
  | .atom ":when" :: .list facts :: rest => do
      pure ((← facts.mapM (fact globals)) ++ (← rewriteOptions globals rest))
  | .atom k :: _ => .error s!"rewrite option {k}"
  | _ => .error "unexpected rewrite option"

namespace State

def binders (st : State) : Binders := fun f => (st.frame.binders.lookup f).getD []

def pushCommand (st : State) (S : Schedule) : State :=
  { st with frame := { st.frame with commands := st.frame.commands.push S } }

def pushAction (st : State) (a : Action) : State := st.pushCommand (.run [⟨[], [a]⟩])

def addBinders (st : State) (f : FnName) (ps : List (Nat × Nat)) : State :=
  if ps.isEmpty then st else
    { st with frame := { st.frame with binders := st.frame.binders ++ [(f, ps)] } }

def addCase (st : State) (q : Query) (expected : Result) : State :=
  let program : Slotted.Program :=
    { plain := { schedule := Schedule.seqAll st.frame.commands.toList, check := q },
      binders := st.binders }
  { st with cases := st.cases.push ⟨st.cases.size, program, expected⟩ }

/-- A constructor declaration: its binder pairs, if it has `:binder` columns. -/
def constructor (st : State) (f : FnName) (sorts : List Sexp) (opts : List Sexp) :
    Except String State := do
  let ps ← binderPairs (← sortNames sorts) (← binderOption opts)
  pure (st.addBinders f ps)

/-- A `datatype` variant `(f sorts… opts…)`. -/
def variant (st : State) : Sexp → Except String State
  | .list (.atom f :: rest) =>
    let sorts := rest.takeWhile fun s => match s with | .atom a => !a.startsWith ":" | _ => false
    st.constructor f sorts (rest.drop sorts.length)
  | _ => .error "a datatype variant is a constructor"

/-- The names of commands that are outside the subset; everything else that is not a known
command is a top-level ground term. -/
def unsupported : List String :=
  ["function", "relation", "set", "delete", "subsume", "extract", "query-extract", "include",
   "run-schedule", "datatype*", "print-size", "print-function", "print-stats", "input",
   "output", "fail", "birewrite", "ruleset", "unstable-combined-ruleset"]

def step (st : State) : Sexp → Except String State
  | .list (.atom "sort" :: _) => .ok st
  | .list (.atom "constructor" :: .atom f :: .list sorts :: _ :: opts) =>
      st.constructor f sorts opts
  | .list (.atom "datatype" :: .atom _ :: variants) => variants.foldlM State.variant st
  | .list [.atom "let", .atom x, e] => do
      if x.startsWith "$" then throw "a global name cannot start with `$`"
      let v ← expr st.frame.globals true e
      let st := { st with frame := { st.frame with globals := (x, v) :: st.frame.globals } }
      -- A slot is a name, not a row; a term is built.
      pure (match v with
        | .app f [] => if isSlotName f then st else st.pushAction (.expr v)
        | _ => st.pushAction (.expr v))
  | .list [.atom "union", a, b] => do
      let a ← expr st.frame.globals true a
      let b ← expr st.frame.globals true b
      pure (st.pushAction (.union a b))
  | .list (.atom "rewrite" :: lhs :: rhs :: opts) => do
      let l ← expr st.frame.globals false lhs
      let r ← expr st.frame.globals false rhs
      let when ← rewriteOptions st.frame.globals opts
      let rule : Rule := ⟨.expr l :: when, [.union l r]⟩
      pure { st with frame := { st.frame with rules := st.frame.rules ++ [rule] } }
  | .list (.atom "rule" :: .list facts :: .list actions :: opts) => do
      unless opts.all (fun s => match s with | .atom ":name" | .str _ => true | _ => false) do
        throw "rule option"
      let rule : Rule :=
        ⟨← facts.mapM (fact st.frame.globals), ← actions.mapM (action st.frame.globals)⟩
      pure { st with frame := { st.frame with rules := st.frame.rules ++ [rule] } }
  | .list [.atom "run", .atom n] =>
      match n.toNat? with
      | some n => .ok ((List.replicate n (Schedule.run st.frame.rules)).foldl State.pushCommand st)
      | none => .error "`run` takes a count"
  | .list (.atom "check" :: facts) => do
      pure (st.addCase (← facts.mapM (fact st.frame.globals)) .ok)
  | .list [.atom "fail", .list (.atom "check" :: facts)] => do
      pure (st.addCase (← facts.mapM (fact st.frame.globals)) .checkFailed)
  | .list [.atom "push"] => .ok { st with stack := st.frame :: st.stack }
  | .list [.atom "pop"] =>
      match st.stack with
      | f :: rest => .ok { st with frame := f, stack := rest }
      | [] => .error "`pop` without `push`"
  | s@(.list (.atom head :: _)) =>
      if head ∈ unsupported || head.startsWith ":" then .error head
      else do pure (st.pushAction (.expr (← expr st.frame.globals true s)))
  | _ => .error "unexpected form"

end State

end Egglog.Slotted.Parse

namespace Egglog.Slotted

/-- Parse a slotted `.egg` file into its cases, or the name of the first unsupported form. -/
def parseFile (src : String) : Except String (List Parse.Case) := do
  let forms ← Sexp.parseAll src
  let st ← forms.foldlM Parse.State.step ({} : Parse.State)
  pure st.cases.toList

end Egglog.Slotted

namespace Egglog.Slotted.Parse.Tests

set_option linter.hashCommand false

/-- The paper's example, in the reference's syntax. -/
private def paperSrc : String :=
  "(datatype Expr (Num i64) (Mul Expr Expr) (Sum Expr Expr :binder 0))\n\
   (let t (Mul (Num 5) (Sum $i (Sum $j (Mul $i $j)))))\n\
   (rewrite (Mul x (Sum $v b)) (Sum $v (Mul x b)) :when ((not-free $v x)))\n\
   (run 2)\n\
   (check (= t (Sum $k (Sum $l (Mul (Num 5) (Mul $k $l))))))\n\
   (fail (check (= t (Sum $k (Sum $l (Mul (Num 5) (Mul $l $l)))))))\n"

private def paperCases : List Case := (parseFile paperSrc).toOption.getD []

#guard paperCases.length = 2
#guard (paperCases.map (·.expected)) = [.ok, .checkFailed]
-- `Sum` binds its first argument in its second; `Mul` binds nothing.
#guard (paperCases.map fun c => c.program.binders "Sum") = [[(0, 1)], [(0, 1)]]
#guard (paperCases.map fun c => c.program.binders "Mul") = [[], []]
-- The global is substituted as a ground term with concrete slots; the check's slots are
-- slot variables; the rule's query has the rewrite's left side and the guard.
#guard (paperCases.map fun c => c.program.plain.check.map Pattern.toEgg) =
  [["(= (Mul (Num 5) (Sum ($i) (Sum ($j) (Mul ($i) ($j))))) \
      (Sum $k (Sum $l (Mul (Num 5) (Mul $k $l)))))"],
   ["(= (Mul (Num 5) (Sum ($i) (Sum ($j) (Mul ($i) ($j))))) \
      (Sum $k (Sum $l (Mul (Num 5) (Mul $l $l)))))"]]
#guard (paperCases.map fun c => c.program.plain.runs.length) = [3, 3]
#guard (paperCases.map fun c => c.program.plain.rules.map fun r => r.query.length) =
  [[0, 2, 2], [0, 2, 2]]
-- Binder columns are counted among the non-payload columns.
#guard ((parseFile "(constructor Let (Expr i64 Var Expr) Expr :binder 1) (check)").map
    fun cs => cs.map fun c => c.program.binders "Let").toOption = some [[(2, 3)]]
#guard ((parseFile "(datatype E (Lam Var Var E :binder 0 1)) (check)").map
    fun cs => cs.map fun c => c.program.binders "Lam").toOption = some [[(0, 2), (1, 2)]]
-- A `let` of a slot binds a concrete slot and builds nothing; `push`/`pop` restore the state.
#guard ((parseFile "(let a $a) (check (= (V a) (V $x)))").map
    fun cs => cs.map fun c =>
      (c.program.plain.rules.length, c.program.plain.check.map Pattern.toEgg)).toOption =
  some [(0, ["(= (V ($a)) (V $x))"])]
#guard ((parseFile "(push) (let t (A)) (pop) (check (A))").map
    fun cs => cs.map fun c => c.program.plain.rules.length).toOption = some [0]
#guard ((parseFile "(let t (A)) (check (A))").map
    fun cs => cs.map fun c => c.program.plain.rules.length).toOption = some [1]

/-- The unsupported form a parse names. -/
private def rejected (src : String) : Option String :=
  match parseFile src with
  | .error e => some e
  | .ok _ => none

-- Unsupported forms name themselves.
#guard rejected "(rewrite (Let v $x b) (subst b $x v))" = some "subst"
#guard rejected "(extract (A))" = some "extract"
#guard rejected "(include \"x.egg\")" = some "include"
#guard rejected "(check (__internal-holds a b))" = some "__internal-holds"
#guard rejected paperSrc = none

end Egglog.Slotted.Parse.Tests
