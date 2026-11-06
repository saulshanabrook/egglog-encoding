import EgglogSemantics.Tests.Egg

/-!
# Parsing egglog source

The inverse of `Program.toEgg`: reads the fragment the emitter writes, so programs can be
kept as `.egg` files and hand-written in egglog's own syntax. The model is untyped and has
no declarations, so `(sort …)`, `(ruleset …)`, `(constructor …)`, `(relation …)`, and
`(print-size)` carry no command; a `(function …)` with a merge is outside the language.
-/

namespace Egglog

inductive Sexp where
  | atom (s : String)
  | str (s : String)
  | list (xs : List Sexp)
  deriving Repr, BEq, Inhabited

namespace Sexp

private inductive Token where
  | open_ | close | atom (s : String) | str (s : String)
  deriving Repr, Inhabited

private def delimiter (c : Char) : Bool := c.isWhitespace || c == '(' || c == ')' || c == ';'

private partial def tokenize (cs : List Char) (acc : Array Token) : Except String (Array Token) :=
  match cs with
  | [] => .ok acc
  | ';' :: rest => tokenize (rest.dropWhile (· != '\n')) acc
  | '(' :: rest => tokenize rest (acc.push .open_)
  | ')' :: rest => tokenize rest (acc.push .close)
  | '"' :: rest =>
    let body := rest.takeWhile (· != '"')
    match rest.drop body.length with
    | '"' :: rest => tokenize rest (acc.push (.str (String.ofList body)))
    | _ => .error "unterminated string"
  | c :: rest =>
    if c.isWhitespace then tokenize rest acc else
      let word := c :: rest.takeWhile (!delimiter ·)
      tokenize (rest.drop (word.length - 1)) (acc.push (.atom (String.ofList word)))

private partial def parseOne (ts : List Token) : Except String (Sexp × List Token) :=
  match ts with
  | [] => .error "unexpected end of input"
  | .close :: _ => .error "unexpected `)`"
  | .atom s :: rest => .ok (.atom s, rest)
  | .str s :: rest => .ok (.str s, rest)
  | .open_ :: rest => do
    let (xs, rest) ← parseMany rest #[]
    pure (.list xs.toList, rest)
where
  parseMany (ts : List Token) (acc : Array Sexp) : Except String (Array Sexp × List Token) :=
    match ts with
    | [] => .error "missing `)`"
    | .close :: rest => .ok (acc, rest)
    | ts => do
      let (x, rest) ← parseOne ts
      parseMany rest (acc.push x)

/-- Every top-level S-expression of `src`. -/
def parseAll (src : String) : Except String (List Sexp) := do
  let ts ← tokenize src.toList #[]
  let rec go (ts : List Token) (acc : Array Sexp) (fuel : Nat) : Except String (List Sexp) :=
    match fuel, ts with
    | _, [] => .ok acc.toList
    | 0, _ => .error "input too long"
    | fuel + 1, ts => do
      let (x, rest) ← parseOne ts
      go rest (acc.push x) fuel
  go ts.toList #[] ts.size

end Sexp

namespace Parse

open Sexp

def expr : Sexp → Except String Expr
  | .atom s => .ok (match s.toInt? with | some n => .lit (.int n) | none => .var s)
  | .str s => .ok (.lit (.str s))
  | .list [.atom "min", a, b] => do pure (.min (← expr a) (← expr b))
  | .list (.atom f :: args) => do pure (.app f (← args.mapM expr))
  | .list _ => .error "an application starts with a name"

def pattern : Sexp → Except String Pattern
  | .list [.atom "=", a, b] => do pure (.eq (← expr a) (← expr b))
  | .list [.atom "!=", a, b] => do pure (.ne (← expr a) (← expr b))
  | s => do pure (.expr (← expr s))

def action : Sexp → Except String Action
  | .list [.atom "union", a, b] => do pure (.union (← expr a) (← expr b))
  | .list [.atom "subsume", target] => do
      match ← expr target with
      | .app f es => pure (.subsume f es)
      | _ => throw "`subsume` names a row by its symbol and arguments"
  | .list [.atom "delete", _] => .error "`delete` is not modelled; the model subsumes rows"
  | .list (.atom "set" :: _) => .error "`set` writes a merge function, which the model has no longer"
  | s => do pure (.expr (← expr s))

/-- Keyword options such as `:ruleset R`, as (keyword, argument) pairs; a keyword with no
argument pairs with `none`. -/
def options : List Sexp → Except String (List (String × Option Sexp))
  | [] => .ok []
  | .atom k :: .atom v :: rest =>
    if !k.startsWith ":" then .error s!"unexpected {k}"
    else if v.startsWith ":" then do pure ((k, none) :: (← options (.atom v :: rest)))
    else do pure ((k, some (.atom v)) :: (← options rest))
  | .atom k :: v :: rest =>
    if k.startsWith ":" then do pure ((k, some v) :: (← options rest))
    else .error s!"unexpected {k}"
  | [.atom k] => if k.startsWith ":" then .ok [(k, none)] else .error s!"unexpected {k}"
  | s :: _ => .error s!"unexpected {repr s}"

/-- A rule and the ruleset it joins; the unnamed ruleset is `""`. -/
def rule (query actions : Sexp) (opts : List Sexp) : Except String (Rule × String) := do
  let .list qs := query | .error "a rule's query is a list"
  let .list as := actions | .error "a rule's actions are a list"
  let opts ← options opts
  let ruleset ← match opts.find? (·.1 == ":ruleset") with
    | some (_, some (.atom r)) => pure r
    | some _ => .error "`:ruleset` takes a name"
    | none => pure ""
  pure (⟨← qs.mapM pattern, ← as.mapM action⟩, ruleset)

/-- A parsed top-level form. -/
inductive Form where
  /-- Register a rule in a ruleset. -/
  | rule (r : Rule) (ruleset : String)
  /-- Fire the ruleset's rules once, `n` times over. -/
  | run (ruleset : String) (n : Nat)
  /-- A `run-schedule` body, to resolve against the rulesets registered so far. -/
  | schedule (s : Sexp)
  | check (q : Query)
  /-- A top-level action, run once. -/
  | action (a : Action)
  | nothing

/-- One top-level form. Declarations carry nothing: the model is untyped, and the emitter
reinvents them from the program's uses. -/
def command : Sexp → Except String Form
  | .list (.atom "check" :: facts) => return .check (← facts.mapM pattern)
  | .list (.atom "sort" :: _) | .list (.atom "ruleset" :: _) | .list [.atom "print-size"]
  | .list (.atom "constructor" :: _) | .list (.atom "relation" :: _) => .ok .nothing
  | .list (.atom "function" :: _) => .error "`function` declares a merge, which the model has no longer"
  | .list (.atom "rule" :: query :: actions :: opts) => do
    let (r, R) ← rule query actions opts
    pure (.rule r R)
  | .list [.atom "run", .atom n] =>
    match n.toNat? with
    | some n => .ok (.run "" n)
    | none => .ok (.run n 1)
  | .list [.atom "run", .atom r, .atom n] =>
    match n.toNat? with
    | some n => .ok (.run r n)
    | none => .error "`run` takes a ruleset and a count"
  | .list (.atom "run-schedule" :: body) => .ok (.schedule (.list (.atom "seq" :: body)))
  | .list (.atom "datatype" :: _) => .error "`datatype` is not supported; use `constructor`"
  | s@(.list (.atom head :: _)) =>
    if head.startsWith ":" then .error s!"unsupported command {head}"
    else do pure (.action (← action s))
  | s => .error s!"unsupported command {repr s}"

/-- The rulesets registered so far, the commands, and the final check once seen. -/
structure State where
  rulesets : List (String × List Rule) := []
  commands : Array Schedule := #[]
  check : Option Query := none

/-- The rules registered in `R` so far, in registration order. -/
def State.rules (st : State) (R : String) : List Rule :=
  ((st.rulesets.find? (·.1 == R)).map Prod.snd).getD []

def State.register (st : State) (R : String) (r : Rule) : State :=
  { st with rulesets :=
      if st.rulesets.any (·.1 == R) then
        st.rulesets.map fun e => if e.1 == R then (e.1, e.2 ++ [r]) else e
      else st.rulesets ++ [(R, [r])] }

/-- Add a command. Nothing may follow the check. -/
def State.push (st : State) (c : Schedule) : Except String State :=
  if st.check.isSome then .error "`check` must be the last command" else
    .ok { st with commands := st.commands.push c }

/-- A `run-schedule` body: `(run R)`, `(saturate S…)`, `(seq S…)`, `(repeat n S…)`, or a
bare ruleset name, over the rules registered so far. -/
partial def State.schedule (st : State) : Sexp → Except String Schedule
  | .atom r => .ok (.run (st.rules r))
  | .list [.atom "run"] => .ok (.run (st.rules ""))
  | .list [.atom "run", .atom r] => .ok (.run (st.rules r))
  | .list (.atom "saturate" :: ss) => do pure (.saturate (Schedule.seqAll (← ss.mapM st.schedule)))
  | .list (.atom "seq" :: ss) => do pure (Schedule.seqAll (← ss.mapM st.schedule))
  | .list (.atom "repeat" :: .atom n :: ss) =>
      match n.toNat? with
      | some n => do
          let body := Schedule.seqAll (← ss.mapM st.schedule)
          pure (Schedule.seqAll (List.replicate n body))
      | none => .error "`repeat` takes a count"
  | s => .error s!"unsupported schedule {repr s}"

def State.step (st : State) : Form → Except String State
  | .nothing => .ok st
  | .rule r R =>
      if st.check.isSome then .error "`check` must be the last command" else
        .ok (st.register R r)
  | .run R n => (List.replicate n (Schedule.run (st.rules R))).foldlM State.push st
  | .schedule s => do st.push (← st.schedule s)
  | .action a => st.push (.run [⟨[], [a]⟩])
  | .check q =>
      if st.check.isSome then .error "a program has one `check`" else
        .ok { st with check := some q }

end Parse

/-- Parse a program from egglog source. A run of a ruleset fires the rules registered in
it so far; a top-level action is a run of an empty-query rule; the top-level commands
become one sequence; the check, if any, comes last, and a program without one ends in the
empty check. -/
def Program.ofEgg (src : String) : Except String Program := do
  let forms ← Sexp.parseAll src
  let st ← forms.foldlM (fun st form => do st.step (← Parse.command form)) ({} : Parse.State)
  pure { schedule := Schedule.seqAll st.commands.toList, check := st.check.getD [] }

end Egglog

namespace Egglog.Parse.Tests

set_option linter.hashCommand false

/-- Parsing rendered source gives it back. -/
private def roundTrip (src : String) : Bool :=
  match Program.ofEgg src with
  | .ok p =>
    match Program.ofEgg p.render with
    | .ok q => q.render == p.render
    | .error _ => false
  | .error _ => false

#guard roundTrip "(sort Math)\n(ruleset R)\n(constructor A () Math)\n(constructor F (Math) Math)\n\
  (F (A))\n(rule ((F x)) ((union (F x) x)) :ruleset R)\n(run-schedule (saturate R))\n(run 1)\n\
  (check (F x))\n"
-- A top-level action is a run of one empty-query rule; every run gets a ruleset of its
-- own, named by position; the declarations come from the uses.
#guard ((Program.ofEgg "(constructor A () Math) (A) (A)").map Program.render).toOption ==
  some "(sort Math)\n(ruleset r0)\n(ruleset r1)\n(constructor A () Math)\n\
    (rule () ((A)) :ruleset r0)\n(run r0 1)\n(rule () ((A)) :ruleset r1)\n(run r1 1)\n"
-- A run fires the rules registered in its ruleset so far; rules never run are dropped.
#guard ((Program.ofEgg "(rule ((A)) ((B))) (run 1) (rule ((B)) ((C))) (run 1)").map
    fun p => p.runs.map List.length).toOption == some [1, 2]
#guard ((Program.ofEgg "(rule ((A)) ((B))) (rule ((B)) ((C)) :ruleset R)").map
    fun p => p.rules.isEmpty).toOption == some true
-- Nested schedules: `seq`, `saturate`, `repeat`, and bare ruleset names.
#guard roundTrip "(rule ((A)) ((B)) :ruleset R)\n(rule ((B)) ((C)) :ruleset Q)\n\
  (run-schedule (saturate (seq (run R) (saturate (run Q)))))\n"
#guard ((Program.ofEgg "(rule ((A)) ((B)) :ruleset R) (run-schedule (repeat 2 R))").map
    fun p => p.runs.length).toOption == some 2
#guard ((Program.ofEgg "(run-schedule (saturate (run)))").map
    fun p => match p.schedule with
      | .saturate (.run []) => true
      | _ => false).toOption == some true
-- The generated tables: relations, disequality guards, and subsumption.
#guard roundTrip "(sort Math)\n(ruleset r0)\n(relation @UF (Math Math))\n\
  (rule ((@UF @a @b) (@UF @b @c) (!= @b @c)) ((subsume (@UF @a @b)) (@UF @a @c)) \
  :ruleset r0)\n(run-schedule (saturate (run r0)))\n"
-- The check is last and unique; a program without one ends in the empty check.
#guard (Program.ofEgg "(check (A)) (A)").isOk == false
#guard (Program.ofEgg "(check (A)) (check (B))").isOk == false
#guard ((Program.ofEgg "(A)").map (·.check.isEmpty)).toOption == some true
#guard ((Program.ofEgg "(A) (check (A) (= (A) (A)))").map (·.check.length)).toOption == some 2
#guard (Program.ofEgg "(datatype Math (A))").isOk == false
#guard (Program.ofEgg "(function Dist (Math) i64 :merge new)").isOk == false
#guard (Program.ofEgg "(constructor A () Math").isOk == false
#guard (Program.ofEgg "; a comment\n(sort Math) (constructor A () Math) (A)").isOk

end Egglog.Parse.Tests
