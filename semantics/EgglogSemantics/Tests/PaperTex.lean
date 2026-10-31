import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Tests.Egg

/-!
# Programs in the paper's notation

Renders a compiled program as the body of the paper's `eggprogram` environment, in the
notation of its semantics section: rules as `Q ⇒ H`, keywords in `\kw`, generated names
without their `@`, and one comment per generated rule saying what it maintains. The
maintenance rules, which every compiled run is followed by, are printed once as `M`. A
head is a set, so each distinct action is printed once, and the nested terms a head builds
are named `t₁, t₂, …` in a `where` clause, innermost first. The paper's shorthand for
leaves applies throughout: `Num(5)` is written `5` and `Var("i")` is written `"i"`, so the
rows for the integer `5` and for the node `Num(5)` print alike and are shown once.
-/

namespace Egglog.PaperTex

open Congruence

/-- A function symbol: `Sum0-10` as the paper spells it, generated names without the `@`,
everything else in typewriter. -/
def name (f : FnName) : String :=
  if f = "Sum0-10" then "\\SumZeroTen"
  else if "@".isPrefixOf f then "\\mathtt{" ++ String.ofList (f.toList.drop 1) ++ "}"
  else "\\mathtt{" ++ f ++ "}"

/-- A variable: generated `@x7` becomes `x_7`; a multi-letter source name is set upright. -/
def var (v : Var) : String :=
  let cs := match v.toList with
    | '@' :: rest => rest
    | cs => cs
  let letters := cs.takeWhile Char.isAlpha
  let digits := cs.drop letters.length
  if letters.length = 1 && digits.all Char.isDigit && !digits.isEmpty then
    String.ofList letters ++ "_{" ++ String.ofList digits ++ "}"
  else if letters.length = 1 && digits.isEmpty then String.ofList letters
  else "\\mathit{" ++ String.ofList cs ++ "}"

/-- Expressions compared by spelling; `Expr` carries no `BEq`. -/
def same (a b : Expr) : Bool := a.toEgg == b.toEgg
def has (l : List Expr) (e : Expr) : Bool := l.any (same e)
def index? (l : List Expr) (e : Expr) : Option Nat := l.findIdx? (same e)
def dedup (l : List Expr) : List Expr := l.foldl (fun acc s => if has acc s then acc else acc ++ [s]) []

/-- Whether an application has an application among its arguments. -/
def nested : Expr → Bool
  | .app _ args => args.any fun a => match a with | .app _ _ => true | _ => false
  | _ => false

/-- The nested applications of an expression, itself included, innermost first, each once. -/
partial def nestedSubs (e : Expr) : List Expr :=
  let inner := dedup <| match e with
    | .app _ args => args.flatMap nestedSubs
    | .min a b => nestedSubs a ++ nestedSubs b
    | _ => []
  if nested e && !has inner e then inner ++ [e] else inner

/-- The nested applications strictly below the top of an expression: what a head
abbreviates, so that each action still names its own table. -/
def argSubs : Expr → List Expr
  | .app _ args => dedup (args.flatMap nestedSubs)
  | .min a b => dedup (nestedSubs a ++ nestedSubs b)
  | _ => []

/-- The width of a rendered item on the page, roughly: commands and braces take no room. -/
def visible (s : String) : Nat :=
  let s := (s.replace "\\SumZeroTen" "Sum").replace "\\texttt" ""
  (s.toList.foldl (fun (acc : Nat × Bool) c =>
    if c = '\\' then (acc.1, true)
    else if acc.2 && c.isAlpha then (acc.1, true)
    else if c = '{' || c = '}' then (acc.1, false)
    else (acc.1 + 1, false)) (0, false)).1

def strLit (s : String) : String := "\\text{\\texttt{\"" ++ s ++ "\"}}"

/-- The paper's shorthand for leaves: `Num(5)` is `5` and `Var("i")` is `"i"`. -/
def leafSugar : Expr → Option String
  | .app "Num" [.lit (.int n)] => some (toString n)
  | .app "Var" [.lit (.str s)] => some (strLit s)
  | _ => none

/-- Render an expression, naming the abbreviated terms `abbrevs` as `t_k`. -/
partial def expr (abbrevs : List Expr) : Expr → String
  | .lit (.int n) => toString n
  | .lit (.str s) => strLit s
  | .var v => var v
  | e@(.app f args) =>
    match index? abbrevs e with
    | some k => "t_{" ++ toString (k + 1) ++ "}"
    | none =>
      let arg (a : Expr) : String := (leafSugar a).getD (expr abbrevs a)
      if args.isEmpty then name f ++ "()"
      else name f ++ "(" ++ String.intercalate ",\\," (args.map arg) ++ ")"
  | .min a b => "\\min(" ++ expr abbrevs a ++ ",\\," ++ expr abbrevs b ++ ")"

def pattern (abbrevs : List Expr) : Pattern → String
  | .expr e => expr abbrevs e
  | .eq a b => expr abbrevs a ++ " = " ++ expr abbrevs b
  | .ne a b => expr abbrevs a ++ " \\ne " ++ expr abbrevs b

def action (abbrevs : List Expr) : Action → String
  | .expr e => expr abbrevs e
  | .union a b => "\\kw{union}(" ++ expr abbrevs a ++ ",\\," ++ expr abbrevs b ++ ")"
  | .subsume f es => "\\kw{subsume}(" ++ expr abbrevs (.app f es) ++ ")"

/-- One `flalign*` line at a nesting depth. A line with `gap` ends a rule or a block: it
adds space after itself and lets the page break there; every other line forbids a break,
so a rule stays together. -/
def line (depth : Nat) (body : String) (comment : Option String := none) (gap : Bool := false) :
    String :=
  "  &" ++ String.join (List.replicate depth "\\quad ") ++ body
    ++ (match comment with | some c => "\\quad\\codecomment{" ++ c ++ "}" | none => "")
    ++ (if gap then "&&\\\\[.3em]\n" else "&&\\\\*\n")

/-- Pack items onto lines; a continuation is indented one level further. With `sepAtEnd` a
broken line ends with the separator (commas), otherwise the continuation starts with it
(conjunctions). The comment goes on the first line. The budget is in visible characters,
less four per indentation level. -/
def pack (depth : Nat) (lead sep : String) (items : List String) (comment : Option String)
    (gap : Bool := false) (sepAtEnd : Bool := true) : String :=
  let budget := 74 - 4 * depth
  -- The comment sits on the first line and takes its share of the width.
  let firstBudget := budget - (match comment with | some c => visible c + 4 | none => 0)
  let emit (first : Bool) (cur : String) (broken : Bool) (c : Option String) (g : Bool) :=
    let body := (if first then lead else if sepAtEnd then "" else "{}" ++ sep) ++ cur
      ++ (if broken && sepAtEnd then sep else "")
    line (if first then depth else depth + 1) body (if first then c else none) g
  let rec go (acc : String) (cur : String) (width : Nat) (first : Bool) : List String → String
    | [] => acc ++ emit first cur false comment gap
    | s :: rest =>
      if cur.isEmpty then go acc s (visible s) first rest
      else if width + visible s + visible sep ≤ (if first then firstBudget else budget) then
        go acc (cur ++ sep ++ s) (width + visible s + visible sep) first rest
      else go (acc ++ emit first cur true comment false) s (visible s) false rest
  go "" "" 0 true items

def ruleComment : RuleOrigin → String
  | .source k => s!"compiled from rule {k + 1}"
  | .rebuild .compress => "path compression"
  | .rebuild .collide => "two parents: keep the smaller"
  | .rebuild (.congruence f) => "congruence of $" ++ name f ++ "$"

/-- The expressions a rule head evaluates. -/
def actionExprs : Action → List Expr
  | .expr e => [e]
  | .union a b => [a, b]
  | .subsume f es => [.app f es]

/-- A rule: its query packed on lines, its distinct actions, and the terms they build. -/
def rule (depth : Nat) (r : Rule) (origin : Option RuleOrigin) : String :=
  let actions := r.actions.foldl
    (fun acc a => if acc.any (fun b => b.toEgg == a.toEgg) then acc else acc ++ [a]) []
  let abbrevs := dedup ((actions.flatMap actionExprs).flatMap argSubs)
  let query := if r.query.isEmpty then ["\\top"] else r.query.map (pattern abbrevs)
  -- Rows that print alike under the leaf shorthand are shown once.
  let heads := (actions.map (action abbrevs)).foldl
    (fun acc h => if acc.contains h then acc else acc ++ [h]) []
  let defs := abbrevs.zipIdx.map fun (e, k) =>
    "t_{" ++ toString (k + 1) ++ "} = " ++ expr (abbrevs.take k) e
  pack depth "" "\\land " query (origin.map ruleComment) (sepAtEnd := false)
    ++ pack (depth + 1) "\\Rightarrow " ",\\ " heads none (gap := defs.isEmpty)
    ++ (if defs.isEmpty then ""
        else pack (depth + 1) "\\text{where }" ",\\ " defs none (gap := true))

/-- Whether a run is exactly the maintenance set, compared by spelling. -/
def isMaintenance (P : Program) (rs : List Rule) : Bool :=
  rs.map Rule.toEgg == (maintenanceRules P).map fun rm => rm.1.toEgg

/-- The schedule, with the maintenance set `M` named rather than repeated. -/
partial def schedule (P : Program) (origins : List RuleOrigin) (depth : Nat) :
    Schedule → String × List RuleOrigin
  | .run rs =>
    if isMaintenance P rs then
      (line depth "\\kw{run}\\ M;", origins.drop rs.length)
    else
      let body := String.join <| (rs.zip (origins.take rs.length)).map
        fun (ro : Rule × RuleOrigin) => rule (depth + 1) ro.1 (some ro.2)
      (line depth "\\kw{run}\\ \\{" ++ body ++ line depth "\\};" (gap := true),
        origins.drop rs.length)
  | .saturate S =>
    match S with
    | .run rs =>
      if isMaintenance P rs then
        (line depth "\\kw{saturate}(\\kw{run}\\ M);" (gap := true), origins.drop rs.length)
      else
        let (inner, rest) := schedule P origins (depth + 1) S
        (line depth "\\kw{saturate}\\bigl(" ++ inner ++ line depth "\\bigr);" (gap := true), rest)
    | _ =>
      let (inner, rest) := schedule P origins (depth + 1) S
      (line depth "\\kw{saturate}\\bigl(" ++ inner ++ line depth "\\bigr);" (gap := true), rest)
  | .seq S₁ S₂ =>
    let (a, rest) := schedule P origins depth S₁
    let (b, rest') := schedule P rest depth S₂
    (a ++ b, rest')

/-- The compiled program as an `eggprogram`: `M`, the schedule, the check. -/
def compiled (source : Program) : String :=
  let c := compile source
  let m := maintenanceRules source
  let mBlock := line 0 "M\\triangleq\\{"
    ++ String.join (m.map fun rm => rule 1 rm.1 (some rm.2)) ++ line 0 "\\}" (gap := true)
  let (sched, _) := schedule source c.origins 0 c.program.schedule
  let check := pack 0 "\\kw{check}\\ " "\\land " (c.program.check.map (pattern [])) none
    (sepAtEnd := false)
  "\\begingroup\\small\n\\begin{eggprogram}\n" ++ mBlock ++ sched ++ check
    ++ "\\end{eggprogram}\n\\endgroup\n"

end Egglog.PaperTex
