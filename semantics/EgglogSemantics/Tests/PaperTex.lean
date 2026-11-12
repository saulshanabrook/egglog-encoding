import EgglogSemantics.Congruence.Encode
import EgglogSemantics.SourceProof.Format
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

/-- Compare expressions by their printed spelling. -/
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
  -- A text-style sum's limits are small; `=0}^{10}` is dropped, leaving the `_{i}`.
  let s := s.replace "=0}^{10}" "}"
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
  | .rebuild (.subsume f) => "subsumed spellings of $" ++ name f ++ "$"
  | .rebuild (.view f) => "view of $" ++ name f ++ "$"
  | .rebuild (.stale f) => "stale view row of $" ++ name f ++ "$"
  | .rebuild (.index f) => "index of $" ++ name f ++ "$'s view"
  | .rebuild (.rekey f i) => s!"column {i + 1} of $" ++ name f ++ "$'s view moves"
  | .rebuild (.viewCongruence f) => "congruence of $" ++ name f ++ "$ over its view"

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
  rs.map Rule.toEgg == (maintenanceRules (!P.schedule.subsumeFreeB) P).map fun rm => rm.1.toEgg

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

/-- Render lines as an `eggprogram` in `\small`, omitting the final line break. -/
def eggprogram (body : String) : String :=
  let body := if body.endsWith "&&\\\\*\n" then body.dropRight 4 ++ "\n"
    else if body.endsWith "&&\\\\[.3em]\n" then body.dropRight 9 ++ "\n"
    else if body.endsWith "&&\\\\\n" then body.dropRight 3 ++ "\n"
    else body
  "\\begingroup\\small\n\\begin{eggprogram}\n" ++ body ++ "\\end{eggprogram}\n\\endgroup\n"

/-- The compiled program as an `eggprogram`: `M`, the schedule, the check. -/
def compiled (source : Program) : String :=
  let c := compile source
  let m := maintenanceRules (!source.schedule.subsumeFreeB) source
  let mBlock := line 0 "M\\triangleq\\{"
    ++ String.join (m.map fun rm => rule 1 rm.1 (some rm.2)) ++ line 0 "\\}" (gap := true)
  let (sched, _) := schedule source c.origins 0 c.program.schedule
  let check := pack 0 "\\kw{check}\\ " "\\land " (c.program.check.map (pattern [])) none
    (sepAtEnd := false)
  eggprogram (mBlock ++ sched ++ check)

/-! ## Proofs

A source proof in the syntax of the paper's proof figure, `rule_i(c, σ; π₁, …, πₙ)`,
`sym(π)`, `trans(π, π)` and `cong_k(π, π)`, with rule indices and child positions counted
from one as the paper does. What recurs is bound first by a `let`: nested terms mentioned in
more than one place as `t₁, t₂, …`, substitutions of more than one rule node as
`σ₁, σ₂, …`, and rule nodes with premises that occur more than once as `π₁, π₂, …`. A node
that fits on a line is printed inline; otherwise its arguments go on the following lines,
one level in. Every line carries a comment saying what its node proves, or what a firing
matched, in the arithmetic reading of the example's constructors. -/

open SourceProof (Proof Claim)

/-- A term at the top level; the leaf shorthand applies there too. -/
def term (abbrevs : List Expr) (t : Term) : String :=
  let e := t.toExpr
  (leafSugar e).getD (expr abbrevs e)

def claim (abbrevs : List Expr) (c : Claim) : String :=
  term abbrevs c.lhs ++ " = " ++ term abbrevs c.rhs

/-- The arithmetic reading of the paper's example, for comments: `Num(n)` is `n`,
`Var("i")` is `i`, `Mul(a, b)` is `a·b` and `Sum0-10("i", b)` is a sum over `i`; any other
constructor applies to the readings of its arguments. -/
partial def math : Expr → String
  | .app "Num" [.lit (.int n)] => toString n
  | .app "Var" [.lit (.str v)] => v
  | .app "Mul" [a, b] =>
    let left := match a with
      | .app "Sum0-10" _ => "(" ++ math a ++ ")"
      | _ => math a
    left ++ "\\cdot " ++ math b
  | .app "Sum0-10" [.lit (.str v), b] => "\\sum_{" ++ v ++ "=0}^{10}" ++ math b
  | .app f args =>
    if args.isEmpty then name f ++ "()"
    else name f ++ "(" ++ String.intercalate ",\\," (args.map math) ++ ")"
  | .lit (.int n) => toString n
  | .lit (.str s) => strLit s
  | .var v => var v
  | .min a b => "\\min(" ++ math a ++ ",\\," ++ math b ++ ")"

/-- Whether a term is arithmetic in that reading, so that its reflexive claim reads as
existence rather than as a relation holding. -/
def arithmetic : Expr → Bool
  | .app f _ => f == "Num" || f == "Var" || f == "Mul" || f == "Sum0-10"
  | .lit _ => true
  | _ => false

/-- Math inside a comment, in text style so that a sum stays on the line. -/
def inMath (s : String) : String := "$\\textstyle " ++ s ++ "$"

/-- What a node proves. -/
def proves (c : Claim) : String :=
  let l := c.lhs.toExpr
  if c.lhs == c.rhs then
    "proves " ++ inMath (math l) ++ " " ++ (if arithmetic l then "exists" else "holds")
  else "proves " ++ inMath (math l ++ " = " ++ math c.rhs.toExpr)

/-- What a node proves, and for a congruence, where: the argument it rewrites. -/
def provesNode (p : Proof) : String :=
  match p with
  | .congr q k _ =>
    match q.claim.rhs with
    | .app f _ =>
      proves p.claim ++ " by congruence in argument " ++ toString (k + 1) ++ " of $" ++ name f ++ "$"
    | _ => proves p.claim
  | _ => proves p.claim

/-- What a firing of rule `i` under `σ` matched: the instances of its query. -/
def matched (P : Program) (i : Nat) (σ : Env) : Option String := do
  let r ← P.rules[i]?
  if r.query.isEmpty then none else
  let parts ← r.query.mapM fun p => match p with
    | .expr e => (e.eval σ).map fun t => math t.toExpr
    | .eq a b => do some (math (← a.eval σ).toExpr ++ " = " ++ math (← b.eval σ).toExpr)
    | .ne a b => do some (math (← a.eval σ).toExpr ++ " \\ne " ++ math (← b.eval σ).toExpr)
  some ("matches " ++ inMath (String.intercalate " \\land " parts))

/-- The variables of a query, left to right, each once. -/
partial def queryVars (q : Query) : List Var :=
  let rec ofExpr : Expr → List Var
    | .var v => [v]
    | .app _ args => args.flatMap ofExpr
    | .min a b => ofExpr a ++ ofExpr b
    | .lit _ => []
  let ofPattern : Pattern → List Var
    | .expr e => ofExpr e
    | .eq a b | .ne a b => ofExpr a ++ ofExpr b
  (q.flatMap ofPattern).foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []

/-- The variable order of rule `i`. -/
def ruleOrder (P : Program) (i : Nat) : List Var :=
  (P.rules[i]?.map fun r => queryVars r.query).getD []

/-- A substitution, its bindings in the order the rule's query first mentions them. -/
def subst (abbrevs : List Expr) (order : List Var) (σ : Env) : String :=
  let σ := (order.filterMap fun v => σ.find? (·.1 == v))
    ++ σ.filter fun b => !order.contains b.1
  if σ.isEmpty then "\\emptyset"
  else "[" ++ String.intercalate ",\\ " (σ.map fun b => var b.1 ++ "\\mapsto " ++ term abbrevs b.2)
    ++ "]"

/-- What an elided rendering leaves out. `shared`: the definitions of the shared subproofs,
whose names remain. `existence`: premises that only prove a term exists (a rule node with a
reflexive arithmetic claim), shown as `…`. `relations`: proofs that a non-arithmetic fact
holds, shown as `rule_i(c, …)`. `localNames`: name only terms that recur in what is shown,
rather than in the full proof. -/
structure Elision where
  shared : Bool := false
  existence : Bool := false
  relations : Bool := false
  localNames : Bool := false

def elideAll : Elision :=
  { shared := true, existence := true, relations := true, localNames := true }

/-- A premise that only proves a term exists. -/
def existenceLeaf : Proof → Bool
  | .rule c _ _ _ => c.lhs == c.rhs && arithmetic c.lhs.toExpr
  | _ => false

def relationProof : Proof → Bool
  | .rule c _ _ _ => c.lhs == c.rhs && !arithmetic c.lhs.toExpr
  | _ => false

/-- Names for repeated terms, substitutions and rule nodes. Substitutions and rule nodes
share a name when their rendered text agrees. -/
structure Names where
  elision : Elision
  terms : List Expr
  substs : List (String × Nat × Nat × Env)
  proofs : List (String × Nat × Proof)

/-- A substitution, by its name when it has one. -/
def substNamed (P : Program) (names : Names) (i : Nat) (σ : Env) : String :=
  let text := subst names.terms (ruleOrder P i) σ
  match names.substs.find? (·.1 == text) with
  | some (_, k, _, _) => "\\sigma_{" ++ toString k ++ "}"
  | none => text

/-- The nested applications of a term under the leaf shorthand, innermost first: an
argument that reads as a leaf, like `5` for `Num(5)`, does not make its parent nested. -/
partial def proofSubs (e : Expr) : List Expr :=
  let args := match e with | .app _ args => args | _ => []
  let inner := dedup (args.flatMap proofSubs)
  let deep := args.any fun a => match a with
    | .app _ _ => (leafSugar a).isNone
    | _ => false
  if deep && !has inner e then inner ++ [e] else inner

/-- The rule nodes, in postorder. -/
partial def ruleNodes : Proof → List Proof
  | p@(.rule _ _ _ ps) => ps.flatMap ruleNodes ++ [p]
  | .symm p => ruleNodes p
  | .trans p q | .congr p _ q => ruleNodes p ++ ruleNodes q

/-- A proof on one line, without abbreviations or names: the key a subproof is recognized
by. -/
partial def inlineProof (P : Program) : Proof → String
  | .rule c i σ ps =>
    "\\kw{rule}_{" ++ toString (i + 1) ++ "}(" ++ claim [] c ++ ",\\ "
      ++ subst [] (ruleOrder P i) σ
      ++ (if ps.isEmpty then ")"
          else ";\\ " ++ String.intercalate ",\\ " (ps.map (inlineProof P)) ++ ")")
  | .symm p => "\\kw{sym}(" ++ inlineProof P p ++ ")"
  | .trans p q => "\\kw{trans}(" ++ inlineProof P p ++ ",\\ " ++ inlineProof P q ++ ")"
  | .congr p k q =>
    "\\kw{cong}_{" ++ toString (k + 1) ++ "}(" ++ inlineProof P p ++ ",\\ " ++ inlineProof P q
      ++ ")"

/-- The keyed items whose key occurs at least twice, each once, in order of first occurrence. -/
def recurring {α : Type} (keyed : List (String × α)) : List (String × α) :=
  let firsts := keyed.foldl
    (fun acc kp => if acc.any (·.1 == kp.1) then acc else acc ++ [kp]) []
  firsts.filter fun kp => (keyed.filter (·.1 == kp.1)).length ≥ 2

/-- What a rendering shows of a proof under an elision, given the keys of the named
subproofs: the rule nodes whose substitution appears, and the terms that appear. A
reference to a named proof shows nothing, an elided existence leaf nothing, and an elided
relation proof only its claim. `top` is the root of a rendering, which is never elided. -/
partial def shown (P : Program) (e : Elision) (hidden : List String) (top : Bool) :
    Proof → List Proof × List Term
  | p@(.rule c _ σ ps) =>
    if !top && hidden.contains (inlineProof P p) then ([], [])
    else if !top && e.existence && existenceLeaf p then ([], [])
    else if !top && e.relations && relationProof p then ([], [c.lhs, c.rhs])
    else
      let rest := ps.map (shown P e hidden false)
      (p :: rest.flatMap (·.1), c.lhs :: c.rhs :: σ.map (·.2) ++ rest.flatMap (·.2))
  | .symm p => shown P e hidden false p
  | .trans p q | .congr p _ q =>
    let a := shown P e hidden false p
    let b := shown P e hidden false q
    (a.1 ++ b.1, a.2 ++ b.2)

/-- What recurs in a proof, under an elision. Rule nodes with premises: those occurring at
least twice, numbered in postorder of first occurrence so that a named proof refers only to
names before it. Terms: the nested applications that occur, as subterms, in at least two
of the full proof's claims and substitution values, and still somewhere in what is shown,
so that an elided rendering names terms as the full one does. Substitutions: those of at
least two distinct shown rule nodes. -/
def names (P : Program) (e : Elision) (pf : Proof) : Names :=
  let nodes := ruleNodes pf
  let shared := recurring (nodes.filterMap fun p => match p with
    | .rule _ _ _ ps => if ps.isEmpty then none else some (inlineProof P p, p)
    | _ => none)
  let hidden := shared.map (·.1)
  let parts := shown P e hidden true pf ::
    (if e.shared then [] else shared.map fun kp => shown P e hidden true kp.2)
  let positions := parts.flatMap (·.2)
  let full := (shown P {} hidden true pf).2
    ++ (shared.map fun kp => shown P {} hidden true kp.2).flatMap (·.2)
  let occurrences (ts : List Term) (x : Expr) : Nat :=
    (ts.filter fun t => t.subtermList.any fun s => same s.toExpr x).length
  let candidates := dedup (full.flatMap fun t => proofSubs t.toExpr)
  -- With local names, a term is named only when the name saves room: it recurs in what
  -- is shown and is wide when spelled out with the names chosen before it.
  let terms :=
    if e.localNames then
      candidates.foldl (fun acc x =>
        if occurrences positions x ≥ 2 && visible (expr acc x) ≥ 15 then acc ++ [x] else acc) []
    else candidates.filter fun x => occurrences full x ≥ 2 && occurrences positions x ≥ 1
  let distinct := ((parts.flatMap (·.1)).map fun p => (inlineProof P p, p)).foldl
    (fun acc kp => if acc.any (·.1 == kp.1) then acc else acc ++ [kp]) []
  let substs := recurring (distinct.filterMap fun kp => match kp.2 with
    | .rule _ i σ _ => if σ.isEmpty then none else some (subst terms (ruleOrder P i) σ, (i, σ))
    | _ => none)
  { elision := e
    terms := terms
    substs := substs.zipIdx.map fun (kp, k) => (kp.1, k + 1, kp.2.1, kp.2.2)
    proofs := shared.zipIdx.map fun (kp, k) => (kp.1, k + 1, kp.2) }

mutual

/-- A proof at a depth, after `lead` and ending in `suffix`: one line if it fits, else
spread over lines. The first line says what the node proves; a substitution on a line of
its own says what the firing matched. `top` is the root of a rendering, never elided. -/
partial def proofLines (P : Program) (names : Names) (depth : Nat) (top : Bool)
    (lead suffix : String) (p : Proof) : String :=
  let comment := provesNode p
  let e := names.elision
  match names.proofs.find? (·.1 == inlineProof P p) with
  | some (_, k, _) => line depth (lead ++ "\\pi_{" ++ toString k ++ "}" ++ suffix) (some comment)
  | none =>
    -- A comment is set in footnotesize, so it takes about four fifths of its width.
    let budget := 74 - 4 * depth - (visible comment * 4 / 5 + 3)
    let one := lead ++ inlineNamed P names top p ++ suffix
    if visible one ≤ budget || (!top && e.existence && existenceLeaf p)
        || (!top && e.relations && relationProof p) then
      line depth one (some comment)
    else
    match p with
    | .rule c i σ ps =>
      let head := lead ++ "\\kw{rule}_{" ++ toString (i + 1) ++ "}(" ++ claim names.terms c ++ ","
      let bindings := substNamed P names i σ ++ (if ps.isEmpty then ")" ++ suffix else ";")
      -- The claim and the substitution share a line when they fit.
      let opening :=
        if visible (head ++ " " ++ bindings) ≤ budget then
          line depth (head ++ "\\ " ++ bindings) (some comment)
        else line depth head (some comment) ++ line (depth + 1) bindings (matched P i σ)
      opening ++ argLines P names (depth + 1) (")" ++ suffix) ps
    | .symm q =>
      line depth (lead ++ "\\kw{sym}(") (some comment)
        ++ proofLines P names (depth + 1) false "" (")" ++ suffix) q
    | .trans q r =>
      line depth (lead ++ "\\kw{trans}(") (some comment)
        ++ argLines P names (depth + 1) (")" ++ suffix) [q, r]
    | .congr q k r =>
      line depth (lead ++ "\\kw{cong}_{" ++ toString (k + 1) ++ "}(") (some comment)
        ++ argLines P names (depth + 1) (")" ++ suffix) [q, r]

/-- Arguments on their own lines, comma-separated, the last closing with `close`. An elided
existence premise, which prints as `…`, shares the line of the argument after it. -/
partial def argLines (P : Program) (names : Names) (depth : Nat) (close : String)
    (ps : List Proof) : String :=
  let e := names.elision
  let elided (p : Proof) : Bool := e.existence && existenceLeaf p
  let rec go (lead : String) : List Proof → String
    | [] => if lead.isEmpty then "" else line depth (lead.dropRight 3 ++ close)
    | [p] => proofLines P names depth false lead close p
    | p :: ps =>
      if elided p then go (lead ++ "\\ldots,\\ ") ps
      else proofLines P names depth false lead "," p ++ go "" ps
  go "" ps

/-- A proof on one line, with the names in use and the elision applied. -/
partial def inlineNamed (P : Program) (names : Names) (top : Bool) (p : Proof) : String :=
  let e := names.elision
  match names.proofs.find? (·.1 == inlineProof P p) with
  | some (_, k, _) => "\\pi_{" ++ toString k ++ "}"
  | none =>
    if !top && e.existence && existenceLeaf p then "\\ldots" else
    match p with
    | .rule c i σ ps =>
      if !top && e.relations && relationProof p then
        "\\kw{rule}_{" ++ toString (i + 1) ++ "}(" ++ claim names.terms c ++ ",\\ \\ldots)"
      else
      "\\kw{rule}_{" ++ toString (i + 1) ++ "}(" ++ claim names.terms c ++ ",\\ "
        ++ substNamed P names i σ
        ++ (if ps.isEmpty then ")"
            else ";\\ " ++ String.intercalate ",\\ " (ps.map (inlineNamed P names false)) ++ ")")
    | .symm q => "\\kw{sym}(" ++ inlineNamed P names false q ++ ")"
    | .trans q r =>
      "\\kw{trans}(" ++ inlineNamed P names false q ++ ",\\ " ++ inlineNamed P names false r
        ++ ")"
    | .congr q k r =>
      "\\kw{cong}_{" ++ toString (k + 1) ++ "}(" ++ inlineNamed P names false q ++ ",\\ "
        ++ inlineNamed P names false r ++ ")"

end

/-- A proof as an `eggprogram`: `let`s for the named terms, substitutions and shared
subproofs, then the proof, under an elision. -/
def proof (P : Program) (pf : Proof) (e : Elision := {}) : String :=
  let ns := names P e pf
  let letKw := "\\kw{let}\\ "
  let terms := ns.terms.zipIdx.map fun (x, k) =>
    line 0 (letKw ++ "t_{" ++ toString (k + 1) ++ "} = " ++ expr (ns.terms.take k) x)
      (some (inMath (math x)))
  let substs := ns.substs.map fun (text, k, i, σ) =>
    line 0 (letKw ++ "\\sigma_{" ++ toString k ++ "} = " ++ text) (matched P i σ)
  let proofs := if e.shared then [] else ns.proofs.map fun (_, k, p) =>
    proofLines P { ns with proofs := ns.proofs.filter (·.2.1 < k) } 0 true
      (letKw ++ "\\pi_{" ++ toString k ++ "} = ") "" p
  let breakable (l : String) : String := (l.dropRight "&&\\\\*\n".length) ++ "&&\\\\\n"
  let lets := String.join ((terms ++ substs).map breakable ++ proofs)
  -- A little room between the last `let` and the proof, whichever line end it has.
  let lets := if lets.endsWith "&&\\\\*\n" then lets.dropRight 6 ++ "&&\\\\[.3em]\n"
    else if lets.endsWith "&&\\\\\n" then lets.dropRight 5 ++ "&&\\\\[.3em]\n"
    else lets
  eggprogram (lets ++ proofLines P ns 0 true "" "" pf)

end Egglog.PaperTex
