import Std.Data.HashMap
import Std.Data.HashSet
import EgglogSemantics.Slotted.Target.Spec

/-!
# An interpreter for target programs

The compiled programs of the slotted pass are too large for the finite reference interpreter,
whose congruence closure is quadratic in the stored terms, so they run on an e-graph of their
own: hash-consed terms, a union-find with congruence closure, subsumption modulo congruent
children, representatives by `Term.blt`, and a matcher that joins table atoms over the rows
modulo congruence, binds computed variables by evaluating their definitions, ranges over the
elements of a `@mem` pattern, and tests equalities and disequalities on reduced values as
`TMatches` does. Rounds match every rule against the pre-state and then apply every firing;
a saturation stops when a pass adds no term, merges no classes and subsumes no live row,
which is when the meaning of the state is unchanged. `observe` is the outcome of a program.
-/

namespace Egglog.Slotted.Target

mutual

def Term.hashT : Term → UInt64
  | .lit (.int n) => mixHash 1 (hash n)
  | .lit (.str s) => mixHash 2 (hash s)
  | .app f args => mixHash (hash f) (Term.hashList args)

def Term.hashList : List Term → UInt64
  | [] => 7
  | t :: ts => mixHash (Term.hashT t) (Term.hashList ts)

end

instance : Hashable Term := ⟨Term.hashT⟩

instance : Inhabited Term := ⟨.lit (.int 0)⟩

/-- A canonical key: a head over the classes of its children. -/
abbrev Key := FnName × List Nat

/-- The e-graph. Ids index `terms`; `parent` is the union-find; the caches after `rebuild`
give each id its class's representative term, the distinct live rows of each head and the
keys of the subsumed rows. -/
structure EGraph where
  terms : Array Term := #[]
  ids : Std.HashMap Term Nat := {}
  parent : Array Nat := #[]
  /-- The head and child ids of an application. -/
  heads : Array (Option (FnName × List Nat)) := #[]
  /-- The rows (application ids) of each head. -/
  rows : Std.HashMap FnName (Array Nat) := {}
  /-- The rows subsumed as written. -/
  subsumedRows : Array Nat := #[]
  /-- Caches, valid after `rebuild`. -/
  repOf : Array Nat := #[]
  subsumedKeys : Std.HashSet Key := {}
  /-- One live row per canonical key, by head: the key and a row id. -/
  liveRows : Std.HashMap FnName (Array (List Nat × Nat)) := {}
  classes : Nat := 0

namespace EGraph

def find (g : EGraph) (i : Nat) : Nat := go i g.parent.size
where
  go (i : Nat) : Nat → Nat
    | 0 => i
    | fuel + 1 => let p := g.parent[i]!; if p = i then i else go p fuel

def idOf (g : EGraph) (t : Term) : Option Nat := g.ids[t]?

/-- The canonical key of an application id. -/
def keyOf (g : EGraph) (i : Nat) : Option Key :=
  (g.heads[i]!).map fun fa => (fa.1, fa.2.map g.find)

/-- Insert a term and its subterms; the term's id. -/
partial def addTerm (g : EGraph) (t : Term) : EGraph × Nat :=
  match g.ids[t]? with
  | some i => (g, i)
  | none =>
    let (g, head) := match t with
      | .lit _ => (g, none)
      | .app f args =>
        let (g, ids) := args.foldl (fun (acc : EGraph × List Nat) a =>
          let (g', j) := acc.1.addTerm a
          (g', acc.2 ++ [j])) (g, [])
        (g, some (f, ids))
    let i := g.terms.size
    let g := { g with terms := g.terms.push t, ids := g.ids.insert t i, parent := g.parent.push i,
                      heads := g.heads.push head }
    match head with
    | some (f, _) => ({ g with rows := g.rows.insert f ((g.rows.getD f #[]).push i) }, i)
    | none => (g, i)

/-- Merge two classes; the smaller root survives. -/
def union (g : EGraph) (i j : Nat) : EGraph :=
  let ri := g.find i
  let rj := g.find j
  if ri = rj then g
  else if ri < rj then { g with parent := g.parent.set! rj ri }
  else { g with parent := g.parent.set! ri rj }

def subsume (g : EGraph) (i : Nat) : EGraph :=
  if g.subsumedRows.contains i then g else { g with subsumedRows := g.subsumedRows.push i }

/-- One pass of congruence: applications with one canonical key are merged. -/
def congruencePass (g : EGraph) : EGraph × Bool := Id.run do
  let mut g := g
  let mut changed := false
  let mut seen : Std.HashMap Key Nat := {}
  for i in [0:g.terms.size] do
    match g.keyOf i with
    | none => pure ()
    | some k =>
      match seen[k]? with
      | some j =>
        if g.find i != g.find j then
          g := g.union i j
          changed := true
      | none => seen := seen.insert k i
  return (g, changed)

partial def closeCongruence (g : EGraph) : EGraph :=
  let (g', changed) := g.congruencePass
  if changed then closeCongruence g' else g'

/-- Close congruence and refresh the caches. -/
def rebuild (g : EGraph) : EGraph := Id.run do
  let mut g := g.closeCongruence
  -- representatives: the least term of each class
  let mut best : Std.HashMap Nat Nat := {}
  for i in [0:g.terms.size] do
    let r := g.find i
    match best[r]? with
    | some j => if Term.blt g.terms[i]! g.terms[j]! then best := best.insert r i
    | none => best := best.insert r i
  let mut rep : Array Nat := Array.replicate g.terms.size 0
  for i in [0:g.terms.size] do
    rep := rep.set! i (best.getD (g.find i) i)
  -- subsumed keys
  let mut subs : Std.HashSet Key := {}
  for i in g.subsumedRows do
    match g.keyOf i with
    | some k => subs := subs.insert k
    | none => pure ()
  -- live rows per head, one per key
  let mut live : Std.HashMap FnName (Array (List Nat × Nat)) := {}
  for (f, is) in g.rows.toList do
    let mut seen : Std.HashSet (List Nat) := {}
    let mut out : Array (List Nat × Nat) := #[]
    for i in is do
      match g.keyOf i with
      | some k =>
        if !subs.contains k && !seen.contains k.2 then
          seen := seen.insert k.2
          out := out.push (k.2, i)
      | none => pure ()
    live := live.insert f out
  return { g with repOf := rep, subsumedKeys := subs, liveRows := live, classes := best.size }

/-- The representative term of an id's class. -/
def repTerm (g : EGraph) (i : Nat) : Term := g.terms[g.repOf[i]!]!

/-- The class of a term, including an unstored spelling with congruent children. -/
partial def classOf (g : EGraph) (t : Term) : Option Nat :=
  match g.idOf t with
  | some i => some (g.find i)
  | none => match t with
    | .lit _ => none
    | .app f args => do
      let cs ← args.mapM g.classOf
      let i ← (g.rows.getD f #[]).toList.find? fun i => g.keyOf i == some (f, cs)
      pure (g.find i)

/-- Membership in `Database.live`: an existing spelling with no subsumed row key. -/
def live (g : EGraph) (t : Term) : Bool :=
  (g.classOf t).isSome && match t with
    | .lit _ => true
    | .app f args => match args.mapM g.classOf with
      | some cs => !g.subsumedKeys.contains (f, cs)
      | none => false

/-- Whether two reduced values agree: the same term, or stored in one class. -/
def agree (g : EGraph) (t u : Term) : Bool :=
  t == u || match g.classOf t, g.classOf u with
    | some a, some b => a == b
    | _, _ => false

end EGraph

/-! ### Matching -/

/-- The executable `TExpr.Matches`. Primitive operands are evaluated; table operands must
match recursively, and table instances must be live even when their class still exists. -/
partial def exprMatches (g : EGraph) (σ : Env) : Expr → Bool
  | .var v => (Env.lookup v σ).isSome
  | .lit l => g.live (.lit l)
  | .min a b => exprMatches g σ a && exprMatches g σ b
  | e@(.app f args) =>
    if isPrimName f then (evalExpr e σ).isSome
    else args.all (exprMatches g σ) && ((evalExpr e σ).map g.live).getD false

/-- The variables of an expression not bound in `σ`. -/
def unbound (σ : Env) (e : Expr) : List Var := e.vars.filter fun v => (Env.lookup v σ).isNone

/-- The kind of a pattern for the matcher. -/
inductive PKind where
  /-- A table atom: the class variable, if any, the head and the arguments. -/
  | atom (cls : Option Var) (f : FnName) (args : List Expr)
  /-- `v = @op(…)`. -/
  | bind (v : Var) (e : Expr)
  /-- `@mem(x, e)`. -/
  | mem (x : Var) (e : Expr)
  | test (p : Pattern)

def classify : Pattern → PKind
  | .eq (.var v) (.app f args) =>
    if isPrimName f then .bind v (.app f args)
    else if f = memName then .test (.eq (.var v) (.app f args))
    else .atom (some v) f args
  | .expr (.app f args) =>
    if f = memName then
      match args with
      | [.var x, e] => .mem x e
      | _ => .test (.expr (.app f args))
    else if isPrimName f then .test (.expr (.app f args))
    else .atom none f args
  | p => .test p

/-- Whether a pattern can be processed under `σ`. -/
def ready (σ : Env) : PKind → Bool
  | .atom _ _ args => args.all fun a => match a with
    | .var _ => true
    | .lit _ => true
    | e => (unbound σ e).isEmpty
  | .bind _ e => (unbound σ e).isEmpty
  | .mem _ e => (unbound σ e).isEmpty
  | .test p => (p.vars.filter fun v => (Env.lookup v σ).isNone).isEmpty

/-- Bind or check a variable. -/
def bindVar (g : EGraph) (σ : Env) (v : Var) (t : Term) : Option Env :=
  match Env.lookup v σ with
  | some u => if g.agree u t then some σ else none
  | none => some ((v, t) :: σ)

/-- Match one argument against a column class. -/
def matchArg (g : EGraph) (σ : Env) (e : Expr) (col : Nat) : Option Env :=
  match e with
  | .var v =>
    match Env.lookup v σ with
    | none => some ((v, g.repTerm col) :: σ)
    | some u => match g.classOf u with
      | some c => if c == col then some σ else none
      | none => none
  | e =>
    match evalExpr e σ with
    | some t => match g.classOf t with
      | some c => if c == col then some σ else none
      | none => none
    | none => none

/-- The matches of one atom. -/
def matchAtom (g : EGraph) (σ : Env) (cls : Option Var) (f : FnName) (args : List Expr) :
    List Env :=
  (g.liveRows.getD f #[]).toList.filterMap fun kr =>
    let (key, rowId) := kr
    if key.length != args.length then none else
    let σ' := (args.zip key).foldlM (fun σ ac => matchArg g σ ac.1 ac.2) σ
    σ'.bind fun σ' =>
      if !args.all (exprMatches g σ') then none else
      match cls with
      | some v => bindVar g σ' v (g.repTerm rowId)
      | none => some σ'

def testHolds (g : EGraph) (σ : Env) : Pattern → Bool
  | .eq a b =>
    match evalExpr a σ, evalExpr b σ with
    | some t, some u => exprMatches g σ a && exprMatches g σ b && g.agree t u
    | _, _ => false
  | .ne a b =>
    match evalExpr a σ, evalExpr b σ with
    | some t, some u => exprMatches g σ a && exprMatches g σ b && !g.agree t u
    | _, _ => false
  | .expr e => exprMatches g σ e

/-- Process one pattern under `σ`: the extended environments. -/
def step (g : EGraph) (σ : Env) : PKind → List Env
  | .atom cls f args => matchAtom g σ cls f args
  | .bind v e =>
    match evalExpr e σ with
    | some t => (bindVar g σ v t).toList
    | none => []
  | .mem x e =>
    match if exprMatches g σ e then evalExpr e σ else none with
    | some t => match Prim.elements t with
      | some ts => ts.filterMap fun u => bindVar g σ x u
      | none => []
    | none => []
  | .test p => if testHolds g σ p then [σ] else []

/-- The first ready pattern, and the rest. -/
def pickReady (σ : Env) : List (Pattern × PKind) → Option ((Pattern × PKind) × List (Pattern × PKind))
  | [] => none
  | p :: ps => if ready σ p.2 then some (p, ps) else (pickReady σ ps).map fun r => (r.1, p :: r.2)

/-- The matches of a query: patterns processed as they become ready. -/
partial def matchQuery (g : EGraph) (q : Query) : List Env :=
  go (q.map fun p => (p, classify p)) [] (q.length + 1)
where
  go (pending : List (Pattern × PKind)) (σ : Env) : Nat → List Env
    | 0 => []
    | fuel + 1 =>
      match pending with
      | [] => [σ]
      | _ =>
        match pickReady σ pending with
        | none => []
        | some (p, rest) => (step g σ p.2).flatMap fun σ' => go rest σ' fuel

/-! ### Actions, rounds and schedules -/

def execAction (g : EGraph) (σ : Env) : Action → Option EGraph
  | .expr e => (e.eval σ).map fun t => (g.addTerm t).1
  | .union a b => do
    let ta ← a.eval σ
    let tb ← b.eval σ
    if ta.isLit || tb.isLit then none else
    let (g, i) := g.addTerm ta
    let (g, j) := g.addTerm tb
    pure (g.union i j)
  | .subsume f es => (Expr.evalList es σ).map fun ts =>
    let (g, i) := g.addTerm (.app f ts)
    g.subsume i

def execActions (g : EGraph) (σ : Env) : List Action → Option EGraph
  | [] => some g
  | a :: as => (execAction g σ a).bind fun g' => execActions g' σ as

/-- One round: every rule matched against the pre-state, then every firing applied. -/
def runRules (g : EGraph) (rs : List Rule) : EGraph :=
  let firings := rs.map fun r => (r, matchQuery g r.query)
  let g' := firings.foldl (fun acc rm => rm.2.foldl (fun acc σ =>
    (execActions acc σ rm.1.actions).getD acc) acc) g
  g'.rebuild

/-- The meaning of a state is unchanged when no term, class or subsumed key changed. -/
def sameMeaning (g g' : EGraph) : Bool :=
  g.terms.size == g'.terms.size && g.classes == g'.classes &&
    g.subsumedKeys.size == g'.subsumedKeys.size

mutual

partial def execSchedule (fuel : Nat) (g : EGraph) : Schedule → Option EGraph
  | .run rs => some (runRules g rs)
  | .seq S₁ S₂ => (execSchedule fuel g S₁).bind fun g' => execSchedule fuel g' S₂
  | .saturate S => execSaturate fuel fuel g S

partial def execSaturate (fuel : Nat) : Nat → EGraph → Schedule → Option EGraph
  | 0, _, _ => none
  | n + 1, g, S => (execSchedule fuel g S).bind fun g' =>
      if sameMeaning g g' then some g' else execSaturate fuel n g' S

end

/-- The pass budget of a saturation. -/
def saturationFuel : Nat := 256

/-- Whether the check holds on a state. -/
def holds (g : EGraph) (q : Query) : Bool := !(matchQuery g q).isEmpty

/-- The outcome of a target program: `some true` when its check holds, `none` when a
saturation exhausts its budget. -/
def observe (P : Program) (fuel : Nat := saturationFuel) : Option Bool :=
  (execSchedule fuel ({} : EGraph).rebuild P.schedule).map fun g => holds g P.check

/-- The final state of a target program. -/
def run (P : Program) (fuel : Nat := saturationFuel) : Option EGraph :=
  execSchedule fuel ({} : EGraph).rebuild P.schedule

/-- Row counts per head, for inspection. -/
def EGraph.sizes (g : EGraph) : List (FnName × Nat) :=
  (g.liveRows.toList.map fun fr => (fr.1, fr.2.size)).mergeSort fun a b => decide (a.1 ≤ b.1)

end Egglog.Slotted.Target
