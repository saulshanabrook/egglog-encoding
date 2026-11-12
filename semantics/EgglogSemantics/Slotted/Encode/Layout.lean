import EgglogSemantics.Source.Domain
import EgglogSemantics.Slotted.Target.Spec
import EgglogSemantics.Slotted.Spec.Eval

/-!
# Names, layouts and the representation of ground terms

The slotted pass's generated tables carry the paper's names under the `@` prefix:
`@RenamesTo(a, m, b)` records `a = m * b`, without ordering its endpoints;
`@FS(a, A)` estimates the free slots of `a`. Self-equations are symmetries.
`@Orbit(a, π)` is a finite membership witness used by disequality: it is unioned
with `@Orbit(a, id)` exactly for symmetries. The slot leaf is the term `$0`.

A **layout** says what each argument position of a constructor holds in the target: a
binding position holds its slot (`bind`), a payload column holds a literal (inferred: some
occurrence of the constructor in the program has a literal there, as the Rust compiler reads
it off the declared sorts), and every other position is a term child, which becomes two
columns, the renaming from the child's slots to the node's and the child. Every row's first
target column is its **generation**, an integer: a source action writes generation `0`, a
maintenance update writes the replaced row's generation plus one, and a query binds it as a
wildcard. The plain `subsume` marks a row key for good, in every spelling, so a replaced
spelling could never return live when a later union makes its class the leader again; the
generation keeps every replacement a new key, as the Rust compiler's `delete` keeps a
reinserted row live. The **representation** `repr` of a ground source term keeps the
source's slot names at every node and represents every slot leaf by `$0` with the edge
`[$0 ↦ $s]`, which is the paper's initialization of the distribution example.
-/

namespace Egglog.Slotted.Encode

open Target

/-! ### Names -/

def renamesToName : FnName := "@RenamesTo"
def fsName : FnName := "@FS"
def orbitName : FnName := "@Orbit"
/-- The goal relation a disjunctive check writes. -/
def goalName : FnName := "@Goal"
/-- The slot leaf. -/
def leafName : FnName := "$0"
def leafExpr : Expr := .app leafName []
def leafTerm : Term := .app leafName []
/-- The generation of a row a source action writes. -/
def genZero : Expr := .lit (.int 0)

/-- A primitive application. -/
def prim (op : String) (args : List Expr) : Expr := .app op args

def vtrue : Expr := .app trueName []
def vfalse : Expr := .app falseName []
def emptySet : Expr := .app setName []

/-- A row pattern. -/
def row (f : FnName) (args : List Expr) : Pattern := .expr (.app f args)
/-- Bind a computed variable. -/
def bindP (v : Var) (e : Expr) : Pattern := .eq (.var v) e
/-- A boolean primitive test. -/
def isTrue (e : Expr) : Pattern := .eq e vtrue
def isFalse (e : Expr) : Pattern := .eq e vfalse
/-- Write a row. -/
def write (f : FnName) (args : List Expr) : Action := .expr (.app f args)

/-- A canonical value as an expression. -/
def valueExpr (t : Term) : Expr := t.toExpr

/-- The slot a nullary application names, if it is a slot. -/
def _root_.Egglog.Expr.slotName? : Expr → Option Slot
  | .app s [] => if isSlotName s then some s else none
  | _ => none

/-! ### Layouts -/

inductive Column where
  | binder
  | payload
  | child
  deriving DecidableEq, Repr

structure Layout where
  bind : Binders
  /-- The payload positions of each constructor. -/
  payloads : List (FnName × List Nat)

namespace Layout

def column (L : Layout) (f : FnName) (j : Nat) : Column :=
  if L.bind.isBinding f j then .binder
  else if j ∈ (L.payloads.lookup f).getD [] then .payload else .child

def columns (L : Layout) (f : FnName) (n : Nat) : List (Nat × Column) :=
  (List.range n).map fun j => (j, L.column f j)

def childPositions (L : Layout) (f : FnName) (n : Nat) : List Nat :=
  (L.columns f n).filterMap fun jc => if jc.2 = .child then some jc.1 else none

def binderPositions (L : Layout) (f : FnName) (n : Nat) : List Nat :=
  (L.columns f n).filterMap fun jc => if jc.2 = .binder then some jc.1 else none

/-- The binding positions whose names are bound in child `i`. -/
def boundIn (L : Layout) (f : FnName) (i : Nat) : List Nat :=
  ((L.bind f).filter fun ji => ji.2 = i).map Prod.fst

/-- The target columns of an application of `f`: the generation, then from the expression
for each source position, a child position contributing its edge and its child. -/
def targetCols (L : Layout) (f : FnName) (n : Nat) (gen : Expr) (edge col : Nat → Expr) :
    List Expr :=
  gen :: (L.columns f n).flatMap fun jc => match jc.2 with
    | .child => [edge jc.1, col jc.1]
    | _ => [col jc.1]

end Layout

/-! ### Payload inference -/

mutual

/-- Every application occurrence in an expression, with its arguments. -/
def _root_.Egglog.Expr.apps : Expr → List (FnName × List Expr)
  | .lit _ => []
  | .var _ => []
  | .app f args => (f, args) :: Expr.appsList args
  | .min a b => a.apps ++ b.apps

def _root_.Egglog.Expr.appsList : List Expr → List (FnName × List Expr)
  | [] => []
  | e :: es => e.apps ++ Expr.appsList es

end

def Pattern.apps : Pattern → List (FnName × List Expr)
  | .expr e => e.apps
  | .eq a b | .ne a b => a.apps ++ b.apps

def Action.apps : Action → List (FnName × List Expr)
  | .expr e => e.apps
  | .union a b => a.apps ++ b.apps
  | .subsume f es => (f, es) :: Expr.appsList es

/-- Every application occurrence in the program. -/
def Program.apps (P : Program) : List (FnName × List Expr) :=
  (P.rules.flatMap fun r => r.query.flatMap Pattern.apps ++ r.actions.flatMap Action.apps) ++
    P.check.flatMap Pattern.apps

/-- Whether an expression is a literal. -/
def _root_.Egglog.Expr.isLit : Expr → Bool
  | .lit _ => true
  | _ => false

/-- The payload positions of each constructor: where some occurrence holds a literal. -/
def inferPayloads (P : Program) : List (FnName × List Nat) :=
  let occs := Program.apps P
  ((occs.map Prod.fst).dedup).filterMap fun f =>
    let positions := (occs.filter (·.1 = f)).flatMap fun fa =>
      (fa.2.zipIdx.filter fun ei => ei.1.isLit).map Prod.snd
    if positions.isEmpty then none else some (f, positions.dedup)

/-- The layout of a program under its binder signature. -/
def Layout.ofProgram (bind : Binders) (P : Program) : Layout :=
  { bind, payloads := inferPayloads P }

/-! ### The representation of ground terms -/

/-- The edge from a child's slots to the parent's names, as an expression. -/
def edgeExpr (m : Renaming) : Expr := valueExpr (encodeRen m)

mutual

/-- `repr(t)` for a ground source term, with its free slots in source names: a slot leaf is
`$0`, a literal is itself, and an application keeps the source names, giving every term
child the identity edge on its free slots and every slot child the edge `[$0 ↦ $s]`. -/
def reprGround (L : Layout) : Expr → Except String (Expr × List Slot)
  | .lit l => .ok (.lit l, [])
  | .var v => .error s!"variable {v} in a ground term"
  | .min _ _ => .error "min in a slotted program"
  | .app f args =>
    match Expr.slotName? (.app f args) with
    | some s => .ok (leafExpr, [s])
    | none => do
      if (Builtin.ofName f).isSome then throw s!"predicate {f} inside a term"
      let cols ← reprArgs L f args args 0
      let free := cols.flatMap Prod.snd
      pure (.app f (genZero :: cols.flatMap Prod.fst), canonSlots free)

/-- The target columns of the arguments from position `j` of `f(all)`, each with its
contribution to the free slots. -/
def reprArgs (L : Layout) (f : FnName) (all : List Expr) :
    List Expr → Nat → Except String (List (List Expr × List Slot))
  | [], _ => .ok []
  | a :: as, j => do
    let rest ← reprArgs L f all as (j + 1)
    match L.column f j with
    | .binder =>
      match Expr.slotName? a with
      | some _ => pure (([a], []) :: rest)
      | none => throw s!"{f}: binding position {j} holds no slot"
    | .payload =>
      if a.isLit then pure (([a], []) :: rest)
      else throw s!"{f}: payload position {j} holds no literal"
    | .child =>
      let bound := (L.boundIn f j).filterMap fun k => all[k]? >>= Expr.slotName?
      match Expr.slotName? a with
      | some s => pure (([edgeExpr [(leafName, s)], leafExpr], [s].filter (· ∉ bound)) :: rest)
      | none => do
        let (a', S) ← reprGround L a
        pure (([edgeExpr (Renaming.id S), a'], S.filter (· ∉ bound)) :: rest)

end

end Egglog.Slotted.Encode
