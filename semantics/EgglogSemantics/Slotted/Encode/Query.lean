import EgglogSemantics.Slotted.Encode.Maintenance

/-!
# Compiling slotted queries and actions

A source query is flattened to depth-one atoms. Each atom's local slots receive
separate temporary names. The unification map identifies required equalities, while
independent arguments `C` and `P` record disequality cliques and fixed pattern literals.
Repeated variables are joined through self-equations `RenamesTo(c,π,c)`. Refinement tries
remaining aliases without collapsing a term's distinct slots or changing literal identities.

Concrete free names and written pattern literals retain their names during unification.
Ground binders are normalized to fresh temporary names within their scopes. Action-only
slots are separate blocks outside refinement. Anchoring changes coordinates to the root's
stored names for the action; it transports every matched literal consistently as well.
Equality selects a self-equation. Disequality compares finite symmetry-membership witnesses
when classes and map images agree, and otherwise uses the differing class or image.

Actions build bottom-up in these root coordinates. A union at the root is a plain union;
a variable with a different invocation contributes a `RenamesTo` equation. Matched row
generations are wildcards; built rows have generation zero.
-/

namespace Egglog.Slotted.Encode

open Target

/-! ### Flattened facts -/

/-- A slot written in a query: a pattern slot variable, or a concrete slot. -/
inductive SlotRef where
  | pat (v : Var)
  | concrete (s : Slot)
  deriving DecidableEq, Repr

/-- A child column of an atom: a variable (a source variable or another atom's root), or a
slot leaf. -/
inductive ChildRef where
  | var (v : Var)
  | slot (r : SlotRef)
  deriving Repr

/-- A column of an atom with the target variables that read it. -/
inductive Col where
  | child (edge : Var) (c : ChildRef)
  | binder (field : Var) (r : SlotRef)
  | payload (e : Expr)

structure Atom where
  root : Var
  fn : FnName
  cols : List Col
  /-- The source application, for an action that names the matched term. -/
  src : Expr

inductive Cmp where
  | eq | ne | renEq | renNe
  deriving DecidableEq, Repr

inductive Fact where
  | atom (a : Atom)
  /-- A comparison of two term references, or of two payload expressions. -/
  | cmp (k : Cmp) (a b : Expr)
  | free (positive : Bool) (s : SlotRef) (ts : List Var)
  | freeNames (t : Var) (ss : List SlotRef)

/-! ### Flattening -/

/-- The flattening state: the layout, the facts so far, counters, and the roles of the
source variables. -/
structure Flat where
  L : Layout
  facts : Array Fact := #[]
  next : Nat := 0
  payloadVars : List Var := []
  termVars : List Var := []
  /-- The fresh slots standing for the binders of ground terms: bound names, kept apart
  from the concrete slots. -/
  groundBinders : List Var := []

abbrev FlatM := StateT Flat (Except String)

def freshName (stem : String) : FlatM Var :=
  modifyGet fun st => (s!"@{stem}{st.next}", { st with next := st.next + 1 })

def emit (f : Fact) : FlatM Unit := modify fun st => { st with facts := st.facts.push f }

/-- Whether an expression mentions a variable. -/
def groundExpr (e : Expr) : Bool := e.vars.isEmpty

def notePayloadVar (v : Var) : FlatM Unit := do
  if isSlotVar v then throw s!"slot variable {v} at a payload position"
  modify fun st => { st with payloadVars := st.payloadVars ∪ [v] }

def noteTermVar (v : Var) : FlatM Unit :=
  modify fun st => { st with termVars := st.termVars ∪ [v] }

def slotRef (e : Expr) : Option SlotRef :=
  match e with
  | .var v => if isSlotVar v then some (.pat v) else none
  | _ => (Expr.slotName? e).map .concrete

mutual

/-- Flatten an application at the given root. -/
partial def flattenApp (root : Var) (f : FnName) (args : List Expr) : FlatM Unit := do
  let L := (← get).L
  if (Builtin.ofName f).isSome then throw s!"predicate {f} inside a term"
  if isSlotName f then throw "a bare slot as a query root"
  let mut cols : Array Col := #[]
  let mut nested : Array (Var × FnName × List Expr) := #[]
  for (a, j) in args.zipIdx do
    match L.column f j with
    | .binder =>
      match slotRef a with
      | some r => cols := cols.push (.binder (← freshName s!"b{j}_") r)
      | none => throw s!"{f}: binding position {j} holds no slot"
    | .payload =>
      match a with
      | .lit _ => cols := cols.push (.payload a)
      | .var v => notePayloadVar v; cols := cols.push (.payload a)
      | _ => throw s!"{f}: payload position {j} holds a term"
    | .child =>
      let edge ← freshName s!"e{j}_"
      match slotRef a with
      | some r => cols := cols.push (.child edge (.slot r))
      | none =>
        match a with
        | .var v => noteTermVar v; cols := cols.push (.child edge (.var v))
        | .app g bs =>
          let r ← freshName "t"
          nested := nested.push (r, g, bs)
          cols := cols.push (.child edge (.var r))
        | .lit _ => throw s!"{f}: literal at a term position {j}"
        | .min _ _ => throw "min in a slotted query"
  emit (.atom { root, fn := f, cols := cols.toList, src := .app f args })
  for (r, g, bs) in nested do flattenApp r g bs

end

/-! ### Binders in source terms

A bound name carries no identity: a ground term matched as a pattern must not identify its
binder with a free slot of the same name, so every binder of a ground application becomes a
fresh pattern slot within its scope, and, as the reference reads source terms, a binder that a
later binder of the same scope shadows binds nothing and becomes a fresh slot as well. -/

/-- Replace the slot `s`, written as a slot variable or a concrete slot, by the slot variable
`v`. -/
partial def substSlot (s : Slot) (v : Var) : Expr → Expr
  | .var w => if w = s then .var v else .var w
  | .app f [] => if f = s then .var v else .app f []
  | .app f args => .app f (args.map (substSlot s v))
  | e => e

/-- The slots a term's binders bind in child `i` of `f`, from the (possibly renamed) args. -/
def binderName : Expr → Option Slot
  | .var w => if isSlotVar w then some w else none
  | e => Expr.slotName? e

/-- α-rename the binders that must be fresh, bottom-up. -/
partial def normalizeBinders : Expr → FlatM Expr
  | .app f args => do
    let L := (← get).L
    let ground := groundExpr (.app f args)
    let mut args ← args.mapM normalizeBinders
    let n := args.length
    for k in L.binderPositions f n do
      let some name := binderName (args.getD k (.lit (.int 0))) | continue
      let covered := ((L.bind f).filter fun ji => ji.1 = k).map Prod.snd
      let shadowed := (L.binderPositions f n).any fun k' =>
        k < k' && ((L.bind f).filter fun ji => ji.1 = k').map Prod.snd = covered &&
          binderName (args.getD k' (.lit (.int 0))) = some name
      if ground || shadowed then
        let v ← freshName "slot"
        let v := "$" ++ v
        if ground then modify fun st => { st with groundBinders := st.groundBinders ++ [v] }
        args := args.zipIdx.map fun ai =>
          if ai.2 = k then .var v
          else if ai.2 ∈ covered && !shadowed then substSlot name v ai.1
          else ai.1
    pure (.app f args)
  | e => pure e

def normalizePattern : Pattern → FlatM Pattern
  | .expr e => do pure (.expr (← normalizeBinders e))
  | .eq a b => do pure (.eq (← normalizeBinders a) (← normalizeBinders b))
  | .ne a b => do pure (.ne (← normalizeBinders a) (← normalizeBinders b))

def normalizeAction : Action → FlatM Action
  | .expr e => do pure (.expr (← normalizeBinders e))
  | .union a b => do pure (.union (← normalizeBinders a) (← normalizeBinders b))
  | .subsume f es => do pure (.subsume f (← es.mapM normalizeBinders))

/-- The variable standing for an expression in a comparison or a predicate argument. -/
def flattenRef (e : Expr) : FlatM Var := do
  match e with
  | .var v =>
    if isSlotVar v then throw s!"slot {v} used as a term" else noteTermVar v; pure v
  | .app f args =>
    let r ← freshName "t"
    flattenApp r f args
    pure r
  | .lit _ => throw "a literal compared as a term"
  | .min _ _ => throw "min in a slotted query"

/-- Whether an expression is a payload operand: a literal or a payload variable. -/
def payloadOperand (st : Flat) : Expr → Bool
  | .lit _ => true
  | .var v => v ∈ st.payloadVars
  | _ => false

/-- `v = f(args)` roots the application at `v`. -/
def rootAt (v : Var) (f : FnName) (args : List Expr) : FlatM Unit := flattenApp v f args

def flattenPattern : Pattern → FlatM Unit
  | .expr (.app f args) =>
    match Builtin.ofName f, args with
    | some .free, x :: es => do
      let some r := slotRef x | throw "free: the first argument is a slot"
      emit (.free true r (← es.mapM flattenRef))
    | some .notFree, x :: es => do
      let some r := slotRef x | throw "not-free: the first argument is a slot"
      emit (.free false r (← es.mapM flattenRef))
    | some .freeNamesAre, e :: xs => do
      let t ← flattenRef e
      let ss ← xs.mapM fun x => match slotRef x with
        | some r => pure r
        | none => throw "free-names-are: a slot argument is not a slot"
      emit (.freeNames t ss)
    | some .renamingEq, [a, b] => do
      emit (.cmp .renEq (.var (← flattenRef a)) (.var (← flattenRef b)))
    | some .renamingNe, [a, b] => do
      emit (.cmp .renNe (.var (← flattenRef a)) (.var (← flattenRef b)))
    | some _, _ => throw s!"{f}: wrong arguments"
    | none, _ => do flattenApp (← freshName "p") f args
  -- A bare variable as a pattern requires nothing of its own: another pattern binds it.
  | .expr (.var v) =>
    if isSlotVar v then throw s!"slot {v} as a pattern" else noteTermVar v
  | .expr _ => throw "a pattern is an application"
  | .eq a b => do
    let st ← get
    if payloadOperand st a || payloadOperand st b then emit (.cmp .eq a b) else
    match a, b with
    | .var v, .app f args =>
      if isSlotVar v then throw s!"slot {v} compared with a term"
      else noteTermVar v; rootAt v f args
    | .app f args, .var v =>
      if isSlotVar v then throw s!"slot {v} compared with a term"
      else noteTermVar v; rootAt v f args
    | _, _ => emit (.cmp .eq (.var (← flattenRef a)) (.var (← flattenRef b)))
  | .ne a b => do
    let st ← get
    if payloadOperand st a || payloadOperand st b then emit (.cmp .ne a b)
    else emit (.cmp .ne (.var (← flattenRef a)) (.var (← flattenRef b)))

/-! ### Emission of the compiled query -/

/-- Where a variable's class slots were first read: as the root of an atom, or as a child
through an edge. -/
inductive Occ where
  | root (atom : Nat)
  | child (atom : Nat) (edge : Var)

/-- The emission state. -/
structure Emit where
  flat : Flat
  pats : Array Pattern := #[]
  next : Nat := 0
  /-- The first occurrence of each term variable, in order. -/
  firstOcc : List (Var × Occ) := []
  /-- The pattern slots and action-only slots. -/
  patSlots : List Var := []
  /-- User-written query literals, excluding generated and action-only names. -/
  fixedSlots : List Var := []
  carried : List Var := []
  concrete : List Slot := []
  /-- The unifications, collected while scanning the atoms and emitted after the unification map. -/
  unifs : Array (Expr × Expr × Bool) := #[]

abbrev EmitM := StateT Emit (Except String)

def push (p : Pattern) : EmitM Unit := modify fun st => { st with pats := st.pats.push p }
def pushAll (ps : List Pattern) : EmitM Unit := ps.forM push

def fresh (stem : String) : EmitM Var :=
  modifyGet fun st => (s!"@{stem}{st.next}", { st with next := st.next + 1 })

/-- Bind a computed variable and return it. -/
def compute (stem : String) (e : Expr) : EmitM Expr := do
  let v ← fresh stem
  push (bindP v e)
  pure (.var v)

/-- The placeholder map of an atom: `@nuA{i}`. -/
def nuAtom (i : Nat) : Expr := .var s!"@nuA{i}"
/-- The placeholder map of a variable's class slots: `@nu_v`. -/
def nuVar (v : Var) : Expr := .var s!"@nu_{v}"
/-- The anchored renaming of a variable: `@mu_v`. -/
def muVar (v : Var) : Expr := .var s!"@mu_{v}"
/-- The final name of a pattern slot `$s`: `@s_s`. -/
def slotVar (v : Var) : Expr := .var s!"@s_{v.drop 1}"
/-- The final name of a concrete slot. -/
def concreteVar (s : Slot) : Expr := .var s!"@c_{s.drop 1}"
def nuG : Expr := .var "@nuG"
def nuLit : Expr := .var "@nuLit"
def slotTerm (s : Slot) : Expr := .app s []

def slotRefExpr : SlotRef → Expr
  | .pat v => slotVar v
  | .concrete s => concreteVar s

/-- The placeholder of a slot reference before anchoring. -/
def slotRefPlaceholder : SlotRef → Expr
  | .pat v => papply nuLit (slotTerm v)
  | .concrete s => papply nuG (slotTerm s)

def noteSlotRef (carriedHere : Bool) : SlotRef → EmitM Unit
  | .pat v => modify fun st =>
    let carried := if carriedHere then st.carried ∪ [v] else st.carried
    { st with patSlots := st.patSlots ∪ [v], carried := carried }
  | .concrete s => modify fun st => { st with concrete := st.concrete ∪ [s] }

/-- Record a unification to emit after the unification map starts. -/
def unifyLater (m m' : Expr) (single : Bool) : EmitM Unit :=
  modify fun st => { st with unifs := st.unifs.push (m, m', single) }

/-- An occurrence of a term variable with its placeholder map at this occurrence: the first
defines `ν_v`, a later one is read through a symmetry and unified. -/
def occur (v : Var) (here : Occ) : EmitM Unit := do
  let st ← get
  if (st.firstOcc.lookup v).isSome then
    let π ← fresh "pi"
    push (renamesTo (.var v) (.var π) (.var v))
    let A ← fresh "symSlots"
    push (fs (.var v) (.var A))
    push (isTrue (pisPerm (.var π) (.var A)))
    let hereMap : Expr := match here with
      | .root i => pcomp (nuAtom i) (.var π)
      | .child i e => pcomp (pcomp (nuAtom i) (.var e)) (.var π)
    unifyLater (nuVar v) hereMap false
  else
    set { st with firstOcc := st.firstOcc ++ [(v, here)] }

/-- The variables of the facts, in order of first occurrence. -/
def scanFacts : EmitM Unit := do
  let facts := (← get).flat.facts.toList
  let mut i := 0
  for f in facts do
    match f with
    | .atom a =>
      push (.eq (.var a.root) (.app a.fn (Expr.var s!"@gen{i}" :: (a.cols.map fun c =>
        match c with
        | .child e (.var v) => [Expr.var e, .var v]
        | .child e (.slot _) => [Expr.var e, leafExpr]
        | .binder b _ => [Expr.var b]
        | .payload e => [e]).flatten)))
      occur a.root (.root i)
      for c in a.cols do
        match c with
        | .child e (.var v) => occur v (.child i e)
        | .child e (.slot r) =>
          noteSlotRef true r
          unifyLater (papply (nuAtom i) (papply (.var e) leafExpr)) (slotRefPlaceholder r) true
        | .binder b r =>
          noteSlotRef false r
          unifyLater (papply (nuAtom i) (.var b)) (slotRefPlaceholder r) true
        | .payload _ => pure ()
      i := i + 1
    | .free _ r _ => noteSlotRef true r
    | .freeNames _ ss => ss.forM (noteSlotRef true)
    | .cmp _ _ _ => pure ()

/-- The atoms in order, numbered as `scanFacts` numbers them. -/
def numberedAtoms (facts : List Fact) : List (Nat × Atom) :=
  ((facts.filterMap fun f => match f with | .atom a => some a | _ => none).zipIdx).map
    fun fi => (fi.2, fi.1)

/-- The class slots of a variable: a row `FS(v, A)` for a root occurrence, the domain of the
edge otherwise. -/
def classSlots (v : Var) : Occ → EmitM Expr
  | .root _ => do
    let A ← fresh "A"
    push (fs (.var v) (.var A))
    pure (.var A)
  | .child _ e => pure (pdom (.var e))

/-- Emit the placeholders, the variables' placeholder maps, the cliques, the unification map, the
unifications, the refinement and the anchor at `anchorVar`; then `μ_v` for every variable and
the final names of the slots. -/
def emitUnification (anchorVar : Var) : EmitM Unit := do
  let facts := (← get).flat.facts.toList
  -- Fixed literals and concrete names are separate from each node's temporary names.
  let st ← get
  let P ← compute "P" (pset ((st.fixedSlots ∪ st.concrete).map slotTerm))
  push (bindP "@nuG" (pid (pset (st.concrete.map slotTerm))))
  let mut used : Expr := P
  -- The concrete slots and the binders of ground terms are pairwise distinct: a bound name
  -- is fresh for the free slots of its term.
  let groundBinders := st.flat.groundBinders.map fun v => papply nuLit (slotTerm v)
  let mut cliques : List Expr :=
    [if groundBinders.isEmpty then pimg nuG else punion (pimg nuG) (pset groundBinders)]
  for (i, a) in numberedAtoms facts do
    let fields := a.cols.filterMap fun c => match c with
      | .binder b _ => some (Expr.var b)
      | _ => none
    let locals := (a.cols.filterMap fun c => match c with
      | .child e _ => some (pimg (.var e))
      | _ => none) ++ (if fields.isEmpty then [] else [pset fields])
    let Lv ← compute "L" (unions locals)
    push (bindP s!"@nuA{i}" (prim "@fresh" [Lv, used]))
    used := punion used (pimg (nuAtom i))
    cliques := cliques ++ [pimg (nuAtom i)]
  let st ← get
  let temporary := st.patSlots.filter (· ∉ st.fixedSlots)
  push (bindP "@nuLit" (prim "@align"
    [pid (pset (st.fixedSlots.map slotTerm)), prim "@fresh" [pset (temporary.map slotTerm), used]]))
  used := punion used (pimg nuLit)
  -- The placeholder map of every variable's class slots.
  for (v, occ) in st.firstOcc do
    let nu : Expr ← match occ with
      | .root i => do pure (prestrict (nuAtom i) (← classSlots v occ))
      | .child i e => pure (pcomp (nuAtom i) (.var e))
    push (bindP s!"@nu_{v}" nu)
  let C ← compute "C" (prim "@cliques" cliques)
  let U ← compute "U" used
  push (bindP "@u0" (prim "@identity" [U]))
  -- The unifications, in order.
  let mut k := 0
  for (m, m', single) in st.unifs do
    let U' := s!"@u{k + 1}"
    push (bindP U' (if single then prim "@unify1" [.var s!"@u{k}", m, m', C, P]
      else prim "@unify" [.var s!"@u{k}", m, m', C, P]))
    k := k + 1
  -- Refinement over the placeholders reached by variables and carried slots, then anchoring.
  let D ← compute "D" (unions ((st.firstOcc.map fun vo => pimg (nuVar vo.1)) ++
    [pimg nuG] ++
    (if st.carried.isEmpty then []
     else [pset (st.carried.map fun v => papply nuLit (slotTerm v))])))
  let q ← fresh "q"
  push (.expr (.app memName [.var q, prim "@refine" [.var s!"@u{k}", C, P, D]]))
  push (bindP "@qa" (prim "@anchor" [.var q, nuVar anchorVar]))
  for (v, _) in st.firstOcc do
    push (bindP s!"@mu_{v}" (pcomp (.var "@qa") (nuVar v)))
  for v in st.patSlots do
    push (bindP s!"@s_{v.drop 1}" (papply (.var "@qa") (papply nuLit (slotTerm v))))
  for s in st.concrete do
    push (bindP s!"@c_{s.drop 1}" (papply (.var "@qa") (papply nuG (slotTerm s))))

/-- The alternatives for a comparison of two class variables under the unification map. -/
def cmpPatterns (k : Cmp) (a b : Expr) (payload : Bool) : EmitM (List (List Pattern)) := do
  if payload then
    let st ← get
    unless payloadOperand st.flat a && payloadOperand st.flat b do
      throw "a payload comparison needs two payload operands"
    pure [[match k with | .eq | .renEq => .eq a b | .ne | .renNe => .ne a b]]
  else
    match a, b, k with
    | .var x, .var y, .renEq => pure [[.eq a b]]
    | .var x, .var y, .renNe => pure [[.ne a b]]
    | .var x, .var y, .eq =>
      let π ← fresh "cmpSym"
      pure [[.eq a b, renamesTo a (.var π) a,
             .eq (muVar x) (pcomp (muVar y) (.var π))]]
    | .var x, .var y, .ne =>
      let m ← fresh "relative"
      let I ← fresh "identity"
      let o ← fresh "orbit"
      let z ← fresh "neutral"
      let A := pdom (muVar x)
      pure [[.ne a b],
            [.eq a b, .ne (pimg (muVar x)) (pimg (muVar y))],
            [.eq a b, .eq (pimg (muVar x)) (pimg (muVar y)),
             bindP m (pcomp (pinv (muVar y)) (muVar x)), bindP I (pid A),
             .eq (.var o) (.app orbitName [a, .var m]),
             .eq (.var z) (.app orbitName [a, .var I]), .ne (.var o) (.var z)]]
    | _, _, _ => throw "a comparison of non-variables"

/-- The guards and comparisons, as alternatives (the product over the `!=` disjunctions). -/
def emitGuards : EmitM (List (List Pattern)) := do
  let st ← get
  let mut alts : List (List Pattern) := [[]]
  for f in st.flat.facts.toList do
    match f with
    | .free positive r ts =>
      let U := unions (ts.map fun t => pimg (muVar t))
      let test := if positive then isTrue (prim "@elem" [slotRefExpr r, U])
        else isFalse (prim "@elem" [slotRefExpr r, U])
      alts := alts.map (· ++ [test])
    | .freeNames t ss =>
      alts := alts.map (· ++ [.eq (pimg (muVar t)) (pset (ss.map slotRefExpr))])
    | .cmp k a b =>
      let payload := payloadOperand st.flat a || payloadOperand st.flat b
      let branches ← cmpPatterns k a b payload
      alts := alts.flatMap fun alt => branches.map fun br => alt ++ br
    | _ => pure ()
  pure alts

/-! ### Actions -/

/-- A built child: its edge expression, the child expression, and its free slots. -/
structure Built where
  edge : Expr
  child : Expr
  slots : Expr

/-- The edge of a slot leaf built at a final name: `[$0 ↦ s′]`. -/
def leafBuilt (s' : Expr) : EmitM Built := do
  let ed ← compute "ed" (.app renName [.app pairName [leafExpr, s']])
  pure ⟨ed, leafExpr, pset [s']⟩

/-- Build a right-hand side bottom-up in the root coordinates, binding every computation. -/
partial def build (e : Expr) : EmitM Built := do
  let st ← get
  match e with
  | .var v =>
    if isSlotVar v then leafBuilt (slotVar v)
    else if v ∈ st.flat.payloadVars then throw s!"payload variable {v} used as a term"
    else if (st.firstOcc.lookup v).isNone then throw s!"head variable {v} is not bound"
    else pure ⟨muVar v, .var v, pimg (muVar v)⟩
  | .lit _ => throw "a literal built as a term"
  | .min _ _ => throw "min in a slotted action"
  | .app f args =>
    match Expr.slotName? e with
    | some s => leafBuilt (concreteVar s)
    | none =>
      if (Builtin.ofName f).isSome then throw s!"predicate {f} inside a term"
      let L := st.flat.L
      let mut cols : Array Expr := #[]
      let mut slotsOf : Array Expr := #[]
      for (a, j) in args.zipIdx do
        match L.column f j with
        | .binder =>
          match slotRef a with
          | some r => cols := cols.push (slotRefExpr r)
          | none => throw s!"{f}: binding position {j} holds no slot"
        | .payload =>
          match a with
          | .lit _ => cols := cols.push a
          | .var v =>
            unless v ∈ st.flat.payloadVars do throw s!"{f}: {v} at a payload position"
            cols := cols.push a
          | _ => throw s!"{f}: a term at payload position {j}"
        | .child =>
          let b ← build a
          cols := cols ++ #[b.edge, b.child]
          let bound := (L.boundIn f j).filterMap fun k => (args[k]?).bind slotRef
          slotsOf := slotsOf.push (if bound.isEmpty then b.slots
            else pdiff b.slots (pset (bound.map slotRefExpr)))
      let node : Expr := .app f (genZero :: cols.toList)
      let S ← compute "S" (unions slotsOf.toList)
      let E ← compute "E" (pid S)
      pure ⟨E, node, S⟩

mutual

/-- Structural equality of expressions. -/
def exprEqB : Expr → Expr → Bool
  | .lit a, .lit b => a == b
  | .var a, .var b => a == b
  | .app f as, .app g bs => f == g && exprsEqB as bs
  | .min a b, .min c d => exprEqB a c && exprEqB b d
  | _, _ => false

def exprsEqB : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => exprEqB a b && exprsEqB as bs
  | _, _ => false

end

/-- Whether an action expression is a query atom's source application. -/
def atomRoot (st : Emit) (e : Expr) : Option Var :=
  st.flat.facts.toList.findSome? fun f => match f with
    | .atom a => if exprEqB a.src e then some a.root else none
    | _ => none

/-- A variable denotes its invocation, a matched application its root class,
anything else a build. -/
def termOf (e : Expr) : EmitM (Expr × Option Var) := do
  let st ← get
  match e with
  | .var v =>
    if isSlotVar v || v ∈ st.flat.payloadVars then throw s!"{v} unioned as a term"
    else pure (.var v, some v)
  | _ =>
    match atomRoot st e with
    | some r => pure (.var r, some r)
    | none => do
      let b ← build e
      pure (b.child, none)

/-- Compile one action. A union with the anchored root, whose renaming is the identity, is a
plain union; a union with another variable's invocation is a `RenamesTo` fact. -/
def compileAction (anchorVar : Var) : Action → EmitM (List Action)
  | .expr (.var _) => pure []
  | .expr e => do pure [.expr (← build e).child]
  | .union a b => do
    let (ta, va) ← termOf a
    let (tb, vb) ← termOf b
    match va, vb with
    | some x, some y =>
      if x = y then pure []
      else if x = anchorVar then pure [wRenamesTo ta (muVar y) tb]
      else if y = anchorVar then pure [wRenamesTo tb (muVar x) ta]
      else pure [wRenamesTo ta (pcomp (pinv (muVar x)) (muVar y)) tb]
    | none, some y =>
      if y = anchorVar then pure [.union ta tb] else pure [wRenamesTo ta (muVar y) tb]
    | some x, none =>
      if x = anchorVar then pure [.union ta tb] else pure [wRenamesTo tb (muVar x) ta]
    | none, none => pure [.union ta tb]
  | .subsume _ _ => throw "subsume in a slotted program"

/-- `RenamesTo` with a computed renaming: bind it first, since actions are plain. -/
def plainActions (as : List Action) : EmitM (List Action) := as.mapM fun a =>
  match a with
  | .expr (.app f [x, m, y]) =>
    if f = renamesToName then do
      match m with
      | .var _ => pure a
      | _ => do let mv ← compute "eqm" m; pure (write renamesToName [x, mv, y])
    else pure a
  | a => pure a

/-! ### Rules and checks -/

/-- The slot variables an action mentions. -/
def actionSlotVars (as : List Action) : List Var :=
  ((as.flatMap actionVars).filter isSlotVar).dedup

/-- Flatten a query, binders normalized; the facts, the roles, and the normalized actions. -/
def flattenQuery (L : Layout) (q : Query) (as : List Action) :
    Except String (Flat × List Action) := do
  let go : FlatM (List Action) := do
    let q ← q.mapM normalizePattern
    let as ← as.mapM normalizeAction
    q.forM flattenPattern
    pure as
  let (as, flat) ← go.run { L }
  pure (flat, as)

/-- The anchor of a query: the first atom's root. -/
def anchorOf (facts : List Fact) : Option Var :=
  facts.findSome? fun f => match f with
    | .atom a => some a.root
    | _ => none

/-- Compile a query with its actions into the alternatives of the compiled query and the
compiled actions. -/
def compileRuleParts (L : Layout) (q : Query) (as : List Action) :
    Except String (List (List Pattern) × List Action) := do
  let (flat, as) ← flattenQuery L q as
  if flat.facts.isEmpty then throw "a query needs a pattern"
  let some anchorVar := anchorOf flat.facts.toList | throw "a query needs a pattern"
  let conflict := flat.payloadVars.filter (· ∈ flat.termVars)
  unless conflict.isEmpty do throw s!"{conflict} used both as payload and as term"
  let go : EmitM (List (List Pattern) × List Action) := do
    scanFacts
    -- Every term variable must have been keyed by an atom.
    let st ← get
    for v in st.flat.termVars do
      if (st.firstOcc.lookup v).isNone then throw s!"variable {v} is bound by no pattern"
    -- A concrete slot in an action must already belong to the query's concrete-name set.
    for (f, args) in as.flatMap Action.apps do
      if isSlotName f && args.isEmpty && f ∉ st.concrete then
        throw s!"action-only concrete slot {f}; use a fresh slot variable"
    -- Query literals have their own fixed-name argument. Generated binder names and
    -- action-only names remain temporary, with freshness handled independently.
    modify fun st => { st with fixedSlots := st.patSlots.filter fun v => !v.startsWith "$@" }
    for v in actionSlotVars as do
      modify fun st => { st with patSlots := st.patSlots ∪ [v] }
    emitUnification anchorVar
    let alts ← emitGuards
    let acts ← plainActions (← as.flatMapM (compileAction anchorVar))
    let st ← get
    pure (alts.map fun alt => st.pats.toList ++ alt, acts)
  (go.run { flat }).map Prod.fst

/-- The compiled rules of a source rule: one per alternative of its query. The distribution
rule compiles as the paper displays it, with the generations `g_0`, `g_1` of the matched
rows bound as wildcards and the built rows at generation `0`; the flattened source variables
`x`, `b` become the pairs `(μ_x, factor)`, `(μ_b, body)`, computed in the query. -/
@[blueprint "def:slotted-compile-rule"
  (statement := /--
  \par\noindent The distribution rule, schematically ($g_0,g_1$ are wildcards):
  \[
  \begin{aligned}
   &\mathit{prod}=\mathtt{Mul}(g_0,\rho_x,\mathit{factor},\rho_s,\mathit{sum})\\
   &\land\mathit{sum}=\SumZeroTen(g_1,\$r,\rho_b,\mathit{body})\\
   &\land(\nu_0,\nu_1)=\operatorname{fresh}
      (\operatorname{img}(\rho_x)\cup\operatorname{img}(\rho_s),
       \{\$r\}\cup\operatorname{img}(\rho_b))\\
   &\land P=\{\$v\}\land C=\operatorname{distinct}(\operatorname{img}(\nu_0))
       \cup\operatorname{distinct}(\operatorname{img}(\nu_1))\\
   &\land\mathtt{RenamesTo}(\mathit{sum},\pi,\mathit{sum})
       \land\mathtt{FS}(\mathit{sum},B)\land\pi\in\operatorname{Perm}(B)\\
   &\land\mathtt{FS}(\mathit{prod},A)
       \land D=\operatorname{img}(\nu_0\circ\rho_x)\cup\operatorname{img}(\nu_1\circ\rho_b)\\
   &\land U_0=\operatorname{identity}
       (\operatorname{img}(\nu_0)\cup\operatorname{img}(\nu_1)\cup P)\\
   &\land U_1=\operatorname{unify}(U_0,\nu_0\circ\rho_s,\nu_1\circ\pi,C,P)\\
   &\land U_2=\operatorname{unify}(U_1,\nu_1(\$r),\$v,C,P)\\
   &\land q\in\operatorname{final\text{-}refine}(U_2,C,P,D)
       \land q'=\operatorname{anchor}(q,\nu_0|_A)\\
   &\land\mu_x=q'\circ\nu_0\circ\rho_x\land\mu_b=q'\circ\nu_1\circ\rho_b\\
   &\land\$v'=q'(\$v)\land\$v'\notin\operatorname{img}(\mu_x)
       \land T=\operatorname{img}(\mu_x)\cup\operatorname{img}(\mu_b)\\
   &\Rightarrow\kw{union}\bigl(\mathit{prod},
       \SumZeroTen(0,\$v',\mathrm{id}_T,
         \mathtt{Mul}(0,\mu_x,\mathit{factor},\mu_b,\mathit{body}))\bigr).
  \end{aligned}
  \]
  The temporary images are disjoint and avoid $P$. Unification preserves $\$v$;
  anchoring then transports the complete match into the product's stored coordinates.
  The generated refinement also lists intermediate roots, whose live slots are already
  reached by $x,b$ here. A variable right-hand side $y$ writes
  $\mathtt{RenamesTo}(\mathit{prod},\mu_y,c_y)$; action-only slots get fresh blocks.
  -/)
  (latexEnv := "paperfragment")]
def compileRule (L : Layout) (r : Rule) : Except String (List Rule) := do
  let (alts, acts) ← compileRuleParts L r.query r.actions
  pure (alts.map fun q => { query := q, actions := acts })

/-- The compiled check: the query's alternatives. -/
def compileCheck (L : Layout) (q : Query) : Except String (List Query) := do
  if q.isEmpty then pure [[]] else
  let (alts, _) ← compileRuleParts L q []
  pure alts

end Egglog.Slotted.Encode
