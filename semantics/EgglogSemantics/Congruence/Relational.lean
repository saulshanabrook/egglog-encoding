import EgglogSemantics.Impl.Observe
import EgglogSemantics.Spec.Scope

/-!
# Execution without equality reasoning

This target interpreter never computes congruence closure. Its equality relation is the
diagonal of the stored values: testing a pair requires structural identity and existence.
Generated union-find and rebuilding rules run as ordinary rules, and a delete removes
exactly the row named.

The matcher is the general one (`Impl/Interp.lean`) with every congruence test specialized
to identity, which makes a test constant-time instead of a scan of the closure. The
congruence gate in `DiffTest.lean` checks executably that this runtime and the general
interpreter agree on every compiled corpus program; the proof of that equivalence awaits
the port of the compiler proofs.
-/

namespace Egglog.Relational

/-- Matching one pattern: structural identity and existence, including existence of both
sides of `=` and `≠`. -/
def patternHolds (d : FDatabase) (p : Pattern) (σ : Env) : Bool :=
  match p with
  | .expr e =>
    match e.eval σ with
    | none => false
    | some t => decide (t ∈ d.terms)
  | .eq e₁ e₂ =>
    match e₁.eval σ, e₂.eval σ with
    | some a, some b => decide (a = b) && decide (a ∈ d.terms)
    | _, _ => false
  | .ne e₁ e₂ =>
    match e₁.eval σ, e₂.eval σ with
    | some a, some b => decide (a ≠ b) && decide (a ∈ d.terms) && decide (b ∈ d.terms)
    | _, _ => false

/-- `joinConsistent` at identity: every determined operand is the row's column. The
planner only produces determined operands the database holds. -/
def joinConsistent (ks : List (Option Term)) (xs : List Term) : Bool :=
  ks.length == xs.length && (ks.zip xs).all fun p =>
    match p.1 with
    | none => true
    | some t => t == p.2

/-- `joinPlan` at identity. -/
def joinPlan (d : FDatabase) (pre : Env) (v : Var) : Pattern → Option JoinAtom
  | .expr e =>
    match e.ctorAtom with
    | none => none
    | some (f, as) =>
      let vars := (Pattern.expr e).freeVars []
      if joinDrivable as && decide (v ∈ vars) then
        let ρ := Env.canon vars pre
        let ka := joinKnown ρ as
        if d.holdsAll (ka.filterMap id) then
          some ⟨vars, as, d.rows.filter fun r => (r.fn == f) && joinConsistent ka r.args⟩
        else none
      else none
  | _ => none

/-- The values a plan's surviving rows admit for `v`: the column at each position where
`v` occurs, when those positions agree. This is `JoinAtom.keeps` projected once per level,
instead of a row scan per candidate. -/
def admits (a : JoinAtom) (v : Var) : List Term :=
  let positions := a.keys.zipIdx.filterMap fun ei => match ei.1 with
    | .var w => if w == v then some ei.2 else none
    | _ => none
  a.rows.filterMap fun r =>
    match positions.filterMap (fun i => r.args[i]?) with
    | [] => none
    | t :: ts => if ts.all (· == t) then some t else none

/-- `joinCands` at identity: the candidates every driving atom admits, in `ts` order. -/
def joinCands (d : FDatabase) (q : Query) (held : Bool) (ts : List Term) (pre : Env)
    (v : Var) : List Term :=
  if held then
    let sets := ((q.filterMap (joinPlan d pre v)).map (admits · v)).mergeSort fun a b =>
      decide (a.length ≤ b.length)
    ts.filter fun t => sets.all fun s => s.contains t
  else ts

/-- `matchJoin` at identity. -/
def matchJoin (d : FDatabase) (q : Query) (ts : List Term) (held : Bool) (pre : Env) :
    List Var → List Env
  | [] =>
      if q.all fun p => patternHolds d p (Env.canon (p.freeVars []) pre) then [[]]
      else []
  | v :: vs =>
      (joinCands d q held ts pre v).flatMap fun t =>
        let pre' := pre ++ [(v, t)]
        if (Query.decided d pre' q).all fun p =>
              patternHolds d p (Env.canon (p.freeVars []) pre') then
          (matchJoin d q ts held pre' vs).map fun σ => (v, t) :: σ
        else []

/-- The substitutions satisfying a query, in the general matcher's order. -/
def matchQuery (d : FDatabase) (q : Query) : List Env :=
  matchJoin d q d.terms (d.holdsAll d.terms) [] (Query.freeVars q [])

/-- Delete at identity: the rows named, and no other spelling. A literal is not a row, so
naming one deletes nothing, as in the specification. -/
def deleteAtoms (X : List Term) (d : FDatabase) : FDatabase :=
  if X.isEmpty then d else
    let gone : Term → Bool := fun s => X.contains s && !s.isLit &&
      !(d.terms.any fun u => u != s && decide (s ∈ u.subtermList)) &&
      !(d.eqs.any fun p => p.1 != p.2 && (p.1 == s || p.2 == s))
    { d with terms := d.terms.filter fun s => !gone s,
             rows := d.rows.filter fun r => !gone (.app r.fn r.args) }

/-- One round of `rs`: match every rule against the pre-state, delete exactly the rows the
firings delete, then add every firing's writes. -/
def runRules (rs : List Rule) (d : FDatabase) : FDatabase :=
  let firings := rs.map fun r => (r, matchQuery d r.query)
  let deleted := firings.flatMap fun rs => rs.2.flatMap fun σ =>
    (actionsDeletes σ rs.1.actions).getD []
  let base := deleteAtoms deleted d
  firings.foldl (fun acc rs => rs.2.foldl (fireWritesInto rs.1) acc) base

def runSaturate (rs : List Rule) : Nat → FDatabase → Option FDatabase
  | 0, d => if d.sameData (runRules rs d) then some d else none
  | n + 1, d =>
    let e := runRules rs d
    if d.sameData e then some d else runSaturate rs n e

def execCmd (d : FDatabase) : Cmd → Option FDatabase
  | .run rs => some (runRules rs d)
  | .saturate rs => runSaturate rs runFuel d

def execProgram (d : FDatabase) : List Cmd → Option FDatabase
  | [] => some d
  | c :: cs => (execCmd d c).bind fun e => execProgram e cs

/-- `QueryHolds` at identity. -/
def holds (d : FDatabase) (q : Query) : Bool := !(matchQuery d q).isEmpty

/-- Execute a union-free program's commands using only structural equality and table
operations. -/
def exec (P : Program) (_ : Program.UnionFree P) : Option FDatabase :=
  execProgram FDatabase.empty P.commands

/-- Structural execution with check failure distinguished from an inconclusive run. -/
def observe (P : Program) (_ : Program.UnionFree P) : Option ExecutionResult :=
  observeWith execCmd holds FDatabase.empty P

end Egglog.Relational
