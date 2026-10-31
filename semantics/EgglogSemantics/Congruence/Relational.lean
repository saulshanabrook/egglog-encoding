import EgglogSemantics.Impl.Observe
import EgglogSemantics.Spec.Scope

/-!
# Execution without equality reasoning

This target interpreter never computes congruence closure. Its equality relation is the
diagonal of the stored values: testing a pair requires structural identity and existence.
Generated union-find and rebuilding rules run as ordinary rules, and a subsumed row is
exactly the row named.

The matcher is the general one (`Impl/Interp.lean`) with every congruence test specialized
to identity, which makes a test constant-time instead of a scan of the closure. The
congruence gate in `DiffTest.lean` checks executably that this runtime and the general
interpreter agree on every compiled corpus program; the proof of that equivalence awaits
the port of the compiler proofs.
-/

namespace Egglog.Relational

/-- A read row at identity: held and, for an application, not subsumed. A literal is not a
row, so a mark on one hides nothing, as in `Database.live`. -/
def liveRow (d : FDatabase) (t : Term) : Bool :=
  decide (t ∈ d.terms) && (t.isLit || !d.subsumed.contains t)

mutual

/-- `Expr.Matches` at identity: the expression evaluates and every application it reads is
held and not subsumed. -/
def exprHolds (d : FDatabase) (σ : Env) : Expr → Bool
  | .lit l => liveRow d (.lit l)
  | .var v => (Env.lookup v σ).isSome
  | .app f args =>
      exprsHold d σ args &&
        match Expr.evalList args σ with
        | some ts => liveRow d (.app f ts)
        | none => false
  | .min a b => exprHolds d σ a && exprHolds d σ b

/-- `exprHolds` over an argument list. -/
def exprsHold (d : FDatabase) (σ : Env) : List Expr → Bool
  | [] => true
  | e :: es => exprHolds d σ e && exprsHold d σ es

end

/-- Matching one pattern: both sides hold, and `=` and `≠` are structural. -/
def patternHolds (d : FDatabase) (p : Pattern) (σ : Env) : Bool :=
  match p with
  | .expr e => exprHolds d σ e
  | .eq e₁ e₂ =>
    exprHolds d σ e₁ && exprHolds d σ e₂ &&
      match e₁.eval σ, e₂.eval σ with
      | some a, some b => a == b
      | _, _ => false
  | .ne e₁ e₂ =>
    exprHolds d σ e₁ && exprHolds d σ e₂ &&
      match e₁.eval σ, e₂.eval σ with
      | some a, some b => a != b
      | _, _ => false

/-- `joinConsistent` at identity: every determined operand is the row's column. The
planner only produces determined operands the database holds. -/
def joinConsistent (ks : List (Option Term)) (xs : List Term) : Bool :=
  ks.length == xs.length && (ks.zip xs).all fun p =>
    match p.1 with
    | none => true
    | some t => t == p.2

/-- `joinPlan` at identity, over the rows that are not subsumed. -/
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
          some ⟨vars, as, d.rows.filter fun r =>
            (r.fn == f) && !d.subsumed.contains (.app r.fn r.args) && joinConsistent ka r.args⟩
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

/-- One round of `rs`: match every rule against the pre-state, then apply every firing. -/
def runRules (rs : List Rule) (d : FDatabase) : FDatabase :=
  let firings := rs.map fun r => (r, matchQuery d r.query)
  firings.foldl (fun acc rs => rs.2.foldl (fireInto rs.1) acc) d

def runSaturate (rs : List Rule) : Nat → FDatabase → Option FDatabase
  | 0, d => if d.sameData (runRules rs d) then some d else none
  | n + 1, d =>
    let e := runRules rs d
    if d.sameData e then some d else runSaturate rs n e

mutual

/-- `Reach` at identity, with `fuel` passes allowed per saturation. -/
def execSchedule (fuel : Nat) (d : FDatabase) : Schedule → Option FDatabase
  | .run rs => some (runRules rs d)
  | .seq S₁ S₂ => (execSchedule fuel d S₁).bind fun e => execSchedule fuel e S₂
  | .saturate S => execSaturate fuel fuel d S
termination_by S => (sizeOf S, 0)

def execSaturate (fuel : Nat) : Nat → FDatabase → Schedule → Option FDatabase
  | 0, d, S => (execSchedule fuel d S).bind fun e => if d.sameData e then some e else none
  | n + 1, d, S => (execSchedule fuel d S).bind fun e =>
      if d.sameData e then some e else execSaturate fuel n e S
termination_by n _ S => (sizeOf S, n + 1)

end

/-- The final check at identity: `QueryHolds` on the state with subsumption forgotten. -/
def holds (d : FDatabase) (q : Query) : Bool := !(matchQuery d.forgetSubsumed q).isEmpty

/-- Execute a union-free program's schedule using only structural equality and table
operations. -/
def exec (P : Program) (_ : Program.UnionFree P) : Option FDatabase :=
  execSchedule runFuel FDatabase.empty P.schedule

/-- Structural execution with check failure distinguished from an inconclusive run. -/
def observe (P : Program) (_ : Program.UnionFree P) : Option ExecutionResult :=
  observeWith (execSchedule runFuel) holds FDatabase.empty P

end Egglog.Relational
