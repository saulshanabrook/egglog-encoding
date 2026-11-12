import EgglogSemantics.Impl.Observe
import EgglogSemantics.Spec.Scope

/-!
# Execution without equality reasoning

This interpreter matches using structural equality and stored-value existence, without
computing congruence closure. Generated union-find and rebuilding rules execute as ordinary
rules, and subsumption hides exactly the named row.

The congruence gate in `DiffTest.lean` compares this runtime with the general interpreter
on compiled corpus programs. Their executable equivalence is not proved in Lean; the
compiler proof under `Proofs/Congruence/` concerns mathematical databases, where compiled
states are diagonal (`Congruence.Rel.diag`).
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

/-- A determined application read at identity, over rows that are not subsumed. -/
def joinAtomPlan (d : FDatabase) (pre : Env) (v : Var) (vars : List Var)
    (f : FnName) (as : List Expr) : Option JoinAtom :=
  let ρ := Env.canon vars pre
  if joinDrivable as && joinReady ρ as &&
      (as.any fun e => match e with | .var w => w == v | _ => false) then
    let ka := joinKnown ρ as
    if d.holdsAll (ka.filterMap id) then
      some ⟨vars, as, d.rows.filter fun r =>
        (r.fn == f) && !d.subsumed.contains (.app r.fn r.args) && joinConsistent ka r.args⟩
    else none
  else none

mutual

/-- Narrow candidates using nested application reads, restricting the environment to the
original pattern's variables. -/
def joinExprPlans (d : FDatabase) (pre : Env) (v : Var) (vars : List Var) :
    Expr → List JoinAtom
  | .app f as =>
      (joinAtomPlan d pre v vars f as).toList ++ joinArgsPlans d pre v vars as
  | _ => []

def joinArgsPlans (d : FDatabase) (pre : Env) (v : Var) (vars : List Var) :
    List Expr → List JoinAtom
  | [] => []
  | e :: es => joinExprPlans d pre v vars e ++ joinArgsPlans d pre v vars es

end

/-- `joinPlan` at identity, including the atom's nested application reads. -/
def joinPlan (d : FDatabase) (pre : Env) (v : Var) : Pattern → List JoinAtom
  | .expr e => joinExprPlans d pre v ((Pattern.expr e).freeVars []) e
  | _ => []

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
    let sets := ((q.flatMap (joinPlan d pre v)).map (admits · v)).mergeSort fun a b =>
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

mutual

/-- Execute `Reach` at structural equality, with at most `fuel` changing passes per
saturation followed by a stability check. Return `none` on budget exhaustion. -/
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

/-- The final check at identity: `QueryHolds` on the final state. -/
def holds (d : FDatabase) (q : Query) : Bool := !(matchQuery d q).isEmpty

/-- Execute a union-free program's schedule using only structural equality and table
operations. -/
def exec (P : Program) (_ : Program.UnionFree P) : Option FDatabase :=
  execSchedule runFuel FDatabase.empty P.schedule

/-- Structural execution with check failure distinguished from an inconclusive run. -/
def observe (P : Program) (_ : Program.UnionFree P) : Option ExecutionResult :=
  observeWith (execSchedule runFuel) holds FDatabase.empty P

end Egglog.Relational
