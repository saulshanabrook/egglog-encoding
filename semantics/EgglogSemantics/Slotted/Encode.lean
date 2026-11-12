import EgglogSemantics.Slotted.Encode.Query
import EgglogSemantics.Slotted.Encode.Premises
import EgglogSemantics.Slotted.Spec.Divergence
import EgglogSemantics.Source.WellFormed

/-!
# The slotted pass

`compile bind P` compiles a slotted program, a plain program `P` with its binder signature
`bind`, to a plain program over the target of `Slotted/Target/`: ground facts become their
representation, every source run becomes the run of its compiled rules followed by the
maintenance saturation, sequences and saturations compile structurally, and the check becomes
its compiled query, or goal rules writing `@Goal()` after the schedule and the check `@Goal()`
when a `!=` makes the query disjunctive. Programs the pass cannot compile faithfully are
rejected with the reason. `Pass.Correct` states what phase 3 proves of the pass.
-/

namespace Egglog.Slotted

open Encode

namespace Encode

/-- A fact: a rule with an empty query, whose actions are ground. -/
def compileGroundRule (L : Layout) (r : Rule) : Except String Rule := do
  let acts ← r.actions.mapM fun a => match a with
    | .expr e => do pure (Action.expr (← reprGround L e).1)
    | .union a b => do
      if a.isLit || b.isLit then throw "a literal unioned as a term"
      if a.slotName?.isSome || b.slotName?.isSome then
        throw "a bare slot union needs an invocation, not the shared slot leaf"
      pure (Action.union (← reprGround L a).1 (← reprGround L b).1)
    | .subsume _ _ => throw "subsume in a slotted program"
  pure ⟨[], acts⟩

/-- A source rule: a fact, or a query with actions. -/
def compileAnyRule (L : Layout) (r : Rule) : Except String (List Rule) :=
  if r.query.isEmpty then (fun r => [r]) <$> compileGroundRule L r else compileRule L r

/-- The source constructors: every applied name that is neither a slot nor a predicate. -/
def sourceCtors (P : Egglog.Program) : List (FnName × Nat) :=
  P.ctors.filter fun fk => !isSlotName fk.1 && (Builtin.ofName fk.1).isNone

/-- Compile a schedule: every run of compiled rules is followed by the rebuild. -/
def compileSchedule (L : Layout) (ctors : List (FnName × Nat)) :
    Schedule → Except String Schedule
  | .run rs => do
    let rs' ← rs.flatMapM (compileAnyRule L)
    pure (.seq (.run rs') (rebuild L ctors))
  | .saturate S => do pure (.saturate (← compileSchedule L ctors S))
  | .seq S₁ S₂ => do
    pure (.seq (← compileSchedule L ctors S₁) (← compileSchedule L ctors S₂))

/-- The static conditions the pass requires. -/
def wellFormed (bind : Binders) (P : Egglog.Program) : Except String Unit := do
  let ctors := sourceCtors P
  let L := Layout.ofProgram bind P
  for (f, n) in ctors do
    unless (bind f).Nodup do throw s!"{f}: duplicate binder annotation"
    for ji in bind f do
      if ji.1 ≥ n || ji.2 ≥ n then throw s!"{f}: binder index outside arity {n}"
      if ji.1 = ji.2 then throw s!"{f}: binding position {ji.1} binds in itself"
      if L.column f ji.2 = .payload then throw s!"{f}: a binder covers a payload column"
      for ki in bind f do
        if ki.2 = ji.1 then throw s!"{f}: binding position {ji.1} is itself bound"
        if ji.2 = ki.2 && coveredBy L f ji.1 != coveredBy L f ki.1 then
          throw s!"{f}: overlapping binder scopes must coincide"
    unless (bind.bindingPositions f).Pairwise (· < ·) do
      throw s!"{f}: binding positions must be listed in increasing order"
  for n in P.names do
    if "@".isPrefixOf n then throw s!"name {n} is in the generated namespace"
    if "$@".isPrefixOf n then throw s!"slot {n} is in the placeholder namespace"
  for (f, args) in Encode.Program.apps P do
    if isSlotName f && !args.isEmpty then throw s!"slot {f} applied to arguments"
  for r in P.rules do
    for v in r.actions.flatMap actionVars do
      unless v ∈ r.query.vars || isSlotVar v do
        throw s!"head variable {v} is not bound"
  unless Egglog.Program.OrderingFree P do throw "min in a slotted program"
  unless P.schedule.subsumeFreeB do throw "subsume in a slotted program"
  unless P.AritiesAgree do throw "a name is applied at two arities"

end Encode

/-- The slotted pass. -/
def compile (bind : Binders) (P : Egglog.Program) : Except String Egglog.Program := do
  wellFormed bind P
  let L := Layout.ofProgram bind P
  let ctors := sourceCtors P
  let S ← compileSchedule L ctors P.schedule
  let alts ← compileCheck L P.check
  match alts with
  | [q] => pure ⟨S, q⟩
  | qs => pure ⟨.seq S (.run (qs.map fun q => ⟨q, [write goalName []]⟩)), [row goalName []]⟩

/-- A program with a failing check, standing in for a rejected program. -/
def rejected : Egglog.Program := ⟨.run [], [.expr (.app "@Rejected" [])]⟩

/-- The pass as a total function: a rejected program compiles to `rejected`. -/
def encode (bind : Binders) (P : Egglog.Program) : Egglog.Program := (compile bind P).toOption.getD rejected

/-- The pass on a slotted program. -/
def Program.encode (P : Slotted.Program) : Egglog.Program := Slotted.encode P.binders P.plain

/-! ### What phase 3 proves -/

/-- **Slotted pass correctness** (phase 3). For a slotted program the pass compiles, the
compiled program has the same outcome under the target semantics as the source under the
slotted semantics, and the compiled schedule diverges exactly when the source one does.
`Pass.Premises` supplies the well-formed binder signature, well-bound expressions, consistent
payload layout, action scope and source-round equivariance. Successful compilation checks
the remaining syntactic conditions. This is a proposition for phase 3, not a theorem. -/
def Pass.Correct (P : Slotted.Program) : Prop :=
  Pass.Premises P → ∀ P' : Egglog.Program, compile P.binders P.plain = .ok P' →
    (∀ o : Result,
      Target.Eval Database.empty P' o ↔ SEval P.binders Database.empty P.plain o) ∧
    (Target.Diverges Database.empty P'.schedule ↔
      SDiverges P.binders Database.empty P.plain.schedule)

/-! ### The congruence pass's fragment -/

/-- The clauses of `Program.Fragment` a compiled program fails, by name: where the slotted
pass's output leaves the congruence pass's fragment. -/
def fragmentReport (P : Egglog.Program) : List String :=
  (if decide (Egglog.Program.OrderingFree P ∨ (P.NoSaturate ∧ P.minOverVarsB = true)) then []
    else ["ordering"]) ++
  (if decide (∀ n ∈ P.names, ¬ "@".isPrefixOf n) then [] else ["noAt"]) ++
  (if decide P.QueriesEncodable then [] else ["queryEncodable"]) ++
  (if decide (P.schedule.unionAppsB = true ∨ P.schedule.litFreeB = true) then []
    else ["noLitUnion"]) ++
  (if decide P.AritiesAgree then [] else ["aritiesAgree"]) ++
  (if decide P.HeadsScoped then [] else ["headsScoped"])

end Egglog.Slotted
