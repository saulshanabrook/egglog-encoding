import EgglogSemantics.Impl.Interp

/-! Outcomes for executable sanity checks. `none` means the interpreter did not produce
an outcome (for example, exhausted fuel); it never means that the check failed. -/

namespace Egglog

inductive ExecutionResult where
  | ok (db : FDatabase)
  | checkFailed

def ExecutionResult.succeeded : ExecutionResult → Bool
  | .ok _ => true
  | .checkFailed => false

/-- Run the schedule with `step`, then decide the final check with `holds`. -/
def observeWith (step : FDatabase → Schedule → Option FDatabase)
    (holds : FDatabase → Query → Bool) (db : FDatabase) (P : Program) :
    Option ExecutionResult :=
  (step db P.schedule).map fun d => if holds d P.check then .ok d else .checkFailed

/-- The state with subsumption forgotten: what egglog's `check` currently sees
(`check_facts` queries with `include_subsumed`). -/
def FDatabase.forgetSubsumed (d : FDatabase) : FDatabase := { d with subsumed := [] }

/-- The final check with egglog's current `check` semantics when `includeSubsumed` is set:
the query runs on the state with subsumption forgotten. Otherwise `FDatabase.holds`. -/
def FDatabase.holdsWith (includeSubsumed : Bool) (d : FDatabase) (q : Query) : Bool :=
  bif includeSubsumed then d.forgetSubsumed.holds q else d.holds q

/-- `Eval`, computed: the general interpreter with observable check failure. With
`checkIncludesSubsumed` the final check sees subsumed rows, as egglog's `check` currently
does; this compatibility mode serves differential testing, and the refinement theorems are
about the default. -/
def observe (P : Program) (checkIncludesSubsumed : Bool := false) : Option ExecutionResult :=
  observeWith (execSchedule runFuel) (FDatabase.holdsWith checkIncludesSubsumed) FDatabase.empty P

end Egglog
