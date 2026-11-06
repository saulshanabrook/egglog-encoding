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

/-- `Eval`, computed: the general interpreter with observable check failure. -/
def observe (P : Program) : Option ExecutionResult :=
  observeWith (execSchedule runFuel) FDatabase.holds FDatabase.empty P

end Egglog
