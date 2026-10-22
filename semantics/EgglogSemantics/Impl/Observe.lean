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

/-- Run the commands with `step`, then decide the final check with `holds`. -/
def observeWith (step : FDatabase → Cmd → Option FDatabase)
    (holds : FDatabase → Query → Bool) (db : FDatabase) (P : Program) :
    Option ExecutionResult :=
  (P.commands.foldlM step db).map fun d => if holds d P.check then .ok d else .checkFailed

/-- `Eval`, computed: the general interpreter with observable check failure. -/
def observe (P : Program) : Option ExecutionResult :=
  observeWith execCmd FDatabase.holds FDatabase.empty P

end Egglog
