import EgglogSemantics.Proofs.Congruence.Properties
import EgglogSemantics.Congruence.Correctness
import EgglogSemantics.Congruence.Relational
import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Tests.Parse
import EgglogSemantics.Tests.Egg

/-! Check outcomes, shared substitutions, and static rejection. -/

namespace Egglog.Tests.Checks

set_option linter.hashCommand false

private def atom (f : FnName) : Expr := .app f []
private def global (as : List Action) : Schedule := .run [⟨[], as⟩]
private def missing : Query := [.expr (atom "Missing")]
private def base : Schedule := global [.expr (.app "F" [atom "A"]), .expr (.app "G" [atom "B"])]
private def joined : Query :=
  [.expr (.app "F" [.var "x"]), .expr (.app "G" [.var "x"])]

private def observation (r : Option ExecutionResult) : Option Bool :=
  r.map ExecutionResult.succeeded

private def compiledObservation (p : Program) : Option Bool :=
  observation (Relational.observe (Congruence.encode p) (Congruence.encode_unionFree p))

-- Mentioning a name does not invent an instance. The whole conjunction needs one substitution.
#guard observation (observe ⟨base, missing⟩) == some false
#guard observation (observe ⟨base, joined⟩) == some false
#guard compiledObservation ⟨base, missing⟩ == some false
#guard compiledObservation ⟨base, joined⟩ == some false

private def unionPrefix : Schedule := .seq base (global [.union (atom "A") (atom "B")])
#guard observation (observe ⟨unionPrefix, joined⟩) == some true
#guard compiledObservation ⟨unionPrefix, joined⟩ == some true
#guard observation (observe ⟨.run [], []⟩) == some true
#guard compiledObservation ⟨.run [], []⟩ == some true

private def nested : Query := [.eq (.app "F" [atom "A"]) (.app "F" [atom "B"])]
#guard observation (observe ⟨base, nested⟩) == some false
#guard compiledObservation ⟨base, nested⟩ == some false
#guard observation (observe ⟨unionPrefix, nested⟩) == some true
#guard compiledObservation ⟨unionPrefix, nested⟩ == some true

-- A free variable fails expression evaluation; the check binds its own variables.
#guard (Expr.var "x").eval [] == none

-- A runner that cannot run the schedule reaches no check; one that does decides it.
#guard observation (observeWith (fun _ _ => none) (fun _ _ => true) FDatabase.empty
  ⟨.saturate (.run []), []⟩) == none
#guard observation (observeWith (fun d _ => some d) (fun _ _ => true) FDatabase.empty
  ⟨.run [], missing⟩) == some true

-- Well-formedness concerns syntax; absence is a valid runtime observation.
#guard (Program.WellFormed ⟨base, missing⟩)
#guard (Program.WellFormed ⟨base, joined⟩)
#guard Program.Fragment ⟨unionPrefix, joined⟩
#guard Program.WellFormed ⟨.run [], missing⟩
#guard !(Program.WellFormed ⟨base, [.expr (.app "F" [])]⟩)
#guard !(Program.WellFormed ⟨.seq base (global [.expr (.app "F" [.var "x"])]), joined⟩)
#guard Program.WellFormed ⟨global [.union (.lit (.int 0)) (.lit (.int 1))], []⟩
#guard !(Program.Fragment ⟨global [.union (.lit (.int 0)) (.lit (.int 1))], []⟩)
-- The check is part of the fragment: a disequality there is outside it.
#guard !(Program.Fragment ⟨base, [.ne (atom "A") (atom "B")]⟩)

-- Query compilation and provenance instrumentation keep the check.
private def provenancedObservation (p : Program) : Option Bool :=
  (Provenance.encode (Congruence.encode p)).bind fun p' =>
    observation (observeWith (Relational.execSchedule runFuel) Relational.holds FDatabase.empty p')
#guard provenancedObservation ⟨base, joined⟩ == some false
#guard provenancedObservation ⟨unionPrefix, joined⟩ == some true

-- Parsing keeps the check; a program without one ends in the empty check.
#guard observation ((Program.ofEgg "(check (Missing))").toOption.bind observe) == some false
#guard observation ((Program.ofEgg "(Missing)").toOption.bind observe) == some true

-- The check decides the outcome and nothing else: a failed check still ran the schedule,
-- and the check reads the final state with subsumption forgotten.
example {db d : Database} {P : Program} (hs : Reach db P.schedule d)
    (h : ¬ QueryHolds d.forgetSubsumed P.check) : Eval db P .checkFailed := .checkFailed hs h

end Egglog.Tests.Checks
