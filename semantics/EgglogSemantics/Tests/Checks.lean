import EgglogSemantics.Proofs.Congruence.Properties
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
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
-- The check is a query like a rule's: it may test a disequality, under saturation too, and
-- it may take the minimum of query variables when the program has no saturation.
private def leastCheck : Query :=
  [.expr (.app "F" [.var "x"]), .expr (.app "G" [.var "y"]),
   .eq (.var "x") (.min (.var "x") (.var "y"))]
#guard Program.Fragment ⟨base, [.ne (atom "A") (atom "B")]⟩
#guard Program.Fragment ⟨.seq base (.saturate (.run [])), [.ne (atom "A") (atom "B")]⟩
#guard Program.Fragment ⟨base, leastCheck⟩
#guard !(Program.Fragment ⟨.seq base (.saturate (.run [])), leastCheck⟩)
#guard !(SourceProof.Fragment ⟨base, [.ne (atom "A") (atom "B")]⟩)
#guard !(SourceProof.Fragment ⟨base, leastCheck⟩)
-- A rule may test a disequality, under saturation too.
private def guarded : Rule :=
  ⟨[.expr (.app "F" [.var "x"]), .expr (.app "G" [.var "y"]), .ne (.var "x") (.var "y")],
   [.expr (.app "H" [.var "x", .var "y"])]⟩
#guard Program.Fragment ⟨.seq base (.saturate (.run [guarded])), joined⟩
#guard !(SourceProof.Fragment ⟨.seq base (.saturate (.run [guarded])), joined⟩)
-- A rule may take the minimum of query variables when the program has no saturation.
private def least : Rule :=
  ⟨[.expr (.app "F" [.var "x"]), .expr (.app "G" [.var "y"])],
   [.expr (.app "H" [.min (.var "x") (.var "y")])]⟩
#guard Program.Fragment ⟨.seq base (.run [least]), joined⟩
#guard !(Program.Fragment ⟨.seq base (.saturate (.run [least])), joined⟩)
#guard !(SourceProof.Fragment ⟨.seq base (.run [least]), joined⟩)
-- A minimum over an application is outside the fragment: the compiled head would build it
-- whether or not it is chosen.
#guard !(Program.Fragment ⟨.seq base (.run [⟨[.expr (.app "F" [.var "x"])],
  [.expr (.app "H" [.min (.app "F" [.var "x"]) (.var "x")])]⟩]), joined⟩)
-- Source rules may subsume rows.
#guard (Program.Fragment ⟨.seq base (.run [⟨[.expr (.app "F" [.var "x"])],
  [.subsume "F" [.var "x"]]⟩]), joined⟩)

-- Query compilation and provenance instrumentation keep the check.
private def provenancedObservation (p : Program) : Option Bool :=
  (Provenance.encode (Congruence.encode p)).bind fun p' =>
    observation (observeWith (Relational.execSchedule runFuel) Relational.holds FDatabase.empty p')
#guard provenancedObservation ⟨base, joined⟩ == some false
#guard provenancedObservation ⟨unionPrefix, joined⟩ == some true

-- The check sees live rows only; the observer's compatibility mode, egglog's current
-- `check`, sees subsumed rows too.
private def subsumedRow : Program :=
  ⟨.seq (global [.expr (.app "F" [atom "A"])])
    (.run [⟨[.expr (.app "F" [.var "x"])], [.subsume "F" [.var "x"]]⟩]),
   [.expr (.app "F" [atom "A"])]⟩
#guard observation (observe subsumedRow) == some false
#guard observation (observe subsumedRow true) == some true
#guard observation (observe ⟨subsumedRow.schedule, [.expr (.app "F" [.var "x"])]⟩) == some false

-- Parsing keeps the check; a program without one ends in the empty check.
#guard observation ((Program.ofEgg "(check (Missing))").toOption.bind observe) == some false
#guard observation ((Program.ofEgg "(Missing)").toOption.bind observe) == some true

-- The check decides the outcome and nothing else: a failed check still ran the schedule,
-- and the check reads the final state as a rule query does.
example {db d : Database} {P : Program} (hs : Reach db P.schedule d)
    (h : ¬ QueryHolds d P.check) : Eval db P .checkFailed := .checkFailed hs h

end Egglog.Tests.Checks
