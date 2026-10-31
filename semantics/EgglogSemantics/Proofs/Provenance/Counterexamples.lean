import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Congruence.Relational

namespace Egglog.Provenance.Counterexamples

set_option linter.hashCommand false

private def row : Term := .app "T" [.lit (.int 2)]
private def replacement : Program :=
  ⟨Schedule.seqAll [.run [⟨[], [.expr row.toExpr]⟩],
    .run [⟨[], [.subsume "T" [.lit (.int 2)]]⟩]], []⟩

-- A certificate records a historical firing, even if its row has since been subsumed.
#guard check replacement (.rule row 0 [] []) == some row
#guard (Relational.execSchedule runFuel FDatabase.empty replacement.schedule).any
  fun d => d.terms.contains row && d.subsumed.contains row
-- A subsume has no certificate constructor in the checker.
#guard (check replacement (.rule row 1 [] [])).isNone

end Egglog.Provenance.Counterexamples
