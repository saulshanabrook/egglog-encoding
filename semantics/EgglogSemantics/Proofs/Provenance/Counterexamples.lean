import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Congruence.Relational

namespace Egglog.Provenance.Counterexamples

set_option linter.hashCommand false

private def row : Term := .app "T" [.lit (.int 2)]
private def replacement : Program :=
  ⟨[.run [⟨[], [.expr row.toExpr]⟩], .run [⟨[], [.delete row.toExpr]⟩]], []⟩

-- A certificate records a historical firing, even if its row has since been deleted.
#guard check replacement (.rule row 0 [] []) == some row
#guard (Relational.execProgram FDatabase.empty replacement.commands).any
  fun d => !d.terms.contains row
-- A delete itself supplies no new fact.
#guard (check replacement (.rule row 1 [] [])).isNone

end Egglog.Provenance.Counterexamples
