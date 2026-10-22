import EgglogSemantics.Provenance.Extract
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Congruence.Relational

/-! The firing log: an instrumented program builds the data of the original, and every
data row of the final state has a checked proof read off the log. -/

namespace Egglog.Provenance.Tests

set_option linter.hashCommand false

private def atom (f : FnName) : Expr := .app f []
private def term (f : FnName) : Term := .app f []
private def global (as : List Action) : Cmd := .run [⟨[], as⟩]
private def prog (cs : List Cmd) : Program := ⟨cs, []⟩

/-- The instrumented run holds the original's terms plus the log, and every data row has
a proof. -/
def validates (P : Program) : Bool := (do
  let encoded ← encode P
  let original ← Relational.execProgram FDatabase.empty P.commands
  let annotated ← Relational.execProgram FDatabase.empty encoded.commands
  let proofs ← extract P annotated.terms
  some (unionFree encoded &&
    decide ((eraseLog annotated.terms).toFinset = original.terms.toFinset) &&
    decide ((proofs.map Prod.fst).toFinset = (dataRows P original.terms).toFinset))).getD false

private def nestedUnion : Program :=
  prog [global [.expr (.app "F" [atom "A"]), .expr (.app "F" [atom "B"]),
    .union (atom "A") (atom "B")]]

#guard validates (Congruence.encode nestedUnion)

private def equalityRule : Program :=
  prog [global [.expr (.app "F" [atom "A"])],
    .saturate [⟨[.eq (.app "F" [.var "x"]) (.app "F" [.var "x"])],
      [.expr (.app "G" [.var "x"])]⟩]]

#guard validates (Congruence.encode equalityRule)

private def emptyQuery : Program := prog [.saturate [⟨[], [.expr (atom "A")]⟩]]

#guard validates (Congruence.encode emptyQuery)

private def missingPremise : Program :=
  prog [.saturate [⟨[.expr (atom "Missing")], [.expr (atom "A")]⟩]]

#guard validates (Congruence.encode missingPremise)

/-- A rule that rewrites a row of its own relation: the replaced row is gone from the
state, and the replacement's proof cites the firing that replaced it. -/
private def rewriting : Program :=
  prog [global [.expr (.app "T" [.lit (.int 3)]), .expr (.app "Goal" [.lit (.int 2)])],
    .saturate [⟨[.expr (.app "T" [.var "x"]), .expr (.app "Goal" [.var "y"]),
      .ne (.var "x") (.var "y")], [.delete (.app "T" [.var "x"]), .expr (.app "T" [.var "y"])]⟩]]

#guard validates rewriting

private def table (n : Int) : Term := .app "T" [.lit (.int n)]
private def goalRow : Term := .app "Goal" [.lit (.int 2)]
private def stored : Proof := .rule (table 3) 0 [] []
private def goal : Proof := .rule goalRow 0 [] []
private def three : Term := .lit (.int 3)
private def rewritten : Proof :=
  .rule (table 2) 1 [("x", three), ("y", .lit (.int 2))] [stored, goal, .subterm three stored]

#guard check rewriting stored == some (table 3)
#guard check rewriting rewritten == some (table 2)
#guard (check rewriting (.rule (table 2) 0 [] [])).isNone
#guard (check rewriting (.rule (table 2) 1 [] [])).isNone
-- The disequality must hold between the bound values.
#guard (check rewriting (.rule (table 2) 1 [("x", .lit (.int 2)), ("y", .lit (.int 2))]
  [stored, goal, .subterm (.lit (.int 2)) goal])).isNone
-- Every node is checked, not only the root.
#guard (check rewriting (.subterm (table 3) (.rule (table 2) 0 [] []))).isNone

-- The log is what the extraction reads: without it no row has a proof.
private def uninstrumented : Option FDatabase :=
  Relational.execProgram FDatabase.empty rewriting.commands
#guard uninstrumented.map (fun d => (extractEach rewriting d.terms).all (·.2.isNone)) == some true
#guard uninstrumented.map (fun d =>
  let rows := dataRows rewriting d.terms
  rows.length == 2 && rows.contains (table 2) && rows.contains goalRow) == some true

-- Instrumentation keeps every rule and adds one log write per rule, numbered by position.
#guard (encode rewriting).map (·.rules.length) == some rewriting.rules.length
#guard (encode rewriting).any fun p => p.rules.zipIdx.all fun rk =>
  rk.1.actions.any fun a => match a with
    | .expr (.app f _) => fireIndex f == some rk.2
    | _ => false
#guard fireIndex (fireName 12) == some 12
#guard fireIndex "@prov:fire:" == none
#guard fireIndex "T" == none

-- Unions, reserved names, and names used both as rows and as values are rejected.
#guard (encode nestedUnion).isNone
#guard (encode (prog [global [.expr (.app (namePrefix ++ "user") [])]])).isNone
#guard (encode (prog [global [.expr (.app "T" [.app "T" []])]])).isNone

end Egglog.Provenance.Tests
