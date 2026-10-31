import EgglogSemantics.Resugar.Execute
import EgglogSemantics.Congruence.Relational

/-! Proofs the Lean and Rust source checkers must judge alike: lifted proofs for small
programs, and hand-written proofs with known verdicts. -/

namespace Egglog.Resugar.Fixtures

private def atom (f : FnName) : Expr := .app f []
private def term (f : FnName) : Term := .app f []
private def global (as : List Action) : Schedule := .run [⟨[], as⟩]
private def prog (cs : List Schedule) (q : Query := []) : Program := ⟨Schedule.seqAll cs, q⟩

def nestedUnion : Program :=
  prog [global [.expr (.app "F" [atom "A"]), .expr (.app "F" [atom "B"]),
    .union (atom "A") (atom "B")]]

def nestedQuery : Program :=
  prog [global [.expr (.app "F" [.app "G" [atom "B"], .app "G" [atom "B"]]),
          .union (atom "A") (atom "B")],
        .saturate (.run [⟨[.expr (.app "F" [.app "G" [.var "x"], .app "G" [.var "x"]])],
          [.expr (.app "H" [.var "x"])]⟩])]

def equalityQuery : Program :=
  prog [global [.expr (.app "F" [atom "A"]), .expr (.app "G" [atom "B"]),
          .union (.app "F" [atom "A"]) (.app "G" [atom "B"])],
        .saturate (.run [⟨[.eq (.app "F" [.var "x"]) (.app "G" [.var "y"])],
          [.union (.var "x") (.var "y")]⟩])]

/-- The seed and the rule saturate together: rule 0 builds `(F (A))`, rule 1 derives. -/
def ruleChain : Program :=
  prog [.saturate (.run [⟨[], [.expr (.app "F" [atom "A"])]⟩,
    ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])]⟩])]

def missingPremise : Program :=
  prog [global [.expr (atom "A"), .expr (atom "B")],
        .saturate (.run [⟨[.expr (atom "Missing")], [.union (atom "A") (atom "B")]⟩])]

def supportCase : Program :=
  prog [global [.expr (.app "F" [atom "A"])],
        .run [⟨[], [.union (atom "A") (.app "G" [atom "B"])]⟩]]

/-- Programs whose every data row lifts to an accepted source proof. -/
def lifted : List (String × Program) :=
  [("nested-union", nestedUnion), ("nested-query", nestedQuery),
   ("equality-query", equalityQuery), ("rule-chain", ruleChain),
   ("missing-premise", missingPremise), ("support", supportCase)]

structure Fixture where
  name : String
  program : Program
  certificates : List SourceProof.Proof

private def a : Term := term "A"
private def b : Term := term "B"
private def missing : Term := term "Missing"
private def fa : Term := .app "F" [a]
private def fb : Term := .app "F" [b]
private def ga : Term := .app "G" [a]
/-- Rule 0 of the seed builds `(F (A))`. -/
private def fact (t : Term) : SourceProof.Proof := .rule ⟨t, t⟩ 0 [] []
/-- Rule 1 of the seed unions `(A)` and `(B)`. -/
private def unionFact (x y : Term) : SourceProof.Proof := .rule ⟨x, y⟩ 1 [] []

private def seed : List Schedule :=
  [.run [⟨[], [.expr fa.toExpr]⟩, ⟨[], [.union a.toExpr b.toExpr]⟩]]

/-- Rule 2 builds `(G x)` from `(F x)`. -/
private def create : Program := prog (seed ++
  [.saturate (.run [⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])]⟩])])

/-- Rule 2 reads `(F x)` and then `(= x (B))`. -/
private def ordered : Program := prog (seed ++
  [.run [⟨[.expr (.app "F" [.var "x"]), .eq (.var "x") b.toExpr],
    [.expr (.app "G" [.var "x"])]⟩]])

/-- Rule 1 reads the nested pattern `(F (F x))` as one premise. -/
private def nested : Program :=
  prog [global [.expr (.app "F" [fa.toExpr])],
        .run [⟨[.expr (.app "F" [.app "F" [.var "x"]])], [.expr (.app "G" [.var "x"])]⟩]]

/-- Rule 2 fires only on `(Missing)`, which is never built. -/
private def absentPremise : Program :=
  prog [.run [⟨[], [.expr a.toExpr]⟩, ⟨[], [.expr b.toExpr]⟩],
        .run [⟨[.expr missing.toExpr], [.union a.toExpr b.toExpr]⟩]]

private def one (name : String) (P : Program) (pf : SourceProof.Proof) : Fixture :=
  ⟨name, P, [pf]⟩

/-- Accepted hand-written proofs: ordered premises and a nested premise. -/
def accepted : List Fixture :=
  [one "ordered-premises" ordered (.rule ⟨ga, ga⟩ 2 [("x", a)] [fact fa, unionFact a b]),
   one "nested-premise" nested (.rule ⟨ga, ga⟩ 1 [("x", a)] [fact (.app "F" [fa])])]

/-- Rejected hand-written proofs: invented initial facts, an absent premise, malformed
substitutions, wrong premise order or count, and wrong endpoints and conclusions. -/
def rejected : List Fixture :=
  [one "invented-initial-fact" create (fact missing),
   one "invented-application" create (fact fb),
   one "absent-premise" absentPremise (.rule ⟨a, b⟩ 2 [] [fact missing]),
   one "unbound-variable" create (.rule ⟨ga, ga⟩ 2 [] [fact fa]),
   one "wrong-binding" create (.rule ⟨ga, ga⟩ 2 [("x", b)] [fact fa]),
   one "missing-premise-proof" create (.rule ⟨ga, ga⟩ 2 [("x", a)] []),
   one "premise-order" ordered (.rule ⟨ga, ga⟩ 2 [("x", a)] [unionFact a b, fact fa]),
   one "wrong-conclusion" create (.rule ⟨a, b⟩ 2 [("x", a)] [fact fa]),
   one "transitivity-endpoints" create (.trans ⟨a, b⟩ (fact a) (fact b)),
   one "congruence-child" create (.congr ⟨fa, fb⟩ (fact fa) 0 (unionFact b a)),
   one "symmetry-claim" create (.symm ⟨a, a⟩ (fact fa))]

/-- Every fixture, with the lifted ones first. `none` if a program fails to lift. A
function, so that running the fixture programs is not part of program start-up. -/
def all (_ : Unit) : Option (List Fixture) := do
  let liftedFixtures ← lifted.mapM fun np => do
    let cs ← certificates (fun P => Relational.execSchedule runFuel FDatabase.empty P.schedule) np.2
    pure (⟨np.1, np.2, cs⟩ : Fixture)
  pure (liftedFixtures ++ accepted ++ rejected)

end Egglog.Resugar.Fixtures
