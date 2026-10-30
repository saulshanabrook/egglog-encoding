import EgglogSemantics.SourceProof.Checker

namespace Egglog.SourceProof.Tests

set_option linter.hashCommand false

private def a : Term := .app "A" []
private def b : Term := .app "B" []
private def missing : Term := .app "Missing" []
private def fa : Term := .app "F" [a]
private def fb : Term := .app "F" [b]
private def ga : Term := .app "G" [a]

private def seed : Program :=
  ⟨[.run [⟨[], [.expr fa.toExpr]⟩], .run [⟨[], [.union a.toExpr b.toExpr]⟩]], []⟩

private def fact (x : Term) : Proof := .rule ⟨x, x⟩ 0 [] []
private def unionFact (x y : Term) : Proof := .rule ⟨x, y⟩ 1 [] []
private def accepts (P : Program) (pf : Proof) (c : Claim) : Bool := check P pf == some c
private def rejects (P : Program) (pf : Proof) : Bool := (check P pf).isNone

#guard accepts seed (fact a) ⟨a, a⟩
#guard accepts seed (unionFact b a) ⟨b, a⟩
#guard rejects seed (fact missing)
#guard rejects seed (fact fb)
#guard rejects (⟨[], []⟩ : Program) (fact (.lit (.int 3)))

private def rewrite : Proof := .congr ⟨fa, fb⟩ (fact fa) 0 (unionFact a b)
private def childRewrite : Proof := .trans ⟨fb, fb⟩ (.symm ⟨fb, fa⟩ rewrite) rewrite

#guard accepts seed childRewrite ⟨fb, fb⟩
#guard rejects seed (.symm ⟨a, a⟩ (fact fa))
#guard rejects seed (.congr ⟨fa, fb⟩ (fact fa) 1 (unionFact a b))
#guard rejects seed (.congr ⟨fa, fb⟩ (fact fa) 0 (unionFact b a))
#guard rejects seed (.trans ⟨a, b⟩ (fact a) (fact b))
-- Every node is checked, not only the root.
#guard rejects seed (.trans ⟨fb, fb⟩ (.symm ⟨fb, fa⟩ rewrite) (.rule ⟨fa, fb⟩ 0 [] []))

private def create : Rule :=
  ⟨[.expr (.app "F" [.var "x"])], [.expr (.app "G" [.var "x"])]⟩
private def program : Program := ⟨seed.commands ++ [.saturate [create]], []⟩
private def creation (premise : Proof) : Proof := .rule ⟨ga, ga⟩ 2 [("x", a)] [premise]

#guard accepts program (creation (fact fa)) ⟨ga, ga⟩
#guard rejects program (fact ga)
#guard rejects program (creation (fact a))
#guard rejects program (.rule ⟨ga, ga⟩ 0 [("x", a)] [fact fa])
#guard rejects program (.rule ⟨ga, ga⟩ 2 [] [fact fa])
#guard rejects program (.rule ⟨ga, ga⟩ 2 [("x", a), ("x", a)] [fact fa])
#guard rejects program (.rule ⟨ga, ga⟩ 2 [("x", a), ("unused", b)] [fact fa])
#guard rejects program (.rule ⟨a, b⟩ 2 [("x", a)] [fact fa])
#guard rejects program (.rule ⟨ga, ga⟩ 2 [("x", a)] [])
#guard rejects program (.rule ⟨ga, ga⟩ 2 [("x", a)] [fact fa, fact fa])

-- Rule indices flatten rule lists; an empty command does not consume an index.
private def grouped : Program :=
  ⟨[.run [], .run [⟨[], [.expr fa.toExpr]⟩, ⟨[], [.union a.toExpr b.toExpr]⟩],
    .saturate [create]], []⟩
#guard accepts grouped (fact fa) ⟨fa, fa⟩
#guard accepts grouped childRewrite ⟨fb, fb⟩
#guard accepts grouped (creation (fact fa)) ⟨ga, ga⟩

private def absentPremise : Program :=
  ⟨[.run [⟨[], [.expr a.toExpr]⟩], .run [⟨[], [.expr b.toExpr]⟩],
    .run [⟨[.expr missing.toExpr], [.union a.toExpr b.toExpr]⟩]], []⟩

#guard rejects absentPremise (.rule ⟨a, b⟩ 2 [] [.rule ⟨missing, missing⟩ 3 [] []])
#guard accepts (⟨absentPremise.commands ++ [.run [⟨[], [.expr missing.toExpr]⟩]], []⟩)
  (.rule ⟨a, b⟩ 2 [] [.rule ⟨missing, missing⟩ 3 [] []]) ⟨a, b⟩

private def gb : Term := .app "G" [b]

-- An expression premise may be anchored at another congruent term.
#guard accepts program (.rule ⟨gb, gb⟩ 2 [("x", b)] [rewrite]) ⟨gb, gb⟩

private def ordered : Program := ⟨seed.commands ++
  [.run [⟨[.expr (.app "F" [.var "x"]), .eq (.var "x") b.toExpr],
    [.expr (.app "G" [.var "x"])]⟩]], []⟩

#guard accepts ordered (.rule ⟨ga, ga⟩ 2 [("x", a)] [fact fa, unionFact a b]) ⟨ga, ga⟩
#guard rejects ordered (.rule ⟨ga, ga⟩ 2 [("x", a)] [unionFact a b, fact fa])

private def unconditional : Program :=
  ⟨[.run [⟨[], [.expr missing.toExpr]⟩]], []⟩

#guard accepts unconditional (.rule ⟨missing, missing⟩ 0 [] []) ⟨missing, missing⟩
#guard rejects unconditional (.rule ⟨missing, missing⟩ 1 [] [])

private def nested : Program :=
  ⟨[.run [⟨[], [.expr (.app "F" [fa.toExpr])]⟩],
   .run [⟨[.expr (.app "F" [.app "F" [.var "x"]])],
     [.expr (.app "G" [.var "x"])]⟩]], []⟩

-- One premise for the original nested query, with no flattening in the checker.
#guard accepts nested (.rule ⟨ga, ga⟩ 1 [("x", a)] [fact (.app "F" [fa])]) ⟨ga, ga⟩

#guard !sourceOk (⟨[.run [⟨[.expr (.app "F" [.min (.var "x") (.var "y")])], []⟩]], []⟩)
-- A bare variable or literal is not a query fact, as in egglog.
#guard !sourceOk (⟨[.run [⟨[.expr (.var "x")], []⟩]], []⟩)
#guard !sourceOk (⟨[.run [⟨[.expr (.lit (.int 3))], []⟩]], []⟩)
#guard !sourceOk (⟨seed.commands ++ [.run [⟨[], [.expr (.app "F" [])]⟩]], []⟩)
#guard rejects (⟨[.run [⟨[], [.expr (.var "unbound")]⟩]], []⟩)
  (.rule ⟨a, a⟩ 0 [] [])

-- The source fragment excludes both nonmonotone language constructs.
#guard !sourceOk ⟨[.run [⟨[], [.delete fa.toExpr]⟩]], []⟩
#guard !sourceOk ⟨[.run [⟨[.ne a.toExpr b.toExpr], []⟩]], []⟩

end Egglog.SourceProof.Tests
