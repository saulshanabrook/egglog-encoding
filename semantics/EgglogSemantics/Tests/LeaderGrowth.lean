import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Impl.Merge

/-! Why the termination theorem excludes source saturation. -/

namespace Egglog.Tests.LeaderGrowth
open Congruence

set_option linter.hashCommand false

private def a : Expr := .app "C" []
private def f (x : Expr) : Expr := .app "F" [x]
private def seed : Program :=
  [.decl "C" (ctorDecl 0), .decl "F" (ctorDecl 1), .action (.union a (f a))]
private def rule : Rule :=
  ⟨[.expr (f (.var "x"))], [.expr (f (f (f (.var "x"))))], "R"⟩
private def program : Program := seed ++ [.rule rule, .saturate "R"]

#guard program.WellFormed
#guard program.Fragment

theorem excluded_by_noSaturate : ¬ program.NoSaturate := by
  intro h
  exact h (.saturate "R") (by simp [program])

-- Every source head is already inferred before the first source round.
#guard (execM seed).any fun d =>
  (matchQuery d rule.query).all fun σ =>
    patternHolds d (.expr (f (f (f (.var "x"))))) σ

private def initial : Option FDatabase := execM
  ((encodePrelude program ++ encodeCmds (seed ++ [.rule rule]) 0).map Command.command)

private def peakAfter (n : Nat) : Option (Nat × Bool) := do
  let mut d ← initial
  let mut stable := false
  for _ in [:n] do
    let e ← d.runRoundM "R"
    stable := d.sameData e
    d := e
  let sizes := (d.terms.filter (Term.isValue d.sig)).map Term.nodeSize
  pure (sizes.foldl max 0, stable)

-- Actual value terms grow, not just displaced row assertions. This is a finite trace,
-- not a proof of divergence or an interpreter-correctness claim.
#guard peakAfter 0 = some (2, false)
#guard peakAfter 1 = some (4, false)
#guard peakAfter 2 = some (6, false)
#guard peakAfter 3 = some (8, false)

end Egglog.Tests.LeaderGrowth
