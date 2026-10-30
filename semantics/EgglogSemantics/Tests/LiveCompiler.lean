import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Impl.Merge
import EgglogSemantics.Impl.Observe

/-! Executable regressions for live rows, size-first leaders, and nested rule heads.
These are sanity checks, not an interpreter-correctness theorem. -/

namespace Egglog.Tests.LiveCompiler
open Congruence

set_option linter.hashCommand false

private def atom (f : FnName) : Expr := .app f []

private def seed : Program :=
  [.decl "C" (ctorDecl 0), .decl "F" (ctorDecl 1),
   .action (.union (atom "C") (.app "F" [atom "C"]))]

private def nestedRule : Rule :=
  ⟨[.expr (.app "F" [.var "x"])],
    [.expr (.app "F" [.app "F" [.var "x"]])], "R"⟩

private def nested : Program := seed ++ [.rule nestedRule, .saturate "R"]

#guard nested.WellFormed
#guard nested.Fragment

-- Every source head is already represented before its first round.
#guard (execM seed).any fun d =>
  (matchQuery d nestedRule.query).all fun σ =>
    patternHolds d (.expr (.app "F" [.app "F" [.var "x"]])) σ

-- Previously the compiled nested head kept introducing taller structural ids.
-- Successful execution here requires the compiled saturation to finish.
#guard (execM (encode nested)).isSome
#guard (observeM (encode (nested ++
    [.check [.expr (.app "F" [.app "F" [.app "F" [atom "C"]]])]]))).any
  ExecutionResult.succeeded

private def absent : Program :=
  [.decl "Missing" (ctorDecl 0)] ++ nested ++ [.check [.expr (atom "Missing")]]

-- A terminating saturation still cannot invent a missing constructor instance.
#guard (observeM (encode absent)).any fun r => !r.succeeded

private def descending : Program :=
  [.decl "c" (ctorDecl 0), .decl "A" (ctorDecl 1), .decl "B" (ctorDecl 1),
   .action (.union (.app "B" [atom "c"]) (.app "A" [.app "B" [atom "c"]])),
   .rule ⟨[.expr (.app "A" [.var "x"])], [.expr (.app "A" [.var "x"])], "R"⟩,
   .saturate "R"]

-- The structural tie-break alone preferred A(B(c)) to B(c), allowing taller leaders.
#guard Term.blt (.app "B" [.app "c" []]) (.app "A" [.app "B" [.app "c" []]])
#guard descending.WellFormed
#guard descending.Fragment
#guard (execM (encode descending)).isSome

private def liveRows : Program :=
  [.decl "C" (ctorDecl 0), .decl "D" (ctorDecl 0),
   .decl ufName (tableDecl 1), .decl "V" (tableDecl 0),
   .action (.expr (.app "V" [atom "D"])),
   .action (.expr (.app "V" [atom "C"]))]

-- A displaced output no longer matches even though its term still exists.
#guard (observeM (liveRows ++ [.check [.expr (.app "V" [atom "C"])]])).any
  ExecutionResult.succeeded
#guard (observeM (liveRows ++ [.check [.expr (.app "V" [atom "D"])]])).any
  fun r => !r.succeeded

end Egglog.Tests.LiveCompiler
