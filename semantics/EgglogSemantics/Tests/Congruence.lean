import EgglogSemantics.Congruence.Reader
import EgglogSemantics.Congruence.Relational
import EgglogSemantics.Proofs.Congruence.Properties
import EgglogSemantics.Tests.Parse

/-! Executable regressions for rebuilding, existence, and ordered query flattening. -/

namespace Egglog.Congruence

set_option linter.hashCommand false

private def atom (f : FnName) : Expr := .app f []
private def term (f : FnName) : Term := .app f []
private def global (a : Action) : Cmd := .run [⟨[], [a]⟩]

private def nestedUnion : Program :=
  ⟨[global (.expr (.app "F" [atom "A"])), global (.expr (.app "F" [atom "B"])),
    global (.union (atom "A") (atom "B"))], []⟩

private def runSameClass (P : Program) (a b : Term) : Bool :=
  (exec P).any fun d => sameClassF d a b

-- Child re-keying and the view collision must make the parents equal.
#guard runSameClass (encode nestedUnion) (.app "F" [term "A"]) (.app "F" [term "B"])

-- This would pass vacuously if the reader ignored the rebuild: removing the saturations
-- must lose the parent equality. The source has no run that could fire maintenance.
#guard !(runSameClass ⟨(encode nestedUnion).commands.filter fun c => match c with
    | .saturate _ => false | _ => true, []⟩ (.app "F" [term "A"]) (.app "F" [term "B"]))

-- Rebuilding leaves one union-find row per value and one view row per class.
#guard (exec (encode nestedUnion)).any fun d =>
  d.rowCount ufName == 4 && d.rowCount (viewName "F") == 1 &&
    d.rowCount (viewName "A") == 1 && d.rowCount (viewName "B") == 1

private def missingPremise : Program :=
  ⟨[global (.expr (atom "A")), global (.expr (atom "B")),
    .saturate [⟨[.expr (atom "Missing")], [.union (atom "A") (atom "B")]⟩]], []⟩

-- A premise that was never built cannot justify this union.
#guard (exec (encode missingPremise)).isSome
#guard !(runSameClass (encode missingPremise) (term "A") (term "B"))
#guard !(runSameClass (encode missingPremise) (term "Missing") (term "Missing"))

-- The target also executes with structural equality alone. Both the positive rebuild
-- case and the absent-premise counterexample are checked through that runtime.
#guard (Relational.exec (encode nestedUnion) (encode_unionFree nestedUnion)).any fun d =>
  sameClassF d (.app "F" [term "A"]) (.app "F" [term "B"])
#guard (Relational.exec (encode missingPremise) (encode_unionFree missingPremise)).any fun d =>
  !sameClassF d (term "A") (term "B") && !sameClassF d (term "Missing") (term "Missing")

-- Structural reflexivity cannot supply a nonexistent premise.
#guard !Relational.patternHolds FDatabase.empty
  (.eq (.var "x") (.var "x")) [("x", term "Missing")]
#guard Relational.patternHolds (FDatabase.empty.addTerm (term "A"))
  (.eq (.var "x") (.var "x")) [("x", term "A")]
-- A disequality needs both sides held and distinct.
#guard !Relational.patternHolds (FDatabase.empty.addTerm (term "A"))
  (.ne (.var "x") (.var "y")) [("x", term "A"), ("y", term "B")]
#guard Relational.patternHolds ((FDatabase.empty.addTerm (term "A")).addTerm (term "B"))
  (.ne (.var "x") (.var "y")) [("x", term "A"), ("y", term "B")]
#guard !Relational.patternHolds ((FDatabase.empty.addTerm (term "A")).addTerm (term "B"))
  (.ne (.var "x") (.var "y")) [("x", term "A"), ("y", term "A")]

private def orderedQuery : Query :=
  [.eq (.app "F" [.app "G" [.var "x"], .app "G" [.var "x"]])
       (.app "H" [.app "G" [.var "x"]])]

-- Repeated subexpressions are separate occurrences, visited children-first and
-- left-to-right on both sides. These are the positions resugaring will consume.
example : encodeQuery orderedQuery 0 =
  ([.expr (.app (viewName "G") [.var "x", .var "@v0"]),
    .expr (.app (viewName "G") [.var "x", .var "@v1"]),
    .expr (.app (viewName "F") [.var "@v0", .var "@v1", .var "@v2"]),
    .expr (.app (viewName "G") [.var "x", .var "@v3"]),
    .expr (.app (viewName "H") [.var "@v3", .var "@v4"]),
    .eq (.var "@v2") (.var "@v4")], 5) := rfl

-- One origin per compiled rule, in `Program.rules` order; the source tag is the rule's
-- position among the source rules, here the third rule.
#guard (compile missingPremise).origins.length == (encode missingPremise).rules.length
#guard (compile missingPremise).origins.contains (.source 2)
#guard ((maintenanceRules missingPremise).map Prod.snd).count (.rebuild .compress) == 1
#guard ((rebuildRules "F" 2).map Prod.snd) ==
  [.rebuild (.eclass "F"), .rebuild (.child "F" 0), .rebuild (.child "F" 1),
   .rebuild (.viewCollide "F")]
#guard tableRole nestedUnion ufName == some .unionFind
#guard tableRole nestedUnion (viewName "F") == some (.view "F")
#guard tableRole nestedUnion "F" == none

-- Every source command compiles to itself and a rebuild.
#guard (encode missingPremise).commands.length == 2 * 3
#guard (encode ⟨[.run [⟨[], [.expr (atom "A")]⟩]], [.expr (atom "A")]⟩).check.map Pattern.toEgg ==
  ["(@AView @v0)"]

end Egglog.Congruence
