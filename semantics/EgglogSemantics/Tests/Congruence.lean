import EgglogSemantics.Congruence.Reader
import EgglogSemantics.Congruence.Relational
import EgglogSemantics.Proofs.Congruence.Properties
import EgglogSemantics.Tests.Parse

/-! Executable regressions for rebuilding, congruence, existence, and ordered query flattening. -/

namespace Egglog.Congruence

set_option linter.hashCommand false

private def atom (f : FnName) : Expr := .app f []
private def term (f : FnName) : Term := .app f []
private def global (a : Action) : Schedule := .run [⟨[], [a]⟩]

private def nestedUnion : Program :=
  ⟨.seqAll [global (.expr (.app "F" [atom "A"])), global (.expr (.app "F" [atom "B"])),
    global (.union (atom "A") (atom "B"))], []⟩

private def runSameClass (P : Program) (a b : Term) : Bool :=
  (exec P).any fun d => sameClassF d a b

-- The congruence rule must make the parents equal.
#guard runSameClass (encode nestedUnion) (.app "F" [term "A"]) (.app "F" [term "B"])

/-- A compiled schedule without its rebuilds. -/
private def stripRebuilds : Schedule → Schedule
  | .seq (.run rs) (.saturate (.run _)) => .run rs
  | .seq S₁ S₂ => .seq (stripRebuilds S₁) (stripRebuilds S₂)
  | .saturate S => .saturate (stripRebuilds S)
  | S => S

-- This would pass vacuously if the reader did the rebuild's work: without the rebuilds
-- the union leaves `B` two live parents, so the terms over it have no id and the parent
-- equality is lost. The source has no run that could fire maintenance.
#guard !(runSameClass ⟨stripRebuilds (encode nestedUnion).schedule, []⟩
  (.app "F" [term "A"]) (.app "F" [term "B"]))

/-- The rows of `f` a query can see: the stale ones are subsumed and stay in the table. -/
private def liveRows (d : FDatabase) (f : FnName) (arity : Nat) : Nat :=
  (matchQuery d [.expr (.app f ((List.range arity).map fun i => .var s!"@v{i}"))]).length

-- Rebuilding leaves one live union-find row per value; the edges they replaced stay
-- subsumed. Both parents read to the one root of their class, the smaller application.
#guard (exec (encode nestedUnion)).any fun d =>
  liveRows d ufName 2 == 4 && d.rowCount ufName > 4 && !d.subsumed.isEmpty &&
    idF d (.app "F" [term "A"]) == some (.app "F" [term "A"]) &&
    idF d (.app "F" [term "B"]) == some (.app "F" [term "A"])

private def missingPremise : Program :=
  ⟨.seqAll [global (.expr (atom "A")), global (.expr (atom "B")),
    .saturate (.run [⟨[.expr (atom "Missing")], [.union (atom "A") (atom "B")]⟩])], []⟩

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

-- Structural reflexivity cannot supply a nonexistent premise: an application looks up,
-- and a binding is a representative, which the matcher never invents.
#guard !Relational.patternHolds FDatabase.empty
  (.eq (atom "Missing") (atom "Missing")) []
#guard Relational.patternHolds (FDatabase.empty.addTerm (term "A"))
  (.eq (.var "x") (.var "x")) [("x", term "A")]
#guard (Relational.matchQuery FDatabase.empty [.eq (.var "x") (.var "x")]).isEmpty
-- A disequality needs both sides held and distinct, and a subsumed row is not held for a
-- query but is for a check.
#guard !Relational.patternHolds (FDatabase.empty.addTerm (term "A"))
  (.ne (atom "A") (atom "B")) []
#guard !Relational.patternHolds ((FDatabase.empty.addTerm (term "A")).subsume (term "B"))
  (.ne (atom "A") (atom "B")) []
#guard Relational.holds ((FDatabase.empty.addTerm (term "A")).subsume (term "B"))
  [.ne (atom "A") (atom "B")]
#guard Relational.patternHolds ((FDatabase.empty.addTerm (term "A")).addTerm (term "B"))
  (.ne (.var "x") (.var "y")) [("x", term "A"), ("y", term "B")]
#guard !Relational.patternHolds ((FDatabase.empty.addTerm (term "A")).addTerm (term "B"))
  (.ne (.var "x") (.var "y")) [("x", term "A"), ("y", term "A")]

private def orderedQuery : Query :=
  [.eq (.app "F" [.app "G" [.var "x"], .app "G" [.var "x"]])
       (.app "H" [.app "G" [.var "x"]])]

-- Repeated subexpressions are separate occurrences, visited children-first and
-- left-to-right on both sides: an application over fresh child variables, one edge per
-- child to the child's id, and, where the id is needed, an edge to a fresh root. These are
-- the positions resugaring will consume.
example : encodeQuery orderedQuery 0 =
  ([.expr (.app "G" [.var "@v0"]), .expr (ufRow (.var "@v0") (.var "x")),
    .expr (ufRow (.app "G" [.var "@v0"]) (.var "@v1")),
    .expr (.app "G" [.var "@v2"]), .expr (ufRow (.var "@v2") (.var "x")),
    .expr (ufRow (.app "G" [.var "@v2"]) (.var "@v3")),
    .expr (.app "F" [.var "@v4", .var "@v5"]),
    .expr (ufRow (.var "@v4") (.var "@v1")), .expr (ufRow (.var "@v5") (.var "@v3")),
    .expr (ufRow (.app "F" [.var "@v4", .var "@v5"]) (.var "@v6")),
    .expr (.app "G" [.var "@v7"]), .expr (ufRow (.var "@v7") (.var "x")),
    .expr (ufRow (.app "G" [.var "@v7"]) (.var "@v8")),
    .expr (.app "H" [.var "@v9"]), .expr (ufRow (.var "@v9") (.var "@v8")),
    .expr (ufRow (.app "H" [.var "@v9"]) (.var "@v10")),
    .eq (.var "@v6") (.var "@v10")], 11) := rfl

-- One origin per compiled rule, in `Program.rules` order; the source tag is the rule's
-- position among the source rules, here the third rule.
#guard (compile missingPremise).origins.length == (encode missingPremise).rules.length
#guard (compile missingPremise).origins.contains (.source 2)
#guard ((maintenanceRules missingPremise).map Prod.snd).count (.rebuild .compress) == 1
#guard ((rebuildRules "F" 2).map Prod.snd) == [.rebuild (.congruence "F")]
#guard (rebuildRules "A" 0).isEmpty
-- The congruence rule of a binary constructor: both applications, the shared parents of
-- their children, both roots, and the orientation guard.
#guard (congruenceRule "F" 2).query.map Pattern.toEgg ==
  ["(F @a0 @a1)", "(F @b0 @b1)", "(@UF @a0 @r0)", "(@UF @b0 @r0)", "(@UF @a1 @r1)",
   "(@UF @b1 @r1)", "(@UF (F @a0 @a1) @y)", "(@UF (F @b0 @b1) @z)", "(= @y (min @y @z))",
   "(!= @y @z)"]

-- Every source schedule compiles to one schedule: each run followed by a rebuild, so a
-- source saturation's passes each rebuild as they go.
#guard (encode missingPremise).schedule.topLevel.length == 3
#guard match (encode missingPremise).schedule.topLevel with
  | [.seq (.run _) (.saturate (.run _)), .seq (.run _) (.saturate (.run _)),
     .saturate (.seq (.run _) (.saturate (.run _)))] => true
  | _ => false
#guard (encode ⟨.run [⟨[], [.expr (atom "A")]⟩], [.expr (atom "A")]⟩).check.map Pattern.toEgg ==
  ["(A)"]
-- A nested check reads the inner application's root through the outer child's edge.
#guard (encode ⟨.run [⟨[], [.expr (.app "F" [atom "A"])]⟩],
    [.expr (.app "F" [atom "A"])]⟩).check.map Pattern.toEgg ==
  ["(A)", "(@UF (A) @v0)", "(F @v1)", "(@UF @v1 @v0)"]

end Egglog.Congruence
