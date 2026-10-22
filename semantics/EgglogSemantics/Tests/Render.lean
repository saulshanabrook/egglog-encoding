import EgglogSemantics.SourceProof.Format
import EgglogSemantics.Tests.Egg

/-! Source proofs as indented text, one node per line, for snapshots under `tests/`. -/

namespace Egglog

def Term.toEgg (t : Term) : String := t.toExpr.toEgg

namespace SourceProof

def Claim.render (c : Claim) : String := c.lhs.toEgg ++ " = " ++ c.rhs.toEgg

private def substRender (σ : Env) : String :=
  "{" ++ String.intercalate ", " (σ.map fun b => b.1 ++ " := " ++ b.2.toEgg) ++ "}"

mutual

/-- The claim and its justification, with the subproofs indented below. -/
def Proof.render (indent : String) : Proof → String
  | .symm c p => indent ++ c.render ++ "  symm\n" ++ p.render (indent ++ "  ")
  | .trans c p q => indent ++ c.render ++ "  trans\n" ++
      p.render (indent ++ "  ") ++ q.render (indent ++ "  ")
  | .congr c p k q => indent ++ c.render ++ s!"  congr {k}\n" ++
      p.render (indent ++ "  ") ++ q.render (indent ++ "  ")
  | .rule c i σ ps => indent ++ c.render ++ s!"  rule {i} {substRender σ}\n" ++
      Proof.renderAll (indent ++ "  ") ps

def Proof.renderAll (indent : String) : List Proof → String
  | [] => ""
  | p :: ps => p.render indent ++ Proof.renderAll indent ps

end

end SourceProof

/-- Every lifted proof, separated by blank lines. -/
def Resugar.renderProofs (ps : List SourceProof.Proof) : String :=
  String.intercalate "\n" (ps.map (·.render ""))

end Egglog
