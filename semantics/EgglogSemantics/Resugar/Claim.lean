import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Congruence.Encode

namespace Egglog.Resugar

open SourceProof (Claim)

/-- Whether a name is a node relation's. -/
def isNodeName (f : FnName) : Bool := "@Node".isPrefixOf f

/-- A union-find row records an equality and a node row the existence of its node;
everything else, a source value or an application the target matched, is its own
reflexive claim. -/
@[blueprint "def:lift-claim"
  (statement := /--
  \[
  \lceil\mathtt{UF}(a,b)\rceil\triangleq(a=b)\qquad\lceil t\rceil\triangleq(t=t)\ \text{ otherwise}
  \]
  -/)
  (latexEnv := "paperfragment")]
def factClaim (_ : Program) (t : Term) : Option Claim := do
  let .app f cols := t | some ⟨t, t⟩
  if f = ufName then
    let [a, b] := cols | none
    some ⟨a, b⟩
  else if isNodeName f then
    let some node := cols.getLast? | none
    some ⟨node, node⟩
  else some ⟨t, t⟩

end Egglog.Resugar
