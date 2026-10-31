import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Congruence.Encode

namespace Egglog.Resugar

open SourceProof (Claim)

/-- A union-find row records an equality; everything else, a source value or an
application the target matched, is its own reflexive claim. -/
def factClaim (_ : Program) (t : Term) : Option Claim := do
  let .app f cols := t | some ⟨t, t⟩
  if f = ufName then
    let [a, b] := cols | none
    some ⟨a, b⟩
  else some ⟨t, t⟩

end Egglog.Resugar
