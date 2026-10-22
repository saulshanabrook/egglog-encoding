import EgglogSemantics.SourceProof.Format

namespace Egglog.SourceProof

def reflClaims (t : Term) : List Claim :=
  t.subtermList.map fun s => ⟨s, s⟩

/-- Only facts produced by this action, including constructed subterms. Source proofs cover
the monotone fragment: a delete produces no fact and makes its firing unusable. -/
def actionFacts (σ : Env) : Action → Option (List Claim)
  | .expr e => do
      let t ← e.eval σ
      some (reflClaims t)
  | .union a b => do
      let x ← a.eval σ
      let y ← b.eval σ
      if x.isLit || y.isLit then none
      else some (⟨x, y⟩ :: ⟨y, x⟩ :: (reflClaims x ++ reflClaims y))
  | .delete _ => none

def actionsFacts (σ : Env) : List Action → Option (List Claim)
  | [] => some []
  | a :: as => do
      let fs ← actionFacts σ a
      let rest ← actionsFacts σ as
      some (fs ++ rest)

end Egglog.SourceProof
