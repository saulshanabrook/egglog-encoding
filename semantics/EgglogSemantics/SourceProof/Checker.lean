import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Source.Domain

/-! Source certificates use original rule queries and retain evidence of term existence.
Arbitrary reflexivity cannot justify a missing rule premise. -/

namespace Egglog.SourceProof

/-- Only the monotone constructor source fragment. -/
def sourceOk (P : Program) : Bool := decide P.Fragment

/-- A fact premise proves its instance equal to some held term; an equality premise proves
its two sides equal. The fragment has no disequality. -/
def premiseMatches (σ : Env) (p : Pattern) (c : Claim) : Bool :=
  match p with
  | .expr e => e.eval σ == some c.rhs
  | .eq a b => a.eval σ == some c.lhs && b.eval σ == some c.rhs
  | .ne _ _ => false

def premisesMatch (σ : Env) : Query → List Claim → Bool
  | [], [] => true
  | p :: ps, c :: cs => premiseMatches σ p c && premisesMatch σ ps cs
  | _, _ => false

def supportedValue (premises : List Claim) (t : Term) : Bool :=
  premises.any fun c => decide (t ∈ c.lhs.subtermList ∨ t ∈ c.rhs.subtermList)

def ruleFacts (r : Rule) (σ : Env) (premises : List Claim) : Option (List Claim) := do
  if decide ((Env.dom σ).Perm r.query.vars) &&
      σ.all (fun b => supportedValue premises b.2) &&
      premisesMatch σ r.query premises then
    actionsFacts σ r.actions
  else none

/-- The root node, against the claims its subproofs state. -/
def checkNode (P : Program) (pf : Proof) : Bool :=
  match pf with
  | .symm c p => c == ⟨p.claim.rhs, p.claim.lhs⟩
  | .trans c p q => p.claim.rhs == q.claim.lhs && c == ⟨p.claim.lhs, q.claim.rhs⟩
  | .congr c p k q =>
      match p.claim.rhs with
      | .app f args =>
          args[k]? == some q.claim.lhs && c == ⟨p.claim.lhs, .app f (args.set k q.claim.rhs)⟩
      | .lit _ => false
  | .rule c i σ ps => (do
      let r ← P.rules[i]?
      let fs ← ruleFacts r σ (ps.map Proof.claim)
      some (decide (c ∈ fs))).getD false

mutual

/-- Every node is valid. -/
def valid (P : Program) : Proof → Bool
  | .symm c p => valid P p && checkNode P (.symm c p)
  | .trans c p q => valid P p && valid P q && checkNode P (.trans c p q)
  | .congr c p k q => valid P p && valid P q && checkNode P (.congr c p k q)
  | .rule c i σ ps => allValid P ps && checkNode P (.rule c i σ ps)

def allValid (P : Program) : List Proof → Bool
  | [] => true
  | p :: ps => valid P p && allValid P ps

end

/-- The claim of a proof whose every node is valid. -/
def check (P : Program) (pf : Proof) : Option Claim := do
  if !sourceOk P then none else
    if valid P pf then some pf.claim else none

end Egglog.SourceProof
