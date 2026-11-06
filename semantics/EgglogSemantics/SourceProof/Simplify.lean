import EgglogSemantics.SourceProof.Checker

/-! Removing the detours a mechanical lifting leaves in a proof, for presentation. Every
rewrite preserves the claim; a user checks the result again. -/

namespace Egglog.SourceProof

instance : Inhabited Proof := ⟨.rule ⟨.lit (.int 0), .lit (.int 0)⟩ 0 [] []⟩

/-- Whether a proof's claim is reflexive. -/
def Proof.reflexive (p : Proof) : Bool := p.claim.lhs == p.claim.rhs

/-- A transitivity through a reflexive side is the other side, a transitivity into a
congruence whose first argument only restates the middle term is that congruence from the
first side, a congruence with a reflexive child is its first argument, a doubled symmetry
cancels, and the symmetry of a rule node whose firing also states the reversed claim is
that rule node. -/
partial def Proof.simplify (P : Program) : Proof → Proof
  | .symm p =>
    let p := p.simplify P
    if p.reflexive then p else
    match p with
    | .symm q => q
    | .rule c i σ ps =>
      let reversed : Proof := .rule ⟨c.rhs, c.lhs⟩ i σ ps
      if checkNode P reversed then reversed else .symm p
    | _ => .symm p
  | .trans p q =>
    let p := p.simplify P
    let q := q.simplify P
    if p.reflexive then q else if q.reflexive then p else
    match q with
    | .congr q' k r =>
      -- `trans(π : a = s, cong_k(s = s, π'))` is `cong_k(π, π')`.
      if q'.reflexive && q'.claim.lhs == p.claim.rhs then .congr p k r else .trans p q
    | _ => .trans p q
  | .congr p k q =>
    let p := p.simplify P
    let q := q.simplify P
    if q.reflexive then p else .congr p k q
  | .rule c i σ ps => .rule c i σ (ps.map (·.simplify P))

end Egglog.SourceProof
