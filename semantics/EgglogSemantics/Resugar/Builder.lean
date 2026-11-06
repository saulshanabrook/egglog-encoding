import EgglogSemantics.SourceProof.Checker

/-! Source proof construction. Every constructor validates the new root node against its
subproofs, so a lifting step fails where its justification is wrong. -/

namespace Egglog.Resugar

open SourceProof (Claim Proof)

def node (P : Program) (pf : Proof) : Option Proof :=
  if SourceProof.checkNode P pf then some pf else none

def symm (P : Program) : Proof → Option Proof
  | .symm p => some p
  | p => node P (.symm p)

def trans (P : Program) (p q : Proof) : Option Proof :=
  if p.claim.rhs != q.claim.lhs then none else node P (.trans p q)

def congr (P : Program) (p : Proof) (k : Nat) (q : Proof) : Option Proof := do
  let .app _ args := p.claim.rhs | none
  if args[k]? != some q.claim.lhs then none else node P (.congr p k q)

def orient (P : Program) (p : Proof) (c : Claim) : Option Proof :=
  if p.claim == c then some p else
    if p.claim.lhs == c.rhs && p.claim.rhs == c.lhs then symm P p else none

/-- The proof a maintenance step rebuilt, oriented as the row's claim reads. -/
def finish (P : Program) (p : Proof) (c : Claim) : Option Proof := orient P p c

end Egglog.Resugar
