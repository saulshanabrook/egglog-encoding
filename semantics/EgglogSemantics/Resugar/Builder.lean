import EgglogSemantics.SourceProof.Checker

/-! Source proof construction. Every constructor validates the new root node against its
subproofs, so a lifting step fails where its justification is wrong. -/

namespace Egglog.Resugar

open SourceProof (Claim Proof)

def node (P : Program) (pf : Proof) : Option Proof :=
  if SourceProof.checkNode P pf then some pf else none

def symm (P : Program) : Proof → Option Proof
  | .symm _ p => some p
  | p => node P (.symm ⟨p.claim.rhs, p.claim.lhs⟩ p)

def trans (P : Program) (p q : Proof) : Option Proof :=
  if p.claim.rhs != q.claim.lhs then none else
    node P (.trans ⟨p.claim.lhs, q.claim.rhs⟩ p q)

def congr (P : Program) (p : Proof) (k : Nat) (q : Proof) : Option Proof := do
  let .app f args := p.claim.rhs | none
  if args[k]? != some q.claim.lhs then none else
    node P (.congr ⟨p.claim.lhs, .app f (args.set k q.claim.rhs)⟩ p k q)

def orient (P : Program) (p : Proof) (c : Claim) : Option Proof :=
  if p.claim == c then some p else
    if p.claim.lhs == c.rhs && p.claim.rhs == c.lhs then symm P p else none

def contains (c : Claim) (t : Term) : Bool :=
  decide (t ∈ c.lhs.subtermList ∨ t ∈ c.rhs.subtermList)

/-- `t = t` from a proof whose claim is an endpoint equation of `t`, else `descend`. -/
def endpoints (P : Program) (t : Term) (p : Proof)
    (descend : Unit → Option Proof) : Option Proof :=
  if !contains p.claim t then none
  else if p.claim.lhs == t then do
    let s ← symm P p
    trans P p s
  else if p.claim.rhs == t then do
    let s ← symm P p
    trans P s p
  else descend ()

/-- Recover subterm existence from a source derivation, without a new proof axiom. -/
def support (P : Program) (t : Term) : Proof → Option Proof
  | p@(.rule _ command σ ps) => endpoints P t p fun _ =>
      node P (.rule ⟨t, t⟩ command σ ps)
  | p@(.symm _ q) => endpoints P t p fun _ => support P t q
  | p@(.trans _ q r) | p@(.congr _ q _ r) => endpoints P t p fun _ =>
      support P t q <|> support P t r

def witness (P : Program) (t : Term) : List Proof → Option Proof
  | [] => none
  | p :: ps => support P t p <|> witness P t ps

def finish (P : Program) (p : Proof) (c : Claim) : Option Proof :=
  orient P p c <|> if c.lhs == c.rhs then support P c.lhs p else none

end Egglog.Resugar
