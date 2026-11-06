import EgglogSemantics.SourceProof.Checker

/-! Certificates for the compiled program are proofs in the one proof language, checked by
the same checker as source certificates. A compiled program has only reflexive equations,
so a certificate's claim is `t = t` for the row or term `t` it establishes. -/

namespace Egglog.Provenance

export SourceProof (Proof)

def unionFree (P : Program) : Bool := P.rules.all fun r =>
  r.actions.all fun a => match a with | .union _ _ => false | _ => true

/-- Check a proof about the compiled program, which has no `union`, and return the fact it
establishes. -/
def check (P : Program) (pf : SourceProof.Proof) : Option Term := do
  if !unionFree P then none else
    let c ← SourceProof.checkIn P pf
    if c.lhs == c.rhs then some c.lhs else none

end Egglog.Provenance
