import EgglogSemantics.Proofs.Resugar.Soundness

/-! Generated relational certificates imply source claims through checked lifting. -/

namespace Egglog.Provenance.Generated

/-- An accepted generated certificate with a successful lift establishes its mapped claim. -/
theorem check_claim_infers {P : Program} {src : Database}
    (hs : Reach Database.empty P.schedule src)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs src)
    {pf : Proof} {t : Term} {claim : SourceProof.Claim} {output : SourceProof.Proof}
    (hc : check (Congruence.encode P) pf = some t)
    (hm : Resugar.factClaim P t = some claim) (hl : Resugar.lift P pf = some output) :
    src.Infers claim.lhs claim.rhs :=
  Resugar.lift_infers hs (hs.wf Database.WF.empty) hclosed hc hm hl

end Egglog.Provenance.Generated
