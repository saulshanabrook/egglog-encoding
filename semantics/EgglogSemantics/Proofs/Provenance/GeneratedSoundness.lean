import EgglogSemantics.Proofs.Provenance.GeneratedClaim

namespace Egglog.Provenance.Generated

/-- A checked lifted UF row proves its two columns equal in the source. -/
theorem check_uf_infers {P : Program} {src : Database}
    (hs : Reach Database.empty P.schedule src)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs src)
    {pf : Proof} {a b : Term} {output : SourceProof.Proof}
    (hc : check (Congruence.encode P) pf = some (.app ufName [a, b]))
    (hl : Resugar.lift P pf = some output) : src.Infers a b := by
  apply check_claim_infers hs hclosed hc (claim := ⟨a, b⟩) _ hl
  simp [Resugar.factClaim]

/-- A checked lifted application, which the target matched as a value, proves that the
source holds it. -/
theorem check_term_infers {P : Program} {src : Database}
    (hs : Reach Database.empty P.schedule src)
    (hclosed : ∀ rs ∈ P.runs, RunSaturated rs src)
    {pf : Proof} {f : FnName} {cs : List Term} {output : SourceProof.Proof}
    (hf : f ≠ ufName)
    (hc : check (Congruence.encode P) pf = some (.app f cs))
    (hl : Resugar.lift P pf = some output) : src.Infers (.app f cs) (.app f cs) := by
  apply check_claim_infers hs hclosed hc (claim := ⟨.app f cs, .app f cs⟩) _ hl
  simp [Resugar.factClaim, hf]

end Egglog.Provenance.Generated
