import EgglogSemantics.Proofs.Provenance.GeneratedClaim

namespace Egglog.Provenance.Generated

/-- A checked lifted UF row proves its two columns equal in the source. -/
theorem check_uf_infers {P : Program} {src : Database}
    (hs : ProgramStep Database.empty P.commands src)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules src)
    {pf : Proof} {a b : Term} {output : SourceProof.Proof}
    (hc : check (Congruence.encode P) pf = some (.app ufName [a, b]))
    (hl : Resugar.lift P pf = some output) : src.Infers a b := by
  apply check_claim_infers hs hclosed hc (claim := ⟨a, b⟩) _ hl
  simp [Resugar.factClaim, Congruence.tableRole]

/-- A checked lifted view proves the source claim read from the view's data columns. -/
theorem check_view_infers {P : Program} {src : Database}
    (hs : ProgramStep Database.empty P.commands src)
    (hclosed : ∀ c ∈ P.commands, RunSaturated c.rules src)
    {pf : Proof} {f : FnName} {cs : List Term} {e : Term} {output : SourceProof.Proof}
    (hc : check (Congruence.encode P) pf = some (.app (viewName f) (cs ++ [e])))
    (hm : Resugar.factClaim P (.app (viewName f) (cs ++ [e])) = some ⟨e, .app f cs⟩)
    (hl : Resugar.lift P pf = some output) : src.Infers e (.app f cs) :=
  check_claim_infers hs hclosed hc hm hl

end Egglog.Provenance.Generated
