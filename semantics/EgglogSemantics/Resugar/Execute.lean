import EgglogSemantics.Resugar.Lift
import EgglogSemantics.Impl.Interp

namespace Egglog.Resugar

open SourceProof (Proof)

/-- Run the instrumented compilation of `P` with `exec` and lift a proof of every row. -/
def certificates (exec : Program → Option FDatabase) (P : Program) :
    Option (List Proof) := do
  let annotated ← Provenance.encode (Congruence.encode P)
  let d ← exec annotated
  extractAll P d.terms

end Egglog.Resugar
