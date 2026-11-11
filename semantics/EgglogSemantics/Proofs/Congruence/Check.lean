import EgglogSemantics.Proofs.Congruence.Source
import EgglogSemantics.Proofs.Congruence.QueryCorr

/-! The final check: at a canonical compiled state, the compiled check holds exactly when the
source check holds on the partner. The check is compiled like a rule query and read at the
same kind of state, so this is the query correspondence. -/

namespace Egglog.Congruence

variable {sub : Bool}

variable {P : Program}

/-- The source check on the partner holds exactly when the compiled check holds on the
canonical compiled state. -/
theorem check_corr (hP : P.Fragment) {x d : Database} (hx : SrcInv P x) (h : Rel sub x d)
    (hc : Canon d) :
    QueryHolds x P.check ↔ QueryHolds d (encodeQueryWith {} P.check 0).1 := by
  have hq := queryOk_check hP
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨σ', hσ', -⟩ := fire_complete h hc hx.wf hq hσ
    exact ⟨σ', hσ'⟩
  · rintro ⟨σ', hσ'⟩
    exact ⟨_, (fire_sound h hc hx.wf hq (check_keyed hP) hσ').1⟩

end Egglog.Congruence
