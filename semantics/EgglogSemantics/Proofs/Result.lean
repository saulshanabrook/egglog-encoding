import EgglogSemantics.Proofs.Step
/-! Finite success and failure are decided by the program's final check. -/

namespace Egglog

@[simp] theorem Eval.ok_iff {db : Database} {p : Program} :
    Eval db p .ok ↔ ∃ d, Reach db p.schedule d ∧ QueryHolds d p.check := by
  constructor
  · intro h; cases h with | ok hs hq => exact ⟨_, hs, hq⟩
  · rintro ⟨d, hs, hq⟩; exact .ok hs hq

@[simp] theorem Eval.failed_iff {db : Database} {p : Program} :
    Eval db p .checkFailed ↔
      ∃ d, Reach db p.schedule d ∧ ¬ QueryHolds d p.check := by
  constructor
  · intro h; cases h with | checkFailed hs hq => exact ⟨_, hs, hq⟩
  · rintro ⟨d, hs, hq⟩; exact .checkFailed hs hq

/-- Finite outcomes are deterministic, including the final check. -/
theorem Eval.det {db : Database} {p : Program} {r s : Result}
    (hr : Eval db p r) (hs : Eval db p s) : r = s := by
  cases hr with
  | ok h hq =>
    cases hs with
    | ok _ _ => rfl
    | checkFailed h' hn => exact (hn (h.det h' ▸ hq)).elim
  | checkFailed h hn =>
    cases hs with
    | ok h' hq => exact (hn ((h.det h').symm ▸ hq)).elim
    | checkFailed => rfl

end Egglog
