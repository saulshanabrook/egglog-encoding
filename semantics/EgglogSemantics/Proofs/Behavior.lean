import EgglogSemantics.Spec.Behavior

namespace Egglog

theorem behaves_success_iff {d : Database} {P : Program} :
    Behaves d P .success ↔ ∃ r, Eval d P r ∧ r.succeeded = true := by
  constructor
  · intro h; exact ⟨.ok, h, rfl⟩
  · rintro ⟨r, hr, hb⟩
    cases r with
    | ok => exact hr
    | checkFailed => contradiction

theorem behaves_failure_iff {d : Database} {P : Program} :
    Behaves d P .checkFailed ↔ ∃ r, Eval d P r ∧ r.succeeded = false := by
  constructor
  · intro h; exact ⟨.checkFailed, h, rfl⟩
  · rintro ⟨r, hr, hb⟩
    cases r with
    | ok => contradiction
    | checkFailed => exact hr

end Egglog
