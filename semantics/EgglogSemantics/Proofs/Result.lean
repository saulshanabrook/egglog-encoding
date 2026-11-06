import EgglogSemantics.Proofs.ActionProgram

/-! Finite success and failure are decided by the program's final check. -/

namespace Egglog

@[simp] theorem Eval.ok_iff {db : Database} {p : Program} :
    Eval db p .ok ↔ ∃ d, Reach db p.schedule d ∧ QueryHolds d.forgetSubsumed p.check := by
  constructor
  · intro h; cases h with | ok hs hq => exact ⟨_, hs, hq⟩
  · rintro ⟨d, hs, hq⟩; exact .ok hs hq

@[simp] theorem Eval.failed_iff {db : Database} {p : Program} :
    Eval db p .checkFailed ↔
      ∃ d, Reach db p.schedule d ∧ ¬ QueryHolds d.forgetSubsumed p.check := by
  constructor
  · intro h; cases h with | checkFailed hs hq => exact ⟨_, hs, hq⟩
  · rintro ⟨d, hs, hq⟩; exact .checkFailed hs hq

/-- Schedules compose before the one final check. -/
theorem Eval.append_of_ok {db mid : Database} {p : Schedule} {q : Program} {r : Result}
    (hp : Reach db p mid) (hq : Eval mid q r) :
    Eval db ⟨.seq p q.schedule, q.check⟩ r := by
  cases hq with
  | ok hs hq => exact .ok (hp.append hs) hq
  | checkFailed hs hq => exact .checkFailed (hp.append hs) hq

theorem Eval.append_iff {db : Database} {p : Schedule} {q : Program} {r : Result} :
    Eval db ⟨.seq p q.schedule, q.check⟩ r ↔
      ∃ mid, Reach db p mid ∧ Eval mid q r := by
  constructor
  · intro h
    cases h with
    | ok hs hq =>
      obtain ⟨mid, hp, ht⟩ := hs.append_inv
      exact ⟨mid, hp, .ok ht hq⟩
    | checkFailed hs hq =>
      obtain ⟨mid, hp, ht⟩ := hs.append_inv
      exact ⟨mid, hp, .checkFailed ht hq⟩
  · rintro ⟨mid, hp, hq⟩; exact append_of_ok hp hq

/-- A schedule prefix contains no check, so evaluation reaches the suffix. -/
theorem Eval.append_of_no_checks {db : Database} {p : Schedule} {q : Program} {r : Result}
    (h : Eval db ⟨.seq p q.schedule, q.check⟩ r) :
    ∃ mid, Reach db p mid ∧ Eval mid q r :=
  Eval.append_iff.mp h

/-- An empty conjunction always passes, including in an empty database. -/
theorem QueryHolds.nil (db : Database) : QueryHolds db [] :=
  queryHolds_iff_validQuerySubst.mpr ⟨[], [], .nil, .nil⟩

/-- A program with an empty final check can only succeed. -/
theorem Eval.ok_of_no_checks {db : Database} {p : Program} {r : Result}
    (hp : p.check = []) (h : Eval db p r) :
    r = .ok ∧ ∃ d, Reach db p.schedule d := by
  cases h with
  | ok hs _ => exact ⟨rfl, _, hs⟩
  | checkFailed hs hq => exact (hq (hp ▸ QueryHolds.nil _)).elim

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
