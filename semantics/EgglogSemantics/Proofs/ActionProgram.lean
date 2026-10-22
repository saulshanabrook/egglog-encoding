import EgglogSemantics.Proofs.Step

/-! Splitting mathematical command sequences. -/

namespace Egglog

/-- Split a successful mathematical execution at a command-list boundary. -/
theorem ProgramStep.append_inv {p q : List Cmd} {d e : Database}
    (hr : ProgramStep d (p ++ q) e) : ∃ mid, ProgramStep d p mid ∧ ProgramStep mid q e := by
  induction p generalizing d with
  | nil => exact ⟨d, .nil, hr⟩
  | cons c cs ih =>
      obtain ⟨mid, hc, hrest⟩ := hr.cons_inv
      obtain ⟨post, hp, hq⟩ := ih hrest
      exact ⟨post, .cons hc hp, hq⟩

end Egglog
