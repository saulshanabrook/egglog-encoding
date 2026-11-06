import EgglogSemantics.Proofs.Step

/-! Splitting mathematical schedule sequences. -/

namespace Egglog

/-- Split a successful execution at a schedule boundary. -/
theorem Reach.append_inv {p q : Schedule} {d e : Database}
    (hr : Reach d (.seq p q) e) : ∃ mid, Reach d p mid ∧ Reach mid q e :=
  hr.seq_inv

end Egglog
