import EgglogSemantics.Proofs.Step

namespace Egglog

theorem Database.terms_empty_of_eqs_empty {d : Database} (h : d.eqs = ∅) : d.terms = ∅ := by
  ext t
  simp [Database.terms, h]

end Egglog
