import EgglogSemantics.Congruence.Read

/-! Shapes of the generated table entries. -/

namespace Egglog.Congruence

def EntryShaped (t : Term) : Prop :=
  (∃ f cs e, t = Term.app (viewName f) (cs ++ [e])) ∨
    (∃ x p, t = Term.app ufName [x, p])

end Egglog.Congruence
