import EgglogSemantics.Proofs.Diagonal

/-! Identity and saturation for an empty rule list. -/

namespace Egglog.LiveTables

theorem sameMeaning_refl (d : Database) : d.SameMeaning d := .refl d

theorem runRules_eq_of_no_rules {d : Database} {R : List Rule}
    (h : R = []) : RunRules R d = d := by
  subst R
  simp [RunRules, Database.sUnion]

theorem runSaturated_of_no_rules {d : Database} {R : List Rule}
    (h : R = []) : RunSaturated R d := by
  rw [RunSaturated, runRules_eq_of_no_rules h]
  exact .refl d

theorem empty_saturateReach :
    Reach Database.empty (.saturate (.run [])) Database.empty := by
  have h : RunRules [] Database.empty = Database.empty := runRules_eq_of_no_rules rfl
  exact .fixpoint (by simpa only [h] using (Reach.run (db := Database.empty) (rs := []))) (.refl _)

end Egglog.LiveTables
