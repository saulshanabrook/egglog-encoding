import EgglogSemantics.Proofs.Diagonal

/-! Identity and saturation for an empty rule list. -/

namespace Egglog.LiveTables

theorem sameMeaning_refl (d : Database) : d.SameMeaning d := .refl d

theorem runRules_eq_of_no_rules {d : Database} {R : List Rule}
    (h : R = []) : RunRules R d = d := by
  subst R
  simp [RunRules, RunWrites, RunErases, Database.addEqs]

theorem runSaturated_of_no_rules {d : Database} {R : List Rule}
    (h : R = []) : RunSaturated R d := by
  rw [RunSaturated, runRules_eq_of_no_rules h]
  exact .refl d

theorem empty_saturateReach : SaturateReach [] Database.empty Database.empty := by
  have h : RunRules [] Database.empty = Database.empty := runRules_eq_of_no_rules rfl
  simpa only [h] using (SaturateReach.fixpoint (rs := []) (db := Database.empty) (by rw [h]))

end Egglog.LiveTables
