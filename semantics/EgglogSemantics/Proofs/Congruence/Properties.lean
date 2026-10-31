import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Spec.Step

/-! Structural properties of the congruence compiler, independent of provenance. -/

namespace Egglog.Congruence

private theorem actions_unionFree_append {as bs : List Action}
    (ha : Actions.UnionFree as) (hb : Actions.UnionFree bs) :
    Actions.UnionFree (as ++ bs) := by
  induction as with
  | nil => exact hb
  | cons a as ih => exact ⟨ha.1, ih ha.2⟩

mutual

/-- Compiled constructions write rows and never assert a built-in union. -/
theorem encodeBuild_unionFree : ∀ e : Expr, Actions.UnionFree (encodeBuild e)
  | .lit _ | .var _ => ⟨trivial, trivial⟩
  | .min a b => actions_unionFree_append (encodeBuild_unionFree a) (encodeBuild_unionFree b)
  | .app _ es => actions_unionFree_append (encodeBuildArgs_unionFree es) ⟨trivial, trivial⟩

theorem encodeBuildArgs_unionFree : ∀ es : List Expr, Actions.UnionFree (encodeBuildArgs es)
  | [] => trivial
  | e :: es => actions_unionFree_append (encodeBuild_unionFree e) (encodeBuildArgs_unionFree es)

end

/-- This includes compilation of a source union. -/
theorem encodeAction_unionFree (a : Action) : Actions.UnionFree (encodeAction a) := by
  cases a with
  | expr e => exact encodeBuild_unionFree e
  | union a b =>
    exact actions_unionFree_append
      (actions_unionFree_append (encodeBuild_unionFree a) (encodeBuild_unionFree b))
      ⟨trivial, trivial, trivial⟩
  | subsume _ => trivial

theorem encodeActions_unionFree (as : List Action) : Actions.UnionFree (encodeActions as) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact actions_unionFree_append (encodeAction_unionFree a) ih

theorem encodeRule_unionFree (r : Rule) : (encodeRule r).UnionFree :=
  encodeActions_unionFree r.actions

/-- Every maintenance rule writes union-find rows; none unions. -/
private theorem rebuildRules_unionFree (f : FnName) (k : Nat) :
    ∀ ro ∈ rebuildRules f k, ro.1.UnionFree := by
  intro ro hro
  unfold rebuildRules at hro
  split at hro
  · simp at hro
  · rw [List.mem_singleton] at hro
    subst hro
    exact ⟨trivial, trivial⟩

private theorem maintenance_unionFree (P : Program) :
    ∀ ro ∈ maintenanceRules P, ro.1.UnionFree := by
  intro ro hro
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hro
  rcases hro with rfl | rfl | ⟨⟨f, k⟩, _, hro⟩
  · exact ⟨trivial, trivial, trivial⟩
  · exact ⟨trivial, trivial, trivial⟩
  · exact rebuildRules_unionFree f k ro hro

private theorem encodeRules_unionFree (i : Nat) (rs : List Rule) :
    ∀ ro ∈ encodeRules i rs, ro.1.UnionFree := by
  intro ro hro
  obtain ⟨ri, _, rfl⟩ := List.mem_map.mp hro
  exact encodeRule_unionFree ri.1

private theorem rebuild_unionFree (P : Program) : ∀ r ∈ (rebuild P).1.rules, r.UnionFree := by
  intro r hr
  simp only [rebuild, Schedule.rules] at hr
  obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
  exact maintenance_unionFree P ro hro

private theorem schedule_unionFree (P : Program) :
    ∀ (S : Schedule) (i : Nat), ∀ r ∈ (encodeSchedule P S i).1.rules, r.UnionFree
  | .run rs, i => by
      intro r hr
      simp only [encodeSchedule, Schedule.rules, List.mem_append] at hr
      rcases hr with hr | hr
      · obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
        exact encodeRules_unionFree i rs ro hro
      · exact rebuild_unionFree P r hr
  | .saturate S, i => by
      intro r hr
      simp only [encodeSchedule, Schedule.rules] at hr
      exact schedule_unionFree P S i r hr
  | .seq S₁ S₂, i => by
      intro r hr
      simp only [encodeSchedule, Schedule.rules, List.mem_append] at hr
      rcases hr with hr | hr
      · exact schedule_unionFree P S₁ i r hr
      · exact schedule_unionFree P S₂ _ r hr

/-- No source union survives in a compiled rule. -/
theorem encode_unionFree (P : Program) : Program.UnionFree (encode P) :=
  fun r hr => schedule_unionFree P P.schedule 0 r hr

end Egglog.Congruence
