import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Spec.Step

/-! Structural properties of the congruence compiler, independent of provenance, under every
choice of options. -/

namespace Egglog.Congruence

private theorem actions_unionFree_append {as bs : List Action}
    (ha : Actions.UnionFree as) (hb : Actions.UnionFree bs) :
    Actions.UnionFree (as ++ bs) := by
  induction as with
  | nil => exact hb
  | cons a as ih => exact ⟨ha.1, ih ha.2⟩

mutual

/-- Compiled constructions write rows and never assert a built-in union. -/
theorem encodeBuildWith_unionFree (o : Options) :
    ∀ e : Expr, Actions.UnionFree (encodeBuildWith o e)
  | .lit _ | .var _ => ⟨trivial, trivial⟩
  | .min a b =>
      actions_unionFree_append (encodeBuildWith_unionFree o a) (encodeBuildWith_unionFree o b)
  | .app _ es =>
      actions_unionFree_append
        (actions_unionFree_append (encodeBuildArgsWith_unionFree o es)
          (by split <;> first | exact ⟨trivial, trivial⟩ | trivial))
        ⟨trivial, trivial⟩

theorem encodeBuildArgsWith_unionFree (o : Options) :
    ∀ es : List Expr, Actions.UnionFree (encodeBuildArgsWith o es)
  | [] => trivial
  | e :: es =>
      actions_unionFree_append (encodeBuildWith_unionFree o e) (encodeBuildArgsWith_unionFree o es)

end

theorem encodeBuild_unionFree (e : Expr) : Actions.UnionFree (encodeBuild e) :=
  encodeBuildWith_unionFree {} e

/-- This includes compilation of a source union. -/
theorem encodeActionWith_unionFree (o : Options) (a : Action) :
    Actions.UnionFree (encodeActionWith o a) := by
  cases a with
  | expr e => exact encodeBuildWith_unionFree o e
  | union a b =>
    exact actions_unionFree_append
      (actions_unionFree_append (encodeBuildWith_unionFree o a) (encodeBuildWith_unionFree o b))
      ⟨trivial, trivial, trivial⟩
  | subsume _ => trivial

theorem encodeActionsWith_unionFree (o : Options) (as : List Action) :
    Actions.UnionFree (encodeActionsWith o as) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact actions_unionFree_append (encodeActionWith_unionFree o a) ih

theorem encodeRuleWith_unionFree (o : Options) (r : Rule) : (encodeRuleWith o r).UnionFree :=
  encodeActionsWith_unionFree o r.actions

/-- Every maintenance rule writes or subsumes rows; none unions. -/
private theorem rebuildRules_unionFree (f : FnName) (k : Nat) :
    ∀ ro ∈ rebuildRules f k, ro.1.UnionFree := by
  intro ro hro
  unfold rebuildRules at hro
  split at hro
  · simp at hro
  · rw [List.mem_singleton] at hro
    subst hro
    exact ⟨trivial, trivial⟩

private theorem exprs_unionFree (f : Expr → Action) (hf : ∀ e, (f e).UnionFree) :
    ∀ es : List Expr, Actions.UnionFree (es.map f)
  | [] => trivial
  | e :: es => ⟨hf e, exprs_unionFree f hf es⟩

private theorem rekeyRules_unionFree (o : Options) (f : FnName) (k : Nat) :
    ∀ ro ∈ rekeyRules o f k, ro.1.UnionFree := by
  intro ro hro
  unfold rekeyRules at hro
  split at hro
  · simp at hro
  · rcases List.mem_cons.mp hro with rfl | hro
    · exact ⟨trivial, trivial⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hro
      exact ⟨trivial, trivial⟩
  · rcases List.mem_cons.mp hro with rfl | hro
    · exact exprs_unionFree
        (fun c => Action.expr (.app hasChildName [viewRow f (rebuildVars k) (.var "@e"), c]))
        (fun _ => trivial) _
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hro
      exact ⟨trivial, trivial, trivial⟩

private theorem mergeRules_unionFree (o : Options) (f : FnName) (k : Nat) :
    ∀ ro ∈ mergeRules o f k, ro.1.UnionFree := by
  intro ro hro
  unfold mergeRules at hro
  split at hro
  · exact rebuildRules_unionFree f k ro hro
  · rw [List.mem_singleton] at hro
    subst hro
    exact ⟨trivial, trivial, trivial⟩

private theorem maintenanceGroups_unionFree (o : Options) (P : Program) :
    ∀ ro ∈ (maintenanceGroups o P).flatten, ro.1.UnionFree := by
  intro ro hro
  obtain ⟨g, hg, hro⟩ := List.mem_flatten.mp hro
  have hg' := List.mem_of_mem_filter hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl
  · rcases List.mem_cons.mp hro with rfl | hro
    · exact ⟨trivial, trivial, trivial⟩
    · rw [List.mem_singleton] at hro
      subst hro
      exact ⟨trivial, trivial, trivial⟩
  · obtain ⟨fk, _, hro⟩ := List.mem_flatMap.mp hro
    exact rekeyRules_unionFree o fk.1 fk.2 ro hro
  · obtain ⟨fk, _, hro⟩ := List.mem_flatMap.mp hro
    exact mergeRules_unionFree o fk.1 fk.2 ro hro

private theorem seqAll_unionFree :
    ∀ ss : List Schedule, (∀ S ∈ ss, S.UnionFree) → (Schedule.seqAll ss).UnionFree
  | [], _ => by simp [Schedule.seqAll, Schedule.rules]
  | [S], h => h S (by simp)
  | S :: S' :: ss, h => by
      intro r hr
      simp only [Schedule.seqAll, Schedule.rules, List.mem_append] at hr
      rcases hr with hr | hr
      · exact h S (by simp) r hr
      · exact seqAll_unionFree (S' :: ss) (fun T hT => h T (by simp [hT])) r hr

private theorem rebuildWith_unionFree (o : Options) (P : Program) :
    (rebuildWith o P).1.UnionFree := by
  have groups := maintenanceGroups_unionFree o P
  have runOf : ∀ g ∈ maintenanceGroups o P, (Schedule.run (g.map Prod.fst)).UnionFree := by
    intro g hg r hr
    obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
    exact groups ro (List.mem_flatten.mpr ⟨g, hg, hro⟩)
  simp only [rebuildWith]
  split
  · split
    · rename_i last hlast
      apply seqAll_unionFree
      intro S hS
      rcases List.mem_append.mp hS with hS | hS
      · obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hS
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ((List.dropLast_sublist _).subset hT)
        exact runOf g hg
      · rw [List.mem_singleton] at hS
        obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp hlast
        have hmem : last ∈ (maintenanceGroups o P).map
            (fun g => Schedule.run (g.map Prod.fst)) := by
          rw [hl']; simp
        obtain ⟨g, hg, hgl⟩ := List.mem_map.mp hmem
        rw [hS, ← hgl]
        exact runOf g hg
    · intro r hr
      simp [Schedule.rules] at hr
  · intro r hr
    obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
    exact groups ro hro

private theorem scheduleWith_unionFree (o : Options) (P : Program) :
    ∀ (S : Schedule) (i : Nat), (encodeScheduleWith o P S i).1.UnionFree
  | .run rs, i => by
      intro r hr
      simp only [encodeScheduleWith, Schedule.rules, List.mem_append] at hr
      rcases hr with hr | hr
      · obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
        obtain ⟨ri, _, rfl⟩ := List.mem_map.mp hro
        exact encodeRuleWith_unionFree o ri.1
      · exact rebuildWith_unionFree o P r hr
  | .saturate S, i => by
      intro r hr
      simp only [encodeScheduleWith, Schedule.rules] at hr
      exact scheduleWith_unionFree o P S i r hr
  | .seq S₁ S₂, i => by
      intro r hr
      simp only [encodeScheduleWith, Schedule.rules, List.mem_append] at hr
      rcases hr with hr | hr
      · exact scheduleWith_unionFree o P S₁ i r hr
      · exact scheduleWith_unionFree o P S₂ _ r hr

/-- No source union survives in a compiled rule, under any options. -/
theorem encodeWith_unionFree (o : Options) (P : Program) : Program.UnionFree (encodeWith o P) :=
  fun r hr => scheduleWith_unionFree o P P.schedule 0 r hr

/-- No source union survives in a compiled rule. -/
theorem encode_unionFree (P : Program) : Program.UnionFree (encode P) :=
  encodeWith_unionFree {} P

end Egglog.Congruence
