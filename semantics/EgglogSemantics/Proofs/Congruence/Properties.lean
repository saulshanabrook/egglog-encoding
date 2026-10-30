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
  | .app _ es => actions_unionFree_append (encodeBuildArgs_unionFree es) ⟨trivial, trivial, trivial⟩

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
  | delete _ => trivial

theorem encodeActions_unionFree (as : List Action) : Actions.UnionFree (encodeActions as) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact actions_unionFree_append (encodeAction_unionFree a) ih

theorem encodeRule_unionFree (r : Rule) : (encodeRule r).UnionFree :=
  encodeActions_unionFree r.actions

/-- Every maintenance rule deletes a row and writes a row; none unions. -/
private theorem rebuildRules_unionFree (f : FnName) (k : Nat) :
    ∀ ro ∈ rebuildRules f k, ro.1.UnionFree := by
  intro ro hro
  unfold rebuildRules at hro
  rcases List.mem_cons.mp hro with rfl | hro
  · exact ⟨trivial, trivial, trivial⟩
  rcases List.mem_append.mp hro with hro | hro
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hro
    exact ⟨trivial, trivial, trivial⟩
  · rw [List.mem_singleton] at hro
    subst hro
    exact ⟨trivial, trivial, trivial⟩

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

private theorem cmd_unionFree (P : Program) (i : Nat) (c : Cmd) :
    ∀ co ∈ encodeCmd P i c, co.1.UnionFree := by
  intro co hco r hr
  cases c with
  | run rs =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hco
      rcases hco with rfl | rfl
      · simp only [Cmd.rules] at hr
        obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
        exact encodeRules_unionFree i rs ro hro
      · simp only [Cmd.rules] at hr
        obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
        exact maintenance_unionFree P ro hro
  | saturate rs =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hco
      rcases hco with rfl | rfl
      · simp only [Cmd.rules] at hr
        obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
        rcases List.mem_append.mp hro with hro | hro
        · exact encodeRules_unionFree i rs ro hro
        · exact maintenance_unionFree P ro hro
      · simp only [Cmd.rules] at hr
        obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
        exact maintenance_unionFree P ro hro

private theorem cmds_unionFree (P : Program) (cs : List Cmd) (i : Nat) :
    ∀ co ∈ encodeCmds P cs i, co.1.UnionFree := by
  induction cs generalizing i with
  | nil => simp [encodeCmds]
  | cons c cs ih =>
      intro co hco
      rcases List.mem_append.mp hco with hco | hco
      · exact cmd_unionFree P i c co hco
      · exact ih _ co hco

/-- No source union survives in a compiled rule. -/
theorem encode_unionFree (P : Program) : Program.UnionFree (encode P) := by
  intro c hc
  simp only [encode, compile] at hc
  obtain ⟨co, hco, rfl⟩ := List.mem_map.mp hc
  exact cmds_unionFree P P.commands 0 co hco

end Egglog.Congruence
