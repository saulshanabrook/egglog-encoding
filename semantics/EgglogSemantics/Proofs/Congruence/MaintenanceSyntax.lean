import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.Bindings

/-! Shapes of maintenance heads, independent of either interpreter. -/

namespace Egglog.Congruence

/-- Maintenance either compresses UF paths or writes another table over held variables. -/
def MaintenanceHead (r : Rule) : Prop :=
  ∃ f cols, r.actions = [.expr (.app f cols)] ∧
    (∀ c ∈ cols, ∃ v, c = Expr.var v) ∧
    (f ≠ ufName ∨ r.query = pathCompressRule.query ∧ r.actions = pathCompressRule.actions)

private theorem rebuildVars_areVars (k : Nat) :
    ∀ c ∈ rebuildVars k, ∃ v, c = Expr.var v := by
  intro c hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  exact ⟨_, rfl⟩

private theorem eclass_headShape (f : FnName) (k : Nat) : MaintenanceHead (eclassRule f k) := by
  refine ⟨viewName f, _, rfl, ?_, Or.inl viewName_ne_ufName⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact rebuildVars_areVars k c hc
  · obtain rfl := List.mem_singleton.mp hc; exact ⟨_, rfl⟩

private theorem child_headShape (f : FnName) (k i : Nat) :
    MaintenanceHead (childRule f k i) := by
  refine ⟨viewName f, _, rfl, ?_, Or.inl viewName_ne_ufName⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases mem_or_eq_of_mem_set hc with hc | rfl
    · exact rebuildVars_areVars k c hc
    · exact ⟨_, rfl⟩
  · obtain rfl := List.mem_singleton.mp hc; exact ⟨_, rfl⟩

private theorem maintenanceRules_headShape (P : Program) :
    ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r → MaintenanceHead r := by
  intro c hc r hr
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · obtain rfl : pathCompressRule = r := Cmd.rule.inj hr
    refine ⟨ufName, _, rfl, ?_, Or.inr ⟨rfl, rfl⟩⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact ⟨_, rfl⟩
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩
    · obtain rfl : eclassRule f k = r := Cmd.rule.inj hr
      exact eclass_headShape f k
    · obtain rfl : childRule f k i = r := Cmd.rule.inj hr
      exact child_headShape f k i

theorem maintenance_headShape {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) : MaintenanceHead r := by
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenanceRules_headShape P c hc r hr
  · unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl : { s with ruleset := R } = r := Cmd.rule.inj hr
      exact maintenanceRules_headShape P c hc s hs
    next => exact maintenanceRules_headShape P c hc r hr


end Egglog.Congruence
