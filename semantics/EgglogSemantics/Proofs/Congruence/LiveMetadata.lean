import EgglogSemantics.Proofs.Congruence.AbstractRuntime
import EgglogSemantics.Proofs.Congruence.AbstractForward
import EgglogSemantics.Proofs.Congruence.AbstractState
import EgglogSemantics.Proofs.Congruence.ActionExprs
import EgglogSemantics.Proofs.Source.Execution

/-! Generated declarations and maintenance copies discharge live rebuilding metadata. -/

namespace Egglog.Congruence.Live

open Abstract

/-- Every retained view row has exactly its declared key width. -/
theorem viewDeclared_of_signature {P : Program} (hp : P.Fragment) {d : Database}
    (hd : d.Diag) (hsig : d.sig = encodeSig P) : ViewDeclared d := by
  intro f cs e ho
  obtain ⟨decl, hdecl, _, hk, _⟩ := (ho.entry hd).1
  obtain ⟨k, _, rfl⟩ := encodeSig_view_census hp (hsig ▸ hdecl)
  have hwidth : cs.length = k := hk
  exact hwidth ▸ hdecl

theorem viewTables_of_signature {P : Program} (hp : P.Fragment) {d : Database}
    (hsig : d.sig = encodeSig P) : ViewTables d :=
  fun _ _ hd => encodeSig_view_shape hp (hsig ▸ hd)

theorem view_census_of_out {P : Program} (hp : P.Fragment) {d : Database}
    (hd : d.Diag) (hsig : d.sig = encodeSig P) {f : FnName} {cs : List Term} {i : Term}
    (ho : d.Out (viewName f) cs [i]) : (f, cs.length) ∈ P.ctors := by
  have hdecl := viewDeclared_of_signature hp hd hsig f cs i ho
  obtain ⟨k, hk, he⟩ := encodeSig_view_census hp (hsig ▸ hdecl)
  have hw : cs.length = k := congrArg FnDecl.arity he
  exact hw ▸ hk

/-- Dedicated maintenance and its source-saturation copies have identical queries and heads. -/
theorem RulesEncoded.maintenance_retag {P : Program} {src d : Database}
    (h : RulesEncoded P src d) {R : RulesetName}
    (hR : R = rebuildRuleset ∨ R ∈ P.saturateRulesets)
    {c : Command} (hc : c ∈ allMaintenanceRules P) {r : Rule}
    (hr : c.command = .rule r) (hbase : r.ruleset = rebuildRuleset) :
    { r with ruleset := R } ∈ d.rules := by
  rcases hR with rfl | hR
  · have he : { r with ruleset := rebuildRuleset } = r := by cases r; simp_all
    rw [he]
    exact h.maintenance hc hr
  · obtain ⟨copy, hcopy, he⟩ := maintenance_copy hc hr hR
    exact h.maintenance hcopy he

theorem RulesEncoded.path {P : Program} {src d : Database} (h : RulesEncoded P src d)
    {R : RulesetName} (hR : R = rebuildRuleset ∨ R ∈ P.saturateRulesets) :
    { pathCompressRule with ruleset := R } ∈ d.rules :=
  h.maintenance_retag hR (List.mem_append_left _ List.mem_cons_self) rfl rfl

theorem RulesEncoded.rebuild_only {P pre : Program} {src d : Database}
    (h : RulesEncoded P src d) (hp : P.Fragment)
    (hpre : ProgramStep Database.empty pre src) (hsub : ∀ c ∈ pre, c ∈ P) :
    ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
  intro r hr hR
  rcases (h r).mp hr with hm | ⟨s, hs, rfl⟩
  · exact hm
  · have hmem : Cmd.rule s ∈ P := hsub _ (by
      simpa [Database.empty] using (hpre.mem_rules_iff s).mp hs)
    exact (ruleset_ne_rebuild hp hmem hR).elim

theorem RulesEncoded.tablesPresent {P : Program} {src d : Database}
    (h : RulesEncoded P src d) (hp : P.Fragment) (hd : d.Diag)
    (hsig : d.sig = encodeSig P) {R : RulesetName}
    (hR : R = rebuildRuleset ∨ R ∈ P.saturateRulesets) : TablesPresent d R := by
  intro f cs i ho
  have hc := view_census_of_out hp hd hsig ho
  exact ⟨viewDeclared_of_signature hp hd hsig f cs i ho,
    h.maintenance_retag hR (eclassRule_mem_maintenance hc) rfl rfl,
    fun j hj => h.maintenance_retag hR (childRule_mem_maintenance hc hj) rfl rfl⟩

theorem rebuilt_of_metadata {P : Program} {src d : Database}
    (h : Runtime d) (hp : P.Fragment) (hsig : d.sig = encodeSig P)
    (hrules : RulesEncoded P src d) {R : RulesetName}
    (hR : R = rebuildRuleset ∨ R ∈ P.saturateRulesets)
    (hfin : d.terms.Finite) (hsat : RunSaturated R d) (hdesc : Descending d) : Rebuilt d :=
  rebuilt_of_saturated h.state h.generated h.noUnions h.storeOk h.rulesSafe h.wf hfin hsat
    (hrules.tablesPresent hp h.noUnions.diag hsig hR) (hrules.path hR)
    (fun _ _ ho => hdesc.out h.noUnions.diag ho)

/-- Query variables and constructors of registered source heads obey the original fragment. -/
theorem rule_query_noAt {P : Program} (hp : P.Fragment) {r : Rule}
    (hr : Cmd.rule r ∈ P) : ∀ v ∈ r.query.vars, ¬ "@".isPrefixOf v = true := by
  intro v hv
  apply hp.noAt v
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  exact ⟨Cmd.rule r, hr, List.mem_union_iff.mpr (Or.inl hv)⟩

theorem rule_head_declared {P : Program} (hp : P.Fragment) {d : Database}
    (hsig : d.sig = encodeSig P) {r : Rule} (hr : Cmd.rule r ∈ P) :
    ∀ a ∈ r.actions, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2) := by
  intro a ha e he fk hk
  have hfk : fk ∈ P.ctors := mem_program_ctors hr
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, actionExprs_ctors he hk⟩))
  exact hsig ▸ (encodeSig_tables hp hfk).2

end Egglog.Congruence.Live
