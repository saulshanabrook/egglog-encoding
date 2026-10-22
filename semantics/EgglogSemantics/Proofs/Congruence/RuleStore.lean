import EgglogSemantics.Proofs.Congruence.Tables
import EgglogSemantics.Proofs.Source.Execution

/-! Exact rule-store correspondence and rebuilding copies within source saturation rulesets. -/

namespace Egglog.Congruence

/-- Rule-store correspondence at an aligned source and target state. -/
def RulesEncoded (P : Program) (src : Database) (d : FDatabase) : Prop :=
  ∀ r, r ∈ d.rules ↔ (∃ c ∈ allMaintenanceRules P, c.command = .rule r) ∨
    ∃ s ∈ src.rules, r = encodeRule s

/-- Actual execution of the prelude and compiled prefix establishes rule-store correspondence. -/
theorem rulesEncoded_of_prefix {P pre : Program} {src : Database} {d e : FDatabase}
    (hsrc : ProgramStep Database.empty pre src)
    (hpre : FDatabase.empty.execProgramM ((encodePrelude P).map Command.command) = some d)
    {i : Nat} (run : d.execProgramM ((encodeCmds pre i).map Command.command) = some e) :
    RulesEncoded P src e := by
  intro r
  rw [Egglog.FDatabase.execProgramM_mem_rules_iff run,
    Egglog.FDatabase.execProgramM_mem_rules_iff hpre, rule_mem_prelude, rule_mem_encodeCmds]
  have hmem : ∀ s, s ∈ src.rules ↔ Cmd.rule s ∈ pre := by
    intro s
    simpa [Database.empty] using hsrc.mem_rules_iff s
  simp only [FDatabase.empty, List.not_mem_nil, false_or, hmem]

/-- Every rule selected by a dedicated rebuilding phase comes from maintenance. -/
theorem RulesEncoded.rebuild_only {P pre : Program} {src : Database} {d : FDatabase}
    (h : RulesEncoded P src d) (hdom : P.Fragment)
    (hpre : ProgramStep Database.empty pre src) (hsub : ∀ c ∈ pre, c ∈ P) :
    ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
  intro r hr hR
  rcases (h r).mp hr with hm | ⟨s, hs, rfl⟩
  · exact hm
  · have hmem : Cmd.rule s ∈ pre := by simpa [Database.empty] using (hpre.mem_rules_iff s).mp hs
    exact (ruleset_ne_rebuild hdom (hsub _ hmem) hR).elim

/-- Being closed under a saturation ruleset also closes the dedicated rebuilding rules,
because the prelude registered copies with the same queries and heads. -/
theorem RulesEncoded.rebuild_closed {P pre : Program} {src : Database} {d : FDatabase}
    (h : RulesEncoded P src d) (hdom : P.Fragment)
    (hpre : ProgramStep Database.empty pre src) (hsub : ∀ c ∈ pre, c ∈ P)
    {R : RulesetName} (hR : R ∈ P.saturateRulesets) (hclosed : d.RoundClosed R) :
    d.RoundClosed rebuildRuleset := by
  intro t ht
  rcases mem_terms_execRunRules.mp ht with ht |
      ⟨r, hr, hrr, σ, hσ, e, hf, ht⟩
  · exact ht
  · obtain ⟨c, hc, hcr⟩ := h.rebuild_only hdom hpre hsub r hr hrr
    obtain ⟨c', hc', hcr'⟩ := maintenance_copy hc hcr hR
    have hmem : { r with ruleset := R } ∈ d.rules := (h _).mpr (Or.inl ⟨c', hc', hcr'⟩)
    exact hclosed.fired hmem rfl hσ hf ht

end Egglog.Congruence
