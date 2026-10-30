import EgglogSemantics.Proofs.Congruence.MetadataSyntax
import EgglogSemantics.Proofs.Congruence.AbstractMaintenance
import EgglogSemantics.Proofs.RuleStore
import EgglogSemantics.Proofs.DiagonalPreservation
import EgglogSemantics.Proofs.StatePreservation
import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Proofs.Source.Ctors

/-! Exact metadata of mathematical compiled prefixes, including the empty prelude. -/

namespace Egglog.Congruence.Abstract

/-- Prelude declarations followed by a compiled prefix keep the hoisted signature. -/
theorem programStep_sig_of_noDecl {p : Program} (hp : ∀ c ∈ p, NoDecl c)
    {d e : Database} (h : ProgramStep d p e) : e.sig = d.sig := by
  induction h with
  | nil => rfl
  | cons hc _ ih =>
      rw [ih (fun c hm => hp c (List.mem_cons_of_mem _ hm)), hc.sig]
      have hn := hp _ List.mem_cons_self
      cases ‹Cmd› <;> first | rfl | contradiction

/-- Rule-store correspondence uses mathematical executions on both sides. -/
def RulesEncoded (P : Program) (src d : Database) : Prop :=
  ∀ r, r ∈ d.rules ↔ (∃ c ∈ allMaintenanceRules P, c.command = .rule r) ∨
    ∃ s ∈ src.rules, r = encodeRule s

theorem rulesEncoded_of_prefix {P pre : Program} {src d : Database} {i : Nat}
    (hs : ProgramStep Database.empty pre src)
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) :
    RulesEncoded P src d := by
  intro r
  rw [ht.mem_rules_iff]
  simp only [Database.empty, Set.mem_empty_iff_false, false_or, List.map_append,
    List.mem_append, rule_mem_prelude, rule_mem_encodeCmds]
  have hm : ∀ s, s ∈ src.rules ↔ Cmd.rule s ∈ pre := by
    intro s
    simpa [Database.empty] using hs.mem_rules_iff s
  simp only [hm]

/-- A prefix is compiled against the whole program's declarations and maintenance rules. -/
structure Metadata (P : Program) (src d : Database) : Prop where
  sig : d.sig = encodeSig P
  rules : RulesEncoded P src d
  env : d.env = []

private theorem foldl_noDecl {p : Program} (hp : ∀ c ∈ p, NoDecl c) (s : Signature) :
    p.foldl (fun sig c => c.sigBind sig) s = s := by
  induction p generalizing s with
  | nil => rfl
  | cons c cs ih =>
      rw [List.foldl_cons, ih (fun c hm => hp c (List.mem_cons_of_mem _ hm))]
      have hn := hp c List.mem_cons_self
      cases c <;> first | rfl | contradiction

/-- The whole prelude fixes every compiled prefix's signature independently of source data. -/
theorem prefix_sig {P pre : Program} {d : Database} {i : Nat}
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) :
    d.sig = encodeSig P := by
  rw [ht.sig, List.map_append, List.foldl_append, foldl_noDecl (cmds_noDecl pre i)]
  rfl

theorem metadata_of_prefix {P pre : Program} {src d : Database} {i : Nat}
    (hs : ProgramStep Database.empty pre src)
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) :
    Metadata P src d := by
  refine ⟨?_, rulesEncoded_of_prefix hs ht, ht.env⟩
  rw [ht.sig, List.map_append, List.foldl_append, foldl_noDecl (cmds_noDecl pre i)]
  rfl

theorem RulesEncoded.maintenance {P : Program} {src d : Database}
    (h : RulesEncoded P src d) {c : Command} (hc : c ∈ allMaintenanceRules P)
    {r : Rule} (hr : c.command = .rule r) : r ∈ d.rules :=
  (h r).mpr (Or.inl ⟨c, hc, hr⟩)

theorem Metadata.uf {P : Program} {src d : Database} (h : Metadata P src d)
    (hp : P.Fragment) : d.sig ufName = some (tableDecl 1) :=
  h.sig ▸ encodeSig_ufName hp

theorem Metadata.path {P : Program} {src d : Database} (h : Metadata P src d) :
    pathCompressRule ∈ d.rules :=
  h.rules.maintenance (List.mem_append_left _ List.mem_cons_self) rfl

theorem Metadata.tablesPresent {P : Program} {src d : Database} (h : Metadata P src d)
    (hp : P.Fragment) (hs : ViewsSound d src) (hc : src.CtorsIn P) : TablesPresent d := by
  intro f cs e ho
  obtain ⟨as, ha, hcs, _⟩ := hs f cs e ho
  have hk : (f, cs.length) ∈ P.ctors := hcs.length_eq ▸ hc f as ha
  exact ⟨h.sig ▸ (encodeSig_tables hp hk).2,
    h.rules.maintenance (eclassRule_mem_maintenance hk) rfl,
    fun i hi => h.rules.maintenance (childRule_mem_maintenance hk hi) rfl⟩

theorem RulesEncoded.rebuild_only {P pre : Program} {src d : Database}
    (h : RulesEncoded P src d) (hp : P.Fragment)
    (hs : ProgramStep Database.empty pre src) (hsub : ∀ c ∈ pre, c ∈ P) :
    ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
  intro r hr hR
  rcases (h r).mp hr with hm | ⟨s, hs', rfl⟩
  · exact hm
  · have hm : Cmd.rule s ∈ pre := by
      simpa [Database.empty] using (hs.mem_rules_iff s).mp hs'
    exact (ruleset_ne_rebuild hp (hsub _ hm) hR).elim

/-- Copies of maintenance in source saturation rulesets establish dedicated closure. -/
theorem RulesEncoded.rebuild_closed {P pre : Program} {src d : Database}
    (h : RulesEncoded P src d) (hp : P.Fragment)
    (hs : ProgramStep Database.empty pre src) (hsub : ∀ c ∈ pre, c ∈ P)
    {R : RulesetName} (hR : R ∈ P.saturateRulesets) (hfix : RunRules R d = d) :
    RunRules rebuildRuleset d = d := by
  apply (runRules_eq_self_iff rebuildRuleset d).mpr
  intro r hr hrr e he
  obtain ⟨c, hc, hcr⟩ := h.rebuild_only hp hs hsub r hr hrr
  obtain ⟨c', hc', hcr'⟩ := maintenance_copy hc hcr hR
  exact (runRules_eq_self_iff R d).mp hfix { r with ruleset := R }
    (h.maintenance hc' hcr') rfl e he

/-- The prelude writes no equations, despite the merge phase after each command. -/
theorem prelude_empty {P : Program} {d : Database}
    (h : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) :
    d.eqs = ∅ ∧ d.terms = ∅ ∧ d.env = [] := by
  have he := h.eqs_empty_of_declOrRule (prelude_setup P) rfl
  exact ⟨he, Database.terms_empty_of_eqs_empty he, h.env⟩


/-- These safety invariants follow from the target execution alone. -/
theorem prefix_noUnions {P pre : Program} {i : Nat} {d : Database}
    (h : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d) : d.NoUnions :=
  h.noUnions Database.NoUnions.empty (encodePrefix_unionFree P pre i)

theorem Metadata.mergeShape {P : Program} {src d : Database} (h : Metadata P src d) :
    MergeShape d.sig := h.sig ▸ encodeSig_mergeShape P

/-- The initial prelude is already a fixed point for every ruleset. All registered rules
need an existing row, and a merge also needs an existing row. -/
theorem prelude_saturated {P : Program} {d : Database}
    (h : ProgramStep Database.empty ((encodePrelude P).map Command.command) d)
    (R : RulesetName) : RunSaturated R d := by
  obtain ⟨he, ht, _⟩ := prelude_empty h
  refine ⟨(runRules_eq_self_iff R d).mpr ?_, ?_⟩
  · intro r hr _ e herr
    have hmem : Cmd.rule r ∈ (encodePrelude P).map Command.command := by
      simpa [Database.empty] using (h.mem_rules_iff r).mp hr
    obtain ⟨c, hc, hcr⟩ := (rule_mem_prelude P r).mp hmem
    have hn := maintenance_query_ne_nil hc hcr
    obtain ⟨σ, ⟨σs, hq, _⟩, _⟩ := herr
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil r.query hn
    obtain ⟨ρ, _, hm⟩ := hq.flip.exists_left hp
    have hw : ∃ w, w ∈ d.terms := by
      cases hm.2 with
      | expr hw _ _ => exact ⟨_, hw⟩
      | eq hw _ _ _ _ => exact ⟨_, hw⟩
    simp [ht] at hw
  · intro e hs
    exact (hs.not_of_empty_eqs he).elim

/-- The mathematical prelude establishes the rebuilding invariant without executing any
rule body or creating any data. -/
theorem prelude_rebuilt {P : Program} {d : Database}
    (h : ProgramStep Database.empty ((encodePrelude P).map Command.command) d) :
    Rebuilt d := by
  obtain ⟨_, ht, _⟩ := prelude_empty h
  have hout : ∀ f as vs, ¬ d.Out f as vs := by
    rintro f as vs ⟨bs, _, hb⟩
    simp [ht] at hb
  refine ⟨h.wf Database.WF.empty, ?_, ?_, ?_⟩
  · rw [ht]; exact Set.finite_empty
  · exact ⟨fun _ _ _ ha _ => (hout _ _ _ ha).elim,
      fun _ _ _ ha _ => (hout _ _ _ ha).elim,
      fun _ _ _ _ ha _ => (hout _ _ _ ha).elim,
      fun _ _ _ _ ha _ => (hout _ _ _ ha).elim,
      fun _ _ _ _ ha _ => (hout _ _ _ ha).elim⟩
  · intro a b hab
    exact (hout _ _ _ hab).elim


/-- Every view reached by a sound execution has the generated declaration. -/
theorem Metadata.viewDeclared {P : Program} {src d : Database} (h : Metadata P src d)
    (hp : P.Fragment) (hs : ViewsSound d src) (hc : src.CtorsIn P) : ViewDeclared d := by
  intro f cs e ho
  simp [(h.tablesPresent hp hs hc f cs e ho).1]

/-- At an actual compiled-prefix fixed point, metadata, diagonality, well-formedness and
finiteness are consequences of execution. Only data soundness and descending edges remain
as dynamic simulation obligations. -/
theorem prefix_rebuilt_of_saturated {P pre : Program} {src d : Database} {i : Nat}
    (hp : P.Fragment) (hsub : ∀ c ∈ pre, c ∈ P)
    (hs : ProgramStep Database.empty pre src)
    (ht : ProgramStep Database.empty
      ((encodePrelude P ++ encodeCmds pre i).map Command.command) d)
    (hviews : ViewsSound d src) (hsat : RunSaturated rebuildRuleset d)
    (hdesc : ∀ a b, d.Out ufName [a] [b] → b = a ∨ Term.blt b a = true) :
    Rebuilt d := by
  have hm := metadata_of_prefix hs ht
  exact rebuilt_of_saturated (prefix_noUnions ht).diag (ht.wf Database.WF.empty)
    (Database.finite_terms ht.finite_from_empty.1) hsat
    (hm.tablesPresent hp hviews (ctorsIn_of_prefixStep hp hsub hs))
    (hm.uf hp) hm.path hdesc

end Egglog.Congruence.Abstract
