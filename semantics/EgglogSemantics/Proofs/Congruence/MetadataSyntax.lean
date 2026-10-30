import EgglogSemantics.Proofs.Congruence.Properties
import EgglogSemantics.Proofs.Source.Arity
import Mathlib.Data.List.Dedup
import EgglogSemantics.Proofs.SignatureLookup
import EgglogSemantics.Proofs.Setup

/-! Generated declarations and rule census, independent of executable databases. -/

namespace Egglog.Congruence

/-- Only UF and constructor views use the generated singleton-output merge. -/
def DeclShape (f : FnName) (dc : FnDecl) : Prop :=
  ∀ {oldVars newVars : List Var} body res, dc.merge = some (.merge oldVars newVars body res) →
    (f = ufName ∨ ∃ g, f = viewName g) ∧ body = mergeBody ∧ res = mergeResult ∧
      dc.outArity = 1 ∧ (f = ufName → dc.arity = 1) ∧
      oldVars = ["old"] ∧ newVars = ["new"]

def MergeShape (sig : Signature) : Prop :=
  ∀ f dc, sig f = some dc → DeclShape f dc

def CommandShape : Cmd → Prop
  | .decl f dc => DeclShape f dc
  | _ => True

theorem MergeShape.empty : MergeShape (fun _ => none) := by
  intro f dc h
  contradiction

theorem MergeShape.update {sig : Signature} (h : MergeShape sig) {f : FnName}
    {dc : FnDecl} (hc : DeclShape f dc) :
    MergeShape (Function.update sig f (some dc)) := by
  intro g dcg hg
  rw [Function.update_apply] at hg
  by_cases hgf : g = f
  · subst g
    obtain rfl : dcg = dc := by simpa [eq_comm] using hg
    exact hc
  · rw [if_neg hgf] at hg
    exact h g dcg hg

private theorem maintenance_shape (P : Program) :
    ∀ c ∈ maintenanceRules P, CommandShape c.command := by
  intro c hc
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · trivial
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩ <;> trivial

private theorem allMaintenance_shape (P : Program) :
    ∀ c ∈ allMaintenanceRules P, CommandShape c.command := by
  intro c hc
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenance_shape P c hc
  · have h := maintenance_shape P c hc
    unfold inRuleset
    split <;> simp_all only [CommandShape]

private theorem prelude_shape (P : Program) :
    ∀ c ∈ encodePrelude P, CommandShape c.command := by
  intro c hc
  simp only [encodePrelude, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | ⟨⟨f, k⟩, _, hc⟩) | hc
  · intro oldVars newVars body res he
    obtain ⟨rfl, rfl, rfl, rfl⟩ :
        ["old"] = oldVars ∧ ["new"] = newVars ∧ mergeBody = body ∧ mergeResult = res := by
      simpa [tableDecl] using he
    exact ⟨Or.inl rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  · rcases hc with rfl | rfl
    · intro oldVars newVars body res he
      simp [ctorDecl] at he
    · intro oldVars newVars body res he
      obtain ⟨rfl, rfl, rfl, rfl⟩ :
        ["old"] = oldVars ∧ ["new"] = newVars ∧ mergeBody = body ∧ mergeResult = res := by
        simpa [tableDecl] using he
      exact ⟨Or.inr ⟨f, rfl⟩, rfl, rfl, rfl,
        fun hu => False.elim (viewName_ne_ufName hu), rfl, rfl⟩
  · exact allMaintenance_shape P c hc

private theorem cmd_shape (i : Nat) (c : Cmd) :
    ∀ d ∈ encodeCmd i c, CommandShape d.command := by
  intro d hd
  cases c with
  | decl _ _ => simp [encodeCmd] at hd
  | rule r =>
      simp only [encodeCmd, List.mem_singleton] at hd
      subst d
      trivial
  | check q =>
      simp only [encodeCmd, List.mem_singleton] at hd
      subst d
      trivial
  | run R | saturate R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> trivial

private theorem cmds_shape (P : Program) (i : Nat) :
    ∀ c ∈ encodeCmds P i, CommandShape c.command := by
  induction P generalizing i with
  | nil => simp [encodeCmds]
  | cons c cs ih =>
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact cmd_shape i c d hd
      · exact ih (i + 1) d hd

theorem encode_commandShape (P : Program) : ∀ c ∈ encode P, CommandShape c := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hd with hd | hd
  · exact prelude_shape P d hd
  · exact cmds_shape P 0 d hd

/-- Every generated merge body records UF entries without asserting a built-in union. -/
theorem MergeShape.unionFree {sig : Signature} (h : MergeShape sig) : sig.UnionFree := by
  intro f dc hd ms hm
  cases ms with
  | merge oldVars newVars body res =>
      have hb := (h f dc hd body res hm).2.1
      rw [hb]
      simp [mergeBody, Action.UnionFree]

private theorem maintenance_setup (P : Program) :
    ∀ c ∈ maintenanceRules P, c.command.DeclOrRule := by
  intro c hc
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · trivial
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩ <;> trivial

private theorem allMaintenance_setup (P : Program) :
    ∀ c ∈ allMaintenanceRules P, c.command.DeclOrRule := by
  intro c hc
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenance_setup P c hc
  · have h := maintenance_setup P c hc
    unfold inRuleset
    split <;> simp_all only [Cmd.DeclOrRule]

theorem prelude_setup (P : Program) :
    ∀ c ∈ (encodePrelude P).map Command.command, c.DeclOrRule := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simp only [encodePrelude, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false] at hd
  rcases hd with (rfl | ⟨⟨f, k⟩, _, hd⟩) | hd
  · trivial
  · rcases hd with rfl | rfl <;> trivial
  · exact allMaintenance_setup P d hd

def NoDecl : Cmd → Prop
  | .decl _ _ => False
  | _ => True

private theorem cmd_noDecl (i : Nat) (c : Cmd) :
    ∀ d ∈ encodeCmd i c, NoDecl d.command := by
  intro d hd
  cases c with
  | decl _ _ => simp [encodeCmd] at hd
  | rule r =>
      simp only [encodeCmd, List.mem_singleton] at hd
      subst d
      trivial
  | check q =>
      simp only [encodeCmd, List.mem_singleton] at hd
      subst d
      trivial
  | run R | saturate R =>
      simp only [encodeCmd, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> trivial

theorem cmds_noDecl (P : Program) (i : Nat) :
    ∀ c ∈ (encodeCmds P i).map Command.command, NoDecl c := by
  have hall : ∀ d ∈ encodeCmds P i, NoDecl d.command := by
    induction P generalizing i with
    | nil => simp [encodeCmds]
    | cons c cs ih =>
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact cmd_noDecl i c d hd
        · exact ih (i + 1) d hd
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact hall d hd

/-- The prelude installs all declarations before any data is written. -/
def encodeSig (P : Program) : Signature :=
  ((encodePrelude P).map Command.command).foldl (fun s c => c.sigBind s) (fun _ => none)

private theorem maintenance_rule (P : Program) :
    ∀ c ∈ maintenanceRules P, ∃ r, c.command = .rule r := by
  intro c hc
  simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
  · exact ⟨_, rfl⟩
  · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨i, _, rfl⟩ <;> exact ⟨_, rfl⟩

private theorem allMaintenance_rule (P : Program) :
    ∀ c ∈ allMaintenanceRules P, ∃ r, c.command = .rule r := by
  intro c hc
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact maintenance_rule P c hc
  · obtain ⟨r, hr⟩ := maintenance_rule P c hc
    simp [inRuleset, hr]

private theorem prelude_decl_iff {P : Program} {f : FnName} {dc : FnDecl} :
    Cmd.decl f dc ∈ (encodePrelude P).map Command.command ↔
      (f = ufName ∧ dc = tableDecl 1) ∨ ∃ g k, (g, k) ∈ P.ctors ∧
        ((f = g ∧ dc = ctorDecl k) ∨ (f = viewName g ∧ dc = tableDecl k)) := by
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := List.mem_map.mp h
    simp only [encodePrelude, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | ⟨⟨g, k⟩, hg, hc⟩) | hc
    · exact Or.inl (by simpa using he.symm)
    · refine Or.inr ⟨g, k, hg, ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl (by simpa using he.symm)
      · exact Or.inr (by simpa using he.symm)
    · obtain ⟨r, hr⟩ := allMaintenance_rule P c hc
      rw [hr] at he
      cases he
  · intro h
    apply List.mem_map.mpr
    rcases h with ⟨rfl, rfl⟩ | ⟨g, k, hg, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, rfl⟩
    · refine ⟨⟨.decl f (ctorDecl k), none⟩,
        List.mem_append_left _ (List.mem_cons_of_mem _ ?_), rfl⟩
      exact List.mem_flatMap.mpr ⟨(f, k), hg, List.mem_cons_self⟩
    · refine ⟨⟨.decl (viewName g) (tableDecl k), none⟩,
        List.mem_append_left _ (List.mem_cons_of_mem _ ?_), rfl⟩
      exact List.mem_flatMap.mpr ⟨(g, k), hg, by simp⟩

private theorem source_ne_view {P : Program} (hdom : P.Fragment)
    {f : FnName} {k : Nat} (hf : (f, k) ∈ P.ctors) (g : FnName) : f ≠ viewName g := by
  intro he
  exact noAt_of_mem_ctors hdom hf (he ▸ (by simp [viewName, String.isPrefixOf]))

private theorem source_ne_uf {P : Program} (hdom : P.Fragment)
    {f : FnName} {k : Nat} (hf : (f, k) ∈ P.ctors) : f ≠ ufName := by
  intro he
  exact noAt_of_mem_ctors hdom hf (he ▸ (by decide +kernel : "@".isPrefixOf ufName = true))

/-- The generated union-find declaration cannot be shadowed by source names or views. -/
theorem encodeSig_ufName {P : Program} (hdom : P.Fragment) :
    encodeSig P ufName = some (tableDecl 1) := by
  apply foldl_sigBind_found _ (prelude_decl_iff.mpr (Or.inl ⟨rfl, rfl⟩))
  intro dc hd
  rcases prelude_decl_iff.mp hd with ⟨_, hd⟩ | ⟨g, k, hg, (⟨he, _⟩ | ⟨he, _⟩)⟩
  · exact hd
  · exact False.elim (source_ne_uf hdom hg he.symm)
  · exact False.elim (viewName_ne_ufName he.symm)

/-- Every source constructor keeps its structural id constructor and gains its view. -/
theorem encodeSig_tables {P : Program} (hdom : P.Fragment) {f : FnName} {k : Nat}
    (hf : (f, k) ∈ P.ctors) :
    encodeSig P f = some (ctorDecl k) ∧
      encodeSig P (viewName f) = some (tableDecl k) := by
  constructor
  · apply foldl_sigBind_found _
      (prelude_decl_iff.mpr (Or.inr ⟨f, k, hf, Or.inl ⟨rfl, rfl⟩⟩))
    intro dc hd
    rcases prelude_decl_iff.mp hd with ⟨he, _⟩ | ⟨g, l, hg, (⟨he, hd⟩ | ⟨he, _⟩)⟩
    · exact False.elim (source_ne_uf hdom hf he)
    · exact hd.trans (congrArg ctorDecl (hdom.aritiesAgree (g, l) hg (f, k) hf he.symm))
    · exact False.elim (source_ne_view hdom hf g he)
  · apply foldl_sigBind_found _
      (prelude_decl_iff.mpr (Or.inr ⟨f, k, hf, Or.inr ⟨rfl, rfl⟩⟩))
    intro dc hd
    rcases prelude_decl_iff.mp hd with ⟨he, _⟩ | ⟨g, l, hg, (⟨he, _⟩ | ⟨he, hd⟩)⟩
    · exact False.elim (viewName_ne_ufName he)
    · exact False.elim (source_ne_view hdom hg f he.symm)
    · exact hd.trans
        (congrArg tableDecl (hdom.aritiesAgree (g, l) hg (f, k) hf (viewName_inj he).symm))

/-- A declared generated view always has the compiler's singleton-output table shape. -/
theorem encodeSig_view_census {P : Program} (hp : P.Fragment) {f : FnName} {dc : FnDecl}
    (hf : encodeSig P (viewName f) = some dc) : ∃ k, (f, k) ∈ P.ctors ∧ dc = tableDecl k := by
  have hfold : ∀ p : Program,
      (∀ decl, Cmd.decl (viewName f) decl ∈ p → ∃ k, (f, k) ∈ P.ctors ∧ decl = tableDecl k) →
      ∀ sig : Signature,
      (∀ decl, sig (viewName f) = some decl → ∃ k, (f, k) ∈ P.ctors ∧ decl = tableDecl k) →
      ∀ decl, (p.foldl (fun s c => c.sigBind s) sig) (viewName f) = some decl →
        ∃ k, (f, k) ∈ P.ctors ∧ decl = tableDecl k := by
    intro p
    induction p with
    | nil => intro _ sig hs; exact hs
    | cons c cs ih =>
      intro hc sig hs
      apply ih (fun decl hd => hc decl (List.mem_cons_of_mem _ hd))
      intro decl hd
      cases c with
      | decl g dg =>
        by_cases he : viewName f = g
        · subst g
          have hde : dg = decl := by simpa [Cmd.sigBind] using hd
          exact hde ▸ hc dg List.mem_cons_self
        · exact hs decl (by simpa [Cmd.sigBind, Function.update_of_ne he] using hd)
      | rule _ | check _ | run _ | saturate _ => exact hs decl hd
  apply hfold ((encodePrelude P).map Command.command) ?_ (fun _ => none) (by simp) dc hf
  intro decl hd
  rcases prelude_decl_iff.mp hd with ⟨hn, _⟩ | ⟨g, k, hg, hd⟩
  · exact (viewName_ne_ufName hn).elim
  · rcases hd with ⟨hn, _⟩ | ⟨hn, rfl⟩
    · exact (source_ne_view hp hg f hn.symm).elim
    · obtain rfl := viewName_inj hn
      exact ⟨k, hg, rfl⟩

theorem encodeSig_view_shape {P : Program} (hp : P.Fragment) {f : FnName} {dc : FnDecl}
    (hf : encodeSig P (viewName f) = some dc) : ∃ k, dc = tableDecl k := by
  obtain ⟨k, _, hk⟩ := encodeSig_view_census hp hf
  exact ⟨k, hk⟩

/-- Every constructor available in a source prefix has an id constructor in the target. -/
theorem sourceConstructors_of_programStep {P p : Program} (hdom : P.Fragment)
    (hp : ∀ c ∈ p, c ∈ P) {src : Database} (hsrc : ProgramStep Database.empty p src)
    {sig : Signature} (hsig : sig = encodeSig P) :
    ∀ f, src.sig.IsCtor f → sig.IsCtor f := by
  intro f hf
  obtain ⟨dc, hd, _⟩ := hf
  rcases hsrc.declared hd with he | hc
  · cases he
  · have hk : (f, dc.arity) ∈ P.ctors := List.mem_dedup.mpr
      (List.mem_flatMap.mpr ⟨.decl f dc, hp _ hc, by simp [Cmd.ctors]⟩)
    exact ⟨ctorDecl dc.arity, hsig ▸ (encodeSig_tables hdom hk).1, rfl⟩

/-- Only source rule commands emit compiled source rules. -/
theorem rule_mem_encodeCmd (i : Nat) (c : Cmd) (r : Rule) :
    Cmd.rule r ∈ (encodeCmd i c).map Command.command ↔
      ∃ s, c = .rule s ∧ r = encodeRule s := by
  cases c <;> simp [encodeCmd, taggedRule, eq_comm]

/-- The compiler's command counter does not change which rules a prefix registers. -/
theorem rule_mem_encodeCmds (pre : Program) (i : Nat) (r : Rule) :
    Cmd.rule r ∈ (encodeCmds pre i).map Command.command ↔
      ∃ s, Cmd.rule s ∈ pre ∧ r = encodeRule s := by
  induction pre generalizing i with
  | nil => simp [encodeCmds]
  | cons c cs ih =>
      rw [encodeCmds, List.map_append, List.mem_append, rule_mem_encodeCmd, ih]
      constructor
      · rintro (⟨s, hs, hr⟩ | ⟨s, hs, hr⟩)
        · exact ⟨s, List.mem_cons.mpr (Or.inl hs.symm), hr⟩
        · exact ⟨s, List.mem_cons_of_mem _ hs, hr⟩
      · rintro ⟨s, hs, hr⟩
        rcases List.mem_cons.mp hs with hs | hs
        · exact Or.inl ⟨s, hs.symm, hr⟩
        · exact Or.inr ⟨s, hs, hr⟩

/-- Every rule in the prelude is tagged maintenance. -/
theorem rule_mem_prelude (P : Program) (r : Rule) :
    Cmd.rule r ∈ (encodePrelude P).map Command.command ↔
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r := by
  simp only [encodePrelude, List.map_append, List.map_cons, List.mem_append,
    List.mem_cons, List.mem_map]
  constructor
  · rintro ((h | ⟨c, hc, hr⟩) | h)
    · cases h
    · obtain ⟨⟨f, k⟩, _, hc⟩ := List.mem_flatMap.mp hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> cases hr
    · exact h
  · exact Or.inr

/-- Any generated maintenance rule has an identical copy in each source saturation ruleset. -/
theorem maintenance_copy {P : Program} {c : Command} (hc : c ∈ allMaintenanceRules P)
    {r : Rule} (hr : c.command = .rule r) {R : RulesetName} (hR : R ∈ P.saturateRulesets) :
    ∃ c' ∈ allMaintenanceRules P, c'.command = .rule { r with ruleset := R } := by
  have hbase : ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r →
      ∃ c' ∈ allMaintenanceRules P, c'.command = .rule { r with ruleset := R } := by
    intro c hc r hr
    refine ⟨inRuleset R c, List.mem_append_right _ ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨R, hR, List.mem_map.mpr ⟨c, hc, rfl⟩⟩
    · simp [inRuleset, hr]
  rcases List.mem_append.mp hc with hc | hc
  · exact hbase c hc r hr
  · obtain ⟨S, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hcbase, rfl⟩ := List.mem_map.mp hc
    unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl := Cmd.rule.inj hr
      exact hbase c hcbase s hs
    next hn => exact hbase c hcbase r hr

private theorem maintenanceRules_query_ne_nil (P : Program) :
    ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r → r.query ≠ [] := by
  intro c hc r hr
  rcases List.mem_cons.mp hc with rfl | hc
  · obtain rfl := Cmd.rule.inj hr
    simp [pathCompressRule]
  · obtain ⟨⟨f, k⟩, _, hc⟩ := List.mem_flatMap.mp hc
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain rfl := Cmd.rule.inj hr
      simp [eclassRule]
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      obtain rfl := Cmd.rule.inj hr
      simp [childRule]

/-- Every maintenance query has live-row premises, so none can fire from empty data. -/
theorem maintenance_query_ne_nil {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) : r.query ≠ [] := by
  rcases List.mem_append.mp hc with hc | hc
  · exact maintenanceRules_query_ne_nil P c hc r hr
  · obtain ⟨R, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hcbase, rfl⟩ := List.mem_map.mp hc
    unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl := Cmd.rule.inj hr
      exact maintenanceRules_query_ne_nil P c hcbase s hs
    next => exact maintenanceRules_query_ne_nil P c hcbase r hr

theorem maintenance_mem_prelude {P : Program} {c : Command} (hc : c ∈ allMaintenanceRules P) :
    c ∈ encodePrelude P := by
  simp only [encodePrelude, List.mem_cons, List.mem_append]
  exact Or.inr hc

theorem eclassRule_mem_maintenance {P : Program} {f : FnName} {k : Nat}
    (hk : (f, k) ∈ P.ctors) :
    taggedRule (eclassRule f k) (.rebuild (.eclass f)) ∈ allMaintenanceRules P := by
  apply List.mem_append_left
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨(f, k), hk, List.mem_cons_self⟩

theorem childRule_mem_maintenance {P : Program} {f : FnName} {k i : Nat}
    (hk : (f, k) ∈ P.ctors) (hi : i < k) :
    taggedRule (childRule f k i) (.rebuild (.child f i)) ∈ allMaintenanceRules P := by
  apply List.mem_append_left
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  exact ⟨(f, k), hk, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)⟩


/-- The hoisted signature has precisely the generated merge-body shape. -/
theorem encodeSig_mergeShape (P : Program) : MergeShape (encodeSig P) := by
  have hall : ∀ c ∈ (encodePrelude P).map Command.command, CommandShape c := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact prelude_shape P d hd
  unfold encodeSig
  generalize (encodePrelude P).map Command.command = p at hall ⊢
  have go : ∀ (sig : Signature), MergeShape sig →
      MergeShape (p.foldl (fun s c => c.sigBind s) sig) := by
    induction p with
    | nil => exact fun _ h => h
    | cons c cs ih =>
        intro sig hs
        apply ih (fun d hd => hall d (List.mem_cons_of_mem c hd))
        have hc := hall c List.mem_cons_self
        cases c with
        | decl f dc => exact hs.update hc
        | _ => exact hs
  exact go _ MergeShape.empty

end Egglog.Congruence
