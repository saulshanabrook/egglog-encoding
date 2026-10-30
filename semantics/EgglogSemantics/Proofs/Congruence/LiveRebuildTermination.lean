import EgglogSemantics.Proofs.Congruence.LiveSaturation
import EgglogSemantics.Proofs.Congruence.UFCoverage
import EgglogSemantics.Proofs.Congruence.LiveMetadata

/-! Rebuilding ranges over existing values and therefore always terminates. -/

namespace Egglog.Congruence.Live

open Abstract

def tableWidths (P : Program) : List (FnName × Nat) :=
  (ufName, 1) :: P.ctors.map (fun fk => (viewName fk.1, fk.2))

def atomsOver (P : Program) (values : Set Term) : Set Term :=
  {t | ∃ fk ∈ tableWidths P, ∃ cols,
    cols.length = fk.2 + 1 ∧ (∀ c ∈ cols, c ∈ values) ∧ t = .app fk.1 cols}

theorem atomsOver_finite (P : Program) {values : Set Term} (hv : values.Finite) :
    (atomsOver P values).Finite := by
  have hf := (List.finite_toSet (tableWidths P)).biUnion fun fk _ =>
    (finite_lists hv (fk.2 + 1)).image (Term.app fk.1)
  apply hf.subset
  rintro t ⟨fk, hk, cols, hlen, hcols, rfl⟩
  exact Set.mem_iUnion₂.mpr ⟨fk, hk, cols, ⟨hlen, hcols⟩, rfl⟩

theorem row_mem_atomsOver {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hsig : d.sig = encodeSig P) {values : Set Term}
    (hv : d.values ⊆ values) {row : Entry} (hr : row ∈ d.entries) :
    row.atom ∈ atomsOver P values := by
  have hd := (h.state.rows row hr).declared
  obtain ⟨a, ha⟩ := (h.state.rows row hr).output
  have hrole := ((hsig ▸ encodeSig_mergeShape P) row.name
    (tableDecl row.key.length) hd mergeBody mergeResult rfl).1
  have hwidth : (row.name, row.key.length) ∈ tableWidths P := by
    rcases hrole with hf | ⟨f, hf⟩
    · have hk : row.key.length = 1 := by
        have he := Option.some.inj ((hf ▸ hd).symm.trans h.state.uf)
        exact congrArg FnDecl.arity he
      simp [tableWidths, hf, hk]
    · obtain ⟨k, hk, he⟩ := encodeSig_view_census hp (hsig ▸ (hf ▸ hd))
      have hk' : row.key.length = k := congrArg FnDecl.arity he
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      exact ⟨(f, k), hk, by simp [hf, hk']⟩
  refine ⟨(row.name, row.key.length), hwidth, row.columns, ?_, ?_, rfl⟩
  · simp [Entry.columns, ha]
  · intro c hc
    exact hv ⟨h.storeOk.columns row hr c hc, (h.storeOk.entry_valid hr).column_values c hc⟩

theorem eqs_bound_of_values {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hsig : d.sig = encodeSig P) {values : Set Term}
    (hv : d.values ⊆ values) :
    d.eqs ⊆ (values ∪ atomsOver P values).prod (values ∪ atomsOver P values) := by
  intro p hp'
  have he := h.noUnions.diag p hp'
  have hm : p.1 ∈ values ∪ atomsOver P values := by
    rcases h.storeOk.typed p hp' with ⟨ha, _⟩ | ⟨row, hr, heq⟩
    · exact Or.inl (hv ⟨(StoredCong.direct hp').mem_left, ha⟩)
    · subst p
      exact Or.inr (row_mem_atomsOver hp h hsig hv ⟨hr.shape, hp'⟩)
  exact ⟨hm, he ▸ hm⟩

theorem localFlat_values_subset {d e : Database} {q : Query} {ρ : Env}
    {f : FnName} {xs : List Expr} (hw : d.WF)
    (hf : ¬ d.sig.IsCtor f) (hvars : ∀ x ∈ xs, ∃ v, x = Expr.var v)
    (hρ : ValidQuerySubst d q ρ)
    (hr : evalLocalActions d [.expr (.app f xs)] ρ = some e) : e.values ⊆ d.values := by
  obtain ⟨ts, us, hts, hus, hterms⟩ := evalLocalActions_entry (args := xs) (out := [])
    (by simpa using hr)
  obtain rfl : us = [] := (Option.some.inj hus).symm
  have henv : ∀ b ∈ ρ, b.2 ∈ d.terms := hρ.mem_terms
  have hcols := evalList_vars_held henv xs hvars hts
  intro t ht
  have hv : t.IsValue d.sig := (evalLocalActions_sig hr) ▸ ht.2
  have hm := hterms ht.1
  rw [Database.addTerm_terms] at hm
  rcases hm with hm | hm
  · exact ⟨hm, hv⟩
  · have hm' : t ∈ (Term.app f ts).subterms := by simpa using hm
    cases hm' with
    | refl => exact (hf (Term.isValue_app_iff.mp hv).1).elim
    | arg hc hs => exact ⟨hw.subtermClosed _ (hcols _ hc) hs, hv⟩

theorem maintenance_values_subset {P : Program} (hp : P.Fragment) {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r)
    {d e : Database} {ρ : Env} (hsig : d.sig = encodeSig P) (hw : d.WF)
    (hρ : ValidQuerySubst d r.query ρ) (he : evalLocalActions d r.actions ρ = some e) :
    e.values ⊆ d.values := by
  obtain ⟨f, xs, ha, hv, _⟩ := maintenance_headShape hc hr
  rw [ha] at he
  exact localFlat_values_subset hw (hsig ▸ maintenance_head_notCtor hp hc hr ha) hv hρ he

theorem maintenance_runRules_values_subset {P : Program} (hp : P.Fragment)
    {d : Database} (h : Runtime d) (hsig : d.sig = encodeSig P) {R : RulesetName}
    (honly : ∀ r ∈ d.rules, r.ruleset = R →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) :
    (RunRules R d).values ⊆ d.values := by
  intro t ht
  have hv : t.IsValue d.sig := ht.2
  have hm := ht.1
  rw [RunRules.eq_sUnion, Database.sUnion_terms] at hm
  rcases hm with hm | hm
  · exact ⟨hm, hv⟩
  · obtain ⟨post, ⟨r, hr, hR, ρ, hρ, he⟩, hm⟩ := Set.mem_iUnion₂.mp hm
    obtain ⟨c, hc, hcr⟩ := honly r hr hR
    exact maintenance_values_subset hp hc hcr hsig h.wf hρ he
      ⟨hm, by rw [evalLocalActions_sig he]; exact hv⟩

theorem maintenance_runReach_values_subset {P : Program} (hp : P.Fragment)
    {d e : Database} (h : Runtime d) (hsig : d.sig = encodeSig P) {R : RulesetName}
    (honly : ∀ r ∈ d.rules, r.ruleset = R →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (hr : Relation.ReflTransGen (RunStep R) d e) : e.values ⊆ d.values := by
  induction hr with
  | refl => exact Set.Subset.refl _
  | @tail mid post hreach hstep ih =>
      have hm := h.runReach hreach
      have hmsig := (RunReach.sig hreach).trans hsig
      exact (mergeClosure_values_subset (hm.runRules R)
        (hmsig ▸ encodeSig_mergeShape P) hstep.1).trans
        ((maintenance_runRules_values_subset hp hm hmsig
          (fun r hr hR => honly r ((runReach_rules hreach) ▸ hr) hR)).trans ih)

/-- Every finite generated state admits a completed rebuilding execution. -/
theorem rebuild_exists {P : Program} (hp : P.Fragment) {d : Database}
    (h : Runtime d) (hn : MergeNormal d) (hsig : d.sig = encodeSig P)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) :
    ∃ e, SaturateReach rebuildRuleset d e := by
  have hv : d.values.Finite := (Database.finite_terms h.state.finite.eqs).subset (fun _ ht => ht.1)
  have hb := hv.union (atomsOver_finite P hv)
  apply saturate_exists_of_finite_bound h hn rebuildRuleset (hb.prod hb)
  intro e he
  exact eqs_bound_of_values hp (h.runReach he) ((RunReach.sig he).trans hsig)
    (maintenance_runReach_values_subset hp h hsig honly he)

end Egglog.Congruence.Live
