import EgglogSemantics.Proofs.Congruence.AbstractRunState
import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Proofs.FiniteSaturation
import EgglogSemantics.Proofs.Congruence.AbstractFiniteRows
import EgglogSemantics.Proofs.RuleStore

/-! Finite support for mathematical generated-table maintenance. These lemmas construct
bounds on actual merge executions; no executable interpreter or fuel is involved. -/

namespace Egglog.Congruence.Abstract

/-- A generated merge can add UF rows over old values, but no new value column. -/
def mergeTermBound (base : Database) : Set Term :=
  base.terms ∪ {t | ∃ a ∈ base.terms, ∃ b ∈ base.terms, t = .app ufName [a, b]}

theorem mergeTermBound_finite {base : Database} (h : base.eqs.Finite) :
    (mergeTermBound base).Finite := by
  have ht := Database.finite_terms h
  apply ht.union
  exact (ht.image2 (fun a b => Term.app ufName [a, b]) ht).subset
    (by rintro t ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩)

/-- Even new UF rows have only values from the original finite state. -/
theorem mergeTermBound_columns {base : Database} (hw : base.WF) {f : FnName}
    {cols : List Term} (ht : Term.app f cols ∈ mergeTermBound base) :
    ∀ c ∈ cols, c ∈ base.terms := by
  rcases ht with ht | ⟨a, ha, b, hb, he⟩
  · exact fun c hc => Database.mem_terms_of_arg hw ht hc
  · obtain ⟨_, rfl⟩ := Term.app.inj he
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ha
    · obtain rfl := List.mem_singleton.mp hc
      exact hb

private theorem addTerm_mergeBound {base d : Database} (hw : base.WF)
    (hd : d.terms ⊆ mergeTermBound base) {f : FnName} {cols : List Term}
    (ht : Term.app f cols ∈ mergeTermBound base) :
    (d.addTerm (.app f cols)).terms ⊆ mergeTermBound base := by
  intro t hm
  rw [Database.addTerm_terms] at hm
  rcases hm with hm | hm
  · exact hd hm
  · by_cases he : t = Term.app f cols
    · exact he ▸ ht
    · exact Or.inl (subterms_of_columns hw (mergeTermBound_columns hw ht) hm he)

/-- Generated collisions remain in a fixed finite universe, independently of scheduling. -/
theorem mergeStep_termBound {base d e : Database} (hw : base.WF) (h : Runtime d)
    (hd : d.terms ⊆ mergeTermBound base) (hm : MergeStep d e) :
    e.terms ⊆ mergeTermBound base := by
  obtain ⟨f, cs, a, b, ha, hb, _, rfl⟩ :=
    mergeStep_form h.shape h.noUnions.diag h.declared h.uf hm
  have ham := mergeTermBound_columns hw (hd ha) a (by simp)
  have hbm := mergeTermBound_columns hw (hd hb) b (by simp)
  have hl : lowerId a b ∈ base.terms := by
    rcases lowerId_eq_or a b with he | he <;> rw [he] <;> assumption
  have hsurv : Term.app f (cs ++ [lowerId a b]) ∈ mergeTermBound base := by
    rcases lowerId_eq_or a b with he | he <;> rw [he]
    · exact hd ha
    · exact hd hb
  exact addTerm_mergeBound hw
    (addTerm_mergeBound hw (addTerm_mergeBound hw hd (Or.inr ⟨a, ham, _, hl, rfl⟩))
      (Or.inr ⟨b, hbm, _, hl, rfl⟩)) hsurv

/-- Every finite prefix of generated merging has the same finite term bound. -/
theorem mergeClosure_termBound {d e : Database} (h : Runtime d)
    (hm : MergeClosure d e) : e.terms ⊆ mergeTermBound d := by
  induction hm with
  | refl => exact Set.subset_union_left
  | tail hreach hstep ih =>
      exact mergeStep_termBound h.wf (h.merge hreach) ih hstep

/-- The finite bound includes every equation of every reachable merge state. -/
theorem mergeClosure_finite_bound {d : Database} (h : Runtime d) (hf : d.eqs.Finite) :
    ∃ B : Set (Term × Term), B.Finite ∧ ∀ e, MergeClosure d e → e.eqs ⊆ B := by
  refine ⟨(mergeTermBound d).prod (mergeTermBound d),
    (mergeTermBound_finite hf).prod (mergeTermBound_finite hf), ?_⟩
  intro e he p hp
  have hm := eqsInTerms_free (Cong.direct hp)
  exact ⟨mergeClosure_termBound h he hm.1, mergeClosure_termBound h he hm.2⟩

/-- Every finite generated-table state admits a finite merge schedule to a fixed point. -/
theorem mergeNormal_exists {d : Database} (h : Runtime d) (hf : d.eqs.Finite) :
    ∃ e, MergeClosure d e ∧ MergeNormal e := by
  obtain ⟨B, hB, hb⟩ := mergeClosure_finite_bound h hf
  exact Egglog.mergeNormal_exists_of_finite_bound d hB hb

/-- Maintenance writes complete UF or view rows, never bare structural constructors. -/
private theorem maintenance_head_generated {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r) :
    ∃ f cols, r.actions = [.expr (.app f cols)] ∧
      ((f = ufName ∧ cols.length = 2) ∨ (∃ g, f = viewName g) ∧ cols ≠ []) := by
  have hbase : ∀ c ∈ maintenanceRules P, ∀ r, c.command = .rule r →
      ∃ f cols, r.actions = [.expr (.app f cols)] ∧
        ((f = ufName ∧ cols.length = 2) ∨ (∃ g, f = viewName g) ∧ cols ≠ []) := by
    intro c hc r hr
    simp only [maintenanceRules, List.mem_cons, List.mem_flatMap] at hc
    rcases hc with rfl | ⟨⟨f, k⟩, _, hc⟩
    · obtain rfl := Cmd.rule.inj hr
      exact ⟨ufName, _, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · simp only [rebuildRules, List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨i, _, rfl⟩
      · obtain rfl := Cmd.rule.inj hr
        exact ⟨viewName f, _, rfl, Or.inr ⟨⟨f, rfl⟩, by simp⟩⟩
      · obtain rfl := Cmd.rule.inj hr
        exact ⟨viewName f, _, rfl, Or.inr ⟨⟨f, rfl⟩, by simp⟩⟩
  simp only [allMaintenanceRules, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨R, _, c, hc, rfl⟩
  · exact hbase c hc r hr
  · unfold inRuleset at hr
    split at hr
    next s hs =>
      obtain rfl := Cmd.rule.inj hr
      exact hbase c hc s hs
    next => exact hbase c hc r hr

private theorem sound_generated_row {src d : Database} (hs : SoundTerms d src)
    {f : FnName} {cols : List Term}
    (hk : (f = ufName ∧ cols.length = 2) ∨ (∃ g, f = viewName g) ∧ cols ≠ [])
    (ht : Term.app f cols ∈ d.terms) : Term.app f cols ∈ SoundRows src := by
  rcases hk with ⟨rfl, hlen⟩ | ⟨⟨g, rfl⟩, hne⟩
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    exact Or.inr ⟨a, b, rfl, hs.2 a b ht⟩
  · have he := List.dropLast_append_getLast hne
    refine Or.inl ⟨g, cols.dropLast, cols.getLast hne, congrArg _ he.symm, ?_⟩
    apply hs.1
    simpa only [he] using ht

/-- A maintenance firing adds only a sound generated row. Its rearranged columns and
their subterms were already held before the firing. -/
theorem maintenance_newTerms {P : Program} {c : Command}
    (hc : c ∈ allMaintenanceRules P) {r : Rule} (hr : c.command = .rule r)
    {src d e : Database} {σ : Env} (hd : d.Diag) (hw : d.WF) (hs : SoundTerms d src)
    (hσ : ValidQuerySubst d r.query σ) (hf : evalLocalActions d r.actions σ = some e) :
    e.terms ⊆ d.terms ∪ SoundRows src := by
  have he := maintenance_soundTerms hc hr hd hw hs hσ hf
  obtain ⟨f, cols, ha, hkind⟩ := maintenance_head_generated hc hr
  obtain ⟨g, cs, ha', hvars, _⟩ := maintenance_headShape hc hr
  obtain ⟨hgf, hcs⟩ := Expr.app.inj (Action.expr.inj (List.cons.inj (ha'.symm.trans ha)).1)
  subst g
  subst cs
  rw [ha] at hf
  obtain ⟨ts, vs, hts, hvs, hterms⟩ := evalLocalActions_entry (args := cols) (out := [])
    (by simpa only [List.append_nil] using hf)
  obtain rfl : vs = [] := (Option.some.inj hvs).symm
  have hval : ∀ b ∈ σ ++ d.env, b.2 ∈ d.terms := by
    intro b hb
    exact (List.mem_append.mp hb).elim (hσ.mem_terms b) (hw.envInTerms b)
  have hcols := evalList_vars_held hval cols hvars hts
  have hlen := Expr.evalList_length hts
  have hkind' : (f = ufName ∧ ts.length = 2) ∨
      (∃ g, f = viewName g) ∧ ts ≠ [] := by
    rcases hkind with ⟨hn, hl⟩ | ⟨hn, hne⟩
    · exact Or.inl ⟨hn, hlen.trans hl⟩
    · refine Or.inr ⟨hn, ?_⟩
      intro hnil
      exact hne (List.length_eq_zero_iff.mp (by simpa [hnil] using hlen.symm))
  intro t ht
  have hm := hterms ht
  rw [List.append_nil, Database.addTerm_terms] at hm
  rcases hm with hm | hm
  · exact Or.inl hm
  · by_cases htop : t = Term.app f ts
    · subst t
      exact Or.inr (sound_generated_row he hkind' ht)
    · exact Or.inl (subterms_of_columns hw hcols hm htop)

private theorem addTerm_soundRows {src d : Database} (hw : d.WF) {f : FnName}
    {cols : List Term} (hc : ∀ c ∈ cols, c ∈ d.terms)
    (ht : Term.app f cols ∈ SoundRows src) :
    (d.addTerm (.app f cols)).terms ⊆ d.terms ∪ SoundRows src := by
  intro t hm
  rw [Database.addTerm_terms] at hm
  rcases hm with hm | hm
  · exact Or.inl hm
  · by_cases he : t = Term.app f cols
    · exact Or.inr (he ▸ ht)
    · exact Or.inl (subterms_of_columns hw hc hm he)

/-- Generated merges add only source-sound UF rows; their values already existed. -/
theorem mergeStep_newTerms {src d e : Database} (h : Runtime d) (hs : SoundTerms d src)
    (hm : MergeStep d e) : e.terms ⊆ d.terms ∪ SoundRows src := by
  have he := mergeStep_soundTerms h.shape h.noUnions.diag h.wf h.declared h.uf hs hm
  obtain ⟨f, cs, a, b, ha, hb, _, rfl⟩ :=
    mergeStep_form h.shape h.noUnions.diag h.declared h.uf hm
  have ham := Database.mem_terms_of_arg h.wf ha (by simp : a ∈ cs ++ [a])
  have hbm := Database.mem_terms_of_arg h.wf hb (by simp : b ∈ cs ++ [b])
  have hl : lowerId a b ∈ d.terms := by
    rcases lowerId_eq_or a b with hl | hl <;> rw [hl] <;> assumption
  have ha' : Term.app ufName [a, lowerId a b] ∈ SoundRows src := by
    apply Or.inr
    refine ⟨a, lowerId a b, rfl, he.2 _ _ ?_⟩
    apply (Database.Contained.addTerm _ _).terms
    apply (Database.Contained.addTerm _ _).terms
    exact Database.mem_addTerm _ _
  have hb' : Term.app ufName [b, lowerId a b] ∈ SoundRows src := by
    apply Or.inr
    refine ⟨b, lowerId a b, rfl, he.2 _ _ ?_⟩
    apply (Database.Contained.addTerm _ _).terms
    exact Database.mem_addTerm _ _
  have hsurv : Term.app f (cs ++ [lowerId a b]) ∈ d.terms := by
    rcases lowerId_eq_or a b with hl | hl <;> rw [hl] <;> assumption
  intro t ht
  simp only [mergeLinks, Database.addTerm_terms, Set.mem_union] at ht
  rcases ht with ((ht | ht) | ht) | ht
  · exact Or.inl ht
  · exact addTerm_soundRows h.wf
      (by simpa using (show a ∈ d.terms ∧ lowerId a b ∈ d.terms from ⟨ham, hl⟩)) ha'
      (by rw [Database.addTerm_terms]; exact Or.inr ht)
  · exact addTerm_soundRows h.wf
      (by simpa using (show b ∈ d.terms ∧ lowerId a b ∈ d.terms from ⟨hbm, hl⟩)) hb'
      (by rw [Database.addTerm_terms]; exact Or.inr ht)
  · exact Or.inl (h.wf.subtermClosed _ hsurv ht)

/-- An arbitrary finite generated merge schedule adds only sound generated rows. -/
theorem mergeClosure_newTerms {src d e : Database} (h : Runtime d) (hs : SoundTerms d src)
    (hm : MergeClosure d e) : e.terms ⊆ d.terms ∪ SoundRows src := by
  induction hm with
  | refl => exact Set.subset_union_left
  | tail hreach hstep ih =>
      have hm := h.merge hreach
      have hsound := mergeClosure_soundTerms h.shape h.noUnions.diag h.wf h.declared
        h.uf hs hreach
      intro t ht
      rcases mergeStep_newTerms hm hsound hstep ht with ht | ht
      · exact ih ht
      · exact Or.inr ht

/-- Every finite run of maintenance stays within the initial terms and the finite set
of rows justified by the same source state. -/
theorem maintenance_reach_termBound {P : Program} {R : RulesetName} {src d e : Database}
    (h : Runtime d) (hs : SoundTerms d src)
    (honly : ∀ r ∈ d.rules, r.ruleset = R →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r)
    (hr : Relation.ReflTransGen (RunStep R) d e) :
    SoundTerms e src ∧ e.terms ⊆ d.terms ∪ SoundRows src := by
  induction hr with
  | refl => exact ⟨hs, Set.subset_union_left⟩
  | @tail mid post hreach hstep ih =>
      have hm := h.runReach hreach
      have hfire : ∀ r ∈ mid.rules, r.ruleset = R → ∀ out ∈ RuleResults mid r,
          SoundTerms out src ∧ out.terms ⊆ mid.terms ∪ SoundRows src := by
        rintro r hr hR out ⟨σ, hσ, hf⟩
        obtain ⟨c, hc, hcr⟩ := honly r ((runReach_rules hreach) ▸ hr) hR
        exact ⟨maintenance_soundTerms hc hcr hm.noUnions.diag hm.wf ih.1 hσ hf,
          maintenance_newTerms hc hcr hm.noUnions.diag hm.wf ih.1 hσ hf⟩
      have hsound : SoundTerms (RunRules R mid) src := by
        apply ih.1.sUnion
        rintro out ⟨r, hr, hR, hout⟩
        exact (hfire r hr hR out hout).1
      have hbound : (RunRules R mid).terms ⊆ d.terms ∪ SoundRows src := by
        intro t ht
        simp only [RunRules, Database.sUnion_terms, Set.mem_union, Set.mem_iUnion,
          exists_prop] at ht
        rcases ht with ht | ⟨out, ⟨r, hr, hR, hout⟩, ht⟩
        · exact ih.2 ht
        · rcases (hfire r hr hR out hout).2 ht with ht | ht
          · exact ih.2 ht
          · exact Or.inr ht
      have hruntime := hm.runRules R
      refine ⟨mergeClosure_soundTerms hruntime.shape hruntime.noUnions.diag hruntime.wf
        hruntime.declared hruntime.uf hsound hstep, ?_⟩
      intro t ht
      rcases mergeClosure_newTerms hruntime hsound hstep ht with ht | ht
      · exact hbound ht
      · exact Or.inr ht

/-- Rebuilding has an actual finite mathematical evaluation whenever its rows are
justified in a finite source state. No bound on the number of rounds is assumed. -/
theorem maintenance_saturate_exists {P : Program} {R : RulesetName} {src d : Database}
    (h : Runtime d) (hs : SoundTerms d src) (hf : d.eqs.Finite) (hsrc : src.terms.Finite)
    (honly : ∀ r ∈ d.rules, r.ruleset = R →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) :
    ∃ e, SaturateReach R d e := by
  have hbound : (d.terms ∪ SoundRows src).Finite :=
    (Database.finite_terms hf).union (SoundRows.finite hsrc)
  apply Egglog.saturateReach_exists_of_finite_bound R d (hbound.prod hbound)
  intro e he p hp
  have hm := eqsInTerms_free (Cong.direct hp)
  have ht := (maintenance_reach_termBound h hs honly he).2
  exact ⟨ht hm.1, ht hm.2⟩

/-- The dedicated compiled rebuilding command always has a finite successful run
from a finite, source-sound runtime state. -/
theorem rebuild_cmd_exists {P : Program} {src d : Database} (h : Runtime d)
    (hs : SoundTerms d src) (hf : d.eqs.Finite) (hsrc : src.terms.Finite)
    (honly : ∀ r ∈ d.rules, r.ruleset = rebuildRuleset →
      ∃ c ∈ allMaintenanceRules P, c.command = .rule r) :
    ∃ e, CmdStep d (.saturate rebuildRuleset) e := by
  obtain ⟨e, he⟩ := maintenance_saturate_exists h hs hf hsrc honly
  exact ⟨e, cmdStep_saturate_iff.mpr he⟩

end Egglog.Congruence.Abstract
