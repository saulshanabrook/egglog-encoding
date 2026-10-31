import EgglogSemantics.Proofs.InterpBase

namespace Egglog

namespace FDatabase

theorem sameRow_app_iff {d : FDatabase} (he : d.Closed) {f : FnName}
    {ts : List Term} (ht : ∀ t ∈ ts, t ∈ d.terms) {u : Term} (hu : u ∈ d.terms) :
    sameRow d.closureF (.app f ts) u = true ↔ d.toDatabase.SameRow (.app f ts) u := by
  cases u with
  | lit l => simp [sameRow, Database.SameRow]
  | app g us =>
    have hus : ∀ u ∈ us, u ∈ d.terms := fun u hu' => he.subterms _ hu u
      (Term.mem_subtermList_of_isSubterm (.arg hu' (.refl u)))
    simp only [sameRow, Bool.and_eq_true, beq_iff_eq, congrTuple_iff he.subterms ht hus]
    constructor
    · rintro ⟨rfl, hc⟩
      exact ⟨f, ts, us, rfl, rfl, hc⟩
    · rintro ⟨k, as, bs, h₁, h₂, hc⟩
      cases h₁
      cases h₂
      exact ⟨rfl, hc⟩

theorem isSubsumed_app_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    {f : FnName} {ts : List Term} (ht : ∀ t ∈ ts, t ∈ d.terms) :
    d.isSubsumed d.closureF (.app f ts) = true ↔
      ∃ u ∈ d.toDatabase.subsumed, d.toDatabase.SameRow (.app f ts) u := by
  simp only [isSubsumed, List.any_eq_true]
  constructor
  · rintro ⟨u, hu, hr⟩
    exact ⟨u, hu, (sameRow_app_iff he ht (hi.subsumed u hu)).mp hr⟩
  · rintro ⟨u, hu, hr⟩
    exact ⟨u, hu, (sameRow_app_iff he ht (hi.subsumed u hu)).mpr hr⟩

theorem hasCtorRow_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {f : FnName} {ts : List Term}
    (ht : ∀ t ∈ ts, t ∈ d.terms) :
    d.hasCtorRow d.closureF f ts = true ↔ Cong d.toDatabase (.app f ts) (.app f ts) := by
  simp only [hasCtorRow, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨g, bs⟩, hr, hf, hbs⟩
    dsimp at hf hbs
    subst g
    have hrow := hi.ctor _ hr
    have hb : ∀ b ∈ bs, b ∈ d.terms := fun b hb => he.subterms _ hrow b
      (Term.mem_subtermList_of_isSubterm (.arg hb (.refl b)))
    have hc := (congrTuple_iff he.subterms ht hb).mp hbs
    have h := Cong.congr (Database.toCong ((mem_toDatabase_terms he.subterms).mpr hrow)) hc.symm
    exact h.symm.trans h
  · intro h
    obtain ⟨bs, hb, hc⟩ := represented_app h
    have hb' := (mem_toDatabase_terms he.subterms).mp hb
    refine ⟨⟨f, bs⟩, hj f bs hb', rfl, (congrTuple_iff he.subterms ht ?_).mpr hc⟩
    exact fun b hmem => he.subterms _ hb' b
      (Term.mem_subtermList_of_isSubterm (.arg hmem (.refl b)))

theorem exists_witness_iff {d : FDatabase} (he : d.Closed) (t : Term) :
    (∃ w ∈ d.terms, (w, t) ∈ (d.addTerm t).closureF) ↔ Cong d.toDatabase t t := by
  constructor
  · rintro ⟨w, hw, hc⟩
    have h := witness_addTerm he hw hc
    exact h.symm.trans h
  · intro h
    obtain ⟨w, hw, hc⟩ := represented_witness h
    have hw' := (mem_toDatabase_terms he.subterms).mp hw
    exact ⟨w, hw', (mem_closureF_addTerm he (mem_addTerm_of_mem hw')
      (self_mem_addTerm d t)).mpr (hc.mono (Database.Contained.addTerm t _))⟩

theorem meaning_addTerm_of_exists {d : FDatabase} (he : d.Closed) {t : Term}
    (ht : Cong d.toDatabase t t) : (d.addTerm t).toDatabase.SameMeaning d.toDatabase := by
  apply (toDatabase_addTerm he).trans
  refine Database.SameMeaning.of_congr (fun a b => ⟨?_, ?_⟩) rfl
  · apply Cong.of_assertions
    rintro p (rfl | hp)
    · exact ht
    · exact .direct hp
  · exact Cong.mono (Database.Contained.addTerm t _)

theorem liveWith_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) (t : Term) :
    d.liveWith d.closureF t = true ↔ t ∈ d.toDatabase.live := by
  cases t with
  | lit l =>
    simp only [liveWith, closureWith_eq, addTerms, List.foldl_cons, List.foldl_nil,
      decide_eq_true_eq, exists_witness_iff he]
    simp [Database.live, Database.SameRow]
  | app f ts =>
    rw [liveWith]
    split
    · rename_i hheld
      have ht : ∀ t ∈ ts, t ∈ d.terms := by
        simp only [holdsAll, List.all_eq_true, decide_eq_true_eq] at hheld
        exact fun t ht => hheld t ht t (Term.self_mem_subtermList t)
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
        hasCtorRow_iff he hi hj ht]
      rw [ne_eq, isSubsumed_app_iff (f := f) he hi ht]
      rfl
    · rw [closureWith_eq]
      change (decide (∃ w ∈ d.terms, (w, .app f ts) ∈ (d.addTerm (.app f ts)).closureF) &&
        !d.isSubsumed (d.addTerm (.app f ts)).closureF (.app f ts)) = true ↔ _
      simp only [Bool.and_eq_true, decide_eq_true_eq, exists_witness_iff he,
        Bool.not_eq_true', Bool.eq_false_iff]
      by_cases ht : Cong d.toDatabase (.app f ts) (.app f ts)
      · have hm := meaning_addTerm_of_exists he ht
        have hts : ∀ t ∈ ts, t ∈ (d.addTerm (.app f ts)).terms := fun t ht' =>
          (he.addTerm _).subterms _ (self_mem_addTerm d _) t
            (Term.mem_subtermList_of_isSubterm (.arg ht' (.refl t)))
        have hx := isSubsumed_app_iff (f := f) (he.addTerm (.app f ts)) (hi.addTerm (.app f ts)) hts
        change d.isSubsumed (d.addTerm (.app f ts)).closureF (.app f ts) = true ↔
          ∃ u ∈ d.toDatabase.subsumed,
            (d.addTerm (.app f ts)).toDatabase.SameRow (.app f ts) u at hx
        simp only [Database.SameRow.iff_of_congr hm.congr] at hx
        simp only [ne_eq, hx, Database.live, Set.mem_setOf_eq]
      · simp [ht, Database.live]

end FDatabase

/-- The executable row test is exactly semantic liveness, for any row list. -/
theorem FDatabase.all_liveWith_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) (ts : List Term) :
    ts.all (d.liveWith d.closureF) = true ↔ ∀ t ∈ ts, t ∈ d.toDatabase.live := by
  simp only [List.all_eq_true, FDatabase.liveWith_iff he hi hj]

mutual

/-- The recursive executable expression test computes the matching judgement. -/
theorem exprHoldsWith_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {σ : Env} (e : Expr) :
    exprHoldsWith d.closureF d σ e = true ↔ Expr.Matches d.toDatabase σ e := by
  match e with
  | .lit l =>
    rw [exprHoldsWith, FDatabase.liveWith_iff he hi hj]
    exact ⟨Expr.Matches.lit, fun h => by cases h with | lit hl => exact hl⟩
  | .var v =>
    simp only [exprHoldsWith, Option.isSome_iff_exists]
    exact ⟨fun ⟨_, hv⟩ => .var hv, fun h => by cases h with | var hv => exact ⟨_, hv⟩⟩
  | .app f args =>
    simp only [exprHoldsWith, Bool.and_eq_true, exprsHoldWith_iff he hi hj]
    cases hev : Expr.evalList args σ with
    | none =>
      simp only [Bool.false_eq_true, and_false]
      exact ⟨False.elim, fun h => by cases h with | app _ hs _ => simp [hev] at hs⟩
    | some ts =>
      rw [FDatabase.liveWith_iff he hi hj]
      constructor
      · rintro ⟨ha, hl⟩
        exact .app ha hev hl
      · intro h
        cases h with
        | app ha hs hl =>
          have hts := Option.some.inj (hev.symm.trans hs)
          subst hts
          exact ⟨ha, hl⟩
  | .min a b =>
    simp only [exprHoldsWith, Bool.and_eq_true, exprHoldsWith_iff he hi hj]
    exact ⟨fun ⟨ha, hb⟩ => .min ha hb, fun h => by cases h with | min ha hb => exact ⟨ha, hb⟩⟩

theorem exprsHoldWith_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {σ : Env} (es : List Expr) :
    exprsHoldWith d.closureF d σ es = true ↔ Expr.MatchesList d.toDatabase σ es := by
  match es with
  | [] => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | e :: es =>
    simp only [exprsHoldWith, Bool.and_eq_true, exprHoldsWith_iff he hi hj,
      exprsHoldWith_iff he hi hj]
    exact ⟨fun ⟨ha, hs⟩ => .cons ha hs, fun h => by cases h with | cons ha hs => exact ⟨ha, hs⟩⟩

end

/-- Historical lookup bridge, now using recursive semantic and executable matching. -/
theorem Lookup.lookupWith {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {σ : Env} {e : Expr} {t : Term}
    (h : e.eval σ = some t ∧ Expr.Matches d.toDatabase σ e) :
    e.eval σ = some t ∧ exprHoldsWith d.closureF d σ e = true :=
  ⟨h.1, (exprHoldsWith_iff he hi hj _).mpr h.2⟩

theorem LookupList.lookupListWith {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {σ : Env} {es : List Expr} {ts : List Term}
    (h : Expr.evalList es σ = some ts ∧ Expr.MatchesList d.toDatabase σ es) :
    Expr.evalList es σ = some ts ∧ exprsHoldWith d.closureF d σ es = true :=
  ⟨h.1, (exprsHoldWith_iff he hi hj _).mpr h.2⟩

theorem lookupWith_lookup {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {σ : Env} (e : Expr) {t : Term}
    (h : e.eval σ = some t ∧ exprHoldsWith d.closureF d σ e = true) :
    e.eval σ = some t ∧ Expr.Matches d.toDatabase σ e :=
  ⟨h.1, (exprHoldsWith_iff he hi hj _).mp h.2⟩

theorem lookupListWith_lookup {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {σ : Env} (es : List Expr) {ts : List Term}
    (h : Expr.evalList es σ = some ts ∧ exprsHoldWith d.closureF d σ es = true) :
    Expr.evalList es σ = some ts ∧ Expr.MatchesList d.toDatabase σ es :=
  ⟨h.1, (exprsHoldWith_iff he hi hj _).mp h.2⟩

theorem lookupWith_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {σ : Env} {e : Expr} {t : Term} :
    (e.eval σ = some t ∧ exprHoldsWith d.closureF d σ e = true) ↔
      (e.eval σ = some t ∧ Expr.Matches d.toDatabase σ e) :=
  ⟨lookupWith_lookup he hi hj e, Lookup.lookupWith he hi hj⟩

/-- Operand closure is conservative when the first operand is represented. -/
theorem closureWith_pair_iff {d : FDatabase} (he : d.Closed) {s t : Term}
    (hs : Cong d.toDatabase s s) :
    (s, t) ∈ d.closureWith d.closureF [s, t] ↔ Cong d.toDatabase s t := by
  rw [FDatabase.closureWith_eq]
  change (s, t) ∈ ((d.addTerm s).addTerm t).closureF ↔ _
  rw [FDatabase.mem_closureF_addTerm₂ he
    (FDatabase.mem_addTerm_of_mem (FDatabase.self_mem_addTerm d s))
    (FDatabase.self_mem_addTerm _ t)]
  constructor
  · intro hc
    have hc' : StoredCongOn d.toDatabase [s, t] s t := hc.toStored
      (Database.mem_addTerms (ts := [s, t]) (by simp))
      (Database.mem_addTerms (ts := [s, t]) (by simp))
    exact InferredFacts.congr_iff_infers.mpr (InferredFacts.infers_of_congOn_core
      (InferredFacts.congr_iff_infers.mp hs) hc')
  · exact Cong.mono (Database.Contained.addTerms [s, t] _)

theorem patternHolds_matches {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {p : Pattern} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Cong d.toDatabase t t)
    (h : patternHolds d p σ = true) : Matches d.toDatabase p σ := by
  cases p with
  | expr e => exact .atom ((exprHoldsWith_iff he hi hj e).mp h)
  | eq a b =>
    simp only [patternHolds, patternHoldsWith, Bool.and_eq_true,
      exprHoldsWith_iff he hi hj] at h
    obtain ⟨⟨h₁, h₂⟩, hc⟩ := h
    obtain ⟨s, ha⟩ := h₁.eval_exists
    obtain ⟨t, hb⟩ := h₂.eval_exists
    simp only [ha, hb, decide_eq_true_eq] at hc
    exact .equal h₁ h₂ ha hb
      ((closureWith_pair_iff he (Lookup.exists_cong hσ ⟨ha, h₁⟩)).mp hc)
  | ne a b =>
    simp only [patternHolds, patternHoldsWith, Bool.and_eq_true,
      exprHoldsWith_iff he hi hj] at h
    obtain ⟨⟨h₁, h₂⟩, hn⟩ := h
    obtain ⟨s, ha⟩ := h₁.eval_exists
    obtain ⟨t, hb⟩ := h₂.eval_exists
    simp only [ha, hb, Bool.not_eq_true', decide_eq_false_iff_not] at hn
    exact .unequal h₁ h₂ ha hb (fun hc =>
      hn ((closureWith_pair_iff he (Lookup.exists_cong hσ ⟨ha, h₁⟩)).mpr hc))

theorem patternHolds_of_matches {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {p : Pattern} {σ : Env}
    (hσ : ∀ v t, Env.lookup v σ = some t → Cong d.toDatabase t t)
    (h : Matches d.toDatabase p σ) : patternHolds d p σ = true := by
  cases h with
  | atom hl => exact (exprHoldsWith_iff he hi hj _).mpr hl
  | equal h₁ h₂ ha hb hc =>
    simp only [patternHolds, patternHoldsWith, ha, hb, Bool.and_eq_true,
      exprHoldsWith_iff he hi hj, decide_eq_true_eq,
      closureWith_pair_iff he (hc.trans hc.symm)]
    exact ⟨⟨h₁, h₂⟩, hc⟩
  | unequal h₁ h₂ ha hb hn =>
    simp only [patternHolds, patternHoldsWith, ha, hb, Bool.and_eq_true,
      exprHoldsWith_iff he hi hj, Bool.not_eq_true', decide_eq_false_iff_not,
      closureWith_pair_iff he (Lookup.exists_cong hσ ⟨ha, h₁⟩)]
    exact ⟨⟨h₁, h₂⟩, hn⟩

theorem FDatabase.patternHolds_validSubst {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent)
    {p : Pattern} {σ : Env} (hv : ValidEnv (p.freeVars []) d.toDatabase σ)
    (h : patternHolds d p σ = true) : ValidSubst d.toDatabase p σ :=
  ⟨hv, patternHolds_matches he hi hj
    (fun _ _ ht => Database.toCong (hv.mem_terms _ (Env.mem_of_lookup ht))) h⟩

theorem validEnv_canon {d : FDatabase} (hc : d.SubtermClosed) {q : Query} {σ : Env}
    {p : Pattern} (hp : p ∈ q) (hd : Env.dom σ = Query.freeVars q [])
    (hv : ∀ b ∈ σ, b.2 ∈ d.repsWith d.closureF) :
    ValidEnv (p.freeVars []) d.toDatabase (Env.canon (p.freeVars []) σ) := by
  constructor
  · rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hd]
  · exact fun b hb => (FDatabase.mem_repsWith_closureF_iff hc).mp
      (hv b (Env.mem_of_lookup (Env.mem_canon hb).2))

theorem validQuerySubst_of_mem_matchQuery {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent)
    {q : Query} {σ : Env} (h : σ ∈ matchQuery d q) :
    ∃ τ, ValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  simp only [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true] at h
  obtain ⟨⟨hd, hv⟩, hall⟩ := h
  obtain ⟨τ, hu, hrf⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => Env.canon (p.freeVars []) σ) (by
      intro ρ hρ
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hρ
      intro b hb
      exact (Env.mem_canon hb).2)
  refine ⟨τ, ⟨_, List.forall₂_map_self (fun p hp =>
    ⟨validEnv_canon he.subterms hp hd hv, patternHolds_matches he hi hj (fun _ _ ht => Database.toCong
      ((validEnv_canon he.subterms hp hd hv).mem_terms _ (Env.mem_of_lookup ht))) (hall p hp)⟩), hu⟩,
    Env.agree_of_refines hrf ?_⟩
  intro v hv
  rw [hd] at hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_freeVars.mp hv
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars []) σ, List.mem_map_of_mem hp, ?_⟩
  rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hd]
  exact hvp

theorem patternHolds_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {p : Pattern} {σ : Env}
    (hv : ValidEnv (p.freeVars []) d.toDatabase σ) :
    patternHolds d p σ = true ↔ ValidSubst d.toDatabase p σ :=
  ⟨fun h => ⟨hv, patternHolds_matches he hi hj
    (fun _ _ ht => Database.toCong (hv.mem_terms _ (Env.mem_of_lookup ht))) h⟩,
    fun h => patternHolds_of_matches he hi hj
      (fun _ _ ht => Database.toCong (hv.mem_terms _ (Env.mem_of_lookup ht))) h.2⟩

theorem mem_matchQuery_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {q : Query} {σ : Env} :
    σ ∈ matchQuery d q ↔ Env.dom σ = Query.freeVars q [] ∧
      (∀ b ∈ σ, b.2 ∈ d.repsWith d.closureF) ∧
      ∀ p ∈ q, ValidSubst d.toDatabase p (Env.canon (p.freeVars []) σ) := by
  simp only [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true]
  constructor
  · rintro ⟨⟨hd, hv⟩, hh⟩
    exact ⟨hd, hv, fun p hp =>
      (patternHolds_iff he hi hj (validEnv_canon he.subterms hp hd hv)).mp (hh p hp)⟩
  · rintro ⟨hd, hv, hh⟩
    exact ⟨⟨hd,hv⟩, fun p hp => patternHolds_of_matches he hi hj
      (fun _ _ ht => Database.toCong ((hh p hp).mem_terms _ (Env.mem_of_lookup ht))) (hh p hp).2⟩

theorem mem_matchQuery_of_validQuerySubst {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) {q : Query} {τ : Env}
    (h : ValidQuerySubst d.toDatabase q τ) :
    Env.canon (Query.freeVars q []) τ ∈ matchQuery d q ∧
      Env.Agree τ (Env.canon (Query.freeVars q []) τ) := by
  have hmd : ∀ v, v ∈ Env.dom τ ↔ v ∈ Query.freeVars q [] := fun v => by
    rw [h.mem_dom_iff, Query.mem_freeVars]
  have hbound : ∀ v ∈ Query.freeVars q [], (Env.lookup v τ).isSome := fun v hv =>
    Env.lookup_isSome_iff_mem_dom.mpr ((hmd v).mpr hv)
  have hdom : Env.dom (Env.canon (Query.freeVars q []) τ) = Query.freeVars q [] :=
    Env.dom_canon hbound
  have hag : Env.Agree τ (Env.canon (Query.freeVars q []) τ) :=
    (Env.agree_of_refines Env.refines_canon (fun v hv => by
      rw [hdom]; exact (hmd v).mp hv)).symm
  refine ⟨(mem_matchQuery_iff he hi hj).mpr ⟨hdom, ?_, ?_⟩, hag⟩
  · exact fun b hb => (FDatabase.mem_repsWith_closureF_iff he.subterms).mpr
      (h.mem_reps b (Env.mem_of_lookup (Env.mem_canon hb).2))
  · intro p hp
    obtain ⟨σs, hall, hu⟩ := h
    obtain ⟨σp, hσp, hvs⟩ := hall.flip.exists_left hp
    have hpsub : p.freeVars [] ⊆ Query.freeVars q [] := Query.freeVars_subset hp
    have hpdom : Env.dom (Env.canon (p.freeVars []) τ) = p.freeVars [] :=
      Env.dom_canon fun v hv => hbound v (hpsub hv)
    have hsc : ∀ ρ ∈ σs, Env.Refines ρ ρ := by
      intro ρ hρ
      obtain ⟨p', -, hvs'⟩ := hall.exists_left hρ
      exact Env.Refines.self_of_nodup (hvs'.validEnv.1.symm.nodup (p'.freeVars_nodup _))
    have hrp : Env.Refines σp τ := (hu.refines_of_mem hsc).1 σp hσp
    rw [Env.canon_canon hpsub (Query.freeVars_nodup q [])]
    refine ValidSubst.of_agree hvs (fun v => ?_) hpdom
    by_cases hv : v ∈ p.freeVars []
    · rw [Env.lookup_canon (p.freeVars_nodup _) hv]
      cases hlk : Env.lookup v σp with
      | none =>
        rw [Env.lookup_eq_none_iff] at hlk
        exact absurd ((ValidSubst.validEnv hvs).1.mem_iff.mpr hv) hlk
      | some t => exact (hrp (v, t) (Env.mem_of_lookup hlk)).symm
    · rw [Env.lookup_eq_none_iff.mpr fun hc => hv ((ValidSubst.validEnv hvs).1.mem_iff.mp hc),
        Env.lookup_eq_none_iff.mpr fun hc => hv (hpdom ▸ hc)]


theorem queryHolds_iff_matchQuery {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) (q : Query) :
    QueryHolds d.toDatabase q ↔ (matchQuery d q).isEmpty = false := by
  rw [queryHolds_iff_validQuerySubst, List.isEmpty_eq_false_iff_exists_mem]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, (mem_matchQuery_of_validQuerySubst he hi hj hσ).1⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ, _⟩ := validQuerySubst_of_mem_matchQuery he hi hj hσ
    exact ⟨τ, hτ⟩



end Egglog
