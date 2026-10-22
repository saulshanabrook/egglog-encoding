import EgglogSemantics.Proofs.Congruence.Tables

/-! Canonical readings of rebuilt view tables. -/

namespace Egglog.Congruence

/-- The unique live UF root. Only the proof chooses it; compilation stores no extra data. -/
noncomputable def Rebuilt.root {d : FDatabase} (h : Rebuilt d) (t : Term) : Term :=
  (exists_ufRowRoot (h.descend.rows h.inv.index h.noUnions.eqsRefl
    (by simp [Signature.mergeOf, h.uf, tableDecl])) t).choose

theorem Rebuilt.root_spec {d : FDatabase} (h : Rebuilt d) (t : Term) :
    UFRowReach d t (h.root t) ∧ UFRowRoot d (h.root t) :=
  (exists_ufRowRoot (h.descend.rows h.inv.index h.noUnions.eqsRefl
    (by simp [Signature.mergeOf, h.uf, tableDecl])) t).choose_spec

theorem Rebuilt.root_eq {d : FDatabase} (h : Rebuilt d) {t : Term} (ht : UFRowRoot d t) :
    h.root t = t := ht.reach_eq (h.root_spec t).1

theorem Rebuilt.root_ufReach {d : FDatabase} (h : Rebuilt d) {a b : Term}
    (hab : UFReach d a b) : h.root a = h.root b :=
  ufRowRoot_of_ufReach h.history h.uf
    (h.descend.rows h.inv.index h.noUnions.eqsRefl
      (by simp [Signature.mergeOf, h.uf, tableDecl])) h.forest h.descend hab
    _ _ (h.root_spec a).1 (h.root_spec a).2 (h.root_spec b).1 (h.root_spec b).2

theorem Rebuilt.root_lit {d : FDatabase} (h : Rebuilt d) {src : Database}
    (hs : SoundTerms d src) (hw : src.WF) (l : Lit) : h.root (.lit l) = .lit l := by
  apply h.root_eq
  intro b hb
  have ht := mem_terms_of_indexOk h.noUnions.eqsRefl h.inv.index hb.1
    (show d.sig.mergeOf ufName ≠ none by simp [Signature.mergeOf, h.uf, tableDecl])
  exact hb.2 ((hs.2 (.lit l) b ht).eq_of_isLit hw.litsIsolated (Or.inl rfl)).symm

section Reading

variable {P : Program} {d : FDatabase} {src : Database}
variable (h : Rebuilt d) (htables : RebuildTables P d)
variable (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
variable (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)


/-- Every live view output is a root, with declaration and rule premises supplied by
its actual source constructor rather than by a separate table-shape assumption. -/
theorem Rebuilt.all_view_roots (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {cs : List Term} {e : Term}
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows) : UFRowRoot d e := by
  have hk := view_row_ctors h.inv h.noUnions hs hctors hr
  exact h.view_root hs hb hc (htables.view _ _ hk) (htables.output _ _ hk) hr

/-- Each retained entry has a live row at the root of its old output. -/
theorem Rebuilt.entry_root_row (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {cs : List Term} {e : Term}
    (ht : Term.app (viewName f) (cs ++ [e]) ∈ d.terms) :
    (⟨viewName f, cs, [h.root e]⟩ : Row) ∈ d.rows := by
  have hk := view_entry_ctors hs hctors ht
  obtain ⟨v, hv, hev⟩ := h.history (viewName f) (tableDecl cs.length)
    (htables.view _ _ hk) mergeBody mergeResult rfl cs e rfl ht
  have hvr := h.all_view_roots htables hs hb hctors hc hv
  have heq : h.root e = v := (h.root_ufReach hev).trans (h.root_eq hvr)
  exact heq ▸ hv

/-- Rebuilding supplies a live row with every key and the output normalized. -/
theorem Rebuilt.entry_normalized (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {cs : List Term} {e : Term}
    (ht : Term.app (viewName f) (cs ++ [e]) ∈ d.terms) :
    (⟨viewName f, cs.map h.root, [h.root e]⟩ : Row) ∈ d.rows := by
  have hk := view_entry_ctors hs hctors ht
  apply h.keys_paths hs hb hc (htables.view _ _ hk) (htables.output _ _ hk)
    (htables.child _ _ hk) (h.entry_root_row htables hs hb hctors hc ht)
  clear ht hk
  induction cs with
  | nil => exact .nil
  | cons c cs ih => exact .cons (h.root_spec c).1 ih

/-- A source view read can be normalized directly to a live row. -/
theorem Rebuilt.out_normalized (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f)
    {f : FnName} {cs : List Term} {e : Term}
    (ho : d.toDatabase.Out (viewName f) cs [e]) :
    (⟨viewName f, cs.map h.root, [h.root e]⟩ : Row) ∈ d.rows := by
  obtain ⟨bs, hcs, ht⟩ := ho
  obtain rfl := CongList.eq_of_eqsRefl h.noUnions.eqsRefl.toDatabase hcs
  exact h.entry_normalized htables hs hb hctors hc (Egglog.FDatabase.mem_toDatabase_terms.mp ht)

/-- A live view row is also a retained entry reading. -/
theorem Rebuilt.out_of_view_row (h : Rebuilt d) {f : FnName} {cs : List Term} {e : Term}
    (hr : (⟨viewName f, cs, [e]⟩ : Row) ∈ d.rows) :
    d.toDatabase.Out (viewName f) cs [e] :=
  h.inv.index.entry _ hr (row_mergeOf_ne_none h.inv.index hr (by simp))


variable (hw : src.WF)

mutual

/-- Normalize a recursive reading by re-keying each view onto the roots of its child ids. -/
theorem Rebuilt.normalize_view (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF) :
    ∀ (t : Term) {e : Term}, ViewRepr d.toDatabase t e →
    ViewRepr d.toDatabase t (h.root e)
  | .lit l, _, .lit => by rw [h.root_lit hs hw l]; exact .lit
  | .app f as, _, .app hl ho =>
      .app (h.normalize_views htables hs hb hctors hc hw as hl)
        (h.out_of_view_row (h.out_normalized htables hs hb hctors hc ho))

@[inherit_doc Rebuilt.normalize_view]
theorem Rebuilt.normalize_views (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF) :
    ∀ (ts : List Term) {es : List Term},
    ViewReprList d.toDatabase ts es → ViewReprList d.toDatabase ts (es.map h.root)
  | [], _, .nil => .nil
  | t :: ts, _, .cons ht hts => .cons (h.normalize_view htables hs hb hctors hc hw t ht)
      (h.normalize_views htables hs hb hctors hc hw ts hts)

end

mutual

/-- Two readings of the same source term have the same root. The induction puts their
child ids at identical keys, where the merge fixed point supplies a unique row. -/
theorem Rebuilt.unique_view (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) : ∀ (t : Term) {a b : Term},
    ViewRepr d.toDatabase t a → ViewRepr d.toDatabase t b → h.root a = h.root b
  | .lit _, _, _, .lit, .lit => rfl
  | .app f as, _, _, .app ha hoa, .app hb' hob => by
      have hkeys := h.unique_views htables hs hb hctors hc as ha hb'
      have hra := h.out_normalized htables hs hb hctors hc hoa
      have hrb := h.out_normalized htables hs hb hctors hc hob
      have hk := view_row_ctors h.inv h.noUnions hs hctors hra
      have he := tableRows_unique_of_settled h.settled h.shape h.uf h.inv h.noUnions
        h.descend (htables.view _ _ hk) rfl hra hrb rfl hkeys
      simpa using congrArg Row.out he

@[inherit_doc Rebuilt.unique_view]
theorem Rebuilt.unique_views (h : Rebuilt d) (htables : RebuildTables P d)
    (hs : SoundTerms d src) (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) : ∀ (ts : List Term) {as bs : List Term},
    ViewReprList d.toDatabase ts as → ViewReprList d.toDatabase ts bs →
      as.map h.root = bs.map h.root
  | [], _, _, .nil, .nil => rfl
  | t :: ts, _, _, .cons ha has, .cons hb' hbs => by
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨h.unique_view htables hs hb hctors hc t ha hb',
        h.unique_views htables hs hb hctors hc ts has hbs⟩

end

include h htables hs hb hctors hc hw

/-- The view-leader invariant follows from actual rebuilding and its data invariants. -/
theorem Rebuilt.viewLeader : ViewLeader d.toDatabase := by
  refine ⟨h.root, fun t _ ht => h.normalize_view htables hs hb hctors hc hw t ht,
    fun t _ _ ha hb' => h.unique_view htables hs hb hctors hc t ha hb', ?_⟩
  intro a b hab
  obtain ⟨as, hargs, ht⟩ := hab
  obtain rfl := CongList.eq_of_eqsRefl h.noUnions.eqsRefl.toDatabase hargs
  exact h.root_ufReach (.single (Egglog.FDatabase.mem_toDatabase_terms.mp ht))

/-- A tuple of common classes can share the normalized keys of any reading of its left side. -/
theorem Rebuilt.share_keys {as bs es : List Term} (ha : ViewReprList d.toDatabase as es)
    (hab : List.Forall₂ (SameClass d.toDatabase) as bs) :
    ViewReprList d.toDatabase as (es.map h.root) ∧
      ViewReprList d.toDatabase bs (es.map h.root) := by
  refine ⟨h.normalize_views htables hs hb hctors hc hw as ha, ?_⟩
  induction hab generalizing es with
  | nil => cases ha; exact .nil
  | @cons a b as bs hab hrest ih =>
      cases ha with
      | @cons _ e _ es hae has =>
          obtain ⟨x, hax, hbx⟩ := hab
          have heq := h.unique_view htables hs hb hctors hc a hae hax
          exact .cons (heq ▸ h.normalize_view htables hs hb hctors hc hw b hbx) (ih has)

/-- Existence of one reading per held source application supplies the shared-key coverage
needed by source congruence. Rebuilding handles all alternative child readings. -/
theorem Rebuilt.viewsCover
    (hex : ∀ t ∈ src.terms, ∃ e, ViewRepr d.toDatabase t e) :
    ViewsCover d.toDatabase src := by
  constructor
  intro f as bs ha hab
  obtain ⟨e, he⟩ := hex (.app f as) ha
  cases he with
  | app hl ho =>
      obtain ⟨hleft, hright⟩ := h.share_keys htables hs hb hctors hc hw hl hab
      exact ⟨_, h.root e, hleft, hright,
        h.out_of_view_row (h.out_normalized htables hs hb hctors hc ho)⟩

/-- After rebuilding, completeness reduces to preserving source existence and explicit
source unions through the command simulation. -/
theorem Rebuilt.corresponds
    (hex : ∀ t ∈ src.terms, ∃ e, ViewRepr d.toDatabase t e)
    (hun : UnionsRead d.toDatabase src) (a b : Term) (ha : a ∈ src.terms) (hb' : b ∈ src.terms) :
    Cong src a b ↔ SameClass d.toDatabase a b :=
  ⟨cong_sameClass_of_state hw (h.viewLeader htables hs hb hctors hc hw)
      (h.viewsCover htables hs hb hctors hc hw hex) hun,
    sameClass_cong_of_state hw (viewsSound_of_soundTerms h.noUnions.eqsRefl hs).1 ha hb'⟩

end Reading

end Egglog.Congruence
