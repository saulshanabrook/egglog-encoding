import EgglogSemantics.Proofs.Congruence.Invariant
import EgglogSemantics.Proofs.Congruence.Rules

/-! One round of the maintenance rules preserves the simulation relation: every row it
writes is derivable from the rows it read, every union-find row it marks has a strictly
smaller replacement, every source row it marks is congruent to a marked spelling, and the
live rows still generate every row. -/

namespace Egglog.Congruence

variable {sub : Bool}

/-- A union-find row one maintenance firing asserts: an existing row, or the replacement a
rule writes for the live edges it matched. -/
inductive MaintRow (d : Database) : Term → Term → Prop
  | old {k p : Term} : Row d k p → MaintRow d k p
  | compress {a b c : Term} : Edge d a b → Edge d b c → b ≠ c → MaintRow d a c
  | collide {a b c : Term} : Edge d a b → Edge d a c → b = Term.least b c → b ≠ c →
      MaintRow d c b
  | congr {f : FnName} {as bs rs : List Term} {y z : Term} :
      List.Forall₂ (Edge d) as rs → List.Forall₂ (Edge d) bs rs →
      Edge d (.app f as) y → Edge d (.app f bs) z → y = Term.least y z → y ≠ z → MaintRow d z y

variable {P : Program} {src d : Database}

/-- Children with the same live parents are congruent in the source. -/
theorem congList_of_edges (h : Rel sub src d) {as bs rs : List Term}
    (hra : List.Forall₂ (Edge d) as rs) (hrb : List.Forall₂ (Edge d) bs rs) :
    CongList src as bs := by
  induction hra generalizing bs with
  | nil => cases hrb; exact .nil
  | cons ha _ ih =>
    cases hrb with
    | cons hb hrb => exact .cons ((h.edge_cong ha).trans (h.edge_cong hb).symm) (ih hrb)

/-- The application a subsumption firing marks is a key of a source name. -/
theorem subsume_key (h : Rel sub src d) {f : FnName} {as bs : List Term} (hm : Marker d f as)
    (hl : Term.app f bs ∈ d.live) : Term.app f bs ∈ Keys d :=
  h.mem_keys_of_src (h.app_mem_src_of_mem_terms (h.key_sourceName (h.marker_key hm))
    ((Congruence.app_live_iff h.diag).mp hl).1)

theorem mem_runWrites_maint (h : Rel sub src d) {q : Term × Term}
    (hq : q ∈ RunWrites (maintenance sub P) d) :
    (∃ k p, q = (ufRowT k p, ufRowT k p) ∧ MaintRow d k p) ∨
      ∃ f bs, q = (Term.app f bs, Term.app f bs) ∧ Term.app f bs ∈ Keys d := by
  obtain ⟨W, ⟨r, hr, σ, hσ, hW⟩, hqW⟩ := Set.mem_sUnion.mp hq
  rcases mem_maintenance.mp hr with rfl | rfl | ⟨fk, _, _, rfl⟩ | ⟨fk, _, _, rfl⟩
  · obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hnc⟩ := compress_inv hσ
    rw [compress_writes ha hb hc] at hW
    obtain rfl := Option.some.inj hW
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hqW
    rcases hqW with rfl | rfl
    · exact Or.inl ⟨a, b, rfl, .old (h.row_of_edge hab)⟩
    · exact Or.inl ⟨a, c, rfl, .compress hab hbc
        (ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hab)) hnc)⟩
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hmin, hnc⟩ := collide_inv h.diag hσ
    rw [collide_writes ha hb hc] at hW
    obtain rfl := Option.some.inj hW
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hqW
    rcases hqW with rfl | rfl
    · exact Or.inl ⟨a, c, rfl, .old (h.row_of_edge hac)⟩
    · exact Or.inl ⟨c, b, rfl, .collide hab hac hmin
        (ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hab)) hnc)⟩
  · obtain ⟨as, bs, rs, y, z, _, _, _, hy, hz, hra, hrb, hey, hez, hmin, hnc⟩ :=
      congruence_inv h.diag h.shape hσ
    rw [congruence_writes hy hz] at hW
    obtain rfl := Option.some.inj hW
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hqW
    subst hqW
    exact Or.inl ⟨z, y, rfl, .congr hra hrb hey hez hmin
      (ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hey)) hnc)⟩
  · obtain ⟨as, bs, rs, _, hbs, _, hm, hl, _, _⟩ := subsume_inv h.diag h.shape hσ
    rw [subsume_writes hbs] at hW
    obtain rfl := Option.some.inj hW
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hqW
    subst hqW
    exact Or.inr ⟨fk.1, bs, rfl, subsume_key h hm hl⟩

theorem mem_runMarks_maint (h : Rel sub src d) {t : Term} (ht : t ∈ RunMarks (maintenance sub P) d) :
    (∃ k p q, t = ufRowT k p ∧ Edge d k p ∧ Term.blt q p = true ∧
      Row (RunRules (maintenance sub P) d) k q ∧ Row (RunRules (maintenance sub P) d) p q) ∨
    ∃ f bs as, t = Term.app f bs ∧ Term.app f bs ∈ Keys d ∧ Marker d f as ∧
      CongList src as bs := by
  have heqs : (RunRules (maintenance sub P) d).eqs = d.eqs ∪ RunWrites (maintenance sub P) d := by
    rw [RunRules.eq_pair]
  obtain ⟨X, ⟨r, hr, σ, hσ, hX⟩, htX⟩ := Set.mem_sUnion.mp ht
  have hwrite : ∀ W, Action.writes σ r.actions = some W → W ⊆ RunWrites (maintenance sub P) d :=
    fun W hW q hq => Set.mem_sUnion.mpr ⟨W, ⟨r, hr, σ, hσ, hW⟩, hq⟩
  rcases mem_maintenance.mp hr with rfl | rfl | ⟨fk, _, _, rfl⟩ | ⟨fk, _, _, rfl⟩
  · obtain ⟨a, b, c, ha, hb, hc, hab, hbc, hnc⟩ := compress_inv hσ
    rw [compress_marks ha hb (by rw [hc]; rfl)] at hX
    obtain rfl := Option.some.inj hX
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at htX
    subst htX
    have hne : b ≠ c := ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hab)) hnc
    refine Or.inl ⟨a, b, c, rfl, hab, ?_, ?_, ?_⟩
    · rcases h.edge_down hbc with heq | hlt
      · exact (hne heq.symm).elim
      · exact hlt
    · change (ufRowT a c, ufRowT a c) ∈ (RunRules (maintenance sub P) d).eqs
      rw [heqs]
      exact Or.inr (hwrite _ (compress_writes ha hb hc) (by simp))
    · exact (h.row_of_edge hbc).mono (heqs ▸ Set.subset_union_left)
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hmin, hnc⟩ := collide_inv h.diag hσ
    rw [collide_marks ha hb hc] at hX
    obtain rfl := Option.some.inj hX
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at htX
    subst htX
    have hne : b ≠ c := ne_of_not_cong (Keys.subset_terms d (h.parent_of_edge hab)) hnc
    refine Or.inl ⟨a, c, b, rfl, hac, ?_, ?_, ?_⟩
    · rw [Term.least_eq_ite] at hmin
      by_contra hlt
      rw [if_neg hlt] at hmin
      exact hne hmin
    · exact (h.row_of_edge hab).mono (heqs ▸ Set.subset_union_left)
    · change (ufRowT c b, ufRowT c b) ∈ (RunRules (maintenance sub P) d).eqs
      rw [heqs]
      exact Or.inr (hwrite _ (collide_writes ha hb hc) (by simp))
  · obtain ⟨as, bs, rs, y, z, _, _, _, hy, hz, -⟩ := congruence_inv h.diag h.shape hσ
    rw [congruence_marks hy hz] at hX
    obtain rfl := Option.some.inj hX
    simp at htX
  · obtain ⟨as, bs, rs, _, hbs, _, hm, hl, hra, hrb⟩ := subsume_inv h.diag h.shape hσ
    rw [subsume_marks hbs] at hX
    obtain rfl := Option.some.inj hX
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at htX
    subst htX
    exact Or.inr ⟨fk.1, bs, as, rfl, subsume_key h hm hl, hm, congList_of_edges h hra hrb⟩

namespace MaintRow

variable (h : Rel sub src d)
include h

theorem key_mem {k p : Term} (hm : MaintRow d k p) : k ∈ Keys d := by
  cases hm with
  | old hr => exact hr.mem_keys
  | compress hab _ _ => exact h.key_of_edge hab
  | collide _ hac _ _ => exact h.parent_of_edge hac
  | congr _ _ _ hez _ _ => exact h.parent_of_edge hez

theorem parent_mem {k p : Term} (hm : MaintRow d k p) : p ∈ Keys d := by
  cases hm with
  | old hr => exact h.parent_mem_keys hr
  | compress _ hbc _ => exact h.parent_of_edge hbc
  | collide hab _ _ _ => exact h.parent_of_edge hab
  | congr _ _ hey _ _ _ => exact h.parent_of_edge hey

theorem down {k p : Term} (hm : MaintRow d k p) : p = k ∨ Term.blt p k = true := by
  cases hm with
  | old hr => exact h.down _ _ hr
  | @compress _ b _ hab hbc hne =>
    have hcb : Term.blt p b = true := by
      rcases h.edge_down hbc with heq | hlt
      · exact (hne heq.symm).elim
      · exact hlt
    rcases h.edge_down hab with rfl | hba
    · exact Or.inr hcb
    · exact Or.inr (Term.blt_trans _ _ _ hcb hba)
  | collide _ _ hmin hne =>
    right
    rw [Term.least_eq_ite] at hmin
    by_contra hlt
    rw [if_neg hlt] at hmin
    exact hne hmin
  | congr _ _ _ _ hmin hne =>
    right
    rw [Term.least_eq_ite] at hmin
    by_contra hlt
    rw [if_neg hlt] at hmin
    exact hne hmin

/-- Every row a maintenance firing asserts is already derivable from the rows. -/
theorem cong_view {k p : Term} (hm : MaintRow d k p) : Cong (view d) k p := by
  cases hm with
  | old hr => exact hr.cong_view
  | compress hab hbc _ =>
    exact (h.row_of_edge hab).cong_view.trans (h.row_of_edge hbc).cong_view
  | collide hab hac _ _ =>
    exact (h.row_of_edge hac).cong_view.symm.trans (h.row_of_edge hab).cong_view
  | @congr f as bs rs _ _ hra hrb hey hez _ _ =>
    have hself : Cong (view d) (.app f as) (.app f as) :=
      (h.selfLoop _ _ (h.row_of_edge hey)).1.cong_view
    have hargs : CongList (view d) as bs := by
      rw [CongList.forall₂]
      have h₁ : List.Forall₂ (fun a r => Cong (view d) a r) as rs :=
        hra.imp fun _ _ he => (h.row_of_edge he).cong_view
      have h₂ : List.Forall₂ (fun b r => Cong (view d) b r) bs rs :=
        hrb.imp fun _ _ he => (h.row_of_edge he).cong_view
      rw [List.forall₂_iff_get] at h₁ h₂ ⊢
      refine ⟨h₁.1.trans h₂.1.symm, fun i h₁' h₂' => ?_⟩
      exact (h₁.2 i h₁' (h₁.1 ▸ h₁')).trans (h₂.2 i h₂' (h₂.1 ▸ h₂')).symm
    have hab : Cong (view d) (.app f as) (.app f bs) := .congr hself hargs
    exact ((h.row_of_edge hez).cong_view.symm.trans hab.symm).trans
      (h.row_of_edge hey).cong_view

end MaintRow

/-- One maintenance round preserves the simulation relation. -/
theorem maint_round (h : Rel sub src d) : Rel sub src (RunRules (maintenance sub P) d) := by
  set d' := RunRules (maintenance sub P) d with hd'
  have heqs : d'.eqs = d.eqs ∪ RunWrites (maintenance sub P) d := by rw [hd', RunRules.eq_pair]
  have hsub : d'.subsumed = d.subsumed ∪ RunMarks (maintenance sub P) d := by
    rw [hd', RunRules.eq_pair]
  have hmono : d.eqs ⊆ d'.eqs := heqs ▸ Set.subset_union_left
  have hkeys_mono : Keys d ⊆ Keys d' := Keys.mono hmono
  -- Every new equation is a union-find row of a maintenance firing or the self-pair of a key.
  have hnew : ∀ q ∈ d'.eqs, q ∈ d.eqs ∨ (∃ k p, q = (ufRowT k p, ufRowT k p) ∧ MaintRow d k p) ∨
      ∃ f bs, q = (Term.app f bs, Term.app f bs) ∧ Term.app f bs ∈ Keys d := by
    intro q hq
    have hq' : q ∈ d.eqs ∪ RunWrites (maintenance sub P) d := heqs ▸ hq
    rcases hq' with hq' | hq'
    · exact Or.inl hq'
    · exact Or.inr (mem_runWrites_maint h hq')
  have hrow : ∀ k p, Row d' k p → MaintRow d k p := by
    intro k p hr
    rcases hnew _ hr with hr' | ⟨k', p', heq, hm⟩ | ⟨f, bs, heq, hkey⟩
    · exact .old hr'
    · obtain ⟨rfl, rfl⟩ := ufRowT_inj (Prod.mk.inj heq).1
      exact hm
    · exact (Term.SourceShaped.ne_ufRowT (h.shape.keys _ hkey) k p (Prod.mk.inj heq).1.symm).elim
  have hnode : ∀ f as, Node d' f as ↔ Node d f as := by
    intro f as
    refine ⟨fun hn => ?_, fun hn => hn.mono hmono⟩
    rcases hnew _ hn with hn' | ⟨k, p, heq, _⟩ | ⟨g, bs, heq, hkey⟩
    · exact hn'
    · exact (nodeName_ne_ufName f (Term.app.inj (Prod.mk.inj heq).1).1).elim
    · exact (Term.SourceShaped.ne_nodeRowT (h.shape.keys _ hkey) f as
        (Prod.mk.inj heq).1.symm).elim
  have hmarker : ∀ f as, Marker d' f as ↔ Marker d f as := by
    intro f as
    refine ⟨fun hm => ?_, fun hm => hm.mono hmono⟩
    rcases hnew _ hm with hm' | ⟨k, p, heq, _⟩ | ⟨g, bs, heq, hkey⟩
    · exact hm'
    · exact (subName_ne_ufName f (Term.app.inj (Prod.mk.inj heq).1).1).elim
    · exact (Term.SourceShaped.ne_subRowT (h.shape.keys _ hkey) f as
        (Prod.mk.inj heq).1.symm).elim
  have hdiag : d'.Diag := by
    intro q hq
    rcases hnew q hq with hq' | ⟨k, p, rfl, _⟩ | ⟨f, bs, rfl, _⟩
    · exact h.diag q hq'
    · rfl
    · rfl
  have hkeys : Keys d' = Keys d := by
    apply Set.Subset.antisymm
    · rintro k ⟨p, hr⟩
      exact (hrow k p hr).key_mem h
    · exact hkeys_mono
  have hself : ∀ k p, Row d' k p → Row d' k k ∧ Row d' p p := by
    intro k p hr
    have hm := hrow k p hr
    obtain ⟨q₁, hk⟩ := hm.key_mem h
    obtain ⟨q₂, hp⟩ := hm.parent_mem h
    exact ⟨(h.selfLoop _ _ hk).1.mono hmono, (h.selfLoop _ _ hp).1.mono hmono⟩
  have hshape : Shape d' := by
    refine ⟨fun q hq => ?_, fun k hk => h.shape.keys k (hkeys ▸ hk), fun k p hr => ?_,
      fun f as hn => ?_, fun f as hm => ?_⟩
    · rcases hnew q hq with hq' | ⟨k, p, rfl, _⟩ | ⟨f, bs, rfl, hkey⟩
      · rcases h.shape.eqs q hq' with hq' | hq' | hq' | ⟨t, rfl, ht⟩
        · exact Or.inl hq'
        · exact Or.inr (Or.inl hq')
        · exact Or.inr (Or.inr (Or.inl hq'))
        · exact Or.inr (Or.inr (Or.inr ⟨t, rfl, hkeys_mono ht⟩))
      · exact Or.inl ⟨k, p, rfl⟩
      · exact Or.inr (Or.inr (Or.inr ⟨_, rfl, hkeys_mono hkey⟩))
    · exact hkeys_mono ((hrow k p hr).parent_mem h)
    · exact hkeys_mono (h.shape.nodes f as ((hnode f as).mp hn))
    · exact hkeys_mono (h.shape.markers f as ((hmarker f as).mp hm))
  have hcong : ∀ a b, Cong src a b ↔ Cong (view d') a b := by
    intro a b
    rw [h.cong]
    constructor
    · exact Cong.mono_eqs (view_mono hmono)
    · exact fun hab => Cong.replay (D := view d') (E := view d)
        (fun q hq => (hrow q.1 q.2 hq).cong_view h) hab
  -- No new union-find row is marked but by a firing with a smaller replacement.
  have huf_marks : ∀ k p, ufRowT k p ∈ RunMarks (maintenance sub P) d →
      ∃ q, Edge d k p ∧ Term.blt q p = true ∧ Row d' k q ∧ Row d' p q := by
    intro k p hs
    rcases mem_runMarks_maint h hs with ⟨k', p', q, heq, he, hlt, hkq, hpq⟩ |
      ⟨f, bs, as, heq, hkey, -, -⟩
    · obtain ⟨rfl, rfl⟩ := ufRowT_inj heq
      exact ⟨q, he, hlt, hkq, hpq⟩
    · exact (Term.SourceShaped.ne_ufRowT (h.shape.keys _ hkey) k p heq.symm).elim
  have hlive : ∀ p ∈ Keys d, ∀ k, Row d' k p → Cong (liveView d') k p := by
    intro p hp
    refine (h.keys_finite.wellFoundedOn (r := fun s t => Term.blt s t = true)).induction hp
      (P := fun p => ∀ k, Row d' k p → Cong (liveView d') k p) ?_
    intro p _ ih k hkp
    by_cases hs : ufRowT k p ∈ d'.subsumed
    · rw [hsub] at hs
      rcases hs with hs | hs
      · obtain ⟨q, _, hkq, hpq, hlt⟩ := h.uf_mark hs
        have hq : q ∈ Keys d := h.parent_mem_keys hkq
        exact (ih q hq hlt k (hkq.mono hmono)).trans (ih q hq hlt p (hpq.mono hmono)).symm
      · obtain ⟨q, _, hlt, hkq, hpq⟩ := huf_marks k p hs
        have hq : q ∈ Keys d := hkeys ▸ (hself _ _ hkq).2.mem_keys
        exact (ih q hq hlt k hkq).trans (ih q hq hlt p hpq).symm
    · exact (Edge.of_row hdiag hshape hkp hs).cong_liveView
  exact {
    diag := hdiag
    shape := hshape
    finite := RunRules.finite_eqs h.finite _
    marks := by
      intro t ht
      rw [hsub] at ht
      rcases ht with ht | ht
      · rcases h.marks t ht with ⟨k, p, q, heq, hkp, hkq, hpq, hlt⟩ |
          ⟨f, bs, as, heq, hkey, hm, hc⟩
        · exact Or.inl ⟨k, p, q, heq, hkp.mono hmono, hkq.mono hmono, hpq.mono hmono, hlt⟩
        · exact Or.inr ⟨f, bs, as, heq, hkeys_mono hkey, hm.mono hmono, hc⟩
      · rcases mem_runMarks_maint h ht with ⟨k, p, q, heq, hkp, hlt, hkq, hpq⟩ |
          ⟨f, bs, as, heq, hkey, hm, hc⟩
        · exact Or.inl ⟨k, p, q, heq, (h.row_of_edge hkp).mono hmono, hkq, hpq, hlt⟩
        · exact Or.inr ⟨f, bs, as, heq, hkeys_mono hkey, hm.mono hmono, hc⟩
    down := fun k p hr => (hrow k p hr).down h
    selfLoop := hself
    keys := hkeys.trans h.keys
    nodes := fun f as hk hon => (h.nodes f as (hkeys ▸ hk) hon).mono hmono
    plain := h.plain
    marker := fun f as => (hmarker f as).trans (h.marker f as)
    cong := hcong
    liveCong := fun k p hr => hlive p (hkeys ▸ (hself k p hr).2.mem_keys) k hr }

/-- Rows only grow along a maintenance round. -/
theorem maint_eqs_mono (d : Database) : d.eqs ⊆ (RunRules (maintenance sub P) d).eqs := by
  rw [RunRules.eq_pair]; exact Set.subset_union_left

theorem maint_subsumed_mono (d : Database) :
    d.subsumed ⊆ (RunRules (maintenance sub P) d).subsumed := by
  rw [RunRules.eq_pair]; exact Set.subset_union_left

/-- The keys are unchanged by a maintenance round. -/
theorem maint_keys (h : Rel sub src d) : Keys (RunRules (maintenance sub P) d) = Keys d :=
  (maint_round (P := P) h).keys.trans h.keys.symm

end Egglog.Congruence
