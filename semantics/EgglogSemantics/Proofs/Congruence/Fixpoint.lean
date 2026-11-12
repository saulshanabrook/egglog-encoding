import EgglogSemantics.Proofs.Congruence.Maintenance
import EgglogSemantics.Proofs.Congruence.Firing
import EgglogSemantics.Proofs.FiniteSaturation
import EgglogSemantics.Proofs.DiagonalRound
import Mathlib.Data.Set.Card

/-! Termination of rebuild saturation and canonicality of its result: every key has one
live edge to a root, congruent applications share a root, and every application whose
children have the roots of a marked spelling's is subsumed. -/

namespace Egglog.Congruence

variable {sub : Bool}

variable {P : Program} {src d : Database}

/-- A row marked by some firing of the round is not live afterwards. -/
theorem not_live_of_runMarks {f : FnName} {ts : List Term}
    (ht : Term.app f ts ∈ RunMarks (maintenance sub P) d) :
    Term.app f ts ∉ (RunRules (maintenance sub P) d).live :=
  not_live_of_subsumed (by rw [RunRules.eq_pair]; exact Or.inr ht)

/-- The write set of a firing is among the round's writes. -/
theorem writes_subset_runWrites {R : List Rule} {d : Database} {r : Rule} (hr : r ∈ R) {σ : Env}
    (hσ : QueryMatches d r.query σ) {W : Set (Term × Term)}
    (hW : Action.writes σ r.actions = some W) : W ⊆ RunWrites R d :=
  fun _ hq => Set.mem_sUnion.mpr ⟨W, ⟨r, hr, σ, hσ, hW⟩, hq⟩

theorem marks_subset_runMarks {R : List Rule} {d : Database} {r : Rule} (hr : r ∈ R) {σ : Env}
    (hσ : QueryMatches d r.query σ) {X : Set Term}
    (hX : Action.marks σ r.actions = some X) : X ⊆ RunMarks R d :=
  fun _ ht => Set.mem_sUnion.mpr ⟨X, ⟨r, hr, σ, hσ, hX⟩, ht⟩

theorem least_swap {p q : Term} (hl : Term.least p q = q) (hne : p ≠ q) : q = Term.least q p := by
  rw [Term.least_eq_ite] at hl ⊢
  have hnpq : ¬ Term.blt p q = true := by
    intro hpq
    rw [if_pos hpq] at hl
    exact hne hl
  rcases Term.blt_total p q hne with hpq | hqp
  · exact (hnpq hpq).elim
  · rw [if_pos hqp]

/-- A meaning-preserving maintenance round means no maintenance rule fires: the state is
canonical. -/
theorem canon_of_fixpoint (h : Rel sub src d) (hcs : src.CtorsIn P)
    (hfix : d.SameMeaning (RunRules (maintenance sub P) d)) : Canon d := by
  have h' := maint_round (P := P) h
  have hterms_eq := hfix.terms_eq_of_diag h.diag h'.diag
  -- Two live edges of one key collide.
  have unique : ∀ k p q, Edge d k p → Edge d k q → p = q := by
    intro k p q hp hq
    by_contra hne
    have main : ∀ p q, Edge d k p → Edge d k q → p = Term.least p q → p ≠ q → False := by
      intro p q hp hq hmin hne
      have hfire := collide_fire h.diag hp hq hmin hne (Keys.subset_terms d (h.key_of_edge hp))
        (Keys.subset_terms d (h.parent_of_edge hp)) (Keys.subset_terms d (h.parent_of_edge hq))
      have hmark : ufRowT k q ∈ RunMarks (maintenance sub P) d :=
        marks_subset_runMarks (mem_maintenance.mpr (Or.inr (Or.inl rfl))) hfire
          (collide_marks (ufEnv_lookup_a k p q) (ufEnv_lookup_b k p q) (ufEnv_lookup_c k p q))
          (by simp)
      exact not_live_of_runMarks hmark ((hfix.live _).mp hq)
    rcases Term.least_eq_or p q with hl | hl
    · exact main p q hp hq hl.symm hne
    · exact main q p hq hp (least_swap hl hne) (Ne.symm hne)
  -- A live parent is a root.
  have root : ∀ k p, Edge d k p → Edge d p p := by
    intro k p hkp
    obtain ⟨m, hpm, _⟩ := h.least_parent (h.parent_of_edge hkp)
    by_cases hmp : p = m
    · exact hmp ▸ hpm
    · exfalso
      have hfire := compress_fire h.diag hkp hpm hmp (Keys.subset_terms d (h.key_of_edge hkp))
        (Keys.subset_terms d (h.parent_of_edge hkp)) (Keys.subset_terms d (h.parent_of_edge hpm))
      have hmark : ufRowT k p ∈ RunMarks (maintenance sub P) d :=
        marks_subset_runMarks (mem_maintenance.mpr (Or.inl rfl)) hfire
          (compress_marks (ufEnv_lookup_a k p m) (ufEnv_lookup_b k p m)
            (by rw [ufEnv_lookup_c]; rfl)) (by simp)
      exact not_live_of_runMarks hmark ((hfix.live _).mp hkp)
  refine ⟨unique, root, ?_, ?_⟩
  · intro f as bs rs y z hka hkb hra hrb hey hez
    by_contra hne
    have main : ∀ (as bs : List Term) (y z : Term), Term.app f as ∈ Keys d →
        Term.app f bs ∈ Keys d → List.Forall₂ (Edge d) as rs → List.Forall₂ (Edge d) bs rs →
        Edge d (.app f as) y → Edge d (.app f bs) z → y = Term.least y z → y ≠ z → False := by
      intro as bs y z hka hkb hra hrb hey hez hmin hne
      by_cases hn : as.length = 0
      · have has : as = [] := List.length_eq_zero_iff.mp hn
        have hbs : bs = [] :=
          List.length_eq_zero_iff.mp (hrb.length_eq.trans (hra.length_eq.symm.trans hn))
        subst has hbs
        exact hne (unique _ _ _ hey hez)
      · have hctor : (f, as.length) ∈ P.ctors := hcs f as (h.key_mem_src hka)
        have hrule : congruenceRule sub f as.length ∈ maintenance sub P :=
          mem_maintenance.mpr (Or.inr (Or.inr (Or.inl ⟨(f, as.length), hctor, hn, rfl⟩)))
        obtain ⟨σ, hfire, hy, hz⟩ := congruence_fire h hra hrb hey hez hmin hne
        have hwrite : (ufRowT z y, ufRowT z y) ∈ RunWrites (maintenance sub P) d :=
          writes_subset_runWrites hrule hfire
            (congruence_writes (f := f) (n := as.length) hy hz)
            (by simp)
        have hmem : ufRowT z y ∈ (RunRules (maintenance sub P) d).terms := by
          refine ⟨(ufRowT z y, ufRowT z y), ?_, Or.inl (Term.self_mem_subterms _)⟩
          rw [RunRules.eq_pair]
          exact Or.inr hwrite
        rw [← hterms_eq, h.shape.uf_mem_terms_iff] at hmem
        obtain ⟨m, hzm, hleast⟩ := h.least_parent (h.parent_of_edge hez)
        have hmz : m = z := unique z m z hzm (root _ _ hez)
        subst hmz
        have hyz : Term.blt y m = true := by
          rw [Term.least_eq_ite] at hmin
          by_contra hlt
          rw [if_neg hlt] at hmin
          exact hne hmin
        rcases hleast y hmem with heq | hlt
        · exact hne heq.symm
        · rw [Term.blt_asymm _ _ hlt] at hyz
          exact Bool.false_ne_true hyz
    rcases Term.least_eq_or y z with hl | hl
    · exact main as bs y z hka hkb hra hrb hey hez hl.symm hne
    · exact main bs as z y hkb hka hrb hra hez hey (least_swap hl hne) (Ne.symm hne)
  · intro f as bs rs hm hkb hra hrb
    by_contra hns
    have hl : Term.app f bs ∈ d.live :=
      (Congruence.app_live_iff h.diag).mpr ⟨Keys.subset_terms d hkb, hns⟩
    have hctor : (f, as.length) ∈ P.ctors := hcs f as (h.key_mem_src (h.marker_key hm))
    have hon : sub = true := by
      cases hs : sub
      · have hm' := h.marker_src hm
        rw [h.plain hs] at hm'
        exact hm'.elim
      · rfl
    have hrule : subsumeRule f as.length ∈ maintenance sub P :=
      mem_maintenance.mpr (Or.inr (Or.inr (Or.inr ⟨(f, as.length), hctor, hon, rfl⟩)))
    have hfire := subsume_fire h hm hl hra hrb
    have hlb : bs.length = as.length := hrb.length_eq.trans hra.length_eq.symm
    have hbs : Expr.evalList (congruenceVars "b" as.length) (subEnv as bs rs as.length) =
        some bs :=
      evalList_congruenceVars hlb fun i hi => subEnv_lookup_b hlb hi
    have hmark : Term.app f bs ∈ RunMarks (maintenance sub P) d :=
      marks_subset_runMarks hrule hfire (subsume_marks (f := f) hbs) (by simp)
    exact not_live_of_runMarks hmark ((hfix.live _).mp hl)

/-- At a meaning-preserving round the next round changes nothing at all. -/
theorem fixpoint_stable (h : Rel sub src d)
    (hfix : d.SameMeaning (RunRules (maintenance sub P) d)) :
    RunRules (maintenance sub P) (RunRules (maintenance sub P) d) = RunRules (maintenance sub P) d := by
  have h' := maint_round (P := P) h
  have hterms := hfix.terms_eq_of_diag h.diag h'.diag
  have hw := RunWrites.eq_of_sameMeaning_terms hfix hterms (maintenance sub P)
  have hm := RunMarks.eq_of_sameMeaning_terms hfix hterms (maintenance sub P)
  conv_lhs => rw [RunRules.eq_pair]
  rw [← hw, ← hm]
  apply Database.ext
  · change (RunRules (maintenance sub P) d).eqs ∪ _ = (RunRules (maintenance sub P) d).eqs
    rw [RunRules.eq_pair]
    exact Set.union_eq_left.mpr Set.subset_union_right
  · change (RunRules (maintenance sub P) d).subsumed ∪ _ = (RunRules (maintenance sub P) d).subsumed
    rw [RunRules.eq_pair]
    exact Set.union_eq_left.mpr Set.subset_union_right

/-! ### Termination -/

/-- Rows only grow along a schedule. -/
theorem Reach.contained {S : Schedule} {d e : Database} (h : Reach d S e) : d.Contained e := by
  induction h with
  | run => rw [RunRules.eq_pair]; exact ⟨Set.subset_union_left, Set.subset_union_left⟩
  | seq _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | fixpoint _ _ ih => exact ih
  | again _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The rows of a state: the terms asserted reflexively. -/
def rowsOf (e : Database) : Set Term := {t | (t, t) ∈ e.eqs}

theorem rowsOf_mono {d e : Database} (h : d.eqs ⊆ e.eqs) : rowsOf d ⊆ rowsOf e :=
  fun _ ht => h ht

theorem rowsOf_finite {d : Database} (h : d.eqs.Finite) : (rowsOf d).Finite :=
  (h.image Prod.fst).subset fun t ht => ⟨(t, t), ht, rfl⟩

/-- On diagonal states the rows determine the equations. -/
theorem eqs_eq_of_rowsOf_eq {d e : Database} (hd : d.Diag) (he : e.Diag)
    (h : rowsOf d = rowsOf e) : d.eqs = e.eqs := by
  ext q
  constructor
  · intro hq
    obtain ⟨t, u⟩ := q
    obtain rfl : t = u := hd _ hq
    exact (show t ∈ rowsOf e from h ▸ hq)
  · intro hq
    obtain ⟨t, u⟩ := q
    obtain rfl : t = u := he _ hq
    exact (show t ∈ rowsOf d from h ▸ hq)

/-- The node row and the marker of a source application, and the term itself otherwise. -/
def nodeOf : Term → Term
  | .app f as => nodeRowT f as
  | t => t

def markerOf : Term → Term
  | .app f as => subRowT f as
  | t => t

/-- Everything a compiled state over the source terms `U` can hold or mark: union-find rows
over `U`, the terms of `U`, and their node rows and markers. -/
def rowSpace (U : Set Term) : Set Term :=
  Set.image2 ufRowT U U ∪ U ∪ nodeOf '' U ∪ markerOf '' U

theorem rowSpace_finite {U : Set Term} (hU : U.Finite) : (rowSpace U).Finite :=
  (((hU.image2 ufRowT hU).union hU).union (hU.image nodeOf)).union (hU.image markerOf)

/-- The rows and marks of a related compiled state lie in the universe of its source
terms. -/
theorem rows_subset_rowSpace {x e : Database} (hre : Rel sub x e) {U : Set Term}
    (hU : ∀ t ∈ x.terms, t ∈ U) : rowsOf e ⊆ rowSpace U ∧ e.subsumed ⊆ rowSpace U := by
  have hkeys : ∀ k ∈ Keys e, k ∈ U := fun k hk => hU k (hre.key_mem_src hk)
  constructor
  · intro t ht
    rcases hre.shape.eqs _ ht with ⟨k, p, heq⟩ | ⟨f, as, heq⟩ | ⟨f, as, heq⟩ | ⟨u, heq, hu⟩
    · obtain rfl : t = ufRowT k p := (Prod.mk.inj heq).1
      have hr : Row e k p := ht
      exact Or.inl (Or.inl (Or.inl ⟨k, hkeys k hr.mem_keys, p, hkeys p (hre.parent_mem_keys hr),
        rfl⟩))
    · obtain rfl : t = nodeRowT f as := (Prod.mk.inj heq).1
      have hn : Node e f as := ht
      exact Or.inl (Or.inr ⟨.app f as, hkeys _ (hre.shape.nodes f as hn), rfl⟩)
    · obtain rfl : t = subRowT f as := (Prod.mk.inj heq).1
      have hm : Marker e f as := ht
      exact Or.inr ⟨.app f as, hkeys _ (hre.shape.markers f as hm), rfl⟩
    · obtain rfl : t = u := (Prod.mk.inj heq).1
      exact Or.inl (Or.inl (Or.inr (hkeys t hu)))
  · intro t ht
    rcases hre.marks t ht with ⟨k, p, q, rfl, hkp, -⟩ | ⟨f, bs, as, rfl, hkey, -, -⟩
    · exact Or.inl (Or.inl (Or.inl ⟨k, hkeys k hkp.mem_keys, p, hkeys p (hre.parent_mem_keys hkp),
        rfl⟩))
    · exact Or.inl (Or.inl (Or.inr (hkeys _ hkey)))

/-- The measure of a compiled state inside a finite universe: the rows not yet asserted and
the rows not yet marked. -/
noncomputable def rank (V : Set Term) (e : Database) : Nat :=
  (V \ rowsOf e).ncard + (V \ e.subsumed).ncard

/-- A meaning-changing step of a diagonal state inside the universe lowers the rank. -/
theorem rank_lt {V : Set Term} (hV : V.Finite) {d d' : Database} (hd : d.Diag)
    (hd' : d'.Diag) (hrows : rowsOf d' ⊆ V) (hmarks : d'.subsumed ⊆ V)
    (heqs : d.eqs ⊆ d'.eqs) (hsub : d.subsumed ⊆ d'.subsumed) (hne : ¬ d.SameMeaning d') :
    rank V d' < rank V d := by
  classical
  have hdiff : d.eqs ≠ d'.eqs ∨ d.subsumed ≠ d'.subsumed := by
    by_contra hc
    push Not at hc
    have : d = d' := Database.ext hc.1 hc.2
    exact hne (this ▸ Database.SameMeaning.refl d)
  have hle₁ : (V \ rowsOf d').ncard ≤ (V \ rowsOf d).ncard :=
    Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right (rowsOf_mono heqs)) hV.sdiff
  have hle₂ : (V \ d'.subsumed).ncard ≤ (V \ d.subsumed).ncard :=
    Set.ncard_le_ncard (Set.sdiff_subset_sdiff_right hsub) hV.sdiff
  unfold rank
  rcases hdiff with hdiff | hdiff
  · have hss : V \ rowsOf d' ⊂ V \ rowsOf d := by
      refine LE.le.ssubset_of_ne (Set.sdiff_subset_sdiff_right (rowsOf_mono heqs)) ?_
      intro heq
      apply hdiff
      apply eqs_eq_of_rowsOf_eq hd hd'
      apply Set.Subset.antisymm (rowsOf_mono heqs)
      intro t ht
      by_contra hnt
      have h₁ : t ∈ V \ rowsOf d := ⟨hrows ht, hnt⟩
      rw [← heq] at h₁
      exact h₁.2 ht
    have := Set.ncard_lt_ncard hss hV.sdiff
    omega
  · have hss : V \ d'.subsumed ⊂ V \ d.subsumed := by
      refine LE.le.ssubset_of_ne (Set.sdiff_subset_sdiff_right hsub) ?_
      intro heq
      apply hdiff
      apply Set.Subset.antisymm hsub
      intro t ht
      by_contra hnt
      have h₁ : t ∈ V \ d.subsumed := ⟨hmarks ht, hnt⟩
      rw [← heq] at h₁
      exact h₁.2 ht
    have := Set.ncard_lt_ncard hss hV.sdiff
    omega

/-- Along maintenance rounds the relation and the keys are kept. -/
theorem rel_of_rounds (h : Rel sub src d) {e : Database}
    (he : Relation.ReflTransGen (fun a b => b = RunRules (maintenance sub P) a) d e) :
    Rel sub src e ∧ Keys e = Keys d := by
  induction he with
  | refl => exact ⟨h, rfl⟩
  | tail _ hbc ih =>
    subst hbc
    exact ⟨maint_round ih.1, (maint_keys ih.1).trans ih.2⟩

/-- The rebuild saturation reaches a state. -/
theorem rebuild_exists (h : Rel sub src d) : ∃ e, Reach d (.saturate (.run (maintenance sub P))) e := by
  classical
  have hV : (rowSpace src.terms).Finite := rowSpace_finite h.src_terms_finite
  apply saturateReach_exists_of_measure (maintenance sub P) d (rank (rowSpace src.terms))
  intro e he hne
  obtain ⟨hre, hkeys⟩ := rel_of_rounds h he
  have hre' := maint_round (P := P) hre
  obtain ⟨hrows, hmarks⟩ := rows_subset_rowSpace hre' fun t ht => ht
  exact rank_lt hV hre.diag hre'.diag hrows hmarks (maint_eqs_mono e) (maint_subsumed_mono e) hne

/-- The result of the rebuild saturation is related, canonical, and has the same keys. -/
theorem rebuild_rel (h : Rel sub src d) (hcs : src.CtorsIn P) {e : Database}
    (hr : Reach d (.saturate (.run (maintenance sub P))) e) :
    Rel sub src e ∧ Canon e ∧ Keys e = Keys d := by
  generalize hS : Schedule.saturate (.run (maintenance sub P)) = S at hr
  induction hr with
  | run => cases hS
  | seq => cases hS
  | @fixpoint d e S hp heq _ =>
    cases hS
    cases hp
    have he := maint_round (P := P) h
    refine ⟨he, ?_, maint_keys h⟩
    apply canon_of_fixpoint he hcs
    rw [fixpoint_stable h heq]
    exact Database.SameMeaning.refl _
  | @again d e _ S hp _ _ _ ih =>
    cases hS
    cases hp
    obtain ⟨h₁, h₂, h₃⟩ := ih (maint_round h) rfl
    exact ⟨h₁, h₂, h₃.trans (maint_keys h)⟩

end Egglog.Congruence
