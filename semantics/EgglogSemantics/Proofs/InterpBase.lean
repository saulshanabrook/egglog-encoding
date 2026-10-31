import EgglogSemantics.Impl.Observe
import EgglogSemantics.Proofs.Closure
import EgglogSemantics.Proofs.Scope
import EgglogSemantics.Proofs.SourceModel
import EgglogSemantics.Proofs.Schedule

/-! Finite-store denotation and the closure, index, and environment invariants used by
matching and execution. Denotation explicitly asserts held subterms. The index also
requires subsumed spellings to be held, so their children are available to finite closure. -/

namespace Egglog
theorem mem_closure_iff_of_diag {db : Database} {terms : Finset Term}
    {rel : Finset (Term × Term)} (hterms : db.terms = ↑terms) (h : rel ⊆ candidates terms)
    (hsub : ∀ p ∈ rel, p ∈ db.eqs) (hsup : ∀ p ∈ db.eqs, p.1 = p.2 ∨ p ∈ rel)
    {a b : Term} (ha : a ∈ db.terms) (hb : b ∈ db.terms) : (a, b) ∈ closure terms rel h ↔ Cong db a b := by
  have hdiag : ∀ t ∈ terms, (t, t) ∈ closure terms rel h := by
    intro t ht
    rw [← closure_fixpoint h]
    refine mem_congStep.mpr (Or.inr ⟨mem_candidates.mpr ⟨ht, ht⟩, ?_⟩)
    simp only [stepAdds, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inl (Or.inl trivial))
  refine ⟨fun hp =>
    closure_sound hterms rel h (fun p hp' => Cong.direct (hsub p hp')) (a, b) hp, fun hc => ?_⟩
  have hs := hc.toStored ha hb
  refine hs.le (R := fun x y => (x, y) ∈ closure terms rel h) ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    rcases hsup (x, y) hxy with heq | hmem
    · have hx : x ∈ db.terms := (StoredCong.direct hxy).mem_left
      have hxy' : x = y := heq
      rw [hterms] at hx
      exact hxy' ▸ hdiag x hx
    · exact subset_closure h hmem
  · intro x y hxy
    have hcand := mem_candidates.mp (closure_subset h hxy)
    rw [← closure_fixpoint h]
    refine mem_congStep.mpr (Or.inr ⟨mem_candidates.mpr ⟨hcand.2, hcand.1⟩, ?_⟩)
    simp only [stepAdds, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inl (Or.inr hxy))
  · intro x y z hxy hyz
    have hx := mem_candidates.mp (closure_subset h hxy)
    have hz := mem_candidates.mp (closure_subset h hyz)
    rw [← closure_fixpoint h]
    refine mem_congStep.mpr (Or.inr ⟨mem_candidates.mpr ⟨hx.1, hz.2⟩, ?_⟩)
    simp only [stepAdds, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inr ⟨y, hx.2, hxy, hyz⟩)
  · intro f as bs ha hb hz
    rw [← closure_fixpoint h]
    refine mem_congStep.mpr (Or.inr ⟨mem_candidates.mpr ?_, ?_⟩)
    · rw [hterms] at ha hb; exact ⟨ha, hb⟩
    · simp only [stepAdds, Bool.or_eq_true]
      exact Or.inr (congrPair_app_iff.mpr ⟨rfl, hz⟩)

  · intro t u ht hu
    have htm : t ∈ db.terms := by
      rw [hterms]
      exact (mem_candidates.mp (closure_subset h ht)).1
    apply hdiag u
    have hu := db.subtermClosed t htm hu
    rwa [hterms] at hu

namespace FDatabase

/-- Subterm closure is required to identify the denotation's terms with its finite list. -/
theorem toDatabase_terms {d : FDatabase} (hc : d.SubtermClosed) :
    d.toDatabase.terms = {t | t ∈ d.terms} := by
  ext t
  constructor
  · rintro ⟨p, hp, ht⟩
    have hh : p.1 ∈ d.terms ∧ p.2 ∈ d.terms := by
      rcases hp with ⟨he, hm⟩ | ⟨_, h1, h2⟩
      · exact ⟨hm, he ▸ hm⟩
      · exact ⟨h1, h2⟩
    rcases ht with ht | ht
    · exact hc _ hh.1 _ ((Term.mem_subtermList _).mpr ht)
    · exact hc _ hh.2 _ ((Term.mem_subtermList _).mpr ht)
  · intro ht
    exact ⟨(t,t), Or.inl ⟨rfl, ht⟩, Or.inl (.refl _)⟩

theorem mem_toDatabase_terms {d : FDatabase} (hc : d.SubtermClosed) {t : Term} :
    t ∈ d.toDatabase.terms ↔ t ∈ d.terms := by rw [toDatabase_terms hc]; rfl

theorem mem_toDatabase_eqs {d : FDatabase} {p : Term × Term} :
    p ∈ d.toDatabase.eqs ↔
      (p.1 = p.2 ∧ p.1 ∈ d.terms) ∨ (p ∈ d.eqs ∧ p.1 ∈ d.terms ∧ p.2 ∈ d.terms) := Iff.rfl

theorem finite_toDatabase (d : FDatabase) : d.toDatabase.eqs.Finite := by
  apply (((List.finite_toSet d.terms).image (fun t => (t, t))).union
    (List.finite_toSet d.eqs)).subset
  rintro ⟨a, b⟩ (⟨hab, ha⟩ | ⟨hp, _, _⟩)
  · exact Or.inl ⟨a, ha, Prod.ext rfl hab⟩
  · exact Or.inr hp

/-- **`Closed` is exactly what makes the restriction invisible.** Every lemma below
that pushes `toDatabase` through a writer is this fact plus set algebra. -/
theorem mem_toDatabase_eqs_of_closed {d : FDatabase} (he : d.Closed)
    {p : Term × Term} :
    p ∈ d.toDatabase.eqs ↔ (p.1 = p.2 ∧ p.1 ∈ d.terms) ∨ p ∈ d.eqs := by
  rw [mem_toDatabase_eqs]
  exact or_congr_right ⟨fun h => h.1, fun h => ⟨h, (he.eqs p h).1, (he.eqs p h).2⟩⟩

@[simp] theorem toDatabase_empty : empty.toDatabase = Database.empty := by
  ext <;> simp [empty, toDatabase, Database.empty]

theorem Closed.addTerms {d : FDatabase} (he : d.Closed) :
    ∀ ts : List Term, (d.addTerms ts).Closed := by
  intro ts
  induction ts generalizing d with
  | nil => exact he
  | cons t ts ih => exact ih (he.addTerm t)

theorem congr_of_assertions {d e : Database}
    (h : ∀ p ∈ d.eqs, Cong e p.1 p.2) {a b : Term} (hc : Cong d a b) : Cong e a b := by
  induction hc using Cong.rec (motive_2 := fun as bs _ => CongList e as bs) with
  | direct hp => exact h _ hp
  | child _ hs ih => exact .child ih hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | congr _ _ ih ih' => exact .congr ih ih'
  | nil => exact .nil
  | cons _ _ ih ih' => exact .cons ih ih'

theorem toDatabase_addTerm {d : FDatabase} (he : d.Closed) {t : Term} :
    (d.addTerm t).toDatabase.SameMeaning (d.toDatabase.addTerm t) := by
  refine Database.SameMeaning.of_congr (fun a b => ⟨congr_of_assertions ?_, congr_of_assertions ?_⟩) rfl
  · intro p hp
    rcases (mem_toDatabase_eqs_of_closed (he.addTerm t)).mp hp with ⟨hp, hm⟩ | hp
    · obtain ⟨x,y⟩ := p
      dsimp at hp hm ⊢
      subst y
      apply Database.toCong
      rcases (mem_addTerm_terms he.subterms).mp hm with hm | hm
      · exact Database.addTerm_terms ▸ Or.inr ((Term.mem_subtermList _).mp hm)
      · exact Database.addTerm_terms ▸ Or.inl ((mem_toDatabase_terms he.subterms).mpr hm)
    · exact (Cong.direct ((mem_toDatabase_eqs_of_closed he).mpr (Or.inr hp))).mono
        (Database.Contained.addTerm t _)
  · rintro p (rfl | hp)
    · exact Cong.direct (Or.inl ⟨rfl, self_mem_addTerm d t⟩)
    · exact Cong.direct ((mem_toDatabase_eqs_of_closed (he.addTerm t)).mpr
        ((mem_toDatabase_eqs_of_closed he).mp hp |>.imp
          (fun h => ⟨h.1, mem_addTerm_of_mem h.2⟩) id))

theorem meaning_addEqs {d e : Database} (h : d.SameMeaning e) (W : Set (Term × Term)) (hX : d.subsumed = e.subsumed) :
    (d.addEqs W).SameMeaning (e.addEqs W) := by
  refine Database.SameMeaning.of_congr (fun a b => ⟨congr_of_assertions ?_, congr_of_assertions ?_⟩) hX
  · rintro p (hp | hp)
    · exact ((h.congr _ _).mp (.direct hp)).mono_eqs Set.subset_union_left
    · exact .direct (Or.inr hp)
  · rintro p (hp | hp)
    · exact ((h.congr _ _).mpr (.direct hp)).mono_eqs Set.subset_union_left
    · exact .direct (Or.inr hp)

theorem meaning_addTerm {d e : Database} (h : d.SameMeaning e) (t : Term) (hX : d.subsumed = e.subsumed) :
    (d.addTerm t).SameMeaning (e.addTerm t) := by
  refine Database.SameMeaning.of_congr (fun a b => ⟨congr_of_assertions ?_, congr_of_assertions ?_⟩) hX
  · rintro p (rfl | hp)
    · exact .direct (Set.mem_insert _ _)
    · exact ((h.congr _ _).mp (.direct hp)).mono (Database.Contained.addTerm t e)
  · rintro p (rfl | hp)
    · exact .direct (Set.mem_insert _ _)
    · exact ((h.congr _ _).mpr (.direct hp)).mono (Database.Contained.addTerm t d)

theorem meaning_addTerms {d e : Database} (h : d.SameMeaning e) (ts : List Term) (hX : d.subsumed = e.subsumed) :
    (d.addTerms ts).SameMeaning (e.addTerms ts) := by
  induction ts generalizing d e with
  | nil => exact h
  | cons t ts ih => exact ih (meaning_addTerm h t hX) hX

theorem toDatabase_addTerms {d : FDatabase} (he : d.Closed) {ts : List Term} :
    (d.addTerms ts).toDatabase.SameMeaning (d.toDatabase.addTerms ts) := by
  induction ts generalizing d with
  | nil => exact .refl _
  | cons t ts ih =>
    exact (ih (he.addTerm t)).trans (meaning_addTerms (toDatabase_addTerm he) ts rfl)

theorem toDatabase_addEq {d : FDatabase} (he : d.Closed) {a b : Term} :
    (d.addEq a b).toDatabase.SameMeaning (d.toDatabase.addEq a b) := by
  refine Database.SameMeaning.of_congr (fun x y => ⟨congr_of_assertions ?_, congr_of_assertions ?_⟩) rfl
  · intro p hp
    rcases (mem_toDatabase_eqs_of_closed (he.addEq a b)).mp hp with ⟨hp, hm⟩ | hp
    · obtain ⟨x,y⟩ := p
      dsimp at hp hm ⊢
      subst y
      apply Database.toCong
      rcases (mem_addTerm_terms (he.subterms.addTerm a)).mp hm with hm | hm
      · exact Database.addEq_terms ▸ Or.inr ((Term.mem_subtermList _).mp hm)
      · rcases (mem_addTerm_terms he.subterms).mp hm with hm | hm
        · exact Database.addEq_terms ▸ Or.inl (Or.inr ((Term.mem_subtermList _).mp hm))
        · exact Database.addEq_terms ▸ Or.inl (Or.inl ((mem_toDatabase_terms he.subterms).mpr hm))
    · rcases List.mem_cons.mp (List.mem_dedup.mp hp) with rfl | hp
      · exact .direct (Set.mem_insert _ _)
      · exact .direct (Or.inr ((mem_toDatabase_eqs_of_closed he).mpr (Or.inr hp)))
  · rintro p (rfl | hp)
    · exact .direct ((mem_toDatabase_eqs_of_closed (he.addEq a b)).mpr
        (Or.inr (List.mem_dedup.mpr (List.mem_cons_self))))
    · apply Cong.direct
      apply (mem_toDatabase_eqs_of_closed (he.addEq a b)).mpr
      rcases (mem_toDatabase_eqs_of_closed he).mp hp with hp | hp
      · exact Or.inl ⟨hp.1, mem_addTerm_of_mem (mem_addTerm_of_mem hp.2)⟩
      · exact Or.inr (List.mem_dedup.mpr (List.mem_cons_of_mem _ hp))

theorem wf_of_sameMeaning {d e : Database} (h : d.SameMeaning e) (he : e.WF) : d.WF := by
  constructor
  intro p hp hl
  exact InferredFacts.infers_eq_of_isLit he
    (InferredFacts.congr_iff_infers.mp ((h.congr _ _).mp (.direct hp))) hl

theorem WF.addTerm {d : FDatabase} (h : d.WF) (he : d.Closed) (t : Term) :
    (d.addTerm t).WF := wf_of_sameMeaning (toDatabase_addTerm he) (Database.WF.addTerm h t)

theorem WF.addEq {d : FDatabase} (h : d.WF) (he : d.Closed) (a b : Term)
    (hl : a.isLit ∨ b.isLit → a = b) : (d.addEq a b).WF :=
  wf_of_sameMeaning (toDatabase_addEq he) (Database.WF.addEq h a b hl)

theorem WF.addTerms {d : FDatabase} (h : d.WF) (he : d.Closed) (ts : List Term) :
    (d.addTerms ts).WF := wf_of_sameMeaning (toDatabase_addTerms he) (Database.WF.addTerms h ts)

theorem empty_wf : empty.WF := by rw [WF, toDatabase_empty]; exact Database.WF.empty

theorem toDatabase_consEq {d : FDatabase} {a b : Term} (ha : a ∈ d.terms) (hb : b ∈ d.terms) :
    ({ d with eqs := ((a, b) :: d.eqs).dedup } : FDatabase).toDatabase
      = { d.toDatabase with eqs := insert (a, b) d.toDatabase.eqs } := by
  refine Database.ext ?_ rfl
  ext p
  simp only [toDatabase, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_dedup,
    List.mem_cons]
  constructor
  · rintro (⟨heq, hm⟩ | ⟨rfl | hp, h₁, h₂⟩)
    · exact Or.inr (Or.inl ⟨heq, hm⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hp, h₁, h₂⟩)
  · rintro (rfl | (⟨heq, hm⟩ | ⟨hp, h₁, h₂⟩))
    · exact Or.inr ⟨Or.inl rfl, ha, hb⟩
    · exact Or.inl ⟨heq, hm⟩
    · exact Or.inr ⟨Or.inr hp, h₁, h₂⟩

@[simp] theorem mem_terms_union {d₁ d₂ : FDatabase} {t : Term} :
    t ∈ (d₁.union d₂).terms ↔ t ∈ d₁.terms ∨ t ∈ d₂.terms := by
  simp [FDatabase.union, List.mem_dedup]

@[simp] theorem mem_rows_union {d₁ d₂ : FDatabase} {r : Row} :
    r ∈ (d₁.union d₂).rows ↔ r ∈ d₁.rows ∨ r ∈ d₂.rows := by
  simp [FDatabase.union, List.mem_dedup]

@[simp] theorem mem_eqs_union {d₁ d₂ : FDatabase} {p : Term × Term} :
    p ∈ (d₁.union d₂).eqs ↔ p ∈ d₁.eqs ∨ p ∈ d₂.eqs := by
  simp [FDatabase.union, List.mem_dedup]

theorem coe_termsF {d : FDatabase} (hc : d.SubtermClosed) :
    ↑d.termsF = d.toDatabase.terms := by
  rw [toDatabase_terms hc]
  ext t; simp [termsF]

theorem mem_closureF_iff {d : FDatabase} (hc : d.SubtermClosed) {a b : Term}
    (ha : a ∈ d.terms) (hb : b ∈ d.terms) :
    (a, b) ∈ d.closureF ↔ Cong d.toDatabase a b := by
  refine mem_closure_iff_of_diag (coe_termsF hc).symm (Finset.filter_subset _ _) ?_ ?_ ((mem_toDatabase_terms hc).mpr ha) ((mem_toDatabase_terms hc).mpr hb)
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact mem_toDatabase_eqs.mpr (Or.inr ⟨List.mem_toFinset.mp hp.2,
      List.mem_toFinset.mp (mem_candidates.mp hp.1).1,
      List.mem_toFinset.mp (mem_candidates.mp hp.1).2⟩)
  · intro p hp
    rcases mem_toDatabase_eqs.mp hp with ⟨heq, -⟩ | ⟨hp', h₁, h₂⟩
    · exact Or.inl heq
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨mem_candidates.mpr ⟨List.mem_toFinset.mpr h₁, List.mem_toFinset.mpr h₂⟩,
          List.mem_toFinset.mpr hp'⟩)
/-- The executable representative filter implements the specification on held terms. -/
theorem mem_repsWith_closureF_iff {d : FDatabase} (hc : d.SubtermClosed) {t : Term} :
    t ∈ d.repsWith d.closureF ↔ t ∈ d.toDatabase.reps := by
  simp only [repsWith, List.mem_filter, Bool.not_eq_true', List.any_eq_false,
    Bool.and_eq_true, decide_eq_true_eq, Database.mem_reps_iff]
  constructor
  · rintro ⟨ht, hmin⟩
    refine ⟨(mem_toDatabase_terms hc).mpr ht, fun s hs hst => ?_⟩
    have hs' := (mem_toDatabase_terms hc).mp hs
    exact fun hlt => hmin s hs' ⟨(mem_closureF_iff hc hs' ht).mpr hst, hlt⟩
  · rintro ⟨ht, hmin⟩
    have ht' := (mem_toDatabase_terms hc).mp ht
    refine ⟨ht', fun s hs hst => ?_⟩
    exact hmin s ((mem_toDatabase_terms hc).mpr hs)
      ((mem_closureF_iff hc hs ht').mp hst.1) hst.2

theorem mem_closureF_addTerm {d : FDatabase} (he : d.Closed) {t a b : Term}
    (ha : a ∈ (d.addTerm t).terms) (hb : b ∈ (d.addTerm t).terms) :
    (a,b) ∈ (d.addTerm t).closureF ↔ Cong (d.toDatabase.addTerm t) a b :=
  (mem_closureF_iff (he.addTerm t).subterms ha hb).trans ((toDatabase_addTerm he).congr a b)

theorem mem_closureF_addTerm₂ {d : FDatabase} (he : d.Closed) {t u a b : Term}
    (ha : a ∈ ((d.addTerm t).addTerm u).terms) (hb : b ∈ ((d.addTerm t).addTerm u).terms) :
    (a,b) ∈ ((d.addTerm t).addTerm u).closureF ↔ Cong ((d.toDatabase.addTerm t).addTerm u) a b :=
  (mem_closureF_iff ((he.addTerm t).addTerm u).subterms ha hb).trans
    (((toDatabase_addTerm (he.addTerm t)).trans (meaning_addTerm (toDatabase_addTerm he) u rfl)).congr a b)

end FDatabase
theorem mem_assignments {terms : List Term} {vars : List Var} {σ : Env} :
    σ ∈ assignments terms vars ↔ Env.dom σ = vars ∧ ∀ b ∈ σ, b.2 ∈ terms := by
  induction vars generalizing σ with
  | nil =>
    simp only [assignments, List.mem_singleton]
    refine ⟨fun h => by simp [h], fun h => ?_⟩
    simpa [Env.dom] using h.1
  | cons v vs ih =>
    simp only [assignments, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨t, ht, τ, hτ, rfl⟩
      obtain ⟨hd, hv⟩ := ih.mp hτ
      refine ⟨by simp [hd], fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ht
      · exact hv b hb
    · rintro ⟨hd, hv⟩
      match σ with
      | [] => simp at hd
      | (w, t) :: τ =>
        simp only [Env.dom_cons, List.cons.injEq] at hd
        obtain ⟨rfl, hd⟩ := hd
        exact ⟨t, hv (w, t) (by simp), τ, ih.mpr ⟨hd, fun b hb => hv b (by simp [hb])⟩, rfl⟩

theorem Env.mem_canon {vars : List Var} {σ : Env} {b : Var × Term}
    (h : b ∈ Env.canon vars σ) : b.1 ∈ vars ∧ Env.lookup b.1 σ = some b.2 := by
  obtain ⟨v, hv, hb⟩ := List.mem_filterMap.mp h
  cases hlk : Env.lookup v σ with
  | none => rw [hlk] at hb; simp at hb
  | some t =>
    rw [hlk] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    exact ⟨hb ▸ hv, hb ▸ hlk⟩

theorem Env.dom_canon_subset {vars : List Var} {σ : Env} :
    Env.dom (Env.canon vars σ) ⊆ vars := fun _ hv =>
  (Env.mem_canon (Env.mem_dom_iff.mp hv).choose_spec).1

theorem Env.canon_cons_none {v : Var} {vs : List Var} {σ : Env}
    (h : Env.lookup v σ = none) : Env.canon (v :: vs) σ = Env.canon vs σ := by
  simp [canon, h]

theorem Env.canon_cons_some {v : Var} {vs : List Var} {σ : Env} {t : Term}
    (h : Env.lookup v σ = some t) : Env.canon (v :: vs) σ = (v, t) :: Env.canon vs σ := by
  simp [canon, h]

theorem Env.dom_canon {vars : List Var} {σ : Env}
    (h : ∀ v ∈ vars, (Env.lookup v σ).isSome) : Env.dom (Env.canon vars σ) = vars := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h v (by simp))
    rw [canon_cons_some ht, dom_cons, ih fun w hw => h w (by simp [hw])]

theorem Env.lookup_canon {vars : List Var} {σ : Env} (hnd : vars.Nodup) {v : Var}
    (hv : v ∈ vars) : Env.lookup v (Env.canon vars σ) = Env.lookup v σ := by
  induction vars with
  | nil => simp at hv
  | cons w vs ih =>
    rw [List.nodup_cons] at hnd
    cases hlk : Env.lookup w σ with
    | none =>
      rw [canon_cons_none hlk]
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hlk]
        exact Env.lookup_eq_none_iff.mpr fun hc => hnd.1 (Env.dom_canon_subset hc)
      · exact ih hnd.2 hv
    | some t =>
      rw [canon_cons_some hlk, Env.lookup_cons]
      rcases List.mem_cons.mp hv with rfl | hv
      · simp [hlk]
      · rw [if_neg (fun hc : v = w => hnd.1 (hc ▸ hv)), ih hnd.2 hv]

/-- Canonicalizing a substitution whose domain is a duplicate-free permutation of `vars`
changes no lookup. This is what lets the enumerator emit one representative per
`Env.Agree` class where the spec admits the whole class. -/
theorem Env.agree_canon {vars : List Var} {σ : Env} (hnd : vars.Nodup)
    (hperm : (Env.dom σ).Perm vars) : Env.Agree σ (Env.canon vars σ) := by
  intro v
  by_cases hv : v ∈ vars
  · exact (Env.lookup_canon hnd hv).symm
  · rw [Env.lookup_eq_none_iff.mpr fun hc => hv (hperm.mem_iff.mp hc),
      Env.lookup_eq_none_iff.mpr fun hc => hv (Env.dom_canon_subset hc)]

@[simp] theorem Query.freeVars_nil {σ : Env} : Query.freeVars [] σ = [] := rfl

@[simp] theorem Query.freeVars_cons {p : Pattern} {ps : Query} {σ : Env} :
    Query.freeVars (p :: ps) σ = p.freeVars σ ∪ Query.freeVars ps σ := rfl

theorem Query.mem_freeVars {q : Query} {σ : Env} {v : Var} :
    v ∈ Query.freeVars q σ ↔ ∃ p ∈ q, v ∈ p.freeVars σ := by
  induction q with
  | nil => simp
  | cons p ps ih =>
    simp only [Query.freeVars_cons, List.mem_union_iff, List.mem_cons, ih]
    aesop

theorem Query.freeVars_nodup (q : Query) (σ : Env) : (Query.freeVars q σ).Nodup := by
  induction q with
  | nil => simp
  | cons p ps ih => exact List.Nodup.union _ ih

/-- A pattern's free variables are among the query's, so a substitution for the query
restricts to one for each pattern. -/
theorem Query.freeVars_subset {q : Query} {σ : Env} {p : Pattern} (hp : p ∈ q) :
    p.freeVars σ ⊆ Query.freeVars q σ := fun _ hv => Query.mem_freeVars.mpr ⟨p, hp, hv⟩

/-- Restricting a query substitution to one pattern gives a substitution with exactly that
pattern's free variables as its domain, and it agrees with the original there. These are
the two facts `patternHolds_iff` and `ValidSubst.of_agree` need. -/
theorem Env.dom_canon_of_subset {vars vars' : List Var} {σ : Env} (hsub : vars ⊆ vars')
    (hdom : Env.dom σ = vars') : Env.dom (Env.canon vars σ) = vars :=
  Env.dom_canon fun v hv =>
    Env.lookup_isSome_iff_mem_dom.mpr (by rw [hdom]; exact hsub hv)

/-- A generic invariant for the write-only half of a firing. -/
theorem Env.canon_canon {vars vars' : List Var} {σ : Env} (hsub : vars ⊆ vars')
    (hnd : vars'.Nodup) : Env.canon vars (Env.canon vars' σ) = Env.canon vars σ := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    have hl : Env.lookup v (Env.canon vars' σ) = Env.lookup v σ :=
      Env.lookup_canon hnd (hsub (by simp))
    have hs : vs ⊆ vars' := fun w hw => hsub (by simp [hw])
    cases hlk : Env.lookup v σ with
    | none =>
      rw [Env.canon_cons_none (by rw [hl, hlk]), Env.canon_cons_none hlk, ih hs]
    | some t =>
      rw [Env.canon_cons_some (by rw [hl, hlk]), Env.canon_cons_some hlk, ih hs]

mutual

theorem Expr.eval_bound {σ : Env} {v : Var} : ∀ {e : Expr} {t : Term},
    e.eval σ = some t → v ∈ e.vars → (Env.lookup v σ).isSome = true
  | .lit _, _, _, hv => by simp [Expr.vars] at hv
  | .var w, _, he, hv => by
    obtain rfl : v = w := by simpa [Expr.vars] using hv
    simp only [Expr.eval] at he
    rw [he]; rfl
  | .app f as, _, he, hv => by
    obtain ⟨ts, ht, _⟩ := Option.map_eq_some_iff.mp he
    exact Expr.evalList_bound ht hv
  | .min a b, _, he, hv => by
    obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨u, hu, _⟩ := Option.map_eq_some_iff.mp he
    exact (List.mem_union_iff.mp hv).elim (Expr.eval_bound ht) (Expr.eval_bound hu)

theorem Expr.evalList_bound {σ : Env} {v : Var} : ∀ {es : List Expr} {ts : List Term},
    Expr.evalList es σ = some ts → v ∈ Expr.varsList es → (Env.lookup v σ).isSome = true
  | [], _, _, hv => by simp [Expr.varsList] at hv
  | e :: es, _, he, hv => by
    obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨us, hus, _⟩ := Option.map_eq_some_iff.mp he
    exact (List.mem_union_iff.mp hv).elim (Expr.eval_bound ht) (Expr.evalList_bound hus)

end

/-- The row index contains only applications held in the finite term list. -/
structure FDatabase.IndexOk (d : FDatabase) : Prop where
  ctor : ∀ r ∈ d.rows, Term.app r.fn r.args ∈ d.terms
  subsumed : ∀ t ∈ d.subsumed, t ∈ d.terms

theorem FDatabase.mem_closureF_imp {d : FDatabase} (hc : d.SubtermClosed)
    {a b : Term} (h : (a,b) ∈ d.closureF) : Cong d.toDatabase a b := by
  have hm := mem_candidates.mp (closure_subset (Finset.filter_subset _ _) h)
  exact (FDatabase.mem_closureF_iff hc (List.mem_toFinset.mp hm.1)
    (List.mem_toFinset.mp hm.2)).mp h

theorem congrTuple_iff {d : FDatabase} (hc : d.SubtermClosed) {as bs : List Term}
    (ha : ∀ a ∈ as, a ∈ d.terms) (hb : ∀ b ∈ bs, b ∈ d.terms) :
    FDatabase.congrTuple d.closureF as bs = true ↔ CongList d.toDatabase as bs := by
  simp only [FDatabase.congrTuple, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq, CongList.forall₂, List.forall₂_iff_zip]
  constructor
  · rintro ⟨hl, hh⟩
    exact ⟨hl, fun hp => FDatabase.mem_closureF_imp hc (hh _ hp)⟩
  · rintro ⟨hl, hh⟩
    refine ⟨hl, fun p hp => ?_⟩
    exact (FDatabase.mem_closureF_iff hc
      (ha _ (List.of_mem_zip hp).1) (hb _ (List.of_mem_zip hp).2)).mpr (hh hp)

theorem witness_addTerm {d : FDatabase} (he : d.Closed) {w t : Term}
    (hw : w ∈ d.terms) (h : (w,t) ∈ (d.addTerm t).closureF) : Cong d.toDatabase w t := by
  have hw' := (FDatabase.mem_toDatabase_terms he.subterms).mpr hw
  have hc := (FDatabase.mem_closureF_addTerm he (FDatabase.mem_addTerm_of_mem hw)
    (FDatabase.self_mem_addTerm d t)).mp h
  have hs : StoredCongOn d.toDatabase [t] w t := hc.toStored
    ((Database.Contained.addTerm t d.toDatabase).terms hw') (Database.mem_addTerm _ _)
  exact InferredFacts.congr_iff_infers.mpr
    (InferredFacts.infers_of_congOn_core (InferredFacts.infers_of_held hw') hs)

theorem witness_addTerm₂ {d : FDatabase} (he : d.Closed) {w t u v : Term}
    (hw : w ∈ d.terms) (hv : v = t ∨ v = u)
    (h : (w,v) ∈ ((d.addTerm t).addTerm u).closureF) : Cong d.toDatabase w v := by
  have hw' := (FDatabase.mem_toDatabase_terms he.subterms).mpr hw
  have hvm : v ∈ ((d.addTerm t).addTerm u).terms := by
    rcases hv with rfl | rfl
    · exact FDatabase.mem_addTerm_of_mem (FDatabase.self_mem_addTerm d _)
    · exact FDatabase.self_mem_addTerm _ _
  have hc := (FDatabase.mem_closureF_addTerm₂ he
    (FDatabase.mem_addTerm_of_mem (FDatabase.mem_addTerm_of_mem hw)) hvm).mp h
  have hs : StoredCongOn d.toDatabase [t,u] w v := hc.toStored
    ((Database.Contained.addTerms [t,u] d.toDatabase).terms hw')
    (Database.mem_addTerms (db := d.toDatabase) (ts := [t,u]) (by simpa using hv))
  exact InferredFacts.congr_iff_infers.mpr
    (InferredFacts.infers_of_congOn_core (InferredFacts.infers_of_held hw') hs)

theorem mem_terms_foldl {g : FDatabase → α → FDatabase} {C : α → Term → Prop}
    (hg : ∀ acc a t, t ∈ (g acc a).terms ↔ t ∈ acc.terms ∨ C a t)
    (l : List α) (init : FDatabase) (t : Term) :
    t ∈ (l.foldl g init).terms ↔ t ∈ init.terms ∨ ∃ a ∈ l, C a t := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, hg]; aesop

theorem mem_eqs_foldl {g : FDatabase → α → FDatabase} {C : α → Term × Term → Prop}
    (hg : ∀ acc a p, p ∈ (g acc a).eqs ↔ p ∈ acc.eqs ∨ C a p)
    (l : List α) (init : FDatabase) (p : Term × Term) :
    p ∈ (l.foldl g init).eqs ↔ p ∈ init.eqs ∨ ∃ a ∈ l, C a p := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, hg]; aesop

theorem mem_rows_foldl {g : FDatabase → α → FDatabase} {C : α → Row → Prop}
    (hg : ∀ acc a q, q ∈ (g acc a).rows ↔ q ∈ acc.rows ∨ C a q)
    (l : List α) (init : FDatabase) (r : Row) :
    r ∈ (l.foldl g init).rows ↔ r ∈ init.rows ∨ ∃ a ∈ l, C a r := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, hg]; aesop

theorem closed_foldl {g : FDatabase → α → FDatabase}
    (hg : ∀ acc a, acc.Closed → (g acc a).Closed)
    (l : List α) {init : FDatabase} (h : init.Closed) :
    (l.foldl g init).Closed := by
  induction l generalizing init with
  | nil => exact h
  | cons a l ih => exact ih (hg init a h)

theorem runSaturateF_sameData {R : List Rule} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateF R n = some e → e.sameData (execRunRules R e) = true := by
  intro n
  induction n with
  | zero =>
    intro d e h
    rw [FDatabase.runSaturateF] at h
    split at h
    · rename_i hs; rw [Option.some.injEq] at h; exact h ▸ hs
    · exact absurd h (by simp)
  | succ n ih =>
    intro d e h
    rw [FDatabase.runSaturateF] at h
    split at h
    · rename_i hs; rw [Option.some.injEq] at h; exact h ▸ hs
    · exact ih h

/-- **And what it returns is an iterate of the round**, so the specification can follow it
one `RunRules` round at a time. -/
theorem runSaturateF_iterate {R : List Rule} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateF R n = some e → ∃ k, (execRunRules R)^[k] d = e := by
  intro n
  induction n with
  | zero =>
    intro d e h
    rw [FDatabase.runSaturateF] at h
    split at h
    · rw [Option.some.injEq] at h; exact ⟨0, h⟩
    · exact absurd h (by simp)
  | succ n ih =>
    intro d e h
    rw [FDatabase.runSaturateF] at h
    split at h
    · rw [Option.some.injEq] at h; exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := ih h
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

theorem toDatabase_eq_of_fields {d e : FDatabase} (ht : d.terms = e.terms)
    (hq : d.eqs = e.eqs) (hX : d.subsumed = e.subsumed) : d.toDatabase = e.toDatabase := by
  unfold FDatabase.toDatabase
  rw [ht, hq, hX]

theorem Env.refines_canon {vars : List Var} {σ : Env} : Env.Refines (Env.canon vars σ) σ :=
  fun _ hb => (Env.mem_canon hb).2

theorem FDatabase.SubtermClosed.addEq {d : FDatabase} (hc : d.SubtermClosed) (a b : Term) :
    (d.addEq a b).SubtermClosed := (hc.addTerm a).addTerm b

/-- The whole action result, including insertion and marking of a subsumed row. -/
theorem execAction_eq_some {σ : Env} {d e : FDatabase} {a : Action}
    (h : execAction σ d a = some e) :
    (∃ ex t, a = .expr ex ∧ ex.eval σ = some t ∧ e = d.addTerm t) ∨
    (∃ ex ey t u, a = .union ex ey ∧ ex.eval σ = some t ∧ ey.eval σ = some u ∧
      ¬(t.isLit ∨ u.isLit) ∧ e = d.addEq t u) ∨
    (∃ f es ts, a = .subsume f es ∧ Expr.evalList es σ = some ts ∧
      e = d.subsume (.app f ts)) := by
  cases a with
  | expr ex =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Or.inl ⟨ex, t, rfl, ht, rfl⟩
  | union ex ey =>
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · rename_i hn
      cases Option.some.inj h
      exact Or.inr (Or.inl ⟨ex, ey, t, u, rfl, ht, hu, by simpa using hn, rfl⟩)
  | subsume f es =>
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Or.inr (Or.inr ⟨f, es, ts, rfl, hts, rfl⟩)

/-- Every held application has its row in the constructor index. -/
def FDatabase.IndexCurrent (d : FDatabase) : Prop :=
  ∀ f ts, Term.app f ts ∈ d.terms → (⟨f, ts⟩ : Row) ∈ d.rows

theorem represented_witness {db : Database} {t : Term} (h : Cong db t t) :
    ∃ w ∈ db.terms, Cong db w t := by
  obtain ⟨w, hw, ht, _⟩ := InferredFacts.infers_iff_interpret_core.mp
    (InferredFacts.congr_iff_infers.mp h)
  exact ⟨w, hw, (InferredFacts.congr_of_interpret t hw ht).symm⟩

theorem congrList_of_interpret {db : Database} : ∀ {as bs : List Term},
    (∀ b ∈ bs, b ∈ db.terms) → InferredFacts.interpretList db as =
      bs.map (fun b => some (Quot.mk (StoredCong db) b)) → CongList db as bs
  | [], [], _, _ => .nil
  | [], _ :: _, _, h => by simp [InferredFacts.interpretList] at h
  | _ :: _, [], _, h => by simp [InferredFacts.interpretList] at h
  | a :: as, b :: bs, hb, h => by
    simp only [InferredFacts.interpretList, List.map_cons, List.cons.injEq] at h
    exact .cons (InferredFacts.congr_of_interpret a (hb b (by simp)) h.1)
      (congrList_of_interpret (fun b hm => hb b (by simp [hm])) h.2)

theorem represented_app {db : Database} {f : FnName} {ts : List Term}
    (h : Cong db (.app f ts) (.app f ts)) :
    ∃ bs, Term.app f bs ∈ db.terms ∧ CongList db ts bs := by
  obtain ⟨w, _, ht, _⟩ := InferredFacts.infers_iff_interpret_core.mp
    (InferredFacts.congr_iff_infers.mp h)
  change InferredFacts.interpretApp db f (InferredFacts.interpretList db ts) = _ at ht
  unfold InferredFacts.interpretApp at ht
  split at ht
  next hex =>
    exact ⟨hex.choose, hex.choose_spec.1,
      congrList_of_interpret (fun b hb => db.subtermClosed _ hex.choose_spec.1 (.arg hb (.refl b)))
        hex.choose_spec.2⟩
  next => cases ht

theorem FDatabase.IndexOk.addTerm {d : FDatabase} (hi : d.IndexOk) (t : Term) :
    (d.addTerm t).IndexOk := by
  refine ⟨?_, fun u hu => FDatabase.mem_addTerm_of_mem (hi.subsumed u hu)⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp hr
    cases s with
    | lit l => simp [Term.ctorRow] at hr
    | app f as =>
      have heq : r = ⟨f, as⟩ := by simpa [Term.ctorRow] using hr
      subst r
      exact List.mem_append_left _ hs
  · exact FDatabase.mem_addTerm_of_mem (hi.ctor r hr)

theorem FDatabase.IndexCurrent.addTerm {d : FDatabase} (hi : d.IndexCurrent) (t : Term) :
    (d.addTerm t).IndexCurrent := by
  intro f as ht
  rcases List.mem_append.mp ht with ht | ht
  · exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨.app f as, ht, by simp [Term.ctorRow]⟩)
  · exact FDatabase.mem_addTerm_rows_of_mem (hi f as ht)

theorem FDatabase.IndexOk.addEq {d : FDatabase} (hi : d.IndexOk) (a b : Term) :
    (d.addEq a b).IndexOk :=
  ⟨((hi.addTerm a).addTerm b).ctor, ((hi.addTerm a).addTerm b).subsumed⟩

theorem FDatabase.IndexCurrent.addEq {d : FDatabase} (hi : d.IndexCurrent) (a b : Term) :
    (d.addEq a b).IndexCurrent := (hi.addTerm a).addTerm b

namespace FDatabase

@[simp] theorem subsume_terms (d : FDatabase) (t : Term) :
    (d.subsume t).terms = (d.addTerm t).terms := rfl

@[simp] theorem subsume_eqs (d : FDatabase) (t : Term) : (d.subsume t).eqs = d.eqs := rfl

@[simp] theorem subsume_rows (d : FDatabase) (t : Term) :
    (d.subsume t).rows = (d.addTerm t).rows := rfl

@[simp] theorem addTerm_subsumed (d : FDatabase) (t : Term) :
    (d.addTerm t).subsumed = d.subsumed := rfl

@[simp] theorem addEq_subsumed (d : FDatabase) (a b : Term) :
    (d.addEq a b).subsumed = d.subsumed := rfl

@[simp] theorem addTerms_subsumed (d : FDatabase) (ts : List Term) :
    (d.addTerms ts).subsumed = d.subsumed := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => exact ih (d.addTerm t)

@[simp] theorem mem_subsume_subsumed (d : FDatabase) (s t : Term) :
    s ∈ (d.subsume t).subsumed ↔ s = t ∨ s ∈ d.subsumed := by
  simp only [subsume, addTerm_subsumed]
  split
  · rename_i ht
    have ht' : t ∈ d.subsumed := List.contains_iff_mem.mp ht
    exact ⟨Or.inr, fun h => h.elim (fun h => h ▸ ht') id⟩
  · simp

theorem Closed.subsume {d : FDatabase} (h : d.Closed) (t : Term) :
    (d.subsume t).Closed := ⟨(h.addTerm t).eqs, (h.addTerm t).subterms⟩

theorem SubtermClosed.subsume {d : FDatabase} (h : d.SubtermClosed) (t : Term) :
    (d.subsume t).SubtermClosed := h.addTerm t

theorem IndexOk.subsume {d : FDatabase} (h : d.IndexOk) (t : Term) :
    (d.subsume t).IndexOk := by
  refine ⟨(h.addTerm t).ctor, ?_⟩
  intro s hs
  rcases (mem_subsume_subsumed d s t).mp hs with rfl | hs
  · exact self_mem_addTerm d _
  · exact mem_addTerm_of_mem (h.subsumed s hs)

theorem IndexCurrent.subsume {d : FDatabase} (h : d.IndexCurrent) (t : Term) :
    (d.subsume t).IndexCurrent := h.addTerm t

theorem toDatabase_subsume_eq (d : FDatabase) (t : Term) :
    (d.subsume t).toDatabase = (d.addTerm t).toDatabase.addSubsumed {t} := by
  refine Database.ext rfl ?_
  ext s
  simp only [toDatabase, Database.addSubsumed, Set.mem_setOf_eq, Set.mem_union,
    Set.mem_singleton_iff, addTerm_subsumed, mem_subsume_subsumed]
  exact or_comm

theorem toDatabase_subsume {d : FDatabase} (he : d.Closed) (t : Term) :
    (d.subsume t).toDatabase.SameMeaning ((d.toDatabase.addTerm t).addSubsumed {t}) := by
  rw [toDatabase_subsume_eq]
  exact (toDatabase_addTerm he).addSubsumed {t}

@[simp] theorem toDatabase_forgetSubsumed (d : FDatabase) :
    d.forgetSubsumed.toDatabase = d.toDatabase.forgetSubsumed := by
  refine Database.ext rfl ?_
  ext t
  simp [FDatabase.forgetSubsumed, toDatabase, Database.forgetSubsumed]

theorem Closed.forgetSubsumed {d : FDatabase} (h : d.Closed) : d.forgetSubsumed.Closed :=
  ⟨h.eqs, h.subterms⟩

theorem IndexOk.forgetSubsumed {d : FDatabase} (h : d.IndexOk) : d.forgetSubsumed.IndexOk :=
  ⟨h.ctor, fun _ ht => (List.not_mem_nil ht).elim⟩

theorem IndexCurrent.forgetSubsumed {d : FDatabase} (h : d.IndexCurrent) :
    d.forgetSubsumed.IndexCurrent := h

end FDatabase

end Egglog
