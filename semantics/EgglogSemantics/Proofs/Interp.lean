import EgglogSemantics.Impl.Observe
import EgglogSemantics.Proofs.Closure
import EgglogSemantics.Proofs.Scope
import EgglogSemantics.Proofs.SourceModel

/-! Finite-store denotation, matching, and executable refinement.
The denotation explicitly asserts held subterms, so writers preserve semantic meaning.
Delete-free rounds and ordering-free programs refine the specification up to `SameMeaning`;
program completeness excludes fuel-bounded saturation. `InterpDeletes` extends this
refinement to union-free programs with deletes, disequality and `min`. -/

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

private theorem congr_of_assertions {d e : Database}
    (h : ∀ p ∈ d.eqs, Cong e p.1 p.2) {a b : Term} (hc : Cong d a b) : Cong e a b := by
  induction hc using Cong.rec (motive_2 := fun as bs _ => CongList e as bs) with
  | direct hp => exact h _ hp
  | subterm _ hs ih => exact .subterm ih hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | congr _ _ ih ih' => exact .congr ih ih'
  | nil => exact .nil
  | cons _ _ ih ih' => exact .cons ih ih'

theorem toDatabase_addTerm {d : FDatabase} (he : d.Closed) {t : Term} :
    (d.addTerm t).toDatabase.SameMeaning (d.toDatabase.addTerm t) := by
  refine ⟨fun a b => ⟨congr_of_assertions ?_, congr_of_assertions ?_⟩⟩
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

theorem meaning_addEqs {d e : Database} (h : d.SameMeaning e) (W : Set (Term × Term)) :
    (d.addEqs W).SameMeaning (e.addEqs W) := by
  refine ⟨fun a b => ⟨congr_of_assertions ?_, congr_of_assertions ?_⟩⟩
  · rintro p (hp | hp)
    · exact ((h.congr _ _).mp (.direct hp)).mono ⟨Set.subset_union_left⟩
    · exact .direct (Or.inr hp)
  · rintro p (hp | hp)
    · exact ((h.congr _ _).mpr (.direct hp)).mono ⟨Set.subset_union_left⟩
    · exact .direct (Or.inr hp)

private theorem meaning_addTerm {d e : Database} (h : d.SameMeaning e) (t : Term) :
    (d.addTerm t).SameMeaning (e.addTerm t) := by
  refine ⟨fun a b => ⟨congr_of_assertions ?_, congr_of_assertions ?_⟩⟩
  · rintro p (rfl | hp)
    · exact .direct (Set.mem_insert _ _)
    · exact ((h.congr _ _).mp (.direct hp)).mono (Database.Contained.addTerm t e)
  · rintro p (rfl | hp)
    · exact .direct (Set.mem_insert _ _)
    · exact ((h.congr _ _).mpr (.direct hp)).mono (Database.Contained.addTerm t d)

private theorem meaning_addTerms {d e : Database} (h : d.SameMeaning e) (ts : List Term) :
    (d.addTerms ts).SameMeaning (e.addTerms ts) := by
  induction ts generalizing d e with
  | nil => exact h
  | cons t ts ih => exact ih (meaning_addTerm h t)

theorem toDatabase_addTerms {d : FDatabase} (he : d.Closed) {ts : List Term} :
    (d.addTerms ts).toDatabase.SameMeaning (d.toDatabase.addTerms ts) := by
  induction ts generalizing d with
  | nil => exact .refl _
  | cons t ts ih =>
    exact (ih (he.addTerm t)).trans (meaning_addTerms (toDatabase_addTerm he) ts)

theorem toDatabase_addEq {d : FDatabase} (he : d.Closed) {a b : Term} :
    (d.addEq a b).toDatabase.SameMeaning (d.toDatabase.addEq a b) := by
  refine ⟨fun x y => ⟨congr_of_assertions ?_, congr_of_assertions ?_⟩⟩
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

private theorem wf_of_sameMeaning {d e : Database} (h : d.SameMeaning e) (he : e.WF) : d.WF := by
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
  refine Database.ext ?_
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


theorem mem_closureF_addTerm {d : FDatabase} (he : d.Closed) {t a b : Term}
    (ha : a ∈ (d.addTerm t).terms) (hb : b ∈ (d.addTerm t).terms) :
    (a,b) ∈ (d.addTerm t).closureF ↔ Cong (d.toDatabase.addTerm t) a b :=
  (mem_closureF_iff (he.addTerm t).subterms ha hb).trans ((toDatabase_addTerm he).congr a b)

theorem mem_closureF_addTerm₂ {d : FDatabase} (he : d.Closed) {t u a b : Term}
    (ha : a ∈ ((d.addTerm t).addTerm u).terms) (hb : b ∈ ((d.addTerm t).addTerm u).terms) :
    (a,b) ∈ ((d.addTerm t).addTerm u).closureF ↔ Cong ((d.toDatabase.addTerm t).addTerm u) a b :=
  (mem_closureF_iff ((he.addTerm t).addTerm u).subterms ha hb).trans
    (((toDatabase_addTerm (he.addTerm t)).trans (meaning_addTerm (toDatabase_addTerm he) u)).congr a b)

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
theorem execWrite_preserves {P : FDatabase → Prop}
    (ht : ∀ d t, P d → P (d.addTerm t))
    (hu : ∀ d a b, P d → ¬(a.isLit ∨ b.isLit) → P (d.addEq a b))
    {σ : Env} {d e : FDatabase} {a : Action} (hd : P d)
    (h : execWrite σ d a = some e) : P e := by
  cases a with
  | expr ex =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ht d t hd
  | delete ex =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact hd
  | union ex ey =>
    obtain ⟨t, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · rename_i hn
      cases Option.some.inj h
      exact hu d t u hd (by simpa using hn)

theorem execWrites_preserves {P : FDatabase → Prop}
    (ht : ∀ d t, P d → P (d.addTerm t))
    (hu : ∀ d a b, P d → ¬(a.isLit ∨ b.isLit) → P (d.addEq a b))
    {σ : Env} {d e : FDatabase} {as : List Action} (hd : P d)
    (h : execWrites σ d as = some e) : P e := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact hd
  | cons a as ih =>
    obtain ⟨m, hm, he⟩ := Option.bind_eq_some_iff.mp h
    exact ih (execWrite_preserves ht hu hd hm) he







/-- Induction over a round's deletion phase and its successful write accumulations. -/
theorem execRunRules_induction_ruleset {R : List Rule} {d : FDatabase}
    {P : FDatabase → Prop}
    (hd : ∀ X, P (d.deleteAtoms d.closureF X))
    (hf : ∀ r ∈ R, ∀ σ ∈ matchQuery d r.query,
      ∀ acc, P acc → P (fireWritesInto r acc σ)) : P (execRunRules R d) := by
  have hfold : ∀ (xs : List (Rule × List Env)),
      (∀ rs ∈ xs, rs.1 ∈ R ∧
        ∀ σ ∈ rs.2, σ ∈ matchQuery d rs.1.query) →
      ∀ acc, P acc → P (xs.foldl (fun acc rs => rs.2.foldl (fireWritesInto rs.1) acc) acc) := by
    intro xs
    induction xs with
    | nil => exact fun _ _ hp => hp
    | cons rs xs ih =>
      intro hx acc hp
      apply ih (fun rs hr => hx rs (by simp [hr]))
      have hr := hx rs (by simp)
      have hin : ∀ (ss : List Env), (∀ σ ∈ ss, σ ∈ matchQuery d rs.1.query) →
          ∀ acc, P acc → P (ss.foldl (fireWritesInto rs.1) acc) := by
        intro ss
        induction ss with
        | nil => exact fun _ _ hp => hp
        | cons σ ss ih =>
          intro hs acc hp
          exact ih (fun σ hm => hs σ (by simp [hm])) _
            (hf rs.1 hr.1 σ (hs σ (by simp)) acc hp)
      exact hin rs.2 hr.2 acc hp
  unfold execRunRules execRunRulesWith
  apply hfold
  · intro rs hrs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrs
    exact ⟨hr,
      fun σ hσ => by simpa only [matchQueryWith_eq] using hσ⟩
  · exact hd _


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

/-- Successful delete-free actions refine sequential specification actions semantically. -/
theorem execAction_toDatabase {σ : Env} {d e : FDatabase} (he : d.Closed)
    {a : Action} (hd : a.DeleteFree) (h : execAction σ d a = some e) :
    ∃ out, evalAction σ d.toDatabase a = some out ∧ e.toDatabase.SameMeaning out := by
  cases a with
  | expr ex =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, by simp [evalAction, ht], FDatabase.toDatabase_addTerm he⟩
  | union ex ey =>
    obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · rename_i hn
      cases Option.some.inj h
      have hnu : ¬(t.isLit ∨ u.isLit) := by simpa using hn
      exact ⟨_, by simp [evalAction, ht, hu, hnu], FDatabase.toDatabase_addEq he⟩
  | delete _ => cases hd

theorem execAction_closed {σ : Env} {d e : FDatabase} (he : d.Closed)
    {a : Action} (hd : a.DeleteFree) (h : execAction σ d a = some e) : e.Closed := by
  cases a with
  | expr ex => obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact he.addTerm t
  | union ex ey =>
    obtain ⟨t, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · cases Option.some.inj h; exact he.addEq t u
  | delete _ => cases hd

theorem execActions_closed {σ : Env} {d e : FDatabase} (he : d.Closed)
    {as : List Action} (hd : Actions.DeleteFree as) (h : execActions σ d as = some e) : e.Closed := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact he
  | cons a as ih =>
    obtain ⟨m, hm, ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih (execAction_closed he (hd a (by simp)) hm) (fun a ha => hd a (by simp [ha])) ht

theorem execWrites_closed {σ : Env} {d e : FDatabase} (he : d.Closed)
    {as : List Action} (h : execWrites σ d as = some e) : e.Closed :=
  execWrites_preserves (fun _ t h => h.addTerm t) (fun _ a b h _ => h.addEq a b) he h

theorem execActions_toDatabase {σ : Env} {d e : FDatabase} (he : d.Closed)
    {as : List Action} (hd : Actions.DeleteFree as) (h : execActions σ d as = some e) :
    ∃ out, evalActions σ d.toDatabase as = some out ∧ e.toDatabase.SameMeaning out := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact ⟨_, rfl, .refl _⟩
  | cons a as ih =>
    obtain ⟨m, hm, ht⟩ := Option.bind_eq_some_iff.mp h
    have hda := hd a (by simp)
    have hdt : Actions.DeleteFree as := fun a ha => hd a (by simp [ha])
    obtain ⟨out, hout, hh⟩ := execAction_toDatabase he hda hm
    obtain ⟨out', hout', hh'⟩ := ih (execAction_closed he hda hm) hdt ht
    rw [evalActions_eq_writes _ _ _ hdt] at hout'
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.mp hout'
    refine ⟨out.addEqs W, ?_, hh'.trans (FDatabase.meaning_addEqs hh W)⟩
    rw [evalActions_cons, hout, Option.bind_some, evalActions_eq_writes _ _ _ hdt, hW]
    rfl

/-- The row index contains only applications held in the finite term list. -/
structure FDatabase.IndexOk (d : FDatabase) : Prop where
  ctor : ∀ r ∈ d.rows, Term.app r.fn r.args ∈ d.terms

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

private theorem witness_addTerm {d : FDatabase} (he : d.Closed) {w t : Term}
    (hw : w ∈ d.terms) (h : (w,t) ∈ (d.addTerm t).closureF) : Cong d.toDatabase w t := by
  have hw' := (FDatabase.mem_toDatabase_terms he.subterms).mpr hw
  have hc := (FDatabase.mem_closureF_addTerm he (FDatabase.mem_addTerm_of_mem hw)
    (FDatabase.self_mem_addTerm d t)).mp h
  have hs : StoredCongOn d.toDatabase [t] w t := hc.toStored
    ((Database.Contained.addTerm t d.toDatabase).terms hw') (Database.mem_addTerm _ _)
  exact InferredFacts.congr_iff_infers.mpr
    (InferredFacts.infers_of_congOn_core (InferredFacts.infers_of_held hw') hs)

private theorem witness_addTerm₂ {d : FDatabase} (he : d.Closed) {w t u v : Term}
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

/-- Soundness of both the indexed fast path and the extended-closure path. -/
theorem patternHolds_matches {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    {p : Pattern} {σ : Env} (h : patternHolds d p σ = true) : Matches d.toDatabase p σ := by
  cases p with
  | expr ex =>
    cases hv : ex.eval σ with
    | none => simp [patternHolds, hv] at h
    | some t =>
      apply Matches.atom hv
      cases t with
      | lit l =>
        obtain ⟨w, hw, hh⟩ : ∃ w ∈ d.terms, (w, .lit l) ∈ (d.addTerm (.lit l)).closureF := by
          simpa [patternHolds, hv] using h
        exact (witness_addTerm he hw hh).symm.trans (witness_addTerm he hw hh)
      | app f ts =>
        simp only [patternHolds, hv] at h
        split at h
        · obtain ⟨r, hr, hh⟩ := List.any_eq_true.mp h
          have hh : (if r.fn = f then FDatabase.congrTuple d.closureF ts r.args else false) = true := by
            simpa using hh
          have hf : r.fn = f := by
            by_contra hn
            simp [hn] at hh
          have ht : FDatabase.congrTuple d.closureF ts r.args = true := by simpa [hf] using hh
          have hrow := (FDatabase.mem_toDatabase_terms he.subterms).mpr (hi.ctor r hr)
          have hl : CongList d.toDatabase ts r.args := by
            apply CongList.forall₂.mpr
            simp only [FDatabase.congrTuple, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
              decide_eq_true_eq] at ht
            exact List.forall₂_iff_zip.mpr ⟨ht.1, fun hp => FDatabase.mem_closureF_imp he.subterms (ht.2 _ hp)⟩
          rw [hf] at hrow
          have hh := Cong.congr (Database.toCong hrow) hl.symm
          exact hh.symm.trans hh
        · obtain ⟨w, hw, hh⟩ := of_decide_eq_true h
          exact (witness_addTerm he hw hh).symm.trans (witness_addTerm he hw hh)
  | eq a b =>
    cases ha : a.eval σ with
    | none => simp [patternHolds, ha] at h
    | some t =>
      cases hb : b.eval σ with
      | none => simp [patternHolds, ha, hb] at h
      | some u =>
        obtain ⟨htu, w, hw, hwt⟩ : (t,u) ∈ ((d.addTerm t).addTerm u).closureF ∧
            ∃ w ∈ d.terms, (w,t) ∈ ((d.addTerm t).addTerm u).closureF := by
          simpa [patternHolds, ha, hb] using h
        have hwt' := witness_addTerm₂ he hw (Or.inl rfl) hwt
        have htu' := (FDatabase.mem_closureF_addTerm₂ he
          (FDatabase.mem_addTerm_of_mem (FDatabase.self_mem_addTerm d t))
          (FDatabase.self_mem_addTerm _ u)).mp htu
        have hs : StoredCongOn d.toDatabase [t,u] t u := htu'.toStored
          (Database.mem_addTerms (db := d.toDatabase) (ts := [t,u]) (by simp))
          (Database.mem_addTerms (db := d.toDatabase) (ts := [t,u]) (by simp))
        exact .equal ha hb (InferredFacts.congr_iff_infers.mpr
          (InferredFacts.infers_of_congOn_core
            (InferredFacts.congr_iff_infers.mp (hwt'.symm.trans hwt')) hs))
  | ne a b =>
    cases ha : a.eval σ with
    | none => simp [patternHolds, ha] at h
    | some t =>
      cases hb : b.eval σ with
      | none => simp [patternHolds, ha, hb] at h
      | some u =>
        obtain ⟨⟨w, hw, hwt⟩, ⟨v, hv, hvu⟩, hn⟩ :
            (∃ w ∈ d.terms, (w,t) ∈ ((d.addTerm t).addTerm u).closureF) ∧
            (∃ v ∈ d.terms, (v,u) ∈ ((d.addTerm t).addTerm u).closureF) ∧
            (t,u) ∉ ((d.addTerm t).addTerm u).closureF := by
          simpa [patternHolds, ha, hb, and_assoc] using h
        have ht := witness_addTerm₂ he hw (Or.inl rfl) hwt
        have hu := witness_addTerm₂ he hv (Or.inr rfl) hvu
        refine .unequal ha hb (ht.symm.trans ht) (hu.symm.trans hu) ?_
        intro hc
        apply hn
        apply (FDatabase.mem_closureF_addTerm₂ he
          (FDatabase.mem_addTerm_of_mem (FDatabase.self_mem_addTerm d t))
          (FDatabase.self_mem_addTerm _ u)).mpr
        exact hc.mono (Database.Contained.addTerms [t,u] d.toDatabase)

theorem FDatabase.patternHolds_validSubst {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    {p : Pattern} {σ : Env} (hv : ValidEnv (p.freeVars []) d.toDatabase σ)
    (h : patternHolds d p σ = true) : ValidSubst d.toDatabase p σ :=
  ⟨hv, patternHolds_matches he hi h⟩

theorem validEnv_canon {d : FDatabase} (hc : d.SubtermClosed) {q : Query} {σ : Env}
    {p : Pattern} (hp : p ∈ q) (hd : Env.dom σ = Query.freeVars q [])
    (hv : ∀ b ∈ σ, b.2 ∈ d.terms) :
    ValidEnv (p.freeVars []) d.toDatabase (Env.canon (p.freeVars []) σ) := by
  constructor
  · rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hd]
  · exact fun b hb => (FDatabase.mem_toDatabase_terms hc).mpr
      (hv b (Env.mem_of_lookup (Env.mem_canon hb).2))

theorem validQuerySubst_of_mem_matchQuery {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
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
    ⟨validEnv_canon he.subterms hp hd hv, patternHolds_matches he hi (hall p hp)⟩), hu⟩,
    Env.agree_of_refines hrf ?_⟩
  intro v hv
  rw [hd] at hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_freeVars.mp hv
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars []) σ, List.mem_map_of_mem hp, ?_⟩
  rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hd]
  exact hvp

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
    (hq : d.eqs = e.eqs) : d.toDatabase = e.toDatabase := by
  unfold FDatabase.toDatabase
  rw [ht, hq]

theorem Env.refines_canon {vars : List Var} {σ : Env} : Env.Refines (Env.canon vars σ) σ :=
  fun _ hb => (Env.mem_canon hb).2

theorem FDatabase.SubtermClosed.addEq {d : FDatabase} (hc : d.SubtermClosed) (a b : Term) :
    (d.addEq a b).SubtermClosed := (hc.addTerm a).addTerm b

/-- The whole action result, including the deletion alternative. -/
theorem execAction_eq_some {σ : Env} {d e : FDatabase} {a : Action}
    (h : execAction σ d a = some e) :
    (∃ ex t, a = .expr ex ∧ ex.eval σ = some t ∧ e = d.addTerm t) ∨
    (∃ ex ey t u, a = .union ex ey ∧ ex.eval σ = some t ∧ ey.eval σ = some u ∧
      ¬(t.isLit ∨ u.isLit) ∧ e = d.addEq t u) ∨
    (∃ ex t, a = .delete ex ∧ ex.eval σ = some t ∧ e = d.deleteAtoms d.closureF [t]) := by
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
  | delete ex =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Or.inr (Or.inr ⟨ex, t, rfl, ht, rfl⟩)

theorem execAction_subtermClosed {σ : Env} {d e : FDatabase} (hc : d.SubtermClosed)
    {a : Action} (hd : a.DeleteFree) (h : execAction σ d a = some e) : e.SubtermClosed := by
  rcases execAction_eq_some h with ⟨_, t, rfl, _, rfl⟩ |
    ⟨_, _, t, u, rfl, _, _, _, rfl⟩ | ⟨_, _, rfl, _⟩
  · exact hc.addTerm t
  · exact hc.addEq t u
  · cases hd

theorem execActions_subtermClosed {σ : Env} {d e : FDatabase} (hc : d.SubtermClosed)
    {as : List Action} (hd : Actions.DeleteFree as) (h : execActions σ d as = some e) :
    e.SubtermClosed := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact hc
  | cons a as ih =>
    obtain ⟨m, hm, ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih (execAction_subtermClosed hc (hd a (by simp)) hm)
      (fun a ha => hd a (by simp [ha])) ht


/-- Every held application has its row in the constructor index. -/
def FDatabase.IndexCurrent (d : FDatabase) : Prop :=
  ∀ f ts, Term.app f ts ∈ d.terms → (⟨f, ts⟩ : Row) ∈ d.rows

private theorem represented_witness {db : Database} {t : Term} (h : Cong db t t) :
    ∃ w ∈ db.terms, Cong db w t := by
  obtain ⟨w, hw, ht, _⟩ := InferredFacts.infers_iff_interpret_core.mp
    (InferredFacts.congr_iff_infers.mp h)
  exact ⟨w, hw, (InferredFacts.congr_of_interpret t hw ht).symm⟩

private theorem congrList_of_interpret {db : Database} : ∀ {as bs : List Term},
    (∀ b ∈ bs, b ∈ db.terms) → InferredFacts.interpretList db as =
      bs.map (fun b => some (Quot.mk (StoredCong db) b)) → CongList db as bs
  | [], [], _, _ => .nil
  | [], _ :: _, _, h => by simp [InferredFacts.interpretList] at h
  | _ :: _, [], _, h => by simp [InferredFacts.interpretList] at h
  | a :: as, b :: bs, hb, h => by
    simp only [InferredFacts.interpretList, List.map_cons, List.cons.injEq] at h
    exact .cons (InferredFacts.congr_of_interpret a (hb b (by simp)) h.1)
      (congrList_of_interpret (fun b hm => hb b (by simp [hm])) h.2)

private theorem represented_app {db : Database} {f : FnName} {ts : List Term}
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

/-- A complete constructor index makes the executable matcher complete. -/
theorem patternHolds_of_matches {d : FDatabase} (he : d.Closed) (hi : d.IndexCurrent)
    {p : Pattern} {σ : Env} (h : Matches d.toDatabase p σ) : patternHolds d p σ = true := by
  have witness₁ : ∀ t, Cong d.toDatabase t t →
      ∃ w ∈ d.terms, (w,t) ∈ (d.addTerm t).closureF := by
    intro t ht
    obtain ⟨w, hw, hc⟩ := represented_witness ht
    have hwm := (FDatabase.mem_toDatabase_terms he.subterms).mp hw
    exact ⟨w, hwm, (FDatabase.mem_closureF_addTerm he (FDatabase.mem_addTerm_of_mem hwm)
      (FDatabase.self_mem_addTerm d t)).mpr (hc.mono (Database.Contained.addTerm t _))⟩
  have witness₂ : ∀ t u v, (v = t ∨ v = u) → Cong d.toDatabase v v →
      ∃ w ∈ d.terms, (w,v) ∈ ((d.addTerm t).addTerm u).closureF := by
    intro t u v hv ht
    obtain ⟨w, hw, hc⟩ := represented_witness ht
    have hwm := (FDatabase.mem_toDatabase_terms he.subterms).mp hw
    have hvm : v ∈ ((d.addTerm t).addTerm u).terms := by
      rcases hv with rfl | rfl
      · exact FDatabase.mem_addTerm_of_mem (FDatabase.self_mem_addTerm d _)
      · exact FDatabase.self_mem_addTerm _ _
    exact ⟨w, hwm, (FDatabase.mem_closureF_addTerm₂ he
      (FDatabase.mem_addTerm_of_mem (FDatabase.mem_addTerm_of_mem hwm)) hvm).mpr
      (hc.mono (Database.Contained.addTerms [t,u] _))⟩
  cases h with
  | @atom ex σ t hv hc =>
    cases t with
    | lit l => simpa [patternHolds, hv] using witness₁ (.lit l) hc
    | app f ts =>
      simp only [patternHolds, hv]
      split
      next hh =>
        obtain ⟨bs, hb, hl⟩ := represented_app hc
        have hbm := (FDatabase.mem_toDatabase_terms he.subterms).mp hb
        have ht : ∀ t ∈ ts, t ∈ d.terms := by
          simp only [FDatabase.holdsAll, List.all_eq_true, decide_eq_true_eq] at hh
          exact fun t ht => hh t ht t (Term.self_mem_subtermList t)
        have hb' : ∀ b ∈ bs, b ∈ d.terms := fun b hb => he.subterms _ hbm b
          (Term.mem_subtermList_of_isSubterm (.arg hb (.refl b)))
        apply List.any_eq_true.mpr
        exact ⟨⟨f,bs⟩, hi f bs hbm, by
          simpa using (congrTuple_iff he.subterms ht hb').mpr hl⟩
      next => exact decide_eq_true (witness₁ (.app f ts) hc)
  | @equal a b σ t u ha hb hc =>
    simp only [patternHolds, ha, hb, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, witness₂ t u t (Or.inl rfl) (hc.trans hc.symm)⟩
    exact (FDatabase.mem_closureF_addTerm₂ he
      (FDatabase.mem_addTerm_of_mem (FDatabase.self_mem_addTerm d t))
      (FDatabase.self_mem_addTerm _ u)).mpr
      (hc.mono (Database.Contained.addTerms [t,u] _))
  | @unequal a b σ t u ha hb ht hu hn =>
    simp only [patternHolds, ha, hb, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, and_assoc]
    refine ⟨witness₂ t u t (Or.inl rfl) ht, witness₂ t u u (Or.inr rfl) hu, ?_⟩
    intro htu
    have hc := (FDatabase.mem_closureF_addTerm₂ he
      (FDatabase.mem_addTerm_of_mem (FDatabase.self_mem_addTerm d t))
      (FDatabase.self_mem_addTerm _ u)).mp htu
    have hs : StoredCongOn d.toDatabase [t,u] t u := hc.toStored
      (Database.mem_addTerms (ts := [t,u]) (by simp))
      (Database.mem_addTerms (ts := [t,u]) (by simp))
    exact hn (InferredFacts.congr_iff_infers.mpr
      (InferredFacts.infers_of_congOn_core (InferredFacts.congr_iff_infers.mp ht) hs))

theorem patternHolds_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {p : Pattern} {σ : Env}
    (hv : ValidEnv (p.freeVars []) d.toDatabase σ) :
    patternHolds d p σ = true ↔ ValidSubst d.toDatabase p σ :=
  ⟨fun h => ⟨hv, patternHolds_matches he hi h⟩, fun h => patternHolds_of_matches he hj h.2⟩

theorem mem_matchQuery_iff {d : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) {q : Query} {σ : Env} :
    σ ∈ matchQuery d q ↔ Env.dom σ = Query.freeVars q [] ∧ (∀ b ∈ σ, b.2 ∈ d.terms) ∧
      ∀ p ∈ q, ValidSubst d.toDatabase p (Env.canon (p.freeVars []) σ) := by
  simp only [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true]
  constructor
  · rintro ⟨⟨hd, hv⟩, hh⟩
    exact ⟨hd, hv, fun p hp =>
      (patternHolds_iff he hi hj (validEnv_canon he.subterms hp hd hv)).mp (hh p hp)⟩
  · rintro ⟨hd, hv, hh⟩
    exact ⟨⟨hd,hv⟩, fun p hp => patternHolds_of_matches he hj (hh p hp).2⟩

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
  · exact fun b hb => (FDatabase.mem_toDatabase_terms he.subterms).mp
      (h.mem_terms b (Env.mem_of_lookup (Env.mem_canon hb).2))
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
    obtain ⟨τ, hτ, _⟩ := validQuerySubst_of_mem_matchQuery he hi hσ
    exact ⟨τ, hτ⟩



/-- The executable erase list denotes exactly the specification's optional erase set. -/
theorem actionDeletes_erase (σ : Env) (a : Action) :
    a.erase σ = (actionDeletes σ a).map (fun X => {t | t ∈ X}) := by
  cases a with
  | expr e =>
    cases he : e.eval σ <;> simp [Action.erase, Action.write, actionDeletes, he]
  | union e f =>
    cases he : e.eval σ <;> cases hf : f.eval σ <;>
      simp only [Action.erase, Action.write, actionDeletes, he, hf, Option.bind_none,
        Option.bind_some, Option.map_none]
    split <;> simp
  | delete e =>
    cases he : e.eval σ <;> simp [Action.erase, actionDeletes, he]

theorem actionsDeletes_erases (σ : Env) (as : List Action) :
    Action.erases σ as = (actionsDeletes σ as).map (fun X => {t | t ∈ X}) := by
  induction as with
  | nil => simp [Action.erases, actionsDeletes]
  | cons a as ih =>
    rw [Action.erases, actionDeletes_erase, ih]
    simp only [actionsDeletes]
    cases actionDeletes σ a <;> cases actionsDeletes σ as <;>
      simp [Set.setOf_or]


theorem actionDeletes_eq_empty {σ : Env} {a : Action} (hd : a.DeleteFree) :
    actionDeletes σ a = (a.write σ).map (fun _ => []) := by
  cases a with
  | expr e => simp [actionDeletes, Action.write, Option.map_map, Function.comp_def]
  | union a b =>
    simp only [actionDeletes, Action.write]
    cases a.eval σ <;> cases b.eval σ <;> simp
    split <;> rfl
  | delete _ => cases hd

theorem actionsDeletes_eq_empty {σ : Env} {as : List Action} (hd : Actions.DeleteFree as) :
    actionsDeletes σ as = (Action.writes σ as).map (fun _ => []) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [actionsDeletes, actionDeletes_eq_empty (hd a (by simp)),
      ih (fun a ha => hd a (by simp [ha]))]
    simp only [Action.writes]
    cases a.write σ <;> cases Action.writes σ as <;> rfl

theorem execRunRules_eq_fold_of_deleteFree {d : FDatabase} (R : List Rule)
    (hd : ∀ r ∈ R, r.DeleteFree) : execRunRules R d =
    (R.map fun r => (r, matchQuery d r.query)).foldl
      (fun acc rs => rs.2.foldl (fireWritesInto rs.1) acc) d := by
  unfold execRunRules execRunRulesWith
  simp only [matchQueryWith_eq]
  have hx : ((R.map fun r => (r, matchQuery d r.query)).flatMap fun rs =>
      rs.2.flatMap fun σ => (actionsDeletes σ rs.1.actions).getD []) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rs hrs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrs
    apply List.flatMap_eq_nil_iff.mpr
    intro σ _
    rw [actionsDeletes_eq_empty (hd r hr)]
    cases Action.writes σ r.actions <;> rfl
  simp only [hx, FDatabase.deleteAtoms, List.isEmpty_nil, if_true]

private theorem execWrite_spec {σ : Env} {d : FDatabase} (he : d.Closed) (a : Action) :
    match a.write σ, execWrite σ d a with
    | none, none => True
    | some W, some e => e.Closed ∧ e.toDatabase.SameMeaning (d.toDatabase.addEqs W)
    | _, _ => False := by
  cases a with
  | expr ex =>
    cases hv : ex.eval σ with
    | none => simp [Action.write, execWrite, execAction, hv]
    | some t =>
      simp only [Action.write, execWrite, execAction, hv, Option.map_some]
      refine ⟨he.addTerm t, ?_⟩
      simpa [Database.addEqs, Database.addTerm, Set.union_singleton] using
        (FDatabase.toDatabase_addTerm he (t := t))
  | union ex ey =>
    cases hx : ex.eval σ <;> cases hy : ey.eval σ <;>
      simp only [Action.write, execWrite, execAction, hx, hy, Option.bind_none,
        Option.bind_some]
    rename_i a b
    by_cases hn : a.isLit ∨ b.isLit
    · simp [hn]
    · simp only [Bool.or_eq_true, hn, ↓reduceIte]
      refine ⟨he.addEq a b, ?_⟩
      simpa [Database.addEqs, Database.addEq, Set.union_singleton] using
        (FDatabase.toDatabase_addEq he (a := a) (b := b))
  | delete ex =>
    cases hv : ex.eval σ with
    | none => simp [Action.write, execWrite, hv]
    | some t =>
      simp only [Action.write, execWrite, hv, Option.map_some]
      exact ⟨he, by simpa [Database.addEqs, FDatabase.toDatabase] using Database.SameMeaning.refl d.toDatabase⟩

private theorem execWrites_spec {σ : Env} {d : FDatabase} (he : d.Closed)
    (as : List Action) :
    match Action.writes σ as, execWrites σ d as with
    | none, none => True
    | some W, some e => e.Closed ∧ e.toDatabase.SameMeaning (d.toDatabase.addEqs W)
    | _, _ => False := by
  induction as generalizing d with
  | nil => exact ⟨he, by simpa [Database.addEqs, FDatabase.toDatabase] using Database.SameMeaning.refl d.toDatabase⟩
  | cons a as ih =>
    have ha := execWrite_spec (σ := σ) he a
    cases hw : a.write σ <;> cases hx : execWrite σ d a <;> simp only [hw, hx] at ha
    · simp [Action.writes, execWrites, hw, hx]
    · rename_i W e
      have ht := ih ha.1
      cases htW : Action.writes σ as <;> cases htE : execWrites σ e as <;>
        simp only [htW, htE] at ht
      · simp [Action.writes, execWrites, hw, hx, htW, htE]
      · rename_i V out
        simp only [Action.writes, execWrites, hw, hx, htW, htE,
          Option.bind_some, Option.map_some]
        refine ⟨ht.1, ?_⟩
        simpa only [Database.addEqs, Set.union_assoc] using
          ht.2.trans (FDatabase.meaning_addEqs ha.2 V)

private noncomputable def firingWrites (rs : Rule × Env) : Set (Term × Term) :=
  (Action.writes rs.2 rs.1.actions).getD ∅

private theorem fireWritesInto_spec {d : FDatabase} (he : d.Closed) (rs : Rule × Env) :
    (fireWritesInto rs.1 d rs.2).Closed ∧
      (fireWritesInto rs.1 d rs.2).toDatabase.SameMeaning
        (d.toDatabase.addEqs (firingWrites rs)) := by
  have h := execWrites_spec (σ := rs.2) he rs.1.actions
  unfold fireWritesInto firingWrites
  cases hw : Action.writes rs.2 rs.1.actions <;>
    cases hx : execWrites rs.2 d rs.1.actions <;> simp only [hw, hx] at h ⊢
  · exact ⟨he, by simpa [Database.addEqs, FDatabase.toDatabase] using Database.SameMeaning.refl d.toDatabase⟩
  · exact h

private noncomputable def firingWritesAll : List (Rule × Env) → Set (Term × Term)
  | [] => ∅
  | rs :: rss => firingWrites rs ∪ firingWritesAll rss

private theorem mem_firingWritesAll {p : Term × Term} {rss : List (Rule × Env)} :
    p ∈ firingWritesAll rss ↔ ∃ rs ∈ rss, p ∈ firingWrites rs := by
  induction rss with
  | nil => simp [firingWritesAll]
  | cons rs rss ih => simp [firingWritesAll, ih, or_and_right, exists_or]

private theorem fold_firingWrites_spec {d : FDatabase} (he : d.Closed)
    (rss : List (Rule × Env)) :
    let out := rss.foldl (fun acc rs => fireWritesInto rs.1 acc rs.2) d
    out.Closed ∧ out.toDatabase.SameMeaning (d.toDatabase.addEqs (firingWritesAll rss)) := by
  induction rss generalizing d with
  | nil => exact ⟨he, by simpa [firingWritesAll, Database.addEqs, FDatabase.toDatabase] using
      Database.SameMeaning.refl d.toDatabase⟩
  | cons rs rss ih =>
    obtain ⟨he', hh⟩ := fireWritesInto_spec he rs
    obtain ⟨ho, hh'⟩ := ih he'
    refine ⟨ho, ?_⟩
    simpa only [firingWritesAll, Database.addEqs, Set.union_assoc, List.foldl_cons] using
      hh'.trans (FDatabase.meaning_addEqs hh (firingWritesAll rss))

private def roundFirings (R : List Rule) (d : FDatabase) : List (Rule × Env) :=
  R.flatMap fun r =>
    (matchQuery d r.query).map (r, ·)

private theorem execRunRules_eq_firings {d : FDatabase} (R : List Rule)
    (hd : ∀ r ∈ R, r.DeleteFree) : execRunRules R d =
    (roundFirings R d).foldl (fun acc rs => fireWritesInto rs.1 acc rs.2) d := by
  rw [execRunRules_eq_fold_of_deleteFree R hd]
  simp only [roundFirings, List.foldl_flatMap, List.foldl_map]

private theorem mem_roundFirings {R : List Rule} {d : FDatabase} {rs : Rule × Env} :
    rs ∈ roundFirings R d ↔
      rs.1 ∈ R ∧ rs.2 ∈ matchQuery d rs.1.query := by
  rcases rs with ⟨r, σ⟩
  simp [roundFirings, List.mem_flatMap, and_assoc]

private theorem mem_firingWrites {p : Term × Term} {rs : Rule × Env} :
    p ∈ firingWrites rs ↔ ∃ W, Action.writes rs.2 rs.1.actions = some W ∧ p ∈ W := by
  unfold firingWrites
  cases Action.writes rs.2 rs.1.actions <;> simp

private theorem firingWritesAll_eq {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) :
    firingWritesAll (roundFirings R d) = RunWrites R d.toDatabase := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨r, σ⟩, hrs, hp⟩ := mem_firingWritesAll.mp hp
    obtain ⟨hr, hσ⟩ := mem_roundFirings.mp hrs
    obtain ⟨W, hW, hp⟩ := mem_firingWrites.mp hp
    obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_mem_matchQuery he hi hσ
    obtain ⟨ρ, hρ, hag'⟩ := hτ.exists_queryMatches
    have hag'' : Env.Agree ρ σ := fun v => (hag' v).trans (hag v)
    exact Set.mem_sUnion.mpr ⟨W, ⟨r, hr, ρ, hρ,
      (Action.writes_agree hag'' _).trans hW⟩, hp⟩
  · rintro ⟨W, ⟨r, hr, σ, hσ, hW⟩, hp⟩
    obtain ⟨τ, hτ, hag⟩ := hσ.exists_validQuerySubst
    obtain ⟨hmem, hag'⟩ := mem_matchQuery_of_validQuerySubst he hi hj hτ
    have hag'' : Env.Agree (Env.canon (Query.freeVars r.query []) τ) σ :=
      fun v => (hag' v).symm.trans (hag v)
    apply mem_firingWritesAll.mpr
    refine ⟨(r, _), mem_roundFirings.mpr ⟨hr, hmem⟩, mem_firingWrites.mpr ?_⟩
    exact ⟨W, (Action.writes_agree hag'' _).trans hW, hp⟩

/-- The rows requested for deletion by all successful pre-state firings. -/
def roundDeletes (R : List Rule) (d : FDatabase) : List Term :=
  (roundFirings R d).flatMap fun rs => (actionsDeletes rs.2 rs.1.actions).getD []

private theorem execRunRules_eq_delete_firings (R : List Rule) (d : FDatabase) :
    execRunRules R d = (roundFirings R d).foldl
      (fun acc rs => fireWritesInto rs.1 acc rs.2)
      (d.deleteAtoms d.closureF (roundDeletes R d)) := by
  simp only [execRunRules, execRunRulesWith, roundDeletes, roundFirings,
    matchQueryWith_eq, List.foldl_flatMap, List.foldl_map,
    List.flatMap_map, List.flatMap_assoc]

private theorem mem_firingDeletes {t : Term} {rs : Rule × Env} :
    t ∈ (actionsDeletes rs.2 rs.1.actions).getD [] ↔
      ∃ X, Action.erases rs.2 rs.1.actions = some X ∧ t ∈ X := by
  rw [actionsDeletes_erases]
  cases actionsDeletes rs.2 rs.1.actions <;> simp

/-- The executable collects exactly the specification's simultaneous erase set. -/
theorem roundDeletes_eq_RunErases {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) :
    {t | t ∈ roundDeletes R d} = RunErases R d.toDatabase := by
  ext t
  constructor
  · intro ht
    obtain ⟨⟨r, σ⟩, hrs, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨hr, hσ⟩ := mem_roundFirings.mp hrs
    obtain ⟨X, hX, ht⟩ := mem_firingDeletes.mp ht
    obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_mem_matchQuery he hi hσ
    obtain ⟨ρ, hρ, hag'⟩ := hτ.exists_queryMatches
    have hag'' : Env.Agree ρ σ := fun v => (hag' v).trans (hag v)
    exact Set.mem_sUnion.mpr ⟨X, ⟨r, hr, ρ, hρ,
      (Action.erases_agree hag'' _).trans hX⟩, ht⟩
  · rintro ⟨X, ⟨r, hr, σ, hσ, hX⟩, ht⟩
    obtain ⟨τ, hτ, hag⟩ := hσ.exists_validQuerySubst
    obtain ⟨hmem, hag'⟩ := mem_matchQuery_of_validQuerySubst he hi hj hτ
    have hag'' : Env.Agree (Env.canon (Query.freeVars r.query []) τ) σ :=
      fun v => (hag' v).symm.trans (hag v)
    apply List.mem_flatMap.mpr
    refine ⟨(r, _), mem_roundFirings.mpr ⟨hr, hmem⟩, mem_firingDeletes.mpr ?_⟩
    exact ⟨X, (Action.erases_agree hag'' _).trans hX, ht⟩

/-- Writes preserve closure once all deletions have been applied. -/
theorem closed_execRunRules_of_deleteAtoms {R : List Rule} {d : FDatabase}
    (hb : (d.deleteAtoms d.closureF (roundDeletes R d)).Closed) :
    (execRunRules R d).Closed := by
  rw [execRunRules_eq_delete_firings]
  exact (fold_firingWrites_spec hb _).1

/-- General round decomposition: every pre-state erase precedes every write.
Only closure of the post-deletion base is needed for the write refinement. -/
theorem execRunRules_deletes_writes {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent)
    (hb : (d.deleteAtoms d.closureF (roundDeletes R d)).Closed) :
    (execRunRules R d).toDatabase.SameMeaning
      ((d.deleteAtoms d.closureF (roundDeletes R d)).toDatabase.addEqs
        (RunWrites R d.toDatabase)) := by
  rw [execRunRules_eq_delete_firings, ← firingWritesAll_eq he hi hj]
  exact (fold_firingWrites_spec hb _).2

/-- Delete-free executable rounds preserve the finite store's closure invariant. -/
theorem closed_execRunRules {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hd : ∀ r ∈ R, r.DeleteFree) : (execRunRules R d).Closed := by
  rw [execRunRules_eq_firings R hd]
  exact (fold_firingWrites_spec he _).1

/-- A delete-free round computes the specification up to redundant subterm assertions.
The pre-state's index must faithfully enumerate its held applications. -/
theorem execRunRules_RunRules {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) (hd : ∀ r ∈ R, r.DeleteFree) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R d.toDatabase) := by
  rw [execRunRules_eq_firings R hd, RunRules.eq_addEqs hd,
    ← firingWritesAll_eq he hi hj]
  exact (fold_firingWrites_spec he _).2

theorem FDatabase.IndexOk.addTerm {d : FDatabase} (hi : d.IndexOk) (t : Term) :
    (d.addTerm t).IndexOk := by
  constructor
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
    (d.addEq a b).IndexOk := ⟨((hi.addTerm a).addTerm b).ctor⟩

theorem FDatabase.IndexCurrent.addEq {d : FDatabase} (hi : d.IndexCurrent) (a b : Term) :
    (d.addEq a b).IndexCurrent := (hi.addTerm a).addTerm b

private theorem fold_firingWrites_index {d : FDatabase}
    (hi : d.IndexOk) (hj : d.IndexCurrent) (rss : List (Rule × Env)) :
    let out := rss.foldl (fun acc rs => fireWritesInto rs.1 acc rs.2) d
    out.IndexOk ∧ out.IndexCurrent := by
  induction rss generalizing d with
  | nil => exact ⟨hi, hj⟩
  | cons rs rss ih =>
    apply ih
    all_goals
      unfold fireWritesInto
      dsimp only
      split
      · rename_i e he
        have h := execWrites_preserves
          (P := fun e => e.IndexOk ∧ e.IndexCurrent)
          (fun e t h => ⟨h.1.addTerm t, h.2.addTerm t⟩)
          (fun e a b h _ => ⟨h.1.addEq a b, h.2.addEq a b⟩) ⟨hi, hj⟩ he
        first | exact h.1 | exact h.2
      · first | exact hi | exact hj

/-- The general round preserves an index already preserved by its deletion phase. -/
theorem execRunRules_index_of_deleteAtoms {R : List Rule} {d : FDatabase}
    (hi : (d.deleteAtoms d.closureF (roundDeletes R d)).IndexOk)
    (hj : (d.deleteAtoms d.closureF (roundDeletes R d)).IndexCurrent) :
    (execRunRules R d).IndexOk ∧ (execRunRules R d).IndexCurrent := by
  rw [execRunRules_eq_delete_firings]
  exact fold_firingWrites_index hi hj _

theorem execRunRules_index {R : List Rule} {d : FDatabase}
    (hi : d.IndexOk) (hj : d.IndexCurrent) (hd : ∀ r ∈ R, r.DeleteFree) :
    (execRunRules R d).IndexOk ∧ (execRunRules R d).IndexCurrent := by
  rw [execRunRules_eq_firings R hd]
  exact fold_firingWrites_index hi hj _

private structure InterpReady (d : FDatabase) : Prop where
  closed : d.Closed
  indexOk : d.IndexOk
  indexCurrent : d.IndexCurrent
  wf : d.toDatabase.WF

private theorem InterpReady.round {d : FDatabase} (h : InterpReady d) (R : List Rule)
    (hd : ∀ r ∈ R, r.DeleteFree) : InterpReady (execRunRules R d) := by
  have hi := execRunRules_index h.indexOk h.indexCurrent hd
  refine ⟨closed_execRunRules h.closed hd, hi.1, hi.2, ?_⟩
  exact FDatabase.wf_of_sameMeaning
    (execRunRules_RunRules h.closed h.indexOk h.indexCurrent hd) (RunRules.wf h.wf)

private theorem InterpReady.empty : InterpReady FDatabase.empty := by
  exact ⟨FDatabase.empty_closed, ⟨by simp [FDatabase.empty]⟩,
    by simp [FDatabase.IndexCurrent, FDatabase.empty], FDatabase.empty_wf⟩

private theorem congr_eq_of_sameMeaning {d e : Database} (h : d.SameMeaning e) :
    Cong d = Cong e := by
  funext a b
  exact propext (h.congr a b)

private theorem saturation_meaning_of_fixed {R : List Rule} {d e : Database}
    (hfix : d.SameMeaning (RunRules R d)) (h : SaturateReach R d e) : d.SameMeaning e := by
  cases h with
  | fixpoint => exact hfix
  | again hn _ => exact (hn (congr_eq_of_sameMeaning hfix)).elim

private theorem round_transport {d : FDatabase} {db : Database} (h : InterpReady d)
    (hw : db.WF) (hh : d.toDatabase.SameMeaning db) (R : List Rule)
    (hd : ∀ r ∈ R, r.DeleteFree) (hn : ∀ r ∈ R, r.OrderingFree) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R db) :=
  (execRunRules_RunRules h.closed h.indexOk h.indexCurrent hd).trans
    (SourceMeaning.round_sameMeaning h.wf hw hh hd hn)

private theorem settled_transport {R : List Rule} {d : FDatabase} {db : Database}
    (h : InterpReady d) (hw : db.WF) (hh : d.toDatabase.SameMeaning db)
    (hd : ∀ r ∈ R, r.DeleteFree) (hn : ∀ r ∈ R, r.OrderingFree)
    (hs : d.sameData (execRunRules R d) = true) :
    db.SameMeaning (RunRules R db) ∧ d.toDatabase.SameMeaning (RunRules R db) := by
  have hr := round_transport h hw hh R hd hn
  simp only [FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at hs
  rw [toDatabase_eq_of_fields hs.1.1 hs.2] at hr
  exact ⟨hh.symm.trans hr, hr⟩

private theorem runSaturateF_transport {R : List Rule}
    (hd : ∀ r ∈ R, r.DeleteFree) (hn : ∀ r ∈ R, r.OrderingFree) : ∀ (n : Nat)
    {d e : FDatabase} {db : Database}, InterpReady d → db.WF →
    d.toDatabase.SameMeaning db → d.runSaturateF R n = some e →
    ∃ out, SaturateReach R db out ∧ e.toDatabase.SameMeaning out := by
  intro n
  induction n with
  | zero =>
    intro d e db h hw hh hs
    unfold FDatabase.runSaturateF at hs
    split at hs
    · rename_i hfixed
      cases Option.some.inj hs
      obtain ⟨hfix, hmean⟩ := settled_transport h hw hh hd hn hfixed
      exact ⟨_, .fixpoint (congr_eq_of_sameMeaning hfix), hmean⟩
    · cases hs
  | succ n ih =>
    intro d e db h hw hh hs
    unfold FDatabase.runSaturateF at hs
    split at hs
    · rename_i hfixed
      cases Option.some.inj hs
      obtain ⟨hfix, hmean⟩ := settled_transport h hw hh hd hn hfixed
      exact ⟨_, .fixpoint (congr_eq_of_sameMeaning hfix), hmean⟩
    · obtain ⟨out, hout, hmean⟩ := ih (h.round R hd) (RunRules.wf hw)
        (round_transport h hw hh R hd hn) hs
      by_cases hfix : Cong db = Cong (RunRules R db)
      · have hdb : db.SameMeaning (RunRules R db) := ⟨fun a b => by rw [hfix]⟩
        have hnext := SourceMeaning.round_sameMeaning hw (RunRules.wf hw) hdb hd hn
        exact ⟨_, .fixpoint hfix,
          hmean.trans (saturation_meaning_of_fixed hnext hout).symm⟩
      · exact ⟨out, .again hfix hout, hmean⟩

/-- Successful saturation refines the semantic fixed point for these rules. -/
theorem runSaturateF_saturateReach {R : List Rule} {n : Nat} {d e : FDatabase}
    (he : d.Closed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hw : d.toDatabase.WF)
    (hd : ∀ r ∈ R, r.DeleteFree) (hn : ∀ r ∈ R, r.OrderingFree)
    (hs : d.runSaturateF R n = some e) :
    ∃ out, SaturateReach R d.toDatabase out ∧ e.toDatabase.SameMeaning out :=
  runSaturateF_transport hd hn n ⟨he, hi, hj, hw⟩ hw (.refl _) hs

private theorem InterpReady.iterate {d : FDatabase} (h : InterpReady d)
    (R : List Rule) (hd : ∀ r ∈ R, r.DeleteFree) (k : Nat) :
    InterpReady ((execRunRules R)^[k] d) := by
  induction k with
  | zero => exact h
  | succ k ih => simpa only [Function.iterate_succ_apply'] using ih.round R hd

private theorem InterpReady.saturate {R : List Rule} {n : Nat} {d e : FDatabase}
    (h : InterpReady d) (hd : ∀ r ∈ R, r.DeleteFree)
    (hs : d.runSaturateF R n = some e) : InterpReady e := by
  obtain ⟨k, rfl⟩ := runSaturateF_iterate n hs
  exact h.iterate R hd k

private theorem InterpReady.cmd {d e : FDatabase} (h : InterpReady d) {c : Cmd}
    (hd : ∀ r ∈ c.rules, r.DeleteFree) (he : execCmd d c = some e) : InterpReady e := by
  cases c with
  | run R => cases Option.some.inj he; exact h.round R hd
  | saturate R => exact h.saturate hd he

private theorem execCmd_transport {d e : FDatabase} {db : Database} (h : InterpReady d)
    (hw : db.WF) (hh : d.toDatabase.SameMeaning db) {c : Cmd}
    (hd : ∀ r ∈ c.rules, r.DeleteFree) (hn : c.OrderingFree)
    (he : execCmd d c = some e) :
    ∃ out, CmdStep db c out ∧ e.toDatabase.SameMeaning out := by
  cases c with
  | run R =>
    cases Option.some.inj he
    exact ⟨_, rfl, round_transport h hw hh R hd hn⟩
  | saturate R => exact runSaturateF_transport hd hn _ h hw hh he

/-- A successful command has a specification result with the same meaning. -/
theorem execCmd_cmdStep {d e : FDatabase} (he : d.Closed) (hi : d.IndexOk)
    (hj : d.IndexCurrent) (hw : d.toDatabase.WF) {c : Cmd}
    (hd : ∀ r ∈ c.rules, r.DeleteFree) (hc : c.OrderingFree)
    (hs : execCmd d c = some e) :
    ∃ out, CmdStep d.toDatabase c out ∧ e.toDatabase.SameMeaning out :=
  execCmd_transport ⟨he, hi, hj, hw⟩ hw (.refl _) hd hc hs

private theorem cmd_deleteFree {c : Cmd} (h : c.monotoneB = true) :
    ∀ r ∈ c.rules, r.DeleteFree := by
  intro r hr
  exact Actions.deleteFree_of_all (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h r hr)).2

private theorem execProgram_transport {p : List Cmd} : ∀ {d e : FDatabase} {db : Database},
    InterpReady d → db.WF → d.toDatabase.SameMeaning db →
    (∀ c ∈ p, c.monotoneB = true) → (∀ c ∈ p, c.OrderingFree) →
    execProgram d p = some e →
    ∃ out, ProgramStep db p out ∧ e.toDatabase.SameMeaning out := by
  induction p with
  | nil =>
    intro d e db _ _ hh _ _ hs
    cases Option.some.inj hs
    exact ⟨db, .nil, hh⟩
  | cons c cs ih =>
    intro d e db hd hw hh hm hn hs
    obtain ⟨mid, hmid, hrest⟩ := Option.bind_eq_some_iff.mp hs
    have hc := cmd_deleteFree (hm c (by simp))
    obtain ⟨out, hout, hmean⟩ := execCmd_transport hd hw hh hc (hn c (by simp)) hmid
    obtain ⟨last, hlast, hmean'⟩ := ih (hd.cmd hc hmid) (hout.wf hw) hmean
      (fun c hc => hm c (by simp [hc])) (fun c hc => hn c (by simp [hc])) hrest
    exact ⟨last, .cons hout hlast, hmean'⟩

theorem execProgram_programStep {p : List Cmd} {d e : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) (hw : d.toDatabase.WF)
    (hp : ∀ c ∈ p, c.monotoneB = true) (ho : ∀ c ∈ p, c.OrderingFree)
    (hs : execProgram d p = some e) :
    ∃ out, ProgramStep d.toDatabase p out ∧ e.toDatabase.SameMeaning out :=
  execProgram_transport ⟨he, hi, hj, hw⟩ hw (.refl _) hp ho hs

/-- `exec` executes commands; the final check is a separate observation. -/
theorem exec_programStep {p : Program} {e : FDatabase}
    (hp : ∀ c ∈ p.commands, c.monotoneB = true) (ho : p.OrderingFree)
    (hs : exec p = some e) :
    ∃ out, ProgramStep Database.empty p.commands out ∧ e.toDatabase.SameMeaning out := by
  have h := InterpReady.empty
  simpa only [FDatabase.toDatabase_empty] using
    execProgram_programStep h.closed h.indexOk h.indexCurrent h.wf hp ho.1 hs

theorem closed_iterate {R : List Rule} (k : Nat) {d : FDatabase}
    (he : d.Closed) (hd : ∀ r ∈ R, r.DeleteFree) : ((execRunRules R)^[k] d).Closed := by
  induction k generalizing d with
  | zero => exact he
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (closed_execRunRules he hd)

theorem execCmd_closed {d e : FDatabase} (he : d.Closed) {c : Cmd}
    (hd : ∀ r ∈ c.rules, r.DeleteFree) (hs : execCmd d c = some e) : e.Closed := by
  cases c with
  | run R => cases Option.some.inj hs; exact closed_execRunRules he hd
  | saturate R =>
    obtain ⟨k, rfl⟩ := runSaturateF_iterate _ hs
    exact closed_iterate k he hd

private theorem iterate_transport {R : List Rule}
    (hd : ∀ r ∈ R, r.DeleteFree) (hn : ∀ r ∈ R, r.OrderingFree) : ∀ (k : Nat)
    {d : FDatabase} {db : Database}, InterpReady d → db.WF →
    d.toDatabase.SameMeaning db →
    ((execRunRules R)^[k] d).toDatabase.SameMeaning ((RunRules R)^[k] db) := by
  intro k
  induction k with
  | zero => intro d db _ _ hh; exact hh
  | succ k ih =>
    intro d db h hw hh
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (h.round R hd) (RunRules.wf hw) (round_transport h hw hh R hd hn)

theorem execRunRules_iterate {R : List Rule} (k : Nat) {d : FDatabase}
    (he : d.Closed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hw : d.toDatabase.WF)
    (hd : ∀ r ∈ R, r.DeleteFree) (hn : ∀ r ∈ R, r.OrderingFree) :
    ((execRunRules R)^[k] d).toDatabase.SameMeaning ((RunRules R)^[k] d.toDatabase) :=
  iterate_transport hd hn k ⟨he, hi, hj, hw⟩ hw (.refl _)

/-- Every nonsaturating command succeeds, independently of its rule heads. -/
theorem execCmd_toDatabase {d : FDatabase} {c : Cmd} (hns : c.NoSaturate) :
    (execCmd d c).isSome = true ↔ ∃ out, CmdStep d.toDatabase c out := by
  cases c with
  | run R => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
  | saturate R => exact hns.elim

private theorem execProgram_complete_transport {p : List Cmd} :
    ∀ {d : FDatabase} {db out : Database}, InterpReady d → db.WF →
    d.toDatabase.SameMeaning db → (∀ c ∈ p, c.monotoneB = true) →
    (∀ c ∈ p, c.OrderingFree) → (∀ c ∈ p, c.NoSaturate) → ProgramStep db p out →
    ∃ e, execProgram d p = some e ∧ e.toDatabase.SameMeaning out := by
  induction p with
  | nil =>
    intro d db out _ _ hh _ _ _ hs
    cases hs
    exact ⟨d, rfl, hh⟩
  | cons c cs ih =>
    intro d db out h hw hh hp hn hns hs
    cases c with
    | saturate R => exact (show False from hns (.saturate R) (by simp)).elim
    | run R =>
      cases hs with
      | cons hc hrest =>
        subst_vars
        have hd := cmd_deleteFree (hp (.run R) (by simp))
        have hm := round_transport h hw hh R hd (hn (.run R) (by simp))
        obtain ⟨last, hlast, hmean⟩ := ih (h.round R hd) (RunRules.wf hw) hm
          (fun c hc => hp c (by simp [hc])) (fun c hc => hn c (by simp [hc]))
          (fun c hc => hns c (by simp [hc])) hrest
        exact ⟨last, by simpa [execProgram, execCmd] using hlast, hmean⟩

theorem execProgram_complete {p : List Cmd} {d : FDatabase} {out : Database}
    (he : d.Closed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hw : d.toDatabase.WF)
    (hp : ∀ c ∈ p, c.monotoneB = true) (ho : ∀ c ∈ p, c.OrderingFree)
    (hns : ∀ c ∈ p, c.NoSaturate) (hs : ProgramStep d.toDatabase p out) :
    ∃ e, execProgram d p = some e ∧ e.toDatabase.SameMeaning out :=
  execProgram_complete_transport ⟨he, hi, hj, hw⟩ hw (.refl _) hp ho hns hs

theorem exec_complete {p : Program} {out : Database}
    (hp : ∀ c ∈ p.commands, c.monotoneB = true) (ho : p.OrderingFree) (hns : p.NoSaturate)
    (hs : ProgramStep Database.empty p.commands out) :
    ∃ e, exec p = some e ∧ e.toDatabase.SameMeaning out := by
  have h := InterpReady.empty
  exact execProgram_complete h.closed h.indexOk h.indexCurrent h.wf hp ho.1 hns
    (by simpa only [FDatabase.toDatabase_empty] using hs)

/-- The executable final check agrees with the existential specification query. -/
theorem FDatabase.holds_iff_queryHolds {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) (q : Query) :
    d.holds q = true ↔ QueryHolds d.toDatabase q := by
  simpa only [FDatabase.holds, Bool.not_eq_true'] using
    (queryHolds_iff_matchQuery he hi hj q).symm

private theorem InterpReady.program {cs : List Cmd} {d e : FDatabase}
    (hd : InterpReady d) (hp : ∀ c ∈ cs, c.monotoneB = true)
    (hs : execProgram d cs = some e) : InterpReady e := by
  induction cs generalizing d with
  | nil => cases Option.some.inj hs; exact hd
  | cons c cs ih =>
    obtain ⟨mid, hc, ht⟩ := Option.bind_eq_some_iff.mp hs
    exact ih (hd.cmd (cmd_deleteFree (hp c (by simp))) hc)
      (fun c hc => hp c (by simp [hc])) ht

/-- Command refinement and final-check agreement for the source fragment. -/
theorem exec_programStep_check {p : Program} {e : FDatabase}
    (hp : ∀ c ∈ p.commands, c.monotoneB = true) (ho : p.OrderingFree)
    (hs : exec p = some e) :
    ∃ out, ProgramStep Database.empty p.commands out ∧ e.toDatabase.SameMeaning out ∧
      (e.holds p.check = true ↔ QueryHolds out p.check) := by
  obtain ⟨out, hout, hm⟩ := exec_programStep hp ho hs
  have he := InterpReady.empty.program hp hs
  exact ⟨out, hout, hm, (FDatabase.holds_iff_queryHolds he.closed he.indexOk
    he.indexCurrent p.check).trans
    (SourceMeaning.queryHolds_iff he.wf (hout.wf Database.WF.empty) hm ho.2)⟩

/-- The observer executes exactly the commands before testing the final query. -/
theorem observe_eq_exec (p : Program) : observe p = (exec p).map
    (fun d => if d.holds p.check then .ok d else .checkFailed) := by
  have h : ∀ (cs : List Cmd) (d : FDatabase), cs.foldlM execCmd d = execProgram d cs := by
    intro cs
    induction cs with
    | nil => intro d; rfl
    | cons c cs ih =>
      intro d
      simp only [List.foldlM_cons, execProgram]
      congr 1
      funext e
      exact ih e
  simp only [observe, observeWith, exec, h]

/-- A command simulation with check agreement gives both observable finite outcomes. -/
theorem observe_eval_of_exec {p : Program} {r : ExecutionResult}
    (hcheck : ∀ e, exec p = some e → ∃ out, ProgramStep Database.empty p.commands out ∧
      (e.holds p.check = true ↔ QueryHolds out p.check))
    (hs : observe p = some r) :
    ∃ result, Eval Database.empty p result ∧ result.succeeded = r.succeeded := by
  rw [observe_eq_exec] at hs
  obtain ⟨e, he, hr⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨out, hout, hq⟩ := hcheck e he
  split at hr
  · rename_i hc
    cases hr
    exact ⟨.ok, .ok hout (hq.mp hc), rfl⟩
  · rename_i hc
    cases hr
    exact ⟨.checkFailed, .checkFailed hout (fun h => hc (hq.mpr h)), rfl⟩

/-- The source interpreter's observable success or failure is a specification outcome. -/
theorem observe_eval {p : Program} {r : ExecutionResult}
    (hp : ∀ c ∈ p.commands, c.monotoneB = true) (ho : p.OrderingFree)
    (hs : observe p = some r) :
    ∃ result, Eval Database.empty p result ∧ result.succeeded = r.succeeded := by
  apply observe_eval_of_exec ?_ hs
  intro e he
  obtain ⟨out, hout, _, hq⟩ := exec_programStep_check hp ho he
  exact ⟨out, hout, hq⟩

end Egglog
