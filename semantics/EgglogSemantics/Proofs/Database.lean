import EgglogSemantics.Spec.Congruence
import EgglogSemantics.Proofs.Term
import EgglogSemantics.Proofs.StoredCong

namespace Egglog
namespace Env
/-- `lookup` is left-biased: a binding in the prefix wins. -/
theorem lookup_append_of_some {v : Var} {t : Term} {σ₁ σ₂ : Env}
    (h : lookup v σ₁ = some t) : lookup v (σ₁ ++ σ₂) = some t := by
  induction σ₁ with
  | nil => rw [lookup] at h; exact absurd h (by simp)
  | cons b σ ih =>
      obtain ⟨w, u⟩ := b
      rw [List.cons_append, lookup]
      rw [lookup] at h
      split at h
      · rename_i hvw; rw [if_pos hvw]; exact h
      · rename_i hvw; rw [if_neg hvw]; exact ih h

@[inherit_doc lookup_append_of_some]
theorem lookup_append_of_none {v : Var} {σ₁ σ₂ : Env} (h : lookup v σ₁ = none) :
    lookup v (σ₁ ++ σ₂) = lookup v σ₂ := by
  induction σ₁ with
  | nil => rfl
  | cons b σ ih =>
      obtain ⟨w, u⟩ := b
      rw [List.cons_append, lookup]
      rw [lookup] at h
      split at h
      · exact absurd h (by simp)
      · rename_i hvw; rw [if_neg hvw]; exact ih h

@[simp] theorem lookup_nil {v : Var} : lookup v [] = none := rfl

@[simp] theorem lookup_cons {v w : Var} {t : Term} {σ : Env} :
    lookup v ((w, t) :: σ) = if v = w then some t else lookup v σ := rfl

@[simp] theorem dom_nil : dom [] = [] := rfl

@[simp] theorem dom_cons {v : Var} {t : Term} {σ : Env} :
    dom ((v, t) :: σ) = v :: dom σ := rfl

theorem mem_dom_of_mem {b : Var × Term} {σ : Env} (h : b ∈ σ) : b.1 ∈ dom σ :=
  List.mem_map_of_mem h

theorem mem_dom_iff {v : Var} {σ : Env} : v ∈ dom σ ↔ ∃ t, (v, t) ∈ σ := by
  constructor
  · intro h
    obtain ⟨⟨w, t⟩, hb, rfl⟩ := List.mem_map.mp h
    exact ⟨t, hb⟩
  · rintro ⟨t, hb⟩
    exact mem_dom_of_mem hb

@[simp] theorem dom_append {σ₁ σ₂ : Env} : dom (σ₁ ++ σ₂) = dom σ₁ ++ dom σ₂ :=
  List.map_append ..

theorem lookup_isSome_iff_mem_dom {v : Var} {σ : Env} :
    (lookup v σ).isSome ↔ v ∈ dom σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases h : v = w <;> simp [h, ih]

theorem lookup_eq_none_iff {v : Var} {σ : Env} : lookup v σ = none ↔ v ∉ dom σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases h : v = w <;> simp [h, ih]

/-- Appending environments never fails, unlike `Env.Union2`, because the only appends
this semantics performs are of a substitution onto the globals, whose domains are
disjoint (`Pattern.freeVars_lookup_eq_none`). `lookup` is left-biased, so `σ₁` shadows
`σ₂` — the same bias `Env.Union2` has. -/
theorem lookup_append_of_not_mem {v : Var} {σ₁ σ₂ : Env} (h : v ∉ dom σ₁) :
    lookup v (σ₁ ++ σ₂) = lookup v σ₂ := by
  induction σ₁ with
  | nil => rfl
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    simp only [dom_cons, List.mem_cons, not_or] at h
    simp [h.1, ih h.2]

theorem lookup_append_of_mem {v : Var} {σ₁ σ₂ : Env} (h : v ∈ dom σ₁) :
    lookup v (σ₁ ++ σ₂) = lookup v σ₁ := by
  induction σ₁ with
  | nil => simp at h
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases hv : v = w
    · simp [hv]
    · simp only [dom_cons, List.mem_cons] at h
      simp [hv, ih (h.resolve_left hv)]

theorem mem_of_lookup {v : Var} {t : Term} {σ : Env} (h : lookup v σ = some t) :
    (v, t) ∈ σ := by
  induction σ with
  | nil => simp at h
  | cons b σ ih =>
    obtain ⟨w, u⟩ := b
    by_cases hv : v = w
    · subst hv
      rw [lookup_cons, if_pos rfl] at h
      cases h
      simp
    · rw [lookup_cons, if_neg hv] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- With no duplicate variables, `lookup` is just membership. -/
theorem lookup_eq_some_iff_mem {v : Var} {t : Term} {σ : Env} (hnd : (dom σ).Nodup) :
    lookup v σ = some t ↔ (v, t) ∈ σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, u⟩ := b
    rw [dom_cons, List.nodup_cons] at hnd
    by_cases hv : v = w
    · subst hv
      simp only [lookup_cons, ↓reduceIte, Option.some.injEq, List.mem_cons, Prod.mk.injEq,
        true_and]
      exact ⟨fun h => Or.inl h.symm,
        fun h => h.elim Eq.symm fun hmem => absurd (mem_dom_of_mem hmem) hnd.1⟩
    · simp only [lookup_cons, hv, ↓reduceIte, List.mem_cons, Prod.mk.injEq, ih hnd.2,
        false_and, false_or]

theorem Agree.refl (σ : Env) : Agree σ σ := fun _ => rfl

theorem Agree.symm {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) : Agree σ₂ σ₁ := fun v => (h v).symm

theorem Agree.trans {σ₁ σ₂ σ₃ : Env} (h₁ : Agree σ₁ σ₂) (h₂ : Agree σ₂ σ₃) :
    Agree σ₁ σ₃ := fun v => (h₁ v).trans (h₂ v)

/-- Reordering a duplicate-free environment's bindings changes no lookup. This is
what makes `ValidEnv`'s use of `Perm`, rather than fixing the order of `σ`'s bindings,
observationally harmless. -/
theorem Agree.of_perm {σ₁ σ₂ : Env} (h : σ₁.Perm σ₂) (hnd : (dom σ₁).Nodup) :
    Agree σ₁ σ₂ := by
  have hp : (dom σ₁).Perm (dom σ₂) := h.map Prod.fst
  intro v
  cases hl : lookup v σ₁ with
  | some t =>
    exact ((lookup_eq_some_iff_mem (hp.nodup hnd)).mpr
      (h.mem_iff.mp ((lookup_eq_some_iff_mem hnd).mp hl))).symm
  | none =>
    rw [lookup_eq_none_iff] at hl
    exact (lookup_eq_none_iff.mpr fun hv => hl (hp.mem_iff.mpr hv)).symm

/-- Agreement survives a shared prefix, which is how a substitution's agreement
lifts to the globals it is appended to. -/
theorem Agree.append_left (ρ : Env) {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) :
    Agree (ρ ++ σ₁) (ρ ++ σ₂) := by
  intro v
  by_cases hv : v ∈ dom ρ
  · rw [lookup_append_of_mem hv, lookup_append_of_mem hv]
  · rw [lookup_append_of_not_mem hv, lookup_append_of_not_mem hv]
    exact h v

/-- Agreement survives a shared **suffix**, which is the order a rule firing appends in: the
substitution first, the globals behind it (`evalLocalActions`). -/
theorem Agree.append_right (ρ : Env) {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) :
    Agree (σ₁ ++ ρ) (σ₂ ++ ρ) := by
  intro v
  by_cases hv : v ∈ dom σ₁
  · have hv₂ : v ∈ dom σ₂ := by
      rw [← lookup_isSome_iff_mem_dom, ← h v, lookup_isSome_iff_mem_dom]; exact hv
    rw [lookup_append_of_mem hv, lookup_append_of_mem hv₂]; exact h v
  · have hv₂ : v ∉ dom σ₂ := by
      rw [← lookup_eq_none_iff, ← h v, lookup_eq_none_iff]; exact hv
    rw [lookup_append_of_not_mem hv, lookup_append_of_not_mem hv₂]

end Env
/-! ### What the database holds -/

/-- Both sides of a derivable equation are present. -/
theorem eqsInTerms_free {db : Database} {a b : Term} (h : StoredCong db a b) :
    a ∈ db.terms ∧ b ∈ db.terms := ⟨h.trans h.symm, h.symm.trans h⟩

/-- Subterm existence follows from congruence, independently of well-formedness. -/
theorem Database.subtermClosed (db : Database) :
    ∀ t ∈ db.terms, t.subterms ⊆ db.terms :=
  fun _ ht _ hs => (StoredCong.subterm (Database.toStored ht) hs).toHeld

theorem Database.WF.subtermClosed {db : Database} (_h : db.WF) :
    ∀ t ∈ db.terms, t.subterms ⊆ db.terms := db.subtermClosed

/-- Congruence endpoints occur within asserted equations. -/
theorem StoredCong.mem_endpoints {db : Database} {a b : Term} (h : StoredCong db a b) :
    (∃ p ∈ db.eqs, a ∈ p.1.subterms ∨ a ∈ p.2.subterms) ∧
      (∃ p ∈ db.eqs, b ∈ p.1.subterms ∨ b ∈ p.2.subterms) := by
  induction h using StoredCong.rec (motive_2 := fun _ _ _ => True) with
  | direct hab =>
    exact ⟨⟨_, hab, Or.inl (Term.self_mem_subterms _)⟩,
      ⟨_, hab, Or.inr (Term.self_mem_subterms _)⟩⟩
  | subterm _ hs ih =>
    obtain ⟨p, hp, ht⟩ := ih.1
    have hm := ht.elim (fun ht => Or.inl (Term.subterms_subset_of_mem ht hs))
      (fun ht => Or.inr (Term.subterms_subset_of_mem ht hs))
    exact ⟨⟨p, hp, hm⟩, ⟨p, hp, hm⟩⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | congr _ _ _ ih₁ ih₂ _ => exact ⟨ih₁.1, ih₂.1⟩
  | nil => trivial
  | cons => trivial

namespace Database
/-- Held terms are precisely subterms of asserted endpoints. -/
theorem mem_terms_iff {db : Database} {t : Term} :
    t ∈ db.terms ↔ ∃ p ∈ db.eqs, t ∈ p.1.subterms ∨ t ∈ p.2.subterms := Iff.rfl

/-- Two databases asserting the same equations hold the same values. -/
theorem terms_eq_of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) :
    d₁.terms = d₂.terms := by
  ext t
  simp only [mem_terms_iff, h]

@[simp] theorem empty_terms : Database.empty.terms = ∅ := by
  ext t; simp [mem_terms_iff, Database.empty]

@[simp] theorem addTerm_terms {t : Term} {db : Database} :
    (db.addTerm t).terms = db.terms ∪ t.subterms := by
  ext s
  simp only [mem_terms_iff, Database.addTerm, Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro ⟨p, rfl | hp, hs⟩
    · exact Or.inr (hs.elim id id)
    · exact Or.inl ⟨p, hp, hs⟩
  · rintro (⟨p, hp, hs⟩ | hs)
    · exact ⟨p, Or.inr hp, hs⟩
    · exact ⟨(t, t), Or.inl rfl, Or.inl hs⟩

@[simp] theorem addTerm_eqs {t : Term} {db : Database} :
    (db.addTerm t).eqs = insert (t, t) db.eqs := rfl


theorem mem_addTerm (t : Term) (db : Database) : t ∈ (db.addTerm t).terms :=
  (StoredCong.direct (Set.mem_insert _ _)).toHeld

@[simp] theorem addEq_eqs {a b : Term} {db : Database} :
    (db.addEq a b).eqs = insert (a, b) db.eqs := rfl

@[simp] theorem addEq_terms {a b : Term} {db : Database} :
    (db.addEq a b).terms = db.terms ∪ a.subterms ∪ b.subterms := by
  ext s
  simp only [mem_terms_iff, Database.addEq, Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro ⟨p, rfl | hp, hs⟩
    · exact hs.elim (fun hs => Or.inl (Or.inr hs)) Or.inr
    · exact Or.inl (Or.inl ⟨p, hp, hs⟩)
  · rintro ((⟨p, hp, hs⟩ | hs) | hs)
    · exact ⟨p, Or.inr hp, hs⟩
    · exact ⟨(a, b), Or.inl rfl, Or.inl hs⟩
    · exact ⟨(a, b), Or.inl rfl, Or.inr hs⟩

/-- Asserting an equation between held terms adds no terms. -/
theorem terms_insert_eq {db : Database} {a b : Term} (ha : a ∈ db.terms) (hb : b ∈ db.terms) :
    ({ db with eqs := insert (a, b) db.eqs } : Database).terms = db.terms := by
  change (db.addEq a b).terms = _
  rw [addEq_terms, Set.union_eq_self_of_subset_right (db.subtermClosed a ha),
    Set.union_eq_self_of_subset_right (db.subtermClosed b hb)]


@[simp] theorem sUnion_eqs {db : Database} {S : Set Database} :
    (db.sUnion S).eqs = db.eqs ∪ ⋃ d ∈ S, d.eqs := rfl

@[simp] theorem sUnion_terms {db : Database} {S : Set Database} :
    (db.sUnion S).terms = db.terms ∪ ⋃ d ∈ S, d.terms := by
  ext s
  simp only [Set.mem_union, Set.mem_iUnion, mem_terms_iff, sUnion_eqs, exists_prop]
  constructor
  · rintro ⟨p, hp | ⟨d, hd, hp⟩, hs⟩
    · exact Or.inl ⟨p, hp, hs⟩
    · exact Or.inr ⟨d, hd, p, hp, hs⟩
  · rintro (⟨p, hp, hs⟩ | ⟨d, hd, p, hp, hs⟩)
    · exact ⟨p, Or.inl hp, hs⟩
    · exact ⟨p, Or.inr ⟨d, hd, hp⟩, hs⟩


/-! ### `addTerms`

`addTerms` is a fold, so its untouched fields need an induction rather than `rfl`. -/

/-- One extension by a concatenation is two extensions in a row: the fold law that lets an
appended operand list be worked with as the nested `(db.addTerms ts).addTerms us` every
other `addTerms` lemma is stated at. -/
theorem addTerms_append {db : Database} {ts us : List Term} :
    db.addTerms (ts ++ us) = (db.addTerms ts).addTerms us :=
  List.foldl_append ..


@[simp] theorem addTerms_eqs {db : Database} {ts : List Term} :
    (db.addTerms ts).eqs = db.eqs ∪ {p | ∃ t ∈ ts, p = (t, t)} := by
  induction ts generalizing db with
  | nil => simp [addTerms]
  | cons t ts ih =>
    change ((db.addTerm t).addTerms ts).eqs = _
    rw [ih, addTerm_eqs]
    ext p
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, List.mem_cons]
    constructor
    · rintro ((rfl | hp) | ⟨u, hu, rfl⟩)
      · exact Or.inr ⟨t, Or.inl rfl, rfl⟩
      · exact Or.inl hp
      · exact Or.inr ⟨u, Or.inr hu, rfl⟩
    · rintro (hp | ⟨u, rfl | hu, rfl⟩)
      · exact Or.inl (Or.inr hp)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨u, hu, rfl⟩

@[simp] theorem addTerms_terms {db : Database} {ts : List Term} :
    (db.addTerms ts).terms = db.terms ∪ {s | ∃ t ∈ ts, s ∈ t.subterms} := by
  induction ts generalizing db with
  | nil => change db.terms = _; simp
  | cons t ts ih =>
    change ((db.addTerm t).addTerms ts).terms = _
    rw [ih, addTerm_terms]
    ext s
    simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons]
    constructor
    · rintro ((hs | hs) | ⟨u, hu, hs⟩)
      · exact Or.inl hs
      · exact Or.inr ⟨t, Or.inl rfl, hs⟩
      · exact Or.inr ⟨u, Or.inr hu, hs⟩
    · rintro (hs | ⟨u, rfl | hu, hs⟩)
      · exact Or.inl (Or.inl hs)
      · exact Or.inl (Or.inr hs)
      · exact Or.inr ⟨u, hu, hs⟩

theorem mem_addTerms {db : Database} {ts : List Term} {t : Term} (h : t ∈ ts) :
    t ∈ (db.addTerms ts).terms :=
  addTerms_terms ▸ Or.inr ⟨t, h, t.self_mem_subterms⟩


namespace Contained
theorem refl (db : Database) : Contained db db := ⟨subset_rfl⟩

theorem trans {d₁ d₂ d₃ : Database} (h₁ : Contained d₁ d₂) (h₂ : Contained d₂ d₃) :
    Contained d₁ d₃ := ⟨h₁.eqs.trans h₂.eqs⟩

theorem addTerm (t : Term) (db : Database) : Contained db (db.addTerm t) :=
  ⟨Set.subset_insert _ _⟩

theorem addTerms (ts : List Term) (db : Database) : Contained db (db.addTerms ts) := by
  induction ts generalizing db with
  | nil => exact refl db
  | cons t ts ih => exact (addTerm t db).trans (ih (db := db.addTerm t))

theorem addEq (a b : Term) (db : Database) : Contained db (db.addEq a b) :=
  ⟨Set.subset_insert _ _⟩

/-! The same operation applied to both sides. This is what makes an action, and hence a
whole action block, transportable along `Contained`. -/
/-- `Contained` is preserved by adding the same term to both sides. -/
theorem addTerm_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (t : Term) :
    (d₁.addTerm t).Contained (d₂.addTerm t) :=
  ⟨Set.insert_subset_insert h.eqs⟩

/-- `addTerm_mono` folded. -/
theorem addTerms_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (ts : List Term) :
    (d₁.addTerms ts).Contained (d₂.addTerms ts) := by
  induction ts generalizing d₁ d₂ with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm_mono t)

/-- The same equality is inserted on both sides, so `Set.insert_subset_insert` closes the
`eqs` component. -/
theorem addEq_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (a b : Term) :
    (d₁.addEq a b).Contained (d₂.addEq a b) :=
  ⟨Set.insert_subset_insert h.eqs⟩

theorem sUnion (db : Database) (S : Set Database) : Contained db (db.sUnion S) :=
  ⟨Set.subset_union_left⟩

theorem mem_sUnion {db d : Database} {S : Set Database} (h : d ∈ S) :
    Contained d (db.sUnion S) :=
  ⟨fun _ ht => Or.inr (Set.mem_biUnion h ht)⟩

end Contained
namespace WF
theorem empty : WF Database.empty where
  litsIsolated := by simp [Database.empty, LitsIsolated]

theorem addTerm {db : Database} (h : WF db) (t : Term) : WF (db.addTerm t) where
  litsIsolated := by
    rintro p (rfl | hp)
    exacts [fun _ => rfl, h.litsIsolated p hp]

theorem addTerms {db : Database} (h : WF db) (ts : List Term) : WF (db.addTerms ts) := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem addEq {db : Database} (h : WF db) (a b : Term)
    (hlit : a.isLit ∨ b.isLit → a = b) : WF (db.addEq a b) where
  litsIsolated := by
    rintro p (rfl | hp)
    · exact hlit
    · exact h.litsIsolated p hp

theorem sUnion {db : Database} (h : WF db) {S : Set Database}
    (hS : ∀ d ∈ S, WF d) : WF (db.sUnion S) where
  litsIsolated := by
    rintro p (hp | hp)
    · exact h.litsIsolated p hp
    · obtain ⟨d, hd, hp⟩ := Set.mem_iUnion₂.mp hp
      exact (hS d hd).litsIsolated p hp

end WF
end Database
end Egglog
