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

/-- If `v` is absent from the first environment, lookup in the append reads the second. -/
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

theorem Agree.symm {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) : Agree σ₂ σ₁ := fun v => (h v).symm

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

@[simp] theorem sUnion_eqs {db : Database} {S : Set Database} :
    (db.sUnion S).eqs = db.eqs ∪ ⋃ d ∈ S, d.eqs := rfl

/-! ### `addTerms`

`addTerms` is a fold, so its untouched fields need an induction rather than `rfl`. -/

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

@[simp] theorem addSubsumed_empty (db : Database) : db.addSubsumed ∅ = db := by
  apply Database.ext <;> simp [addSubsumed]

@[simp] theorem addSubsumed_eqs (db : Database) (X : Set Term) :
    (db.addSubsumed X).eqs = db.eqs := rfl

@[simp] theorem addSubsumed_subsumed (db : Database) (X : Set Term) :
    (db.addSubsumed X).subsumed = db.subsumed ∪ X := rfl

@[simp] theorem addSubsumed_terms (db : Database) (X : Set Term) :
    (db.addSubsumed X).terms = db.terms := rfl

@[simp] theorem addEq_subsumed (db : Database) (a b : Term) :
    (db.addEq a b).subsumed = db.subsumed := rfl

@[simp] theorem addTerms_subsumed (db : Database) (ts : List Term) :
    (db.addTerms ts).subsumed = db.subsumed := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih (db.addTerm t)

theorem live_of_subsumed_empty {db : Database} (h : db.subsumed = ∅) :
    db.live = {t | Cong db t t} := by
  ext t
  simp [Database.live, h]

namespace Contained

theorem addSubsumed (db : Database) (X : Set Term) :
    db.Contained (db.addSubsumed X) := ⟨subset_rfl, Set.subset_union_left⟩

theorem refl (db : Database) : Contained db db := ⟨subset_rfl, subset_rfl⟩

theorem trans {d₁ d₂ d₃ : Database} (h₁ : Contained d₁ d₂) (h₂ : Contained d₂ d₃) :
    Contained d₁ d₃ := ⟨h₁.eqs.trans h₂.eqs, h₁.subsumed.trans h₂.subsumed⟩

theorem addTerm (t : Term) (db : Database) : Contained db (db.addTerm t) :=
  ⟨Set.subset_insert _ _, subset_rfl⟩

theorem addTerms (ts : List Term) (db : Database) : Contained db (db.addTerms ts) := by
  induction ts generalizing db with
  | nil => exact refl db
  | cons t ts ih => exact (addTerm t db).trans (ih (db := db.addTerm t))

theorem addEq (a b : Term) (db : Database) : Contained db (db.addEq a b) :=
  ⟨Set.subset_insert _ _, subset_rfl⟩

/-! The same operation applied to both sides. This is what makes an action, and hence a
whole action block, transportable along `Contained`. -/
/-- `Contained` is preserved by adding the same term to both sides. -/
theorem addTerm_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (t : Term) :
    (d₁.addTerm t).Contained (d₂.addTerm t) :=
  ⟨Set.insert_subset_insert h.eqs, h.subsumed⟩

/-- `addTerm_mono` folded. -/
theorem addTerms_mono {d₁ d₂ : Database} (h : d₁.Contained d₂) (ts : List Term) :
    (d₁.addTerms ts).Contained (d₂.addTerms ts) := by
  induction ts generalizing d₁ d₂ with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm_mono t)

theorem mem_sUnion {db d : Database} {S : Set Database} (h : d ∈ S) :
    Contained d (db.sUnion S) :=
  ⟨fun _ ht => Or.inr (Set.mem_biUnion h ht),
    fun _ ht => Or.inr (Set.mem_biUnion h ht)⟩

end Contained
namespace WF

theorem addSubsumed {db : Database} (h : WF db) (X : Set Term) :
    WF (db.addSubsumed X) := ⟨h.litsIsolated⟩

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

theorem mem_terms_of_eqs {d e : Database} (h : d.eqs ⊆ e.eqs) {t : Term}
    (ht : t ∈ d.terms) : t ∈ e.terms := by
  obtain ⟨p, hp, ht⟩ := ht
  exact ⟨p, h hp, ht⟩

end Database
end Egglog
