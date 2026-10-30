import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.StatePreservation
import EgglogSemantics.Proofs.Order

/-! Deletion preserves proper subterms and respects equal meaning on diagonal stores. -/

namespace Egglog

/-- The paper's reading of deletion: remove the deleted rows' reflexive facts and re-assert
their columns. -/
theorem Database.deleteRows_eq (X : Set Term) (db : Database) :
    db.deleteRows X = { eqs := (db.eqs \ db.deletedFacts X) ∪
      {p | ∃ q ∈ db.deletedFacts X, ∃ c ∈ q.1.children, p = (c, c)} } := by
  apply Database.ext
  ext ⟨a, b⟩
  simp only [Database.deleteRows, Database.deletedFacts, Set.mem_union, Set.mem_diff,
    Set.mem_setOf_eq]
  constructor
  · rintro (⟨hab, hn⟩ | ⟨r, hr, c, hc, he⟩)
    · exact Or.inl ⟨hab, fun h => hn ⟨h.2.1, h.2.2⟩⟩
    · exact Or.inr ⟨(r, r), ⟨hr.1, rfl, hr⟩, c, hc, he⟩
  · rintro (⟨hab, hn⟩ | ⟨⟨q₁, q₂⟩, ⟨hq, hqe, hqd⟩, c, hc, he⟩)
    · exact Or.inl ⟨hab, fun h => hn ⟨hab, h.1, h.2⟩⟩
    · exact Or.inr ⟨q₁, hqd, c, hc, he⟩


/-- On a diagonal store, semantic existence is exactly stored subterm membership. -/
theorem Cong.iff_eq_and_mem_of_diag {db : Database} (hd : db.Diag) {a b : Term} :
    Cong db a b ↔ a = b ∧ a ∈ db.terms := by
  constructor
  · intro h
    induction h using Cong.rec (motive_2 := fun as bs _ => as = bs) with
    | direct hp => exact ⟨hd _ hp, ⟨_, hp, Or.inl (.refl _)⟩⟩
    | subterm _ hs ih => exact ⟨rfl, db.subtermClosed _ ih.2 hs⟩
    | symm _ ih => exact ⟨ih.1.symm, ih.1 ▸ ih.2⟩
    | trans _ _ ih ih' => exact ⟨ih.1.trans ih'.1, ih.2⟩
    | congr _ _ ih ih' => exact ⟨congrArg _ ih', ih.2⟩
    | nil => rfl
    | cons _ _ ih ih' => exact congrArg₂ List.cons ih.1 ih'
  · rintro ⟨rfl, ha⟩
    exact Database.toCong ha

/-- In a diagonal store, deletion names a held application by structural identity. -/
theorem Database.mem_deletedRows_of_diag {db : Database} (hd : db.Diag)
    {X : Set Term} {t : Term} :
    t ∈ db.deletedRows X ↔ (t, t) ∈ db.eqs ∧ t ∈ X ∧ t.isLit = false := by
  constructor
  · rintro ⟨ht, u, hu, f, as, bs, rfl, rfl, hc⟩
    have hab := hc.eq_of_diag hd
    subst bs
    exact ⟨ht, hu, rfl⟩
  · rintro ⟨ht, hx, hn⟩
    cases t with
    | lit l => cases hn
    | app f as =>
      refine ⟨ht, _, hx, f, as, as, rfl, rfl, CongList.refl ?_⟩
      intro a ha
      exact ⟨_, ht, Or.inl (.arg ha (.refl _))⟩

/-- Deletion preserves every proper subterm of a term the pre-state holds, even when
both the enclosing row and that subterm are requested for deletion. -/
theorem Database.proper_subterm_mem_deleteRows {db : Database} (X : Set Term)
    {s t : Term} (ht : t ∈ db.terms) (hs : s ∈ t.subterms) (hne : s ≠ t) :
    s ∈ (db.deleteRows X).terms := by
  classical
  obtain ⟨p, hp, ht | ht⟩ := ht
  all_goals
    have hsp := hs.trans ht
    have hstrict := lt_of_lt_of_le (hs.nodeSize_lt hne) ht.nodeSize_le
    by_cases hg : p.1 = p.2 ∧ p.1 ∈ db.deletedRows X
    · have heq := hg.1
      rcases p with ⟨a, b⟩
      dsimp at heq hsp hstrict hg hp
      subst b
      cases hsp with
      | refl => exact (Nat.lt_irrefl _ hstrict).elim
      | @arg c f as hc hsc =>
        exact ⟨(c, c), Or.inr ⟨_, hg.2, c, hc, rfl⟩, Or.inl hsc⟩
    · exact ⟨p, Or.inl ⟨hp, hg⟩, by first | exact Or.inl hsp | exact Or.inr hsp⟩

/-- The held terms after deletion depend only on the old held terms in a diagonal
state. Literal terms and proper subterms survive. -/
theorem Database.mem_deleteRows_terms_of_diag {db : Database} (hd : db.Diag)
    {X : Set Term} {s : Term} :
    s ∈ (db.deleteRows X).terms ↔ s ∈ db.terms ∧
      (¬ (s ∈ X ∧ s.isLit = false) ∨ ∃ t ∈ db.terms, s ≠ t ∧ s ∈ t.subterms) := by
  classical
  constructor
  · intro hs
    refine ⟨db.deleteRows_terms_subset X hs, ?_⟩
    obtain ⟨⟨a, b⟩, hp | ⟨r, hr, c, hc, heq⟩, hsub⟩ := hs
    · have hab : a = b := hd _ hp.1
      subst b
      have hsa := hsub.elim id id
      by_cases heq : s = a
      · subst a
        exact Or.inl (fun hx => hp.2 ⟨rfl, (db.mem_deletedRows_of_diag hd).mpr
          ⟨hp.1, hx⟩⟩)
      · exact Or.inr ⟨a, ⟨_, hp.1, Or.inl (.refl _)⟩, heq, hsa⟩
    · cases heq
      have hsc := hsub.elim id id
      cases r with
      | lit l => simp [Term.children] at hc
      | app f as =>
        refine Or.inr ⟨.app f as, ⟨_, hr.1, Or.inl (.refl _)⟩, ?_, .arg hc hsc⟩
        intro heq
        have hlt := lt_of_le_of_lt hsc.nodeSize_le (Term.nodeSize_lt_app (f := f) hc)
        rw [heq] at hlt
        exact (Nat.lt_irrefl _ hlt)
  · rintro ⟨hs, hkeep | ⟨t, ht, hne, hsub⟩⟩
    · obtain ⟨⟨a, b⟩, hp, hsub⟩ := hs
      have hab : a = b := hd _ hp
      subst b
      have hsa := hsub.elim id id
      by_cases heq : s = a
      · subst a
        refine ⟨(s, s), Or.inl ⟨hp, ?_⟩, Or.inl (.refl _)⟩
        intro hg
        exact hkeep ((db.mem_deletedRows_of_diag hd).mp hg.2).2
      · exact db.proper_subterm_mem_deleteRows X
          ⟨(a, a), hp, Or.inl (.refl _)⟩ hsa heq
    · exact db.proper_subterm_mem_deleteRows X ht hsub hne

/-- Equal meaning is a congruence for deletion on diagonal states; redundant reflexive
subterm assertions do not change the result. -/
theorem Database.SameMeaning.deleteRows_of_diag {d e : Database}
    (h : d.SameMeaning e) (hd : d.Diag) (he : e.Diag) (X : Set Term) :
    (d.deleteRows X).SameMeaning (e.deleteRows X) := by
  have ht := h.terms_eq_of_diag hd he
  refine ⟨fun a b => ?_⟩
  rw [Cong.iff_eq_and_mem_of_diag (hd.deleteRows X),
    Cong.iff_eq_and_mem_of_diag (he.deleteRows X),
    Database.mem_deleteRows_terms_of_diag hd, Database.mem_deleteRows_terms_of_diag he, ht]

end Egglog
