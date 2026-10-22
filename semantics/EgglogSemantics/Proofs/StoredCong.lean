import EgglogSemantics.Spec.Congruence

/-! The finite stored congruence used by the compiler invariants. -/

namespace Egglog
mutual
inductive StoredCong (db : Database) : Term → Term → Prop where
  | direct {a b : Term} : (a, b) ∈ db.eqs → StoredCong db a b
  | subterm {t s : Term} : StoredCong db t t → s ∈ t.subterms → StoredCong db s s
  | symm {a b : Term} : StoredCong db a b → StoredCong db b a
  | trans {a b c : Term} : StoredCong db a b → StoredCong db b c → StoredCong db a c
  | congr {f : FnName} {as bs : List Term} :
      StoredCong db (.app f as) (.app f as) → StoredCong db (.app f bs) (.app f bs) →
      StoredCongList db as bs → StoredCong db (.app f as) (.app f bs)

/-- Pointwise `StoredCong` over argument lists. -/
inductive StoredCongList (db : Database) : List Term → List Term → Prop where
  | nil : StoredCongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      StoredCong db a b → StoredCongList db as bs → StoredCongList db (a :: as) (b :: bs)

end

private theorem subterm_trans {s t u : Term}
    (hs : s ∈ t.subterms) (ht : t ∈ u.subterms) : s ∈ u.subterms := by
  induction ht with
  | refl => exact hs
  | arg hm _ ih => exact .arg hm ih

/-- A stored derivation cannot introduce an unstored endpoint. -/
theorem StoredCong.toHeld {db : Database} {a b : Term} (h : StoredCong db a b) :
    a ∈ db.terms := by
  have hh : a ∈ db.terms ∧ b ∈ db.terms := by
    induction h using StoredCong.rec (motive_2 := fun _ _ _ => True) with
    | direct hp => exact ⟨⟨_, hp, .inl (.refl _)⟩, ⟨_, hp, .inr (.refl _)⟩⟩
    | subterm _ hs ih =>
        obtain ⟨p, hp, ht⟩ := ih.1
        have hm := ht.elim (fun ht => Or.inl (subterm_trans hs ht))
          (fun ht => Or.inr (subterm_trans hs ht))
        exact ⟨⟨p, hp, hm⟩, ⟨p, hp, hm⟩⟩
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
    | congr _ _ _ ih₁ ih₂ _ => exact ⟨ih₁.1, ih₂.1⟩
    | nil => trivial
    | cons => trivial
  exact hh.1

/-- Raw stored terms have a reflexive stored derivation. -/
theorem Database.toStored {db : Database} {t : Term} (h : t ∈ db.terms) :
    StoredCong db t t := by
  obtain ⟨p, hp, ht | ht⟩ := h
  · exact .subterm ((StoredCong.direct hp).trans (.symm (.direct hp))) ht
  · exact .subterm ((StoredCong.direct hp).symm.trans (.direct hp)) ht

theorem Database.mem_terms_iff_storedCong {db : Database} {t : Term} :
    t ∈ db.terms ↔ StoredCong db t t := ⟨Database.toStored, StoredCong.toHeld⟩

instance {db : Database} {t : Term} : Coe (t ∈ db.terms) (StoredCong db t t) :=
  ⟨Database.toStored⟩

instance {db : Database} {t : Term} : Coe (StoredCong db t t) (t ∈ db.terms) :=
  ⟨StoredCong.toHeld⟩

/-- `db` plus the terms `ts`, used to relate a term the database may not hold — a pattern
instance, say — to one it does. It records that each of `ts` exists and **adds no equation
between distinct terms**, so it can relate `a` to `b` only for a reason `db` already had. -/
def Database.withOperands (db : Database) (ts : List Term) : Database := db.addTerms ts

@[inherit_doc Database.withOperands] def StoredCongOn
    (db : Database) (ts : List Term) (a b : Term) : Prop := StoredCong (db.withOperands ts) a b

/-- An inferred equality has a witness in the original database. Its diagonal expresses
represented existence; merely mentioning an absent term does not establish it. -/
def Database.Infers (db : Database) (a b : Term) : Prop :=
  ∃ w ∈ db.terms, StoredCongOn db [a, b] w a ∧ StoredCongOn db [a, b] a b


end Egglog
