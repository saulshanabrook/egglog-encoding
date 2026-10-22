import EgglogSemantics.Proofs.SourceProof.Actions
import EgglogSemantics.Proofs.Completion

namespace Egglog.SourceProof

open Conservativity

def ambient (db : Database) : Database :=
  { db with eqs := db.eqs ∪ {p | p.1 = p.2} }

theorem ambient_refl (db : Database) (t : Term) : StoredCong (ambient db) t t :=
  .direct (Or.inr rfl)

theorem ambient_contains (db : Database) : db.Contained (ambient db) := ⟨fun _ hp => Or.inl hp⟩

/-- Every subterm has a representative that actually exists in the source. -/
def Supports (db : Database) (t : Term) : Prop :=
  ∀ s ∈ t.subterms, ∃ u ∈ db.terms, StoredCong (ambient db) s u

structure Claim.Supported (db : Database) (c : Claim) : Prop where
  equality : c.Holds (ambient db)
  lhs : Supports db c.lhs
  rhs : Supports db c.rhs

theorem supports_of_mem {db : Database} (hw : db.WF) {t : Term} (ht : t ∈ db.terms) :
    Supports db t := fun s hs =>
  ⟨s, hw.subtermClosed t ht hs, ambient_refl db s⟩

theorem Claim.Holds.supported {db : Database} (hw : db.WF) {c : Claim}
    (h : c.Holds db) : c.Supported db :=
  ⟨h.mono (ambient_contains db), supports_of_mem hw (eqsInTerms_free h).1,
    supports_of_mem hw (eqsInTerms_free h).2⟩

private theorem ambient_interpret {db : Database} (hw : db.WF) {a b : Term}
    (hc : StoredCong (ambient db) a b) :
    InferredFacts.interpret db a = InferredFacts.interpret db b := by
  apply InferredFacts.interpret_congr (e := ambient db) ?_ hc
  rintro p (hp | hp)
  · exact InferredFacts.interpret_assert hw hp
  · exact congrArg (InferredFacts.interpret db) hp

theorem Claim.Supported.infers {db : Database} (hw : db.WF) {c : Claim}
    (hc : c.Supported db) : db.Infers c.lhs c.rhs := by
  obtain ⟨u, hu, hlu⟩ := hc.lhs c.lhs (Term.self_mem_subterms _)
  have hi := (ambient_interpret hw hlu).trans (InferredFacts.interpret_of_held hw u hu)
  exact (InferredFacts.infers_iff_interpret hw).mpr
    ⟨u, hu, hi, (ambient_interpret hw hc.equality).symm.trans hi⟩

theorem Claim.Supported.holds {db : Database} (hw : db.WF) {c : Claim}
    (h : c.Supported db) (hl : c.lhs ∈ db.terms) (hr : c.rhs ∈ db.terms) : c.Holds db :=
  (InferredFacts.infers_iff_cong_of_held hw hl hr).mp (h.infers hw)

theorem Claim.Supported.symm {db : Database} {a b : Term}
    (h : Claim.Supported db ⟨a, b⟩) : Claim.Supported db ⟨b, a⟩ :=
  ⟨h.equality.symm, h.rhs, h.lhs⟩

theorem Claim.Supported.trans {db : Database} {a b c : Term}
    (h₁ : Claim.Supported db ⟨a, b⟩) (h₂ : Claim.Supported db ⟨b, c⟩) :
    Claim.Supported db ⟨a, c⟩ := ⟨h₁.equality.trans h₂.equality, h₁.lhs, h₂.rhs⟩

private theorem congrList_set {db : Database} {as : List Term} {i : Nat} {x y : Term}
    (hi : as[i]? = some x) (hxy : StoredCong (ambient db) x y) :
    StoredCongList (ambient db) as (as.set i y) := by
  induction as generalizing i with
  | nil => simp at hi
  | cons a as ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst a
          exact .cons hxy (StoredCongList.refl fun t _ => ambient_refl db t)
      | succ i => exact .cons (ambient_refl db a) (ih hi)

private theorem mem_set_cases {as : List Term} {i : Nat} {y t : Term}
    (ht : t ∈ as.set i y) : t = y ∨ t ∈ as := by
  induction as generalizing i with
  | nil => simp at ht
  | cons a as ih =>
      cases i with
      | zero =>
          rcases List.mem_cons.mp ht with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      | succ i =>
          rcases List.mem_cons.mp ht with h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · exact (ih h).imp_right (List.mem_cons_of_mem _)

/-- The base proof supplies existence of the enclosing application. -/
theorem Claim.Supported.congr {db : Database} {a x y : Term} {f : FnName}
    {as : List Term} {i : Nat} (base : Claim.Supported db ⟨a, .app f as⟩)
    (child : Claim.Supported db ⟨x, y⟩) (hi : as[i]? = some x) :
    Claim.Supported db ⟨a, .app f (as.set i y)⟩ := by
  have hc : StoredCong (ambient db) (.app f as) (.app f (as.set i y)) :=
    .congr (ambient_refl db _) (ambient_refl db _) (congrList_set hi child.equality)
  refine ⟨base.equality.trans hc, base.lhs, ?_⟩
  intro s hs
  cases hs with
  | refl =>
      obtain ⟨u, hu, hcu⟩ := base.rhs _ (Term.self_mem_subterms _)
      exact ⟨u, hu, hc.symm.trans hcu⟩
  | @arg t _ _ ht hst =>
      rcases mem_set_cases ht with rfl | ht
      · exact child.rhs s hst
      · exact base.rhs s (.arg ht hst)

theorem Claim.Supported.completion {db : Database} (hw : db.WF) {c : Claim}
    (hc : c.Supported db) : c.Holds db.completion :=
  (Database.cong_completion_iff hw).mpr (hc.infers hw)

theorem Claim.Supported.of_completion {db : Database} (hw : db.WF) {c : Claim}
    (hc : c.Holds db.completion) : c.Supported db := by
  have hi := (Database.cong_completion_iff hw).mp hc
  have hamb {a b : Term} (h : db.Infers a b) : StoredCong (ambient db) a b := by
    exact h.choose_spec.2.2.mono
      (show (db.withOperands [a, b]).Contained (ambient db) from
        ⟨fun p hp => Conservativity.mem_addTerms_eqs _ db p hp⟩)
  have hs {t : Term} (ht : db.Infers t t) : Supports db t := by
    intro s hst
    obtain ⟨u, hu, hus, _⟩ := InferredFacts.infers_subterm hw ht hst
    exact ⟨u, hu, hus.symm.mono
      (show (db.withOperands [s, s]).Contained (ambient db) from
        ⟨fun p hp => Conservativity.mem_addTerms_eqs _ db p hp⟩)⟩
  exact ⟨hamb hi, hs (InferredFacts.infers_left hw hi),
    hs (InferredFacts.infers_right hw hi)⟩

end Egglog.SourceProof
