import EgglogSemantics.Proofs.Congruence

namespace Egglog

/-- Every subterm of an existing term exists, by iterating the child rule. -/
theorem Cong.subterm {db : Database} {t s : Term} (h : Cong db t t)
    (hs : s ∈ t.subterms) : Cong db s s := by
  induction hs with
  | refl => exact h
  | arg ha _ ih => exact ih (.child h ha)

mutual

theorem StoredCong.toCong {db : Database} {a b : Term} (h : StoredCong db a b) :
    Cong db a b := by
  match h with
  | .direct hp => exact .direct hp
  | .subterm ht hs => exact .subterm ht.toCong hs
  | .symm h => exact .symm h.toCong
  | .trans h₁ h₂ => exact .trans h₁.toCong h₂.toCong
  | .congr ha _ hs => exact .congr ha.toCong hs.toCong

theorem StoredCongList.toCong {db : Database} {as bs : List Term}
    (h : StoredCongList db as bs) : CongList db as bs := by
  match h with
  | .nil => exact .nil
  | .cons h hs => exact .cons h.toCong hs.toCong

end

theorem Database.toCong {db : Database} {t : Term} (h : t ∈ db.terms) : Cong db t t :=
  (Database.toStored h).toCong

namespace CongList

theorem forall₂ {db : Database} {as bs : List Term} :
    CongList db as bs ↔ List.Forall₂ (Cong db) as bs := by
  constructor
  · intro h
    induction h using CongList.rec (motive_1 := fun _ _ _ => True) with
    | nil => exact .nil
    | cons h _ _ ih => exact .cons h ih
    | _ => trivial
  · intro h
    induction h with
    | nil => exact .nil
    | cons h _ ih => exact .cons h ih

theorem refl {db : Database} {as : List Term} (h : ∀ a ∈ as, a ∈ db.terms) :
    CongList db as as := (StoredCongList.refl h).toCong

theorem symm {db : Database} {as bs : List Term} (h : CongList db as bs) :
    CongList db bs as := by
  match h with
  | .nil => exact .nil
  | .cons h hs => exact .cons h.symm hs.symm

theorem trans {db : Database} {as bs cs : List Term}
    (h₁ : CongList db as bs) (h₂ : CongList db bs cs) : CongList db as cs := by
  match h₁, h₂ with
  | .nil, .nil => exact .nil
  | .cons h₁ hs₁, .cons h₂ hs₂ => exact .cons (h₁.trans h₂) (hs₁.trans hs₂)

end CongList

mutual

theorem Cong.mono {d e : Database} (h : d.Contained e) {a b : Term}
    (hc : Cong d a b) : Cong e a b := by
  match hc with
  | .direct hp => exact .direct (h.eqs hp)
  | .child ht hs => exact .child (ht.mono h) hs
  | .symm ht => exact .symm (ht.mono h)
  | .trans hl hr => exact .trans (hl.mono h) (hr.mono h)
  | .congr ht hs => exact .congr (ht.mono h) (hs.mono h)

theorem CongList.mono {d e : Database} (h : d.Contained e) {as bs : List Term}
    (hc : CongList d as bs) : CongList e as bs := by
  match hc with
  | .nil => exact .nil
  | .cons ht hs => exact .cons (ht.mono h) (hs.mono h)

end

mutual

theorem Cong.of_assertions {d e : Database}
    (h : ∀ p ∈ d.eqs, Cong e p.1 p.2) {a b : Term}
    (hc : Cong d a b) : Cong e a b := by
  match hc with
  | .direct hp => exact h _ hp
  | .child ht hs => exact .child (ht.of_assertions h) hs
  | .symm ht => exact .symm (ht.of_assertions h)
  | .trans hl hr => exact .trans (hl.of_assertions h) (hr.of_assertions h)
  | .congr ht hs => exact .congr (ht.of_assertions h) (hs.of_assertions h)

theorem CongList.of_assertions {d e : Database}
    (h : ∀ p ∈ d.eqs, Cong e p.1 p.2) {as bs : List Term}
    (hc : CongList d as bs) : CongList e as bs := by
  match hc with
  | .nil => exact .nil
  | .cons ht hs => exact .cons (ht.of_assertions h) (hs.of_assertions h)

end

theorem Cong.mono_eqs {d e : Database} (h : d.eqs ⊆ e.eqs) {a b : Term}
    (hc : Cong d a b) : Cong e a b := hc.of_assertions (fun _ hp => .direct (h hp))

theorem Cong.iff_of_eqs_eq {d e : Database} (h : d.eqs = e.eqs) {a b : Term} :
    Cong d a b ↔ Cong e a b := ⟨Cong.mono_eqs h.subset, Cong.mono_eqs h.symm.subset⟩

theorem CongList.iff_of_congr {d e : Database}
    (h : ∀ a b, Cong d a b ↔ Cong e a b) {as bs : List Term} :
    CongList d as bs ↔ CongList e as bs := by
  simp only [CongList.forall₂]
  induction as generalizing bs with
  | nil => cases bs <;> simp
  | cons a as ih => cases bs <;> simp [h, ih]

theorem Database.SameRow.iff_of_congr {d e : Database}
    (h : ∀ a b, Cong d a b ↔ Cong e a b) {s t : Term} :
    d.SameRow s t ↔ e.SameRow s t := by
  simp only [Database.SameRow, CongList.iff_of_congr h]

theorem Database.SameMeaning.of_congr {d e : Database}
    (h : ∀ a b, Cong d a b ↔ Cong e a b) (hX : d.subsumed = e.subsumed) :
    d.SameMeaning e := by
  refine ⟨h, fun t => ?_⟩
  simp only [Database.live, Set.mem_setOf_eq, h, hX, Database.SameRow.iff_of_congr h]

theorem Database.SameMeaning.of_congr_empty {d e : Database}
    (hd : d.subsumed = ∅) (he : e.subsumed = ∅)
    (h : ∀ a b, Cong d a b ↔ Cong e a b) : d.SameMeaning e :=
  .of_congr h (hd.trans he.symm)

theorem Database.sameMeaning_iff_congr_of_empty {d e : Database}
    (hd : d.subsumed = ∅) (he : e.subsumed = ∅) :
    d.SameMeaning e ↔ Cong d = Cong e := by
  constructor
  · intro h; funext a b; exact propext (h.congr a b)
  · intro h; exact .of_congr_empty hd he (fun a b => by rw [h])

theorem Database.live_addSubsumed {db : Database} {X : Set Term} {t : Term} :
    t ∈ (db.addSubsumed X).live ↔
      t ∈ db.live ∧ ¬ ∃ u ∈ X, db.SameRow t u := by
  have hc := fun a b => Cong.iff_of_eqs_eq (d := db.addSubsumed X) (e := db)
    (show (db.addSubsumed X).eqs = db.eqs from rfl) (a := a) (b := b)
  simp only [Database.live, Set.mem_setOf_eq, hc,
    Database.SameRow.iff_of_congr hc, Database.addSubsumed_subsumed,
    Set.mem_union, or_and_right, exists_or, not_or]
  tauto

theorem Database.SameMeaning.addSubsumed {d e : Database} (h : d.SameMeaning e)
    (X : Set Term) : (d.addSubsumed X).SameMeaning (e.addSubsumed X) := by
  refine ⟨fun a b => ?_, fun t => ?_⟩
  · exact (Cong.iff_of_eqs_eq (d := d.addSubsumed X) (e := d) rfl).trans
      ((h.congr a b).trans (Cong.iff_of_eqs_eq (d := e.addSubsumed X) (e := e) rfl).symm)
  · simp only [Database.live_addSubsumed, h.live, Database.SameRow.iff_of_congr h.congr]

theorem Database.SameMeaning.forgetSubsumed {d e : Database} (h : d.SameMeaning e) :
    d.forgetSubsumed.SameMeaning e.forgetSubsumed :=
  .of_congr (fun a b =>
    (Cong.iff_of_eqs_eq (d := d.forgetSubsumed) (e := d) rfl).trans
      ((h.congr a b).trans
        (Cong.iff_of_eqs_eq (d := e.forgetSubsumed) (e := e) rfl).symm)) rfl

end Egglog
