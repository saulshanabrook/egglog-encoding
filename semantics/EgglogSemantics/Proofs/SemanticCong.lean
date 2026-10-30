import EgglogSemantics.Proofs.Congruence

namespace Egglog

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
  | .subterm ht hs => exact .subterm (ht.mono h) hs
  | .symm ht => exact .symm (ht.mono h)
  | .trans hl hr => exact .trans (hl.mono h) (hr.mono h)
  | .congr ht hs => exact .congr (ht.mono h) (hs.mono h)

theorem CongList.mono {d e : Database} (h : d.Contained e) {as bs : List Term}
    (hc : CongList d as bs) : CongList e as bs := by
  match hc with
  | .nil => exact .nil
  | .cons ht hs => exact .cons (ht.mono h) (hs.mono h)

end

end Egglog
