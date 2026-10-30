import EgglogSemantics.Proofs.SourceModel
import EgglogSemantics.Proofs.ActionMonotone
import EgglogSemantics.Proofs.MatchMonotone
import EgglogSemantics.Proofs.Diagonal

/-! Generic assertion transport retained from the former merge development.
Merge steps, declaration environments, leaders, and current-table invariants no longer
exist. `Recorded` and positive, delete-free rule monotonicity remain useful independently. -/

namespace Egglog

theorem CongList.append {db : Database} : ∀ {as bs cs ds : List Term},
    CongList db as bs → CongList db cs ds → CongList db (as ++ cs) (bs ++ ds)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h hs, h' => .cons h (CongList.append hs h')

def CongListOn (db : Database) (ts as bs : List Term) : Prop :=
  StoredCongList (db.withOperands ts) as bs

theorem mem_congOn_self {db : Database} {ts : List Term} {a : Term} (h : a ∈ ts) :
    StoredCongOn db ts a a := Database.toStored (Database.mem_addTerms h)

theorem Database.addTerms_eqs_of_eqs {d e : Database} (h : d.eqs = e.eqs)
    (ts : List Term) : (d.addTerms ts).eqs = (e.addTerms ts).eqs := by
  simp only [Database.addTerms_eqs, h]


namespace Conservativity

theorem cong_replay {D E : Database} (h : ∀ p ∈ D.eqs, Cong E p.1 p.2) {a b : Term}
    (hc : Cong D a b) : Cong E a b := by
  induction hc using Cong.rec (motive_2 := fun as bs _ => CongList E as bs) with
  | direct hp => exact h _ hp
  | subterm _ hs ih => exact .subterm ih hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | congr _ _ ih ih' => exact .congr ih ih'
  | nil => exact .nil
  | cons _ _ ih ih' => exact .cons ih ih'

theorem eqs_subset_addTerms (ts : List Term) (db : Database) :
    db.eqs ⊆ (db.addTerms ts).eqs := (Database.Contained.addTerms ts db).eqs

theorem mem_addTerms_eqs' (ts : List Term) (db : Database) (p : Term × Term)
    (h : p ∈ (db.addTerms ts).eqs) : p ∈ db.eqs ∨ ∃ t ∈ ts, p = (t, t) := by
  simpa only [Database.addTerms_eqs, Set.mem_union, Set.mem_setOf_eq] using h

theorem refl_mem_addTerms {t : Term} (ts : List Term) (db : Database) (ht : t ∈ ts) :
    (t, t) ∈ (db.addTerms ts).eqs := by
  rw [Database.addTerms_eqs]
  exact Or.inr ⟨t, ht, rfl⟩

theorem addTerms_eqs_mono {d e : Database} (h : d.eqs ⊆ e.eqs) (ts : List Term) :
    (d.addTerms ts).eqs ⊆ (e.addTerms ts).eqs :=
  (Database.Contained.addTerms_mono ⟨h⟩ ts).eqs

theorem withOperands_mono_list {db : Database} {ts us : List Term} (h : ∀ t ∈ ts, t ∈ us) :
    (db.withOperands ts).eqs ⊆ (db.withOperands us).eqs := by
  intro p hp
  rcases mem_addTerms_eqs' ts db p hp with hp | ⟨t, ht, rfl⟩
  · exact eqs_subset_addTerms us db hp
  · exact refl_mem_addTerms us db (h t ht)

theorem terms_subtermClosed {E : Database} : ∀ t ∈ E.terms, t.subterms ⊆ E.terms :=
  E.subtermClosed

theorem withOperands_subtermClosed (db : Database) (ts : List Term) :
    ∀ t ∈ (db.withOperands ts).terms, t.subterms ⊆ (db.withOperands ts).terms :=
  (db.withOperands ts).subtermClosed

/-- Hypothetical operands cannot change equality anchored at a represented term. -/
theorem congOn_elim {db : Database} {ts : List Term} {a b : Term}
    (ha : a ∈ db.terms) (hc : StoredCongOn db ts a b) : Cong db a b :=
  InferredFacts.congr_iff_infers.mpr
    (InferredFacts.infers_of_congOn_core (InferredFacts.infers_of_held ha) hc)

end Conservativity

/-- Recording transports semantic congruence directly; endpoints need not be stored. -/
theorem Cong.mono_recorded {d e : Database} (h : d.Recorded e) {a b : Term}
    (hc : Cong d a b) : Cong e a b := by
  apply Conservativity.cong_replay ?_ hc
  intro p hp
  obtain ⟨q, hq, h1, h2⟩ := h.eqs p hp
  have hh := (StoredCong.direct hq).mem_of
  exact (Conservativity.congOn_elim hh.1 h1.symm).symm.trans
    ((Cong.direct hq).trans (Conservativity.congOn_elim hh.2 h2.symm))

theorem CongList.mono_recorded {d e : Database} (h : d.Recorded e) {as bs : List Term}
    (hc : CongList d as bs) : CongList e as bs :=
  CongList.forall₂.mpr (CongList.forall₂.mp hc |>.imp fun _ _ hp => hp.mono_recorded h)

namespace Database.Recorded

theorem refl {db : Database} : db.Recorded db :=
  ⟨fun p hp => ⟨p, hp, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩⟩

theorem of_contained {d e : Database} (h : d.Contained e) : d.Recorded e :=
  ⟨fun p hp => ⟨p, h.eqs hp, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩⟩


theorem trans_contained {d e f : Database} (h : d.Recorded e) (hf : e.Contained f) :
    d.Recorded f :=
  ⟨fun p hp => let ⟨q, hq, h1, h2⟩ := h.eqs p hp
    ⟨q, hf.eqs hq, congOn_mono hf h1, congOn_mono hf h2⟩⟩

theorem trans {d e f : Database} (h : d.Recorded e) (hf : e.Recorded f) : d.Recorded f := by
  constructor
  intro p hp
  obtain ⟨q, hq, h1, h2⟩ := h.eqs p hp
  obtain ⟨r, hr, hr1, hr2⟩ := hf.eqs q hq
  have hqm := (StoredCong.direct hq).mem_of
  have hrm := (StoredCong.direct hr).mem_of
  have side : ∀ {x y z : Term}, y ∈ e.terms → z ∈ f.terms →
      StoredCongOn e [p.1,p.2] x y → StoredCongOn f [q.1,q.2] y z →
      x ∈ [p.1,p.2] → StoredCongOn f [p.1,p.2] x z := by
    intro x y z hy hz hxy hyz hx
    have hc := ((Conservativity.congOn_elim hy hxy.symm).symm.mono_recorded hf).trans
      (Conservativity.congOn_elim hz hyz.symm).symm
    exact (hc.mono (Contained.addTerms _ f)).toStored (mem_addTerms hx)
      ((Contained.addTerms _ f).terms hz)
  exact ⟨r, hr, side hqm.1 hrm.1 h1 hr1 (by simp), side hqm.2 hrm.2 h2 hr2 (by simp)⟩

theorem addTerm_mono {d e : Database} (h : d.Recorded e) (t : Term) :
    (d.addTerm t).Recorded (e.addTerm t) := by
  constructor
  rintro p (rfl | hp)
  · exact ⟨(t,t), Set.mem_insert _ _, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩
  · exact (h.trans_contained (Contained.addTerm t e)).eqs p hp

theorem addTerms_mono {d e : Database} (h : d.Recorded e) (ts : List Term) :
    (d.addTerms ts).Recorded (e.addTerms ts) := by
  induction ts generalizing d e with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm_mono t)

theorem addEq_mono {d e : Database} (h : d.Recorded e) (a b : Term) :
    (d.addEq a b).Recorded (e.addEq a b) := by
  constructor
  rintro p (rfl | hp)
  · exact ⟨(a,b), Set.mem_insert _ _, mem_congOn_self (by simp), mem_congOn_self (by simp)⟩
  · exact (h.trans_contained (Contained.addEq a b e)).eqs p hp

theorem contained_of_diag {d e : Database} (h : d.Recorded e) (hd : e.Diag) :
    d.Contained e := by
  constructor
  intro p hp
  obtain ⟨q, hq, h1, h2⟩ := h.eqs p hp
  have hpq : p = q := Prod.ext (h1.eq_of_diag (hd.addTerms _)) (h2.eq_of_diag (hd.addTerms _))
  exact hpq.symm ▸ hq

end Database.Recorded

theorem Database.addTerm_eq_self {db : Database} {t : Term}
    (ht : (t,t) ∈ db.eqs) : db.addTerm t = db := by
  apply Database.ext
  · exact Set.insert_eq_of_mem ht

theorem Env.Agree.cons {σ τ : Env} (h : Env.Agree σ τ) (w : Var) (t : Term) :
    Env.Agree ((w,t)::σ) ((w,t)::τ) := by
  intro v
  simp [Env.lookup_cons, h v]

theorem Database.mem_terms_of_eqs {d e : Database} (h : d.eqs ⊆ e.eqs) {t : Term}
    (ht : t ∈ d.terms) : t ∈ e.terms := (Contained.terms ⟨h⟩) ht

theorem RuleResults.mono {A C : Database} (hc : A.Contained C) {r : Rule}
    (hq : ∀ p ∈ r.query, p.monotoneB = true) (hd : r.DeleteFree)
    {d : Database} (h : d ∈ RuleResults A r) :
    ∃ e ∈ RuleResults C r, d.Contained e := by
  obtain ⟨σ, hσ, he⟩ := h
  obtain ⟨e, he', hh⟩ := evalActions_mono hc hd he
  exact ⟨e, ⟨σ, hσ.mono hc hq, he'⟩, hh⟩

theorem RunRules.mono {R : List Rule} {A C : Database} (hc : A.Contained C)
    (ha : ∀ r ∈ R, r.DeleteFree)
    (hq : ∀ r ∈ R, ∀ p ∈ r.query, p.monotoneB = true) :
    (RunRules R A).Contained (RunRules R C) := by
  rw [RunRules.eq_sUnion R A ha, RunRules.eq_sUnion R C ha]
  constructor
  rintro p (hp | hp)
  · exact Or.inl (hc.eqs hp)
  · obtain ⟨d, ⟨r, hr, hd⟩, hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨e, he, hh⟩ := RuleResults.mono hc (hq r hr) (ha r hr) hd
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e, ⟨r, hr, he⟩, hh.eqs hp⟩)

end Egglog
