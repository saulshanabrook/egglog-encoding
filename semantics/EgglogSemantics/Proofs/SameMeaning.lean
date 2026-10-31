import EgglogSemantics.Proofs.SemanticCong
import EgglogSemantics.Proofs.Operands
import Mathlib.Logic.Relation

/-!
# Inferred constructor facts

A partial interpretation in the database's existing congruence classes distinguishes
represented terms from unsupported terms. It characterizes `Database.Infers` without
enumerating the possibly infinite family of represented constructor spellings.
-/

namespace Egglog

namespace Database.SameMeaning

theorem refl (d : Database) : d.SameMeaning d :=
  ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem symm {d e : Database} (h : d.SameMeaning e) : e.SameMeaning d :=
  ⟨fun a b => (h.congr a b).symm, fun t => (h.live t).symm⟩

theorem trans {d e f : Database} (h : d.SameMeaning e) (h' : e.SameMeaning f) :
    d.SameMeaning f :=
  ⟨fun a b => (h.congr a b).trans (h'.congr a b), fun t => (h.live t).trans (h'.live t)⟩

end Database.SameMeaning

namespace InferredFacts

abbrev Class (d : Database) := Quot (StoredCong d)

private theorem eq_or_cong_of_eqvGen {d : Database} {a b : Term}
    (h : Relation.EqvGen (StoredCong d) a b) : a = b ∨ StoredCong d a b := by
  induction h with
  | rel _ _ hr => exact Or.inr hr
  | refl _ => exact Or.inl rfl
  | symm _ _ _ ih =>
      rcases ih with rfl | hc
      exacts [Or.inl rfl, Or.inr hc.symm]
  | trans _ _ _ _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | h₁
      · exact ih₂
      · rcases ih₂ with rfl | h₂
        exacts [Or.inr h₁, Or.inr (h₁.trans h₂)]

private theorem cong_of_class_eq {d : Database} {a b : Term} (ha : a ∈ d.terms)
    (h : Quot.mk (StoredCong d) a = Quot.mk (StoredCong d) b) : StoredCong d a b := by
  rcases eq_or_cong_of_eqvGen (Quot.eqvGen_exact h) with rfl | hc
  exacts [Database.toStored ha, hc]

open Classical in
/-- An application is supported precisely when its interpreted children form the
key of a held constructor application. Unsupported children cannot form a key. -/
noncomputable def interpretApp (d : Database) (f : FnName)
    (values : List (Option (Class d))) : Option (Class d) :=
  if h : ∃ bs : List Term, Term.app f bs ∈ d.terms ∧
      values = bs.map (fun b => some (Quot.mk (StoredCong d) b)) then
    some (Quot.mk (StoredCong d) (Term.app f h.choose))
  else none

open Classical in
mutual

/-- Interpretation in existing classes; `none` means no represented constructor. -/
noncomputable def interpret (d : Database) : Term → Option (Class d)
  | .lit l => if Term.lit l ∈ d.terms then some (Quot.mk (StoredCong d) (.lit l)) else none
  | .app f args => interpretApp d f (interpretList d args)

noncomputable def interpretList (d : Database) : List Term → List (Option (Class d))
  | [] => []
  | t :: ts => interpret d t :: interpretList d ts

end

theorem interpretList_eq_map (d : Database) (ts : List Term) :
    interpretList d ts = ts.map (interpret d) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact congrArg (List.cons (interpret d t)) ih

private theorem congList_of_map_eq {d : Database} :
    ∀ {as bs : List Term}, (∀ a ∈ as, a ∈ d.terms) →
      as.map (fun a => some (Quot.mk (StoredCong d) a)) =
        bs.map (fun b => some (Quot.mk (StoredCong d) b)) → StoredCongList d as bs
  | [], [], _, _ => .nil
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, hm, h => by
      simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
      exact .cons (cong_of_class_eq (hm a (by simp)) h.1)
        (congList_of_map_eq (fun t ht => hm t (List.mem_cons_of_mem a ht)) h.2)

/-- Every held term interprets to its own class. -/
theorem interpret_of_held_core {d : Database} :
    ∀ t : Term, t ∈ d.terms → interpret d t = some (Quot.mk (StoredCong d) t) := by
  intro t
  induction t using Term.rec (motive_2 := fun ts => (∀ x ∈ ts, x ∈ d.terms) →
      interpretList d ts = ts.map (fun x => some (Quot.mk (StoredCong d) x))) with
  | lit l => intro ht; simp [interpret, ht]
  | app f args ih =>
      intro ht
      have hargs : ∀ a ∈ args, a ∈ d.terms := fun a ha =>
        d.subtermClosed _ ht (.arg ha (.refl a))
      have hi := ih hargs
      have hex : ∃ bs : List Term, Term.app f bs ∈ d.terms ∧
          interpretList d args = bs.map (fun b => some (Quot.mk (StoredCong d) b)) :=
        ⟨args, ht, hi⟩
      change interpretApp d f (interpretList d args) = _
      rw [interpretApp, dif_pos hex]
      apply congrArg some
      apply Quot.sound
      have hc : ∀ a ∈ hex.choose, a ∈ d.terms := fun a ha =>
        d.subtermClosed _ hex.choose_spec.1 (.arg ha (.refl a))
      exact .congr hex.choose_spec.1 ht
        (congList_of_map_eq hc (hex.choose_spec.2.symm.trans hi))
  | nil => rfl
  | cons t ts iht ihts =>
      have ht : ∀ x ∈ t :: ts, x ∈ d.terms := by assumption
      change interpret d t :: interpretList d ts = _
      rw [iht (ht t (by simp)), ihts (fun x hx => ht x (List.mem_cons_of_mem t hx))]
      rfl

/-- The partial interpretation respects any database whose assertions it validates. -/
theorem interpret_congr {d e : Database}
    (he : ∀ p ∈ e.eqs, interpret d p.1 = interpret d p.2)
    {a b : Term} (hc : StoredCong e a b) : interpret d a = interpret d b := by
  induction hc using StoredCong.rec
      (motive_2 := fun as bs _ => interpretList d as = interpretList d bs) with
  | direct hp => exact he _ hp
  | subterm => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ _ _ _ ih => exact congrArg (interpretApp d _) ih
  | nil => rfl
  | cons _ _ ih ihs => exact congrArg₂ List.cons ih ihs

theorem interpret_assert_core {d : Database} {p : Term × Term}
    (hp : p ∈ d.eqs) : interpret d p.1 = interpret d p.2 := by
  have hc := StoredCong.direct hp
  rw [interpret_of_held_core _ hc.mem_of.1, interpret_of_held_core _ hc.mem_of.2]
  exact congrArg some (Quot.sound hc)

theorem interpret_congOn_core {d : Database} {ts : List Term} {a b : Term}
    (hc : StoredCongOn d ts a b) : interpret d a = interpret d b := by
  apply interpret_congr (e := d.withOperands ts) ?_ hc
  intro p hp
  rcases Conservativity.mem_addTerms_eqs ts d p hp with hp | hp
  · exact interpret_assert_core hp
  · exact congrArg (interpret d) hp

private theorem mem_addTerms_eqs : ∀ (ts : List Term) (d : Database) (p : Term × Term),
    p ∈ (d.addTerms ts).eqs → p ∈ d.eqs ∨ ∃ t ∈ ts, p = (t, t)
  | [], _, _, h => Or.inl h
  | t :: ts, d, p, h => by
      rcases mem_addTerms_eqs ts (d.addTerm t) p h with h' | ⟨u, hu, rfl⟩
      · rcases h' with rfl | h'
        · exact Or.inr ⟨t, List.mem_cons_self .., rfl⟩
        · exact Or.inl h'
      · exact Or.inr ⟨u, List.mem_cons_of_mem t hu, rfl⟩

private theorem refl_mem_addTerms {t : Term} :
    ∀ (ts : List Term) (d : Database), t ∈ ts → (t, t) ∈ (d.addTerms ts).eqs
  | [], _, h => by simp at h
  | u :: ts, d, h => by
      rcases List.mem_cons.mp h with rfl | ht
      · exact (Database.Contained.addTerms ts (d.addTerm t)).eqs (Or.inl rfl)
      · exact refl_mem_addTerms ts (d.addTerm u) ht

private theorem operands_mono_list {d : Database} {ts us : List Term}
    (h : ∀ t ∈ ts, t ∈ us) : (d.withOperands ts).Contained (d.withOperands us) := by
  refine ⟨?_, by simp [Database.withOperands]⟩
  intro p hp
  rcases mem_addTerms_eqs ts d p hp with hp | ⟨t, ht, rfl⟩
  · exact (Database.Contained.addTerms us d).eqs hp
  · exact refl_mem_addTerms us d (h t ht)

private theorem operand_subterm {d : Database} {t parent : Term}
    (ht : t ∈ parent.subterms) {a b : Term} (hc : StoredCongOn d [t] a b) :
    StoredCongOn d [parent] a b := by
  apply StoredCong.of_assertions (d := d.withOperands [t]) ?_ hc
  rintro p (rfl | hp)
  · exact .subterm (Database.toStored (Database.mem_addTerm parent d)) ht
  · exact .direct (Or.inr hp)

mutual

/-- A supported interpretation has a witness in the original database. The
hypothetical ambient needs only the term being interpreted. -/
theorem congOn_of_interpret_core {d : Database} :
    ∀ (t : Term) {u : Term}, u ∈ d.terms →
      interpret d t = some (Quot.mk (StoredCong d) u) → StoredCongOn d [t] t u
  | .lit l, u, hu, hi => by
      simp only [interpret] at hi
      split at hi
      next ht =>
        exact (cong_of_class_eq ht (Option.some.inj hi)).mono
          (Database.Contained.addTerms [Term.lit l] d)
      next => cases hi
  | .app f args, u, hu, hi => by
      change interpretApp d f (interpretList d args) = _ at hi
      rw [interpretApp] at hi
      split at hi
      next hex =>
        have hb := hex.choose_spec
        have hargs : ∀ b ∈ hex.choose, b ∈ d.terms := fun b hmem =>
          d.subtermClosed _ hb.1 (.arg hmem (.refl b))
        have hl := congListOn_of_interpret_core args (parent := .app f args) hargs hb.2
          (fun t ht => Term.IsSubterm.arg ht (.refl t))
        have ha : StoredCongOn d [Term.app f args] (.app f args) (.app f hex.choose) :=
          .congr (Database.toStored (Database.mem_addTerm (.app f args) d))
            ((Database.toStored hb.1).mono (Database.Contained.addTerms _ d)) hl
        exact ha.trans ((cong_of_class_eq hb.1 (Option.some.inj hi)).mono
          (Database.Contained.addTerms _ d))
      next => cases hi

theorem congListOn_of_interpret_core {d : Database} :
    ∀ (ts : List Term) {bs : List Term} {parent : Term},
      (∀ b ∈ bs, b ∈ d.terms) →
      interpretList d ts = bs.map (fun b => some (Quot.mk (StoredCong d) b)) →
      (∀ t ∈ ts, t ∈ parent.subterms) → StoredCongList (d.withOperands [parent]) ts bs
  | [], [], _, _, _, _ => .nil
  | [], _ :: _, _, _, h, _ => by simp [interpretList] at h
  | _ :: _, [], _, _, h, _ => by simp [interpretList] at h
  | t :: ts, b :: bs, _, hb, hi, hs => by
      simp only [interpretList, List.map_cons, List.cons.injEq] at hi
      exact .cons
        (operand_subterm (hs t (by simp))
          (congOn_of_interpret_core t (hb b (by simp)) hi.1))
        (congListOn_of_interpret_core ts
          (fun x hx => hb x (List.mem_cons_of_mem b hx)) hi.2
          (fun x hx => hs x (List.mem_cons_of_mem t hx)))

end

/-- Anchored inference is exactly equality at a supported interpreted class. -/
theorem infers_iff_interpret_core {d : Database} {a b : Term} :
    d.Infers a b ↔ ∃ w ∈ d.terms,
      interpret d a = some (Quot.mk (StoredCong d) w) ∧
      interpret d b = some (Quot.mk (StoredCong d) w) := by
  constructor
  · rintro ⟨w, hw', hwa, hab⟩
    have ha := (interpret_congOn_core hwa).symm.trans (interpret_of_held_core w hw')
    exact ⟨w, hw', ha, (interpret_congOn_core hab).symm.trans ha⟩
  · rintro ⟨w, hw', ha, hb⟩
    have ha' := (congOn_of_interpret_core a hw' ha).mono
      (operands_mono_list (d := d) (ts := [a]) (us := [a, b]) (by simp))
    have hb' := (congOn_of_interpret_core b hw' hb).mono
      (operands_mono_list (d := d) (ts := [b]) (us := [a, b]) (by simp))
    exact ⟨w, hw', ha'.symm, ha'.trans hb'.symm⟩

/-- The interpretation belongs to a class already represented in the database. -/
def Supported (d : Database) (t : Term) : Prop :=
  ∃ w ∈ d.terms, interpret d t = some (Quot.mk (StoredCong d) w)

theorem infers_self_iff_supported_core {d : Database} {t : Term} :
    d.Infers t t ↔ Supported d t := by
  simp only [infers_iff_interpret_core, and_self, Supported]

/-- Represented existence entails represented existence of every subterm. -/
theorem supported_subterm_core {d : Database} {s t : Term}
    (hs : s ∈ t.subterms) : Supported d t → Supported d s := by
  induction hs with
  | refl => exact id
  | @arg a f args ha _ ih =>
      rintro ⟨w, _, hi⟩
      change interpretApp d f (interpretList d args) = _ at hi
      rw [interpretApp] at hi
      split at hi
      next hex =>
        have hm : interpret d a ∈ interpretList d args := by
          rw [interpretList_eq_map]
          exact List.mem_map.mpr ⟨a, ha, rfl⟩
        rw [hex.choose_spec.2] at hm
        obtain ⟨b, hb, hbi⟩ := List.mem_map.mp hm
        exact ih ⟨b, d.subtermClosed _ hex.choose_spec.1 (.arg hb (.refl b)), hbi.symm⟩
      next => cases hi

theorem infers_subterm_core {d : Database} {s t : Term}
    (ht : d.Infers t t) (hs : s ∈ t.subterms) : d.Infers s s :=
  (infers_self_iff_supported_core).mpr
    (supported_subterm_core hs ((infers_self_iff_supported_core).mp ht))

theorem infers_mono {d e : Database} (h : d.Contained e) {a b : Term}
    (hi : d.Infers a b) : e.Infers a b := by
  obtain ⟨w, hw, hwa, hab⟩ := hi
  have hg := Database.Contained.addTerms_mono h [a, b]
  exact ⟨w, h.terms hw, hwa.mono hg, hab.mono hg⟩

theorem infers_iff_of_eqs_eq {d e : Database} (h : d.eqs = e.eqs) {a b : Term} :
    d.Infers a b ↔ e.Infers a b := by
  have forward : ∀ {d e : Database}, d.eqs = e.eqs → d.Infers a b → e.Infers a b := by
    intro d e h ⟨w, hw, hwa, hab⟩
    have ht := Database.terms_eq_of_eqs_eq h
    have ha : ∀ p ∈ (d.withOperands [a, b]).eqs,
        StoredCong (e.withOperands [a, b]) p.1 p.2 := by
      intro p hp
      apply StoredCong.direct
      simpa [Database.withOperands, Database.addTerms_eqs, h] using hp
    exact ⟨w, ht ▸ hw, hwa.of_assertions ha, hab.of_assertions ha⟩
  exact ⟨forward h, forward h.symm⟩

theorem infers_of_held {d : Database} {t : Term} (ht : t ∈ d.terms) : d.Infers t t := by
  have h := (Database.toStored ht).mono (Database.Contained.addTerms [t, t] d)
  exact ⟨t, ht, h, h⟩

theorem infers_symm_core {d : Database} {a b : Term}
    (h : d.Infers a b) : d.Infers b a := by
  obtain ⟨w, hw', ha, hb⟩ := (infers_iff_interpret_core).mp h
  exact (infers_iff_interpret_core).mpr ⟨w, hw', hb, ha⟩

theorem infers_trans_core {d : Database} {a b c : Term}
    (hab : d.Infers a b) (hbc : d.Infers b c) : d.Infers a c := by
  obtain ⟨w, hw', ha, hb⟩ := (infers_iff_interpret_core).mp hab
  obtain ⟨u, _, hb', hc⟩ := (infers_iff_interpret_core).mp hbc
  exact (infers_iff_interpret_core).mpr ⟨w, hw', ha, hc.trans (hb'.symm.trans hb)⟩

theorem infers_left_core {d : Database} {a b : Term}
    (h : d.Infers a b) : d.Infers a a := infers_trans_core h (infers_symm_core h)

theorem infers_right_core {d : Database} {a b : Term}
    (h : d.Infers a b) : d.Infers b b := infers_trans_core (infers_symm_core h) h

/-- Phantom operands do not change an equality's meaning once one endpoint is
represented. The ambient list may contain any additional hypothetical terms. -/
theorem infers_of_congOn_core {d : Database} {ts : List Term} {a b : Term}
    (ha : d.Infers a a) (hc : StoredCongOn d ts a b) : d.Infers a b := by
  obtain ⟨w, hw', hi, _⟩ := (infers_iff_interpret_core).mp ha
  exact (infers_iff_interpret_core).mpr
    ⟨w, hw', hi, (interpret_congOn_core hc).symm.trans hi⟩

theorem infers_of_cong {d : Database} {a b : Term} (h : StoredCong d a b) : d.Infers a b := by
  have hg := Database.Contained.addTerms [a, b] d
  exact ⟨a, h.mem_of.1, (Database.toStored h.mem_of.1).mono hg, h.mono hg⟩

/-- For recorded endpoints, anchored inference recovers ordinary congruence. -/
theorem infers_iff_cong_of_held_core {d : Database} {a b : Term}
    (ha : a ∈ d.terms) (hb : b ∈ d.terms) : d.Infers a b ↔ StoredCong d a b := by
  refine ⟨fun h => ?_, infers_of_cong⟩
  obtain ⟨w, _, hai, hbi⟩ := (infers_iff_interpret_core).mp h
  have he := hai.trans hbi.symm
  rw [interpret_of_held_core _ ha, interpret_of_held_core _ hb] at he
  exact cong_of_class_eq ha (Option.some.inj he)

theorem infers_eq_of_isLit {d : Database} (hw : d.WF) {a b : Term}
    (h : d.Infers a b) (hl : a.isLit ∨ b.isLit) : a = b :=
  h.choose_spec.2.2.eq_of_isLit (hw.addTerms [a, b]).litsIsolated hl

/-- Replacing argument representatives preserves a represented application. -/
theorem infers_congr_core {d : Database} {f : FnName} {as bs : List Term}
    (ha : d.Infers (.app f as) (.app f as)) (hs : List.Forall₂ (d.Infers) as bs) :
    d.Infers (.app f as) (.app f bs) := by
  have hl : interpretList d as = interpretList d bs := by
    clear ha
    induction hs with
    | nil => rfl
    | cons hab _ ih =>
        obtain ⟨w, _, hai, hbi⟩ := (infers_iff_interpret_core).mp hab
        exact congrArg₂ List.cons (hai.trans hbi.symm) ih
  obtain ⟨w, hw', hi, _⟩ := (infers_iff_interpret_core).mp ha
  exact (infers_iff_interpret_core).mpr
    ⟨w, hw', hi, (congrArg (interpretApp d f) hl).symm.trans hi⟩

theorem congr_infers {d : Database} {a b : Term} (h : Cong d a b) : d.Infers a b := by
  induction h using Cong.rec
      (motive_2 := fun as bs _ => List.Forall₂ d.Infers as bs) with
  | direct hp => exact infers_of_cong (.direct hp)
  | child _ hs ih => exact infers_subterm_core ih (.arg hs (.refl _))
  | symm _ ih => exact infers_symm_core ih
  | trans _ _ ih₁ ih₂ => exact infers_trans_core ih₁ ih₂
  | congr _ _ ih ihs => exact infers_congr_core ih ihs
  | nil => exact .nil
  | cons _ _ ih ihs => exact .cons ih ihs

mutual

theorem congr_of_interpret {d : Database} :
    ∀ (t : Term) {u : Term}, u ∈ d.terms →
      interpret d t = some (Quot.mk (StoredCong d) u) → Cong d t u
  | .lit l, u, hu, hi => by
      simp only [interpret] at hi
      split at hi
      next ht => exact (cong_of_class_eq ht (Option.some.inj hi)).toCong
      next => cases hi
  | .app f args, u, hu, hi => by
      change interpretApp d f (interpretList d args) = _ at hi
      rw [interpretApp] at hi
      split at hi
      next hex =>
        have hb := hex.choose_spec
        have hargs : ∀ b ∈ hex.choose, b ∈ d.terms := fun b hmem =>
          d.subtermClosed _ hb.1 (.arg hmem (.refl b))
        have hl := congrList_of_interpret args hargs hb.2
        have ha : Cong d (.app f args) (.app f hex.choose) :=
          (Cong.congr (Database.toStored hb.1).toCong hl.symm).symm
        exact ha.trans (cong_of_class_eq hb.1 (Option.some.inj hi)).toCong
      next => cases hi

theorem congrList_of_interpret {d : Database} :
    ∀ (ts : List Term) {bs : List Term}, (∀ b ∈ bs, b ∈ d.terms) →
      interpretList d ts = bs.map (fun b => some (Quot.mk (StoredCong d) b)) →
      CongList d ts bs
  | [], [], _, _ => .nil
  | [], _ :: _, _, h => by simp [interpretList] at h
  | _ :: _, [], _, h => by simp [interpretList] at h
  | t :: ts, b :: bs, hb, hi => by
      simp only [interpretList, List.map_cons, List.cons.injEq] at hi
      exact .cons (congr_of_interpret t (hb b (by simp)) hi.1)
        (congrList_of_interpret ts (fun x hx => hb x (List.mem_cons_of_mem b hx)) hi.2)

end

/-- The direct semantic closure equals anchored inference, without a state invariant. -/
theorem congr_iff_infers {d : Database} {a b : Term} : Cong d a b ↔ d.Infers a b := by
  refine ⟨congr_infers, ?_⟩
  intro h
  obtain ⟨w, hw, ha, hb⟩ := infers_iff_interpret_core.mp h
  exact (congr_of_interpret a hw ha).trans (congr_of_interpret b hw hb).symm

end InferredFacts

namespace Cong

theorem toStored {d : Database} {a b : Term} (h : Cong d a b)
    (ha : a ∈ d.terms) (hb : b ∈ d.terms) : StoredCong d a b :=
  (InferredFacts.infers_iff_cong_of_held_core ha hb).mp
    (InferredFacts.congr_iff_infers.mp h)

end Cong

namespace Database.SameMeaning

theorem inferred {d e : Database} (h : d.SameMeaning e) (a b : Term) :
    d.Infers a b ↔ e.Infers a b :=
  InferredFacts.congr_iff_infers.symm.trans
    ((h.congr a b).trans InferredFacts.congr_iff_infers)

theorem of_inferred {d e : Database} (hX : d.subsumed = e.subsumed)
    (hi : ∀ a b, d.Infers a b ↔ e.Infers a b) : d.SameMeaning e :=
  .of_congr (fun a b => InferredFacts.congr_iff_infers.trans
    ((hi a b).trans InferredFacts.congr_iff_infers.symm)) hX

end Database.SameMeaning

namespace InferredFacts

abbrev interpret_of_held {d : Database} (_hw : d.WF) := @interpret_of_held_core d
abbrev interpret_assert {d : Database} (_hw : d.WF) := @interpret_assert_core d
abbrev interpret_congOn {d : Database} (_hw : d.WF) := @interpret_congOn_core d
abbrev congOn_of_interpret {d : Database} (_hw : d.WF) := @congOn_of_interpret_core d
abbrev congListOn_of_interpret {d : Database} (_hw : d.WF) := @congListOn_of_interpret_core d
abbrev infers_iff_interpret {d : Database} (_hw : d.WF) := @infers_iff_interpret_core d
abbrev infers_self_iff_supported {d : Database} (_hw : d.WF) := @infers_self_iff_supported_core d
abbrev supported_subterm {d : Database} (_hw : d.WF) := @supported_subterm_core d
abbrev infers_subterm {d : Database} (_hw : d.WF) := @infers_subterm_core d
abbrev infers_symm {d : Database} (_hw : d.WF) := @infers_symm_core d
abbrev infers_trans {d : Database} (_hw : d.WF) := @infers_trans_core d
abbrev infers_left {d : Database} (_hw : d.WF) := @infers_left_core d
abbrev infers_right {d : Database} (_hw : d.WF) := @infers_right_core d
abbrev infers_of_congOn {d : Database} (_hw : d.WF) := @infers_of_congOn_core d
abbrev infers_iff_cong_of_held {d : Database} (_hw : d.WF) := @infers_iff_cong_of_held_core d
abbrev infers_congr {d : Database} (_hw : d.WF) := @infers_congr_core d

/-- Inferred facts of an extension reflect back when its assertions are valid in
the partial interpretation and every recorded term remains represented. -/
theorem infers_of_interpreted_extension {d e : Database} (hw : d.WF)
    (he : ∀ p ∈ e.eqs, interpret d p.1 = interpret d p.2)
    (ht : ∀ t ∈ e.terms, Supported d t) {a b : Term}
    (hi : e.Infers a b) : d.Infers a b := by
  obtain ⟨w, hw', hwa, hab⟩ := hi
  have hassert : ∀ p ∈ (e.withOperands [a, b]).eqs,
      interpret d p.1 = interpret d p.2 := by
    intro p hp
    rcases Conservativity.mem_addTerms_eqs [a, b] e p hp with hp | hp
    · exact he p hp
    · exact congrArg (interpret d) hp
  obtain ⟨u, hu, hwu⟩ := ht w hw'
  have ha := (interpret_congr hassert hwa).symm.trans hwu
  exact (infers_iff_interpret hw).mpr
    ⟨u, hu, ha, (interpret_congr hassert hab).symm.trans ha⟩

/-- Materializing an already inferred constructor term changes no inferred fact. -/
theorem sameMeaning_addTerm {d : Database} (hw : d.WF) {t : Term}
    (ht : d.Infers t t) : d.SameMeaning (d.addTerm t) := by
  refine Database.SameMeaning.of_inferred rfl (fun a b => ⟨infers_mono
    (Database.Contained.addTerm t d), ?_⟩)
  apply infers_of_interpreted_extension hw
  · rintro p (rfl | hp)
    · rfl
    · exact interpret_assert hw hp
  · intro s hs
    rw [Database.addTerm_terms] at hs
    rcases hs with hs | hs
    · exact ⟨s, hs, interpret_of_held hw s hs⟩
    · exact supported_subterm hw hs ((infers_self_iff_supported hw).mp ht)

/-- The semantic no-change test for a constructor write is exactly prior inference. -/
theorem sameMeaning_addTerm_iff {d : Database} (hw : d.WF) {t : Term} :
    d.SameMeaning (d.addTerm t) ↔ d.Infers t t := by
  refine ⟨fun h => ?_, sameMeaning_addTerm hw⟩
  exact (h.inferred t t).mpr (infers_of_held (Database.mem_addTerm t d))

/-- An already inferred union, including its endpoint constructions, also changes
no inferred fact. The premise includes existence, even for `a = a`. -/
theorem sameMeaning_addEq {d : Database} (hw : d.WF) {a b : Term}
    (hab : d.Infers a b) : d.SameMeaning (d.addEq a b) := by
  obtain ⟨w, hw', ha, hb⟩ := (infers_iff_interpret hw).mp hab
  refine Database.SameMeaning.of_inferred rfl (fun x y => ⟨infers_mono
    (Database.Contained.addEq a b d), ?_⟩)
  apply infers_of_interpreted_extension hw
  · rintro p (rfl | hp)
    · exact ha.trans hb.symm
    · exact interpret_assert hw hp
  · intro s hs
    rw [Database.addEq_terms] at hs
    rcases hs with (hs | hs) | hs
    · exact ⟨s, hs, interpret_of_held hw s hs⟩
    · exact supported_subterm hw hs ⟨w, hw', ha⟩
    · exact supported_subterm hw hs ⟨w, hw', hb⟩

/-- Hypothetically congruent spellings give equivalent constructor writes,
including when neither spelling has been materialized yet. -/
theorem sameMeaning_addTerm_congr {d : Database} (hw : d.WF) {a b : Term}
    (hc : StoredCongOn d [a, b] a b) : (d.addTerm a).SameMeaning (d.addTerm b) := by
  have ha : (d.addTerm a).Infers b b := by
    have hc' := hc.mono ((Database.Contained.addTerm a d).addTerms_mono [a, b])
    exact infers_right (hw.addTerm a)
      (infers_of_congOn (hw.addTerm a)
        (infers_of_held (Database.mem_addTerm a d)) hc')
  have hb : (d.addTerm b).Infers a a := by
    have hc' := hc.symm.mono ((Database.Contained.addTerm b d).addTerms_mono [a, b])
    exact infers_right (hw.addTerm b)
      (infers_of_congOn (hw.addTerm b)
        (infers_of_held (Database.mem_addTerm b d)) hc')
  have hcomm : (d.addTerm a).addTerm b = (d.addTerm b).addTerm a := by
    apply Database.ext <;> try rfl
    exact Set.insert_comm _ _ _
  have hr := (sameMeaning_addTerm (hw.addTerm b) hb).symm
  rw [← hcomm] at hr
  exact (sameMeaning_addTerm (hw.addTerm a) ha).trans hr

/-- A general way to compare represented extensions, without requiring their
stored constructor spellings to coincide. -/
theorem infers_of_assertions {d e : Database} (hw : d.WF)
    (he : ∀ p ∈ e.eqs, d.Infers p.1 p.2)
    (ht : ∀ t ∈ e.terms, d.Infers t t) {a b : Term}
    (hi : e.Infers a b) : d.Infers a b := by
  apply infers_of_interpreted_extension hw ?_ ?_ hi
  · intro p hp
    obtain ⟨w, _, ha, hb⟩ := (infers_iff_interpret hw).mp (he p hp)
    exact ha.trans hb.symm
  · intro t ht'
    exact (infers_self_iff_supported hw).mp (ht t ht')

/-- Every held term is a subterm of an asserted endpoint. -/
theorem infers_of_assertions_only {d e : Database} (hw : d.WF)
    (he : ∀ p ∈ e.eqs, d.Infers p.1 p.2) {a b : Term}
    (hi : e.Infers a b) : d.Infers a b := by
  apply infers_of_assertions hw he ?_ hi
  intro t ht
  obtain ⟨p, hp, ht | ht⟩ := Database.mem_terms_iff.mp ht
  · exact infers_subterm hw (infers_left hw (he p hp)) ht
  · exact infers_subterm hw (infers_right hw (he p hp)) ht

/-- Replacing both operands by hypothetically congruent terms preserves a union's
meaning. Literal legality is stated separately for the two concrete writes. -/
theorem sameMeaning_addEq_congr {d : Database} (hw : d.WF)
    {a b a' b' : Term} {as bs : List Term}
    (ha : StoredCongOn d as a a') (hb : StoredCongOn d bs b b')
    (hlit : a.isLit ∨ b.isLit → a = b)
    (hlit' : a'.isLit ∨ b'.isLit → a' = b') :
    (d.addEq a b).SameMeaning (d.addEq a' b') := by
  have forward : ∀ {a b a' b' : Term}, StoredCongOn d as a a' → StoredCongOn d bs b b' →
      (a'.isLit ∨ b'.isLit → a' = b') →
      ∀ {x y}, (d.addEq a b).Infers x y → (d.addEq a' b').Infers x y := by
    intro a b a' b' ha hb hlit' x y hi
    have hD := hw.addEq a' b' hlit'
    have hg := Database.Contained.addEq a' b' d
    have hu : (d.addEq a' b').Infers a' b' :=
      infers_of_cong (.direct (Set.mem_insert _ _))
    have haa := infers_of_congOn hD (infers_left hD hu)
      (ha.symm.mono (hg.addTerms_mono as))
    have hbb := infers_of_congOn hD (infers_right hD hu)
      (hb.symm.mono (hg.addTerms_mono bs))
    have hab := infers_trans hD (infers_symm hD haa) (infers_trans hD hu hbb)
    apply infers_of_assertions_only hD ?_ hi
    rintro p (rfl | hp)
    · exact hab
    · exact infers_mono hg (infers_of_cong (.direct hp))
  exact Database.SameMeaning.of_inferred rfl fun x y =>
    ⟨forward ha hb hlit', forward ha.symm hb.symm hlit⟩


end InferredFacts

namespace Database.SameMeaning

/-- The same constructor write preserves equivalence of inferred states. -/
theorem addTerm {d e : Database} (h : d.SameMeaning e) (hd : d.WF) (he : e.WF)
    (t : Term) (hX : d.subsumed = e.subsumed) : (d.addTerm t).SameMeaning (e.addTerm t) := by
  refine of_inferred hX fun a b => ?_
  have forward : ∀ {d e : Database}, d.SameMeaning e → e.WF →
      ∀ {a b}, (d.addTerm t).Infers a b → (e.addTerm t).Infers a b := by
    intro d e h he a b hi
    apply InferredFacts.infers_of_assertions_only (he.addTerm t) ?_ hi
    rintro p (rfl | hp)
    · exact InferredFacts.infers_of_held (Database.mem_addTerm t e)
    · exact InferredFacts.infers_mono (Database.Contained.addTerm t e)
        ((h.inferred _ _).mp (InferredFacts.infers_of_cong (.direct hp)))
  exact ⟨forward h he, forward h.symm hd⟩

/-- The same asserted equation preserves equivalence of inferred states. The
well-formed endpoints are explicit because literal isolation is a database invariant. -/
theorem addEq {d e : Database} (h : d.SameMeaning e) (hd : d.WF) (he : e.WF)
    (a b : Term) (hlit : a.isLit ∨ b.isLit → a = b)
    (hX : d.subsumed = e.subsumed) :
    (d.addEq a b).SameMeaning (e.addEq a b) := by
  refine of_inferred hX fun x y => ?_
  have forward : ∀ {d e : Database}, d.SameMeaning e → e.WF →
      ∀ {x y}, (d.addEq a b).Infers x y → (e.addEq a b).Infers x y := by
    intro d e h he x y hi
    apply InferredFacts.infers_of_assertions_only (he.addEq a b hlit) ?_ hi
    rintro p (rfl | hp)
    · exact InferredFacts.infers_of_cong (.direct (Set.mem_insert _ _))
    · exact InferredFacts.infers_mono (Database.Contained.addEq a b e)
        ((h.inferred _ _).mp (InferredFacts.infers_of_cong (.direct hp)))
  exact ⟨forward h he, forward h.symm hd⟩

end Database.SameMeaning
end Egglog
