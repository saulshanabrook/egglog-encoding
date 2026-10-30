import EgglogSemantics.Congruence.Read
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.Step

/-!
# Correspondence reductions

View coverage, represented unions, and sound entries relate source congruence to the
compiled table reading. `Complete.lean` establishes these invariants for full executions.
-/

namespace Egglog.Congruence

theorem ViewReprList.mem_read {d : Database} : ∀ {as is : List Term},
    ViewReprList d as is → ∀ t ∈ as, ∃ i, ViewRepr d t i
  | _, _, .nil, _, ht => absurd ht (by simp)
  | _, _, .cons ha hs, _, ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨_, ha⟩
      · exact ViewReprList.mem_read hs _ ht

/-- Reading a parent already contains readings of every one of its source subterms. -/
theorem ViewRepr.subterms {d : Database} {t i : Term} (h : ViewRepr d t i) :
    ∀ s ∈ t.subterms, ∃ j, ViewRepr d s j := by
  intro s hs
  induction hs generalizing i with
  | refl => exact ⟨i, h⟩
  | arg hm _ ih =>
      cases h with
      | app hl _ =>
          obtain ⟨j, hj⟩ := hl.mem_read _ hm
          exact ih hj

/-- Closure obligations for the source congruence rules. -/
structure CongObligations (src tgt : Database) : Prop where
  direct : ∀ a b, (a, b) ∈ src.eqs → SameClass tgt a b

  trans : ∀ a b c, SameClass tgt a b → SameClass tgt b c → SameClass tgt a c

  congr : ∀ f as bs, Term.app f as ∈ src.terms → Term.app f bs ∈ src.terms →
    List.Forall₂ (SameClass tgt) as bs → SameClass tgt (.app f as) (.app f bs)

theorem cong_sameClass {src tgt : Database} (h : CongObligations src tgt) {a b : Term}
    (hc : StoredCong src a b) : SameClass tgt a b := by
  refine StoredCong.le h.direct (fun _ _ hab => hab.symm) h.trans h.congr ?_ hc
  intro t s ht hs
  obtain ⟨i, hi, _⟩ := ht
  obtain ⟨j, hj⟩ := hi.subterms s hs
  exact ⟨j, hj, hj⟩

/-- View ids normalize to a common leader, consistently with every UF edge. -/
def ViewLeader (d : Database) : Prop :=
  ∃ lead : Term → Term,
    (∀ t e, ViewRepr d t e → ViewRepr d t (lead e)) ∧
    (∀ t e₁ e₂, ViewRepr d t e₁ → ViewRepr d t e₂ → lead e₁ = lead e₂) ∧
    (∀ x y, d.Out ufName [x] [y] → lead x = lead y)

theorem SameClass.trans_of_viewLeader {d : Database} (h : ViewLeader d) {a b c : Term}
    (hab : SameClass d a b) (hbc : SameClass d b c) : SameClass d a c := by
  obtain ⟨lead, hmem, huniq, -⟩ := h
  obtain ⟨e₁, ha₁, hb₁⟩ := hab
  obtain ⟨e₂, hb₂, hc₂⟩ := hbc
  refine ⟨lead e₁, hmem a e₁ ha₁, ?_⟩
  rw [← huniq b e₂ e₁ hb₂ hb₁]
  exact hmem c e₂ hc₂

/-- Each held application has an entry at some shared tuple of child ids. -/
structure ViewsCover (d src : Database) : Prop where
  shared : ∀ f as bs, Term.app f as ∈ src.terms → List.Forall₂ (SameClass d) as bs →
    ∃ es e, ViewReprList d as es ∧ ViewReprList d bs es ∧ d.Out (viewName f) es [e]

theorem sameClass_congr_of_shared {src d : Database} (hc : ViewsCover d src) {f : FnName}
    {as bs : List Term} (ha : Term.app f as ∈ src.terms)
    (hl : List.Forall₂ (SameClass d) as bs) :
    SameClass d (.app f as) (.app f bs) := by
  obtain ⟨es, e, h₁, h₂, ho⟩ := hc.shared f as bs ha hl
  exact ⟨e, .app h₁ ho, .app h₂ ho⟩

theorem sameClass_self_of_viewReprList {d : Database} : ∀ {as es : List Term},
    ViewReprList d as es → List.Forall₂ (SameClass d) as as
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => .cons ⟨_, h, h⟩ (sameClass_self_of_viewReprList hl)

mutual

/-- View coverage gives every held source term an id. -/
theorem viewRepr_total {d src : Database} (hc : ViewsCover d src) (hw : src.WF) :
    ∀ t : Term, t ∈ src.terms → ∃ e, ViewRepr d t e
  | .lit l, _ => ⟨.lit l, .lit⟩
  | .app f as, ht => by
      obtain ⟨es, hes⟩ := viewRepr_list_total hc hw as fun a ha =>
        hw.subtermClosed _ ht (Term.arg_subterms ha (Term.self_mem_subterms a))
      obtain ⟨es', e, h₁, -, ho⟩ :=
        hc.shared f as as ht (sameClass_self_of_viewReprList hes)
      exact ⟨e, .app h₁ ho⟩

@[inherit_doc viewRepr_total]
theorem viewRepr_list_total {d src : Database} (hc : ViewsCover d src) (hw : src.WF) :
    ∀ as : List Term, (∀ a ∈ as, a ∈ src.terms) → ∃ es, ViewReprList d as es
  | [], _ => ⟨[], .nil⟩
  | a :: as, ht => by
      obtain ⟨e, he⟩ := viewRepr_total hc hw a (ht a (List.mem_cons_self ..))
      obtain ⟨es, hes⟩ := viewRepr_list_total hc hw as fun b hb =>
        ht b (List.mem_cons_of_mem _ hb)
      exact ⟨e :: es, .cons he hes⟩

end

theorem sameClass_self_of_viewsCover {src d : Database} (hc : ViewsCover d src) (hw : src.WF)
    {a : Term} (h : (a, a) ∈ src.eqs) : SameClass d a a :=
  let ⟨e, he⟩ := viewRepr_total hc hw a (StoredCong.direct h).toHeld
  ⟨e, he, he⟩

/-- Every nonreflexive source equation has a shared view id. -/
def UnionsRead (d src : Database) : Prop :=
  ∀ a b, (a, b) ∈ src.eqs → a ≠ b → SameClass d a b

/-- Source union endpoints read to ids linked by a generated UF entry. -/
def UnionsJoined (d src : Database) : Prop :=
  ∀ a b, (a, b) ∈ src.eqs → a ≠ b →
    ∃ e₁ e₂, ViewRepr d a e₁ ∧ ViewRepr d b e₂ ∧
      (d.Out ufName [e₁] [e₂] ∨ d.Out ufName [e₂] [e₁])

theorem unionsRead_of_unionsJoined {src d : Database} (hlead : ViewLeader d)
    (h : UnionsJoined d src) : UnionsRead d src := by
  intro a b hab hne
  obtain ⟨lead, hmem, -, huf⟩ := hlead
  obtain ⟨e₁, e₂, h₁, h₂, ho⟩ := h a b hab hne
  refine ⟨lead e₁, hmem a e₁ h₁, ?_⟩
  rcases ho with ho | ho
  · rw [huf e₁ e₂ ho]; exact hmem b e₂ h₂
  · rw [← huf e₂ e₁ ho]; exact hmem b e₂ h₂

theorem cong_sameClass_of_state {src d : Database} (hw : src.WF) (hlead : ViewLeader d)
    (hcov : ViewsCover d src) (hun : UnionsRead d src) {a b : Term} (h : StoredCong src a b) :
    SameClass d a b :=
  cong_sameClass
    ⟨fun x y hxy => if hxyeq : x = y then hxyeq ▸ sameClass_self_of_viewsCover hcov hw
        (hxyeq ▸ hxy) else hun x y hxy hxyeq,
     fun _ _ _ => SameClass.trans_of_viewLeader hlead,
     fun _ _ _ ha _ hl => sameClass_congr_of_shared hcov ha hl⟩ h

/-- A view row is justified by an existing source application at congruent children. -/
def EntrySound (src : Database) (f : FnName) (cs : List Term) (e : Term) : Prop :=
  ∃ as, Term.app f as ∈ src.terms ∧ StoredCongList src as cs ∧ StoredCong src (.app f as) e

theorem EntrySound.cong_of_congList {src : Database} {f : FnName} {cs : List Term} {e : Term}
    (h : EntrySound src f cs e) {as : List Term} (ha : Term.app f as ∈ src.terms)
    (hl : StoredCongList src as cs) : StoredCong src (.app f as) e :=
  let ⟨_, hbm, hbl, hbe⟩ := h
  (StoredCong.congr (Database.toStored ha) (Database.toStored hbm) (hl.trans hbl.symm)).trans hbe

/-- Every recorded view entry has a source witness. -/
def ViewsSound (d src : Database) : Prop :=
  ∀ f cs e, d.Out (viewName f) cs [e] → EntrySound src f cs e

/-- Every recorded UF edge relates source-congruent terms. -/
def EdgesSound (d src : Database) : Prop :=
  ∀ t p, d.Out ufName [t] [p] → StoredCong src t p

mutual

/-- A represented source term is congruent to every id it reads. -/
theorem cong_of_viewRepr {src d : Database} (hw : src.WF) (hs : ViewsSound d src) :
    ∀ (a : Term) {e : Term}, a ∈ src.terms → ViewRepr d a e → StoredCong src a e
  | .lit _, _, ha, .lit => Database.toStored ha
  | .app f as, _, ha, .app hl ho =>
      (hs f _ _ ho).cong_of_congList ha
        (congList_of_viewReprList hw hs as
          (fun a h => hw.subtermClosed _ ha (Term.arg_subterms h (Term.self_mem_subterms a)))
          hl)

@[inherit_doc cong_of_viewRepr]
theorem congList_of_viewReprList {src d : Database} (hw : src.WF) (hs : ViewsSound d src) :
    ∀ (as : List Term) {es : List Term}, (∀ a ∈ as, a ∈ src.terms) →
      ViewReprList d as es → StoredCongList src as es
  | [], _, _, .nil => .nil
  | a :: as, _, ha, .cons h₁ h₂ =>
      .cons (cong_of_viewRepr hw hs a (ha a (List.mem_cons_self ..)) h₁)
        (congList_of_viewReprList hw hs as (fun b hb => ha b (List.mem_cons_of_mem _ hb)) h₂)

end

/-- The conclusion of the structural reading induction. -/
def ViewsJustified (d src : Database) : Prop :=
  ∀ a e, a ∈ src.terms → ViewRepr d a e → StoredCong src a e

@[inherit_doc cong_of_viewRepr]
theorem ViewsSound.justified {src d : Database} (hw : src.WF)
    (hs : ViewsSound d src) : ViewsJustified d src := fun a _ ha h => cong_of_viewRepr hw hs a ha h

theorem sameClass_cong_of_justified {src d : Database} (hj : ViewsJustified d src) {a b : Term}
    (ha : a ∈ src.terms) (hb : b ∈ src.terms) (h : SameClass d a b) : StoredCong src a b :=
  let ⟨e, hae, hbe⟩ := h
  (hj a e ha hae).trans (hj b e hb hbe).symm

theorem sameClass_cong_of_state {src d : Database} (hw : src.WF) (hs : ViewsSound d src)
    {a b : Term} (ha : a ∈ src.terms) (hb : b ∈ src.terms) (h : SameClass d a b) :
    StoredCong src a b :=
  sameClass_cong_of_justified (hs.justified hw) ha hb h

/-- The source and target agree when the execution establishes the data invariants. -/
theorem corresponds_of_invariants {src d : Database} (hw : src.WF)
    (hlead : ViewLeader d) (hcov : ViewsCover d src) (hun : UnionsJoined d src)
    (hsound : ViewsSound d src) (a b : Term) (ha : a ∈ src.terms) (hb : b ∈ src.terms) :
    StoredCong src a b ↔ SameClass d a b :=
  ⟨cong_sameClass_of_state hw hlead hcov (unionsRead_of_unionsJoined hlead hun),
   sameClass_cong_of_state hw hsound ha hb⟩

end Egglog.Congruence
