import EgglogSemantics.Proofs.Congruence.LiveFixedpoint

/-! Intermediate readings follow current UF connectivity through destructive merges. -/

namespace Egglog.Congruence.Live

mutual

inductive Repr (d : Database) : Term → Term → Prop where
  | lit {l : Lit} : Repr d (.lit l) (.lit l)
  | app {f : FnName} {as cs : List Term} {i : Term} :
      ReprList d as cs → Entry.mk (viewName f) cs [i] ∈ d.entries →
      Repr d (.app f as) i
  | joined {t i j : Term} : Repr d t i → Joined d i j → Repr d t j

inductive ReprList (d : Database) : List Term → List Term → Prop where
  | nil : ReprList d [] []
  | cons {t i : Term} {ts is : List Term} :
      Repr d t i → ReprList d ts is → ReprList d (t :: ts) (i :: is)

end

theorem Repr.transport {d e : Database}
    (hrow : ∀ f cs a, Entry.mk f cs [a] ∈ d.entries →
      ∃ b, Entry.mk f cs [b] ∈ e.entries ∧ Joined e a b)
    (hjoin : ∀ a b, Joined d a b → Joined e a b)
    {t i : Term} (hr : Repr d t i) : Repr e t i := by
  induction hr using Repr.rec (motive_2 := fun as cs _ => ReprList e as cs) with
  | lit => exact .lit
  | @app f as cs i _ hrow' ih =>
      obtain ⟨j, hj, he⟩ := hrow (viewName f) cs i hrow'
      exact .joined (.app ih hj) he.symm
  | joined _ hj ih => exact .joined ih (hjoin _ _ hj)
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂

theorem Repr.mono {d e : Database} (h : d.entries ⊆ e.entries)
    {t i : Term} (hr : Repr d t i) : Repr e t i :=
  hr.transport (fun _ _ a ha => ⟨a, h ha, .refl a⟩) (fun _ _ hj => hj.mono h)

theorem ReprList.mono {d e : Database} (h : d.entries ⊆ e.entries)
    : ∀ {ts is : List Term}, ReprList d ts is → ReprList e ts is
  | _, _, .nil => .nil
  | _, _, .cons ht hs => .cons (ht.mono h) (hs.mono h)

theorem Repr.mergeClosure {d e : Database} (h : State d) (hd : d.Diag)
    (hc : MergeClosure d e) {t i : Term} (hr : Repr d t i) : Repr e t i :=
  hr.transport (fun _ _ _ ha => by
    obtain ⟨b, hb, hj, _⟩ := row_closure h hd hc ha
    exact ⟨b, hb, hj⟩) (fun _ _ hj => hj.mergeClosure h hd hc)

theorem Repr.of_view {d : Database} (hd : d.Diag) {t i : Term}
    (hr : ViewRepr d t i) : Repr d t i := by
  induction hr using ViewRepr.rec (motive_2 := fun as cs _ => ReprList d as cs) with
  | lit => exact .lit
  | app _ ho ih => exact .app ih (ho.entry hd)
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂

theorem Repr.normalize {d src : Database} (h : Abstract.Rebuilt d) (hs : d.StoreOk)
    (hsound : EdgesSound d src) (hw : src.WF) {t i : Term} (hr : Repr d t i) :
    ViewRepr d t (h.root i) := by
  induction hr using Repr.rec
      (motive_2 := fun as cs _ => ViewReprList d as (cs.map h.root)) with
  | @lit l => rw [h.root_lit hsound hw l]; exact .lit
  | app _ ho ih => exact .app ih (h.out_normalized (Abstract.out_of_current hs ho))
  | joined _ hj ih => exact h.root_joined hs hj ▸ ih
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂

theorem ReprList.mem_read {d : Database} : ∀ {as is : List Term},
    ReprList d as is → ∀ t ∈ as, ∃ i, Repr d t i
  | _, _, .nil, _, ht => by simp at ht
  | _, _, .cons ha hs, _, ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨_, ha⟩
      · exact hs.mem_read _ ht

theorem Repr.arg {d : Database} {f : FnName} {as : List Term} {i : Term}
    (hr : Repr d (.app f as) i) {a : Term} (ha : a ∈ as) : ∃ j, Repr d a j := by
  generalize ht : Term.app f as = t at hr
  induction hr using Repr.rec (motive_2 := fun _ _ _ => True) with
  | lit => cases ht
  | app hl _ _ => cases ht; exact hl.mem_read _ ha
  | joined _ _ ih => exact ih ht
  | nil => trivial
  | cons => trivial

theorem Repr.subterms {d : Database} {t i : Term} (hr : Repr d t i) :
    ∀ s ∈ t.subterms, ∃ j, Repr d s j := by
  intro s hs
  induction hs generalizing i with
  | refl => exact ⟨i, hr⟩
  | arg ha _ ih => obtain ⟨j, hj⟩ := hr.arg ha; exact ih hj

/-- Facts retained between completed rebuilding phases. -/
structure Reads (d src : Database) : Prop where
  terms : ∀ t ∈ src.terms, ∃ i, Repr d t i
  unions : ∀ a b, (a, b) ∈ src.eqs → a ≠ b → ∃ i, Repr d a i ∧ Repr d b i

theorem Reads.transport {d e src : Database} (h : Reads d src)
    (hr : ∀ t i, Repr d t i → Repr e t i) : Reads e src :=
  ⟨fun t ht => (h.terms t ht).imp (hr t), fun a b hab hn => by
    obtain ⟨i, ha, hb⟩ := h.unions a b hab hn
    exact ⟨i, hr a i ha, hr b i hb⟩⟩

theorem Reads.mono {d e src : Database} (h : Reads d src) (he : d.entries ⊆ e.entries) :
    Reads e src := h.transport (fun _ _ hr => hr.mono he)

theorem Reads.mergeClosure {d e src : Database} (h : Reads d src) (hd : State d)
    (hdiag : d.Diag) (hc : MergeClosure d e) : Reads e src :=
  h.transport (fun _ _ hr => hr.mergeClosure hd hdiag hc)

theorem Reads.normalize {d src ref : Database} (h : Reads d src)
    (hr : Abstract.Rebuilt d) (hs : d.StoreOk) (hsound : EdgesSound d ref) (hw : ref.WF) :
    (∀ t ∈ src.terms, ∃ i, ViewRepr d t i) ∧ UnionsRead d src := by
  refine ⟨fun t ht => ?_, fun a b hab hn => ?_⟩
  · obtain ⟨i, hi⟩ := h.terms t ht
    exact ⟨hr.root i, hi.normalize hr hs hsound hw⟩
  · obtain ⟨i, ha, hb⟩ := h.unions a b hab hn
    exact ⟨hr.root i, ha.normalize hr hs hsound hw, hb.normalize hr hs hsound hw⟩

theorem Reads.restrict {d src src' : Database} (h : Reads d src)
    (hc : src'.Contained src) : Reads d src' :=
  ⟨fun t ht => h.terms t (hc.terms ht), fun a b hab => h.unions a b (hc.eqs hab)⟩

theorem Reads.addTerm {d src : Database} (h : Reads d src) {t i : Term}
    (ht : Repr d t i) : Reads d (src.addTerm t) := by
  refine ⟨?_, fun a b hab hn => ?_⟩
  · intro s hs
    rcases Database.addTerm_terms ▸ hs with hs | hs
    · exact h.terms s hs
    · exact ht.subterms s hs
  · rcases Database.addTerm_eqs ▸ hab with heq | hab
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact (hn rfl).elim
    · exact h.unions a b hab hn

theorem Reads.addEq {d src : Database} (h : Reads d src) {a b i j : Term}
    (ha : Repr d a i) (hb : Repr d b j) (hu : Joined d i j) : Reads d (src.addEq a b) := by
  have ht := (h.addTerm ha).addTerm hb
  refine ⟨?_, fun x y hxy hn => ?_⟩
  · intro t hm
    apply ht.terms t
    simpa only [Database.addTerm_terms] using Database.addEq_terms ▸ hm
  · rcases Database.addEq_eqs ▸ hxy with heq | hxy
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨j, .joined ha hu, hb⟩
    · exact h.unions x y hxy hn

theorem Reads.sUnion {d src : Database} {S : Set Database} (h : Reads d src)
    (hs : ∀ s ∈ S, Reads d s) : Reads d (src.sUnion S) := by
  refine ⟨fun t ht => ?_, fun a b hab hn => ?_⟩
  · rcases Database.sUnion_terms ▸ ht with ht | ht
    · exact h.terms t ht
    · obtain ⟨s, hs', ht⟩ := Set.mem_iUnion₂.mp ht
      exact (hs s hs').terms t ht
  · rcases Database.sUnion_eqs ▸ hab with hab | hab
    · exact h.unions a b hab hn
    · obtain ⟨s, hs', hab⟩ := Set.mem_iUnion₂.mp hab
      exact (hs s hs').unions a b hab hn

end Egglog.Congruence.Live
