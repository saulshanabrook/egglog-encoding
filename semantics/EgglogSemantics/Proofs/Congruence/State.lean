import EgglogSemantics.Proofs.Congruence.EntryShape
import EgglogSemantics.Proofs.Congruence.Read
import EgglogSemantics.Proofs.Congruence.Properties
import EgglogSemantics.Proofs.Congruence.Correspond

/-! Soundness invariants on retained single-output view and union-find entries. -/

namespace Egglog.Congruence

def SoundTerms (d : FDatabase) (src : Database) : Prop :=
  (∀ f cs e, Term.app (viewName f) (cs ++ [e]) ∈ d.terms → EntrySound src f cs e) ∧
  (∀ t p, Term.app ufName [t, p] ∈ d.terms → Cong src t p)

theorem SoundTerms.mono_terms {src : Database} {d e : FDatabase}
    (ht : ∀ t ∈ e.terms, t ∈ d.terms) (h : SoundTerms d src) : SoundTerms e src :=
  ⟨fun f cs x hm => h.1 f cs x (ht _ hm), fun x p hm => h.2 x p (ht _ hm)⟩

theorem viewsSound_of_soundTerms {src : Database} {d : FDatabase} (hr : d.EqsRefl)
    (h : SoundTerms d src) :
    ViewsSound d.toDatabase src ∧ EdgesSound d.toDatabase src := by
  refine ⟨fun f cs e ho => ?_, fun t p ho => ?_⟩
  · obtain ⟨bs, hcl, hmem⟩ := ho
    obtain rfl : cs = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
    exact h.1 f cs e (by rw [FDatabase.toDatabase_terms] at hmem; exact hmem)
  · obtain ⟨bs, hcl, hmem⟩ := ho
    obtain rfl : [t] = bs := CongList.eq_of_eqsRefl hr.toDatabase hcl
    refine h.2 t p ?_
    rw [FDatabase.toDatabase_terms] at hmem
    exact hmem

theorem soundTerms_of_viewsSound {src : Database} {d : FDatabase} (hsc : d.SubtermClosed)
    (hv : ViewsSound d.toDatabase src) (he : EdgesSound d.toDatabase src) : SoundTerms d src := by
  have hout : ∀ (f : FnName) (as vs : List Term), Term.app f (as ++ vs) ∈ d.terms →
      d.toDatabase.Out f as vs := by
    intro f as vs hmem
    refine Database.out_self (by rw [FDatabase.toDatabase_terms]; exact hmem) (fun a ha => ?_)
    rw [FDatabase.toDatabase_terms]
    exact hsc _ hmem a ((Term.mem_subtermList (Term.app f (as ++ vs))).mpr
      (Term.arg_subterms (List.mem_append_left _ ha) (Term.self_mem_subterms a)))
  exact ⟨fun f cs e hmem => hv f cs e (hout _ _ _ hmem),
    fun t p hmem => he t p (hout ufName [t] [p] hmem)⟩

theorem EntrySound.mono {src src' : Database} (h : src.eqs ⊆ src'.eqs) {f : FnName}
    {cs : List Term} {e : Term} (hs : EntrySound src f cs e) : EntrySound src' f cs e :=
  let ⟨as, ham, hal, hae⟩ := hs
  ⟨as, Cong.mono ⟨h⟩ ham, hal.mono ⟨h⟩, Cong.mono ⟨h⟩ hae⟩

theorem SoundTerms.mono_src {src src' : Database} {d : FDatabase}
    (h : src.eqs ⊆ src'.eqs) (hs : SoundTerms d src) : SoundTerms d src' :=
  ⟨fun f cs e hm => (hs.1 f cs e hm).mono h,
    fun t p hm => Cong.mono ⟨h⟩ (hs.2 t p hm)⟩

theorem SoundTerms.addTerm {src : Database} {d : FDatabase} {t : Term}
    (h : SoundTerms d src)
    (hv : ∀ f cs e, Term.app (viewName f) (cs ++ [e]) ∈ t.subtermList →
      EntrySound src f cs e)
    (hu : ∀ x p, Term.app ufName [x, p] ∈ t.subtermList → Cong src x p) :
    SoundTerms (d.addTerm t) src := by
  constructor
  · intro f cs e hm
    rcases FDatabase.mem_addTerm_terms_imp hm with hm' | hm'
    · exact hv f cs e hm'
    · exact h.1 f cs e hm'
  · intro x p hm
    rcases FDatabase.mem_addTerm_terms_imp hm with hm' | hm'
    · exact hu x p hm'
    · exact h.2 x p hm'

theorem SoundTerms.addRow {src : Database} {d : FDatabase} {g : FnName}
    {as vs : List Term} (h : SoundTerms d src)
    (hv : ∀ f cs e,
      Term.app (viewName f) (cs ++ [e]) ∈ (Term.app g (as ++ vs)).subtermList →
      EntrySound src f cs e)
    (hu : ∀ x p, Term.app ufName [x, p] ∈ (Term.app g (as ++ vs)).subtermList →
      Cong src x p) :
    SoundTerms (d.addRow g as vs) src := h.addTerm hv hu

theorem SoundTerms.addTerm_of_mem {src : Database} {d : FDatabase}
    (hsc : d.SubtermClosed) (h : SoundTerms d src) {t : Term} (ht : t ∈ d.terms) :
    SoundTerms (d.addTerm t) src :=
  h.addTerm (fun f cs e hm => h.1 f cs e (hsc t ht _ hm))
    (fun a b hm => h.2 a b (hsc t ht _ hm))

theorem SoundTerms.union {src : Database} {d₁ d₂ : FDatabase}
    (h₁ : SoundTerms d₁ src) (h₂ : SoundTerms d₂ src) : SoundTerms (d₁.union d₂) src := by
  constructor
  · intro f cs e hm
    rcases List.mem_append.mp (List.mem_dedup.mp hm) with hm' | hm'
    · exact h₁.1 f cs e hm'
    · exact h₂.1 f cs e hm'
  · intro x p hm
    rcases List.mem_append.mp (List.mem_dedup.mp hm) with hm' | hm'
    · exact h₁.2 x p hm'
    · exact h₂.2 x p hm'

theorem empty_soundTerms {src : Database} : SoundTerms FDatabase.empty src :=
  ⟨fun _ _ _ hm => absurd hm (by simp [FDatabase.empty]),
    fun _ _ hm => absurd hm (by simp [FDatabase.empty])⟩

theorem SoundTerms.addTerm_top {src : Database} {d : FDatabase} {t : Term}
    (h : SoundTerms d src)
    (hsub : ∀ s ∈ t.subtermList, s ≠ t → EntryShaped s → s ∈ d.terms)
    (hv : ∀ f cs e, t = Term.app (viewName f) (cs ++ [e]) → EntrySound src f cs e)
    (hu : ∀ x p, t = Term.app ufName [x, p] → Cong src x p) :
    SoundTerms (d.addTerm t) src := by
  refine h.addTerm (fun f cs e hm => ?_) (fun x p hm => ?_)
  · by_cases he : Term.app (viewName f) (cs ++ [e]) = t
    · exact hv f cs e he.symm
    · exact h.1 f cs e (hsub _ hm he (Or.inl ⟨f, cs, e, rfl⟩))
  · by_cases he : Term.app ufName [x, p] = t
    · exact hu x p he.symm
    · exact h.2 x p (hsub _ hm he (Or.inr ⟨x, p, rfl⟩))

theorem SoundTerms.addRow_top {src : Database} {d : FDatabase} {g : FnName}
    {as vs : List Term} (h : SoundTerms d src)
    (hsub : ∀ s ∈ (Term.app g (as ++ vs)).subtermList, s ≠ Term.app g (as ++ vs) →
      EntryShaped s → s ∈ d.terms)
    (hv : ∀ f cs e, Term.app g (as ++ vs) = Term.app (viewName f) (cs ++ [e]) →
      EntrySound src f cs e)
    (hu : ∀ x p, Term.app g (as ++ vs) = Term.app ufName [x, p] → Cong src x p) :
    SoundTerms (d.addRow g as vs) src := h.addTerm_top hsub hv hu

theorem FDatabase.subterms_of_columns {d : FDatabase} (hsc : d.SubtermClosed) {g : FnName}
    {cols : List Term} (hcol : ∀ c ∈ cols, c ∈ d.terms) :
    ∀ s ∈ (Term.app g cols).subtermList, s ≠ Term.app g cols → s ∈ d.terms := by
  intro s hs hne
  rw [Term.subtermList, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact absurd rfl hne
  · obtain ⟨a, ha, hsa⟩ := (Term.mem_subtermListL cols).mp hs
    exact hsc a (hcol a ha) s ((Term.mem_subtermList a).mpr hsa)

theorem not_entryShaped_of_ne {g : FnName} (hv : ∀ f, g ≠ viewName f) (hu : g ≠ ufName)
    {as : List Term} : ¬ EntryShaped (Term.app g as) := by
  rintro (⟨f, cs, e, h⟩ | ⟨x, p, h⟩)
  · exact hv f (Term.app.inj h).1
  · exact hu (Term.app.inj h).1

/-- Writing an already justified edge cannot introduce an unjustified entry through
its children: both columns and all their subterms were already held. -/
theorem SoundTerms.addUF {src : Database} {d : FDatabase} (hsc : d.SubtermClosed)
    (h : SoundTerms d src) {a b : Term} (ha : a ∈ d.terms) (hb : b ∈ d.terms)
    (hc : Cong src a b) : SoundTerms (d.addAtom (.app ufName [a, b])) src := by
  apply SoundTerms.mono_terms (d := d.addTerm (.app ufName [a, b])) (fun _ ht => ht)
  refine h.addTerm_top (fun s hs hn _ => ?_) (fun f cs e he => ?_) (fun x p he => ?_)
  · have hcol : ∀ c ∈ [a, b], c ∈ d.terms := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    exact FDatabase.subterms_of_columns hsc hcol s hs hn
  · exact False.elim (viewName_ne_ufName (Term.app.inj he).1.symm)
  · have hab : a = x ∧ b = p := by simpa using (Term.app.inj he).2
    simpa [← hab.1, ← hab.2] using hc

theorem SoundTerms.addView {src : Database} {d : FDatabase} (hsc : d.SubtermClosed)
    (h : SoundTerms d src) {f : FnName} {cs : List Term} {e : Term}
    (hcs : ∀ c ∈ cs, c ∈ d.terms) (he : e ∈ d.terms) (hs : EntrySound src f cs e) :
    SoundTerms (d.addAtom (.app (viewName f) (cs ++ [e]))) src := by
  apply SoundTerms.mono_terms
    (d := d.addTerm (.app (viewName f) (cs ++ [e]))) (fun _ ht => ht)
  refine h.addTerm_top (fun s ht hn _ => ?_) (fun g ks out ht => ?_) (fun x p ht => ?_)
  · apply FDatabase.subterms_of_columns hsc (cols := cs ++ [e]) _ s ht hn
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcs c hc
    · obtain rfl := List.mem_singleton.mp hc
      exact he
  · obtain ⟨hname, hcols⟩ := Term.app.inj ht
    obtain rfl := viewName_inj hname
    obtain ⟨hkeys, hout⟩ := List.append_inj' hcols rfl
    have hv : e = out := by simpa using hout
    rw [← hkeys, ← hv]
    exact hs
  · exact False.elim (viewName_ne_ufName (Term.app.inj ht).1)

end Egglog.Congruence
