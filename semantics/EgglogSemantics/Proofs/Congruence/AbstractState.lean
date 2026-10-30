import EgglogSemantics.Proofs.Congruence.Correspond
import EgglogSemantics.Proofs.Diagonal

/-! Soundness and order invariants on the mathematical target's retained rows. -/

namespace Egglog.Congruence.Abstract

/-- Every retained generated row has a justification in the source database. -/
def SoundTerms (d src : Database) : Prop :=
  (∀ f cs e, Term.app (viewName f) (cs ++ [e]) ∈ d.terms → EntrySound src f cs e) ∧
  (∀ t p, Term.app ufName [t, p] ∈ d.terms → StoredCong src t p)

/-- Every retained union-find edge points weakly down in the structural term order. -/
def Descending (d : Database) : Prop :=
  ∀ a b, Term.app ufName [a, b] ∈ d.terms → b = a ∨ Term.blt b a = true

theorem SoundTerms.mono_terms {src d e : Database}
    (ht : e.terms ⊆ d.terms) (h : SoundTerms d src) : SoundTerms e src :=
  ⟨fun f cs x hm => h.1 f cs x (ht hm), fun x p hm => h.2 x p (ht hm)⟩

theorem Descending.mono_terms {d e : Database} (ht : e.terms ⊆ d.terms)
    (h : Descending d) : Descending e := fun a b hm => h a b (ht hm)

theorem SoundTerms.congr_terms {src d e : Database} (ht : e.terms = d.terms)
    (h : SoundTerms d src) : SoundTerms e src := h.mono_terms ht.subset

theorem SoundTerms.mono_src {src src' d : Database} (h : src.eqs ⊆ src'.eqs)
    (hs : SoundTerms d src) : SoundTerms d src' := by
  constructor
  · intro f cs e hm
    obtain ⟨as, ha, hal, hae⟩ := hs.1 f cs e hm
    exact ⟨as, (Database.Contained.mk h).terms ha, hal.mono ⟨h⟩, StoredCong.mono ⟨h⟩ hae⟩
  · exact fun a b hm => StoredCong.mono ⟨h⟩ (hs.2 a b hm)

theorem SoundTerms.viewsSound {src d : Database} (h : SoundTerms d src) (hd : d.Diag) :
    ViewsSound d src := fun f cs e ho => h.1 f cs e (ho.term hd)

theorem SoundTerms.edgesSound {src d : Database} (h : SoundTerms d src) (hd : d.Diag) :
    EdgesSound d src := fun a b ho => h.2 a b (ho.term hd)

theorem Descending.out {d : Database} (h : Descending d) (hd : d.Diag) {a b : Term}
    (ho : d.Out ufName [a] [b]) : b = a ∨ Term.blt b a = true := h a b (ho.term hd)

theorem SoundTerms.addTerm {src d : Database} {t : Term} (h : SoundTerms d src)
    (hv : ∀ f cs e, Term.app (viewName f) (cs ++ [e]) ∈ t.subterms → EntrySound src f cs e)
    (hu : ∀ a b, Term.app ufName [a, b] ∈ t.subterms → StoredCong src a b) :
    SoundTerms (d.addTerm t) src := by
  constructor
  · intro f cs e hm
    rcases Database.addTerm_terms ▸ hm with hm | hm
    · exact h.1 f cs e hm
    · exact hv f cs e hm
  · intro a b hm
    rcases Database.addTerm_terms ▸ hm with hm | hm
    · exact h.2 a b hm
    · exact hu a b hm

theorem SoundTerms.addTerm_of_mem {src d : Database} (hw : d.WF)
    (h : SoundTerms d src) {t : Term} (ht : t ∈ d.terms) : SoundTerms (d.addTerm t) src :=
  h.addTerm (fun f cs e hm => h.1 f cs e (hw.subtermClosed _ ht hm))
    (fun a b hm => h.2 a b (hw.subtermClosed _ ht hm))

theorem Descending.addTerm_of_mem {d : Database} (hw : d.WF) (h : Descending d)
    {t : Term} (ht : t ∈ d.terms) : Descending (d.addTerm t) := by
  intro a b hm
  rcases Database.addTerm_terms ▸ hm with hm | hm
  · exact h a b hm
  · exact h a b (hw.subtermClosed _ ht hm)

/-- Proper subterms of a new row already occur in its columns. -/
theorem subterms_of_columns {d : Database} (hw : d.WF) {g : FnName} {cols : List Term}
    (hcol : ∀ c ∈ cols, c ∈ d.terms) {s : Term}
    (hs : s ∈ (Term.app g cols).subterms) (hne : s ≠ Term.app g cols) : s ∈ d.terms := by
  change Term.IsSubterm s (.app g cols) at hs
  rw [← Term.mem_subtermList, Term.subtermList, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact (hne rfl).elim
  · obtain ⟨a, ha, hsa⟩ := (Term.mem_subtermListL cols).mp hs
    exact hw.subtermClosed _ (hcol a ha) hsa

theorem SoundTerms.addTerm_top {src d : Database} {t : Term} (h : SoundTerms d src)
    (hsub : ∀ s ∈ t.subterms, s ≠ t → s ∈ d.terms)
    (hv : ∀ f cs e, t = Term.app (viewName f) (cs ++ [e]) → EntrySound src f cs e)
    (hu : ∀ a b, t = Term.app ufName [a, b] → StoredCong src a b) :
    SoundTerms (d.addTerm t) src := by
  apply h.addTerm
  · intro f cs e hm
    by_cases he : Term.app (viewName f) (cs ++ [e]) = t
    · exact hv f cs e he.symm
    · exact h.1 f cs e (hsub _ hm he)
  · intro a b hm
    by_cases he : Term.app ufName [a, b] = t
    · exact hu a b he.symm
    · exact h.2 a b (hsub _ hm he)

theorem SoundTerms.addUF {src d : Database} (hw : d.WF) (h : SoundTerms d src)
    {a b : Term} (ha : a ∈ d.terms) (hb : b ∈ d.terms) (hc : StoredCong src a b) :
    SoundTerms (d.addTerm (.app ufName [a, b])) src := by
  have hcol : ∀ c ∈ [a, b], c ∈ d.terms := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption
  refine h.addTerm_top (fun _ hs hn => subterms_of_columns hw hcol hs hn) ?_ ?_
  · intro f cs e he
    exact (viewName_ne_ufName (Term.app.inj he).1.symm).elim
  · intro x p he
    have hab : a = x ∧ b = p := by simpa using (Term.app.inj he).2
    simpa [← hab.1, ← hab.2] using hc

theorem Descending.addUF {d : Database} (hw : d.WF) (h : Descending d)
    {a b : Term} (ha : a ∈ d.terms) (hb : b ∈ d.terms)
    (hab : b = a ∨ Term.blt b a = true) : Descending (d.addTerm (.app ufName [a, b])) := by
  intro x p hm
  rcases Database.addTerm_terms ▸ hm with hm | hm
  · exact h x p hm
  · by_cases he : Term.app ufName [x, p] = Term.app ufName [a, b]
    · have hxp : x = a ∧ p = b := by simpa using (Term.app.inj he).2
      simpa [hxp.1, hxp.2] using hab
    · apply h x p
      apply subterms_of_columns hw _ hm he
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption

theorem SoundTerms.addView {src d : Database} (hw : d.WF) (h : SoundTerms d src)
    {f : FnName} {cs : List Term} {e : Term} (hcs : ∀ c ∈ cs, c ∈ d.terms)
    (he : e ∈ d.terms) (hs : EntrySound src f cs e) :
    SoundTerms (d.addTerm (.app (viewName f) (cs ++ [e]))) src := by
  have hcol : ∀ c ∈ cs ++ [e], c ∈ d.terms := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcs c hc
    · obtain rfl := List.mem_singleton.mp hc
      exact he
  refine h.addTerm_top (fun _ ht hn => subterms_of_columns hw hcol ht hn) ?_ ?_
  · intro g ks out ht
    obtain ⟨hname, hcols⟩ := Term.app.inj ht
    obtain rfl := viewName_inj hname
    obtain ⟨hkeys, hout⟩ := List.append_inj' hcols rfl
    have hv : e = out := by simpa using hout
    simpa [← hkeys, ← hv] using hs
  · intro x p ht
    exact (viewName_ne_ufName (Term.app.inj ht).1).elim

theorem SoundTerms.sUnion {src d : Database} {S : Set Database}
    (h : SoundTerms d src) (hs : ∀ e ∈ S, SoundTerms e src) : SoundTerms (d.sUnion S) src := by
  constructor
  · intro f cs e hm
    simp only [Database.sUnion_terms, Set.mem_union, Set.mem_iUnion, exists_prop] at hm
    rcases hm with hm | ⟨d', hd', hm⟩
    · exact h.1 f cs e hm
    · exact (hs d' hd').1 f cs e hm
  · intro a b hm
    simp only [Database.sUnion_terms, Set.mem_union, Set.mem_iUnion, exists_prop] at hm
    rcases hm with hm | ⟨d', hd', hm⟩
    · exact h.2 a b hm
    · exact (hs d' hd').2 a b hm

theorem empty_soundTerms (src : Database) : SoundTerms Database.empty src := by
  constructor <;> intros <;> simp_all

theorem empty_descending : Descending Database.empty := by
  intro a b hm
  simp at hm

end Egglog.Congruence.Abstract
