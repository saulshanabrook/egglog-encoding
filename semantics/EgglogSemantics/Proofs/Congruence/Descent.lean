import EgglogSemantics.Proofs.Congruence.Roots

/-! Table merges preserve descending historical UF edges. -/

namespace Egglog.Congruence

theorem UFTermsDescend.mono_terms {d e : FDatabase} (h : UFTermsDescend d)
    (ht : ∀ t ∈ e.terms, t ∈ d.terms) : UFTermsDescend e := fun a b hab => h a b (ht _ hab)

theorem UFTermsDescend.union {d e : FDatabase} (hd : UFTermsDescend d)
    (he : UFTermsDescend e) : UFTermsDescend (d.union e) := by
  intro a b hab
  rcases Egglog.FDatabase.mem_terms_union.mp hab with h | h
  · exact hd a b h
  · exact he a b h

/-- Only new UF-shaped subterms can affect descent. -/
theorem UFTermsDescend.addTerm {d : FDatabase} (h : UFTermsDescend d) {t : Term}
    (hn : ∀ a b, Term.app ufName [a, b] ∈ t.subtermList →
      b = a ∨ Term.blt b a = true) : UFTermsDescend (d.addTerm t) := by
  intro a b hm
  rcases Egglog.FDatabase.mem_addTerm_terms_imp hm with hm | hm
  · exact hn a b hm
  · exact h a b hm

theorem UFTermsDescend.addTerm_held {d : FDatabase} (h : UFTermsDescend d)
    (hsc : d.SubtermClosed) {t : Term} (ht : t ∈ d.terms) :
    UFTermsDescend (d.addTerm t) :=
  h.addTerm fun a b hm => h a b (hsc t ht _ hm)

/-- For held columns, checking the newly written UF edge is sufficient. -/
theorem UFTermsDescend.addAtom {d : FDatabase} (h : UFTermsDescend d)
    (hsc : d.SubtermClosed) {f : FnName} {cols : List Term}
    (hc : ∀ t ∈ cols, t ∈ d.terms)
    (hu : ∀ a b, Term.app f cols = Term.app ufName [a, b] → b = a ∨ Term.blt b a = true) :
    UFTermsDescend (d.addAtom (.app f cols)) := by
  apply h.addTerm
  intro a b hm
  by_cases he : Term.app ufName [a, b] = Term.app f cols
  · exact hu a b he.symm
  · exact h a b (FDatabase.subterms_of_columns hsc hc _ hm he)

/-- Linking two held ids to the smaller one writes only descending edges. -/
theorem UFTermsDescend.mergeLinks {d : FDatabase} (h : UFTermsDescend d)
    (hsc : d.SubtermClosed) {old new : Term} (ho : old ∈ d.terms) (hn : new ∈ d.terms) :
    UFTermsDescend (mergeLinks d old new) := by
  have hl : lowerId old new ∈ d.terms := by
    rcases lowerId_eq_or old new with heq | heq <;> rw [heq] <;> assumption
  have h₁ : UFTermsDescend (d.addAtom (.app ufName [old, lowerId old new])) :=
    h.addAtom hsc
      (by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> assumption)
      (by
        intro a b hab
        obtain ⟨rfl, rfl⟩ : old = a ∧ lowerId old new = b := by simpa using hab
        exact lowerId_le_left old new)
  exact h₁.addAtom (hsc.addTerm _)
    (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact Egglog.FDatabase.mem_addTerm_of_mem ‹_›)
    (by
      intro a b hab
      obtain ⟨rfl, rfl⟩ : new = a ∧ lowerId old new = b := by simpa using hab
      exact lowerId_le_right old new)

/-- A collision only links `old` and `new` to `min(old,new)`; its survivor was already held. -/
theorem mergeOneOriented_ufTermsDescend {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (h : UFTermsDescend d) (run : d.mergeOneOriented cl r₁ r₂ = some e) :
    UFTermsDescend e := by
  obtain ⟨old, new, hold, hnew, hfn, hargs, hm₁, hm₂, hmg, he⟩ :=
    mergeOneOriented_single hshape hidx hcl hne run
  have ht₁ := mem_terms_of_indexOk hr hidx hm₁ hmg
  have ht₂ := mem_terms_of_indexOk hr hidx hm₂ (by rw [← hfn]; exact hmg)
  have hn : new ∈ d.terms := FDatabase.mem_terms_of_column hsc ht₁
    (by rw [hnew]; simp)
  have ho : old ∈ d.terms := FDatabase.mem_terms_of_column hsc ht₂
    (by rw [hold]; simp)
  have hs : Term.app r₂.fn (r₂.args ++ [lowerId old new]) ∈ d.terms := by
    unfold lowerId
    split
    · simpa only [hnew, hfn, hargs] using ht₁
    · simpa only [hold] using ht₂
  have hm : UFTermsDescend (mergeLinks d old new) := h.mergeLinks hsc ho hn
  rw [he]
  exact hm.addTerm fun a b hab => h a b (hsc _ hs _ hab)

theorem mergeOneWith_ufTermsDescend {cl : Finset (Term × Term)} {d e : FDatabase}
    {r₁ r₂ : Row} (hshape : MergeShape d.sig) (hr : d.EqsRefl) (hsc : d.SubtermClosed)
    (hidx : d.IndexOk) (hcl : ∀ p ∈ cl, p.1 = p.2) (hne : r₁ ≠ r₂)
    (h : UFTermsDescend d) (run : d.mergeOneWith cl r₁ r₂ = some e) : UFTermsDescend e := by
  rcases Egglog.FDatabase.mergeOneWith_eq_oriented (cl := cl) (d := d) r₁ r₂ with he | he
  · exact mergeOneOriented_ufTermsDescend hshape hr hsc hidx hcl hne.symm h (he ▸ run)
  · exact mergeOneOriented_ufTermsDescend hshape hr hsc hidx hcl hne h (he ▸ run)

/-- A merge round preserves descent, including the runtime's inert rebuilding step. -/
theorem mergeRound_ufTermsDescend {d : FDatabase} (hshape : MergeShape d.sig)
    (hinv : d.Inv) (hn : d.NoUnions) (h : UFTermsDescend d) : UFTermsDescend d.mergeRound := by
  have hdiag : ∀ p ∈ d.closureF, p.1 = p.2 := fun _ hp => diag_closureF hn.eqsRefl hp
  have hreb : UFTermsDescend (FDatabase.rebuild d.closureF d) := h
  have key : d.mergeRound.Inv ∧ d.mergeRound.sig = d.sig ∧ d.mergeRound.NoUnions ∧
      UFTermsDescend d.mergeRound := by
    refine Egglog.FDatabase.mergeRound_induction_ne
      (P := fun x => x.Inv ∧ x.sig = d.sig ∧ x.NoUnions ∧ UFTermsDescend x)
      ⟨hinv, rfl, hn, h⟩
      ⟨Egglog.FDatabase.Inv.rebuild hinv Egglog.FDatabase.closureSound_closureF,
        rfl, rebuild_noUnions hn, hreb⟩ ?_
    intro x y r₁ r₂ hne hx hy
    refine ⟨Egglog.FDatabase.mergeOneWith_inv hx.1
        (by rw [hx.2.1]; exact hshape.mergesLegal) hy,
      ((Egglog.FDatabase.mergeOneWith_confined hy).2.2.1).trans hx.2.1,
      mergeOneWith_noUnions hx.2.2.1 hy, ?_⟩
    exact mergeOneWith_ufTermsDescend (by rw [hx.2.1]; exact hshape) hx.2.2.1.eqsRefl
      (Egglog.FDatabase.SubtermClosed.of_wf hx.1.wf) hx.1.index hdiag hne hx.2.2.2 hy
  exact key.2.2.2

/-- A successful merge phase preserves historical UF descent. -/
theorem mergeSaturateF_ufTermsDescend : ∀ (n : Nat) {d e : FDatabase},
    MergeShape d.sig → d.Inv → d.NoUnions → UFTermsDescend d →
      Egglog.FDatabase.mergeSaturateF n d = some e → UFTermsDescend e
  | 0, d, e, _, _, _, h, run => by
      rw [Egglog.FDatabase.mergeSaturateF] at run
      split at run
      · obtain rfl := Option.some.inj run; exact h
      · exact absurd run (by simp)
  | n + 1, d, e, hshape, hinv, hn, h, run => by
      rw [Egglog.FDatabase.mergeSaturateF] at run
      split at run
      · obtain rfl := Option.some.inj run; exact h
      · have hsig : d.mergeRound.sig = d.sig := Egglog.FDatabase.mergeRound_confined.2.2.1
        exact mergeSaturateF_ufTermsDescend n (by rw [hsig]; exact hshape)
          (Egglog.FDatabase.Inv.mergeRound_of_legalMerges hinv hshape.mergesLegal)
          (mergeRound_noUnions hn) (mergeRound_ufTermsDescend hshape hinv hn h) run

end Egglog.Congruence
