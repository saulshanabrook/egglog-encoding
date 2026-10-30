import EgglogSemantics.Proofs.Order
import EgglogSemantics.Spec.Order
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Card

/-!
# Term ordering over a finite vocabulary

The size-first order has finite initial segments when constructor names and literal
values come from fixed finite sets. Consequently, its restriction to such terms is
well founded. No well-foundedness claim is made for arbitrary integers or names.
-/

namespace Egglog.Term

theorem UsesVocabulary.subterm {names : Set FnName} {literals : Set Lit}
    {s t : Term} (ht : UsesVocabulary names literals t) (hs : IsSubterm s t) :
    UsesVocabulary names literals s := by
  induction hs with
  | refl => exact ht
  | arg ha _ ih =>
    cases ht with
    | app _ hargs => exact ih (hargs _ ha)

theorem length_le_nodeSizeList (args : List Term) : args.length ≤ nodeSizeList args := by
  induction args with
  | nil => simp
  | cons a args ih =>
    have := nodeSize_pos a
    simp only [List.length_cons, nodeSizeList_cons]
    omega

private theorem finite_bounded_lists {α : Type*} {s : Set α} (hs : s.Finite) (n : Nat) :
    {as : List α | (∀ a ∈ as, a ∈ s) ∧ as.length ≤ n}.Finite := by
  classical
  letI : Fintype s := hs.fintype
  apply ((List.finite_length_le s n).image (List.map Subtype.val)).subset
  intro as h
  refine ⟨as.attachWith (· ∈ s) h.1, ?_, List.attachWith_map_subtype_val h.1⟩
  simpa using h.2

/-- A finite vocabulary admits only finitely many terms of bounded node count. -/
theorem finite_nodeSize_le {names : Set FnName} {literals : Set Lit}
    (hn : names.Finite) (hl : literals.Finite) (n : Nat) :
    {t : Term | UsesVocabulary names literals t ∧ t.nodeSize ≤ n}.Finite := by
  induction n with
  | zero =>
    apply Set.finite_empty.subset
    intro t ht
    have := nodeSize_pos t
    have hbound : t.nodeSize ≤ 0 := ht.2
    exact False.elim (by omega)
  | succ n ih =>
    have hargs := finite_bounded_lists ih n
    apply ((hl.image Term.lit).union
      ((hn.prod hargs).image fun p => Term.app p.1 p.2)).subset
    intro t ht
    cases ht.1 with
    | lit h => exact Or.inl ⟨_, h, rfl⟩
    | @app f args hf hall =>
      refine Or.inr ⟨(f, args), ⟨hf, ?_⟩, rfl⟩
      change (∀ a ∈ args, UsesVocabulary names literals a ∧ a.nodeSize ≤ n) ∧
        args.length ≤ n
      have hbound : (Term.app f args).nodeSize ≤ n + 1 := ht.2
      constructor
      · intro a ha
        refine ⟨hall a ha, ?_⟩
        have := nodeSize_lt_app (f := f) ha
        omega
      · have := length_le_nodeSizeList args
        have hsize := ht.2
        simp only [nodeSize_app] at hsize
        omega

/-- Even if the upper bound uses other symbols, its predecessors drawn from a fixed
finite vocabulary form a finite set. -/
theorem finite_predecessors {names : Set FnName} {literals : Set Lit}
    (hn : names.Finite) (hl : literals.Finite) (t : Term) :
    {s : Term | UsesVocabulary names literals s ∧ blt s t = true}.Finite :=
  (finite_nodeSize_le hn hl t.nodeSize).subset
    fun _ hs => ⟨hs.1, nodeSize_le_of_blt hs.2⟩

/-- Both the strict and inclusive initial segments are finite. -/
theorem finite_initialSegment {names : Set FnName} {literals : Set Lit}
    (hn : names.Finite) (hl : literals.Finite) (t : Term) :
    {s : Term | UsesVocabulary names literals s ∧ (s = t ∨ blt s t = true)}.Finite := by
  apply (finite_nodeSize_le hn hl t.nodeSize).subset
  rintro s ⟨hs, rfl | hlt⟩
  · exact ⟨hs, Nat.le_refl _⟩
  · exact ⟨hs, nodeSize_le_of_blt hlt⟩

/-- Counting predecessors supplies a natural-number rank for strict descent. -/
theorem predecessor_count_lt {names : Set FnName} {literals : Set Lit}
    (hn : names.Finite) (hl : literals.Finite) {s t : Term}
    (hs : UsesVocabulary names literals s) (hst : blt s t = true) :
    {a : Term | UsesVocabulary names literals a ∧ blt a s = true}.ncard <
      {a : Term | UsesVocabulary names literals a ∧ blt a t = true}.ncard := by
  apply Set.ncard_lt_ncard ?_ (finite_predecessors hn hl t)
  refine ⟨?_, ?_⟩
  · intro a ha
    exact ⟨ha.1, blt_trans a s t ha.2 hst⟩
  · intro h
    have := (h ⟨hs, hst⟩).2
    simp at this

/-- Size-first comparison is well founded on terms over a fixed finite vocabulary. -/
theorem blt_wellFounded_on_vocabulary {names : Set FnName} {literals : Set Lit}
    (hn : names.Finite) (hl : literals.Finite) :
    WellFounded (fun s t : {a : Term // UsesVocabulary names literals a} =>
      blt s.val t.val = true) := by
  let rank (t : {a : Term // UsesVocabulary names literals a}) : Nat :=
    {a : Term | UsesVocabulary names literals a ∧ blt a t.val = true}.ncard
  apply (measure rank).wf.mono
  intro s t hst
  exact predecessor_count_lt hn hl s.property hst

/-- The implementation's size-first order satisfies the paper's order requirements. -/
@[blueprint "thm:order"
  (title := /-- Concrete order -/)
  (statement := /-- The model's size-first term order satisfies the preceding
  requirements. Structural comparison breaks ties of equal node count. -/)
  (hasProof := false) (latexEnv := "theorem")]
theorem blt_admissible : AdmissibleOrder (fun s t => blt s t = true) where
  irrefl := by intro t; simp
  trans := blt_trans
  total := blt_total
  subterm := fun _ _ hs hn => hs.blt hn
  literals := by intro m n; simp [blt_lit_lit, Lit.blt]
  finiteLower := fun _ _ hn hl t => finite_predecessors hn hl t

end Egglog.Term
