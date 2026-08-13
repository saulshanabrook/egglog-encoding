import EgglogSemantics.Spec.Term
import EgglogSemantics.Proofs.Syntax

namespace Egglog
namespace Term
/-- Structural induction over `Term`, with the induction hypothesis given for
every element of an application's argument list. -/
@[elab_as_elim]
theorem recTerm {motive : Term → Prop} (lit : ∀ l, motive (.lit l))
    (app : ∀ f args, (∀ a ∈ args, motive a) → motive (.app f args)) (t : Term) :
    motive t :=
  Term.rec (motive_1 := motive) (motive_2 := fun args => ∀ a ∈ args, motive a) lit
    (fun f args ih => app f args ih) (fun a ha => by simp at ha)
    (fun _ _ iht ihts a ha => (List.mem_cons.mp ha).elim (fun h => h ▸ iht) (ihts a)) t

@[simp] theorem mem_subterms {s t : Term} : s ∈ t.subterms ↔ IsSubterm s t := Iff.rfl

@[simp]
theorem self_mem_subterms (t : Term) : t ∈ t.subterms := IsSubterm.refl t

theorem arg_subterms {f : FnName} {args : List Term} {a : Term} (h : a ∈ args) :
    a.subterms ⊆ (Term.app f args).subterms :=
  fun _ hs => IsSubterm.arg h hs

@[simp]
theorem subterms_lit {l : Lit} : (Term.lit l).subterms = {Term.lit l} := by
  ext s
  constructor
  · intro h; cases h; rfl
  · intro h; exact h ▸ IsSubterm.refl _

@[simp]
theorem subterms_app {f : FnName} {args : List Term} :
    (Term.app f args).subterms = insert (Term.app f args) (⋃ a ∈ args, a.subterms) := by
  ext s
  constructor
  · intro h
    cases h with
    | refl => exact Set.mem_insert _ _
    | arg hmem hsub => exact Set.mem_insert_of_mem _ (Set.mem_biUnion hmem hsub)
  · intro h
    rcases Set.mem_insert_iff.mp h with rfl | h
    · exact IsSubterm.refl _
    · obtain ⟨a, ha, hs⟩ := Set.mem_iUnion₂.mp h
      exact IsSubterm.arg ha hs

@[simp] theorem subtermList_lit {l : Lit} : subtermList (.lit l) = [.lit l] := rfl

@[simp] theorem subtermList_app {f : FnName} {args : List Term} :
    subtermList (.app f args) = .app f args :: subtermListL args := rfl

@[simp] theorem subtermListL_nil : subtermListL [] = [] := rfl

@[simp] theorem subtermListL_cons {t : Term} {ts : List Term} :
    subtermListL (t :: ts) = subtermListL ts ++ subtermList t := rfl

mutual

theorem mem_subtermList {s : Term} (t : Term) : s ∈ subtermList t ↔ IsSubterm s t := by
  match t with
  | .lit l =>
    simp only [subtermList_lit, List.mem_singleton]
    exact ⟨fun h => h ▸ .refl _, fun h => by cases h; rfl⟩
  | .app f args =>
    simp only [subtermList_app, List.mem_cons, mem_subtermListL args]
    constructor
    · rintro (rfl | ⟨a, ha, hs⟩)
      · exact .refl _
      · exact .arg ha hs
    · intro h
      cases h with
      | refl => exact Or.inl rfl
      | arg ha hs => exact Or.inr ⟨_, ha, hs⟩

theorem mem_subtermListL {s : Term} (ts : List Term) :
    s ∈ subtermListL ts ↔ ∃ a ∈ ts, IsSubterm s a := by
  match ts with
  | [] => simp
  | t :: ts =>
    simp only [subtermListL_cons, List.mem_append, mem_subtermList t, mem_subtermListL ts,
      List.mem_cons]
    constructor
    · rintro (⟨a, ha, hs⟩ | h)
      · exact ⟨a, Or.inr ha, hs⟩
      · exact ⟨t, Or.inl rfl, h⟩
    · rintro ⟨a, rfl | ha, hs⟩
      · exact Or.inr hs
      · exact Or.inl ⟨a, ha, hs⟩

end

theorem IsSubterm.trans {s t u : Term} (hst : IsSubterm s t) (htu : IsSubterm t u) :
    IsSubterm s u := by
  induction htu with
  | refl => exact hst
  | arg hmem _ ih => exact IsSubterm.arg hmem ih

/-- Subterm sets are transitively closed. -/
theorem subterms_subset_of_mem {s t : Term} (h : s ∈ t.subterms) :
    s.subterms ⊆ t.subterms :=
  fun _ hu => hu.trans h

end Term
end Egglog
