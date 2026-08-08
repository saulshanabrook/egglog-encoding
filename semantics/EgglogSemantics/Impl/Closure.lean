import Mathlib.Data.Finset.Prod
import EgglogSemantics.Spec.Congruence

/-!
# A decidable congruence closure

`Cong` is a predicate, so nothing in the semantics computes it. This computes it for a
finite, subterm-closed term set, which is what an executable interpreter needs
(`PLAN.md`, M10) and what lets a ported test case be discharged by `decide` rather than
by a hand-built derivation.

Deliberately the *obvious* algorithm rather than the efficient one: iterate a
one-step-derivable relation to a fixpoint over the finite candidate universe
`terms ×ˢ terms`. Union-find with upward merging is what egglog does and what the
proof-encoding theorems are eventually *about*; using it here would put the thing
under study inside the thing doing the studying.

Termination is by well-founded recursion on how much of the candidate universe is
still missing. Stopping only at a fixpoint is what makes `Cong.le` applicable in
`mem_closure_iff`'s completeness direction.
-/

namespace Egglog
/-- The pairs a congruence over `terms` can mention. -/
def candidates (terms : Finset Term) : Finset (Term × Term) := terms ×ˢ terms

/-- `Cong.congr`'s premise, as a computation. The two membership conditions are left
to `candidates`. -/
def congrPair (rel : Finset (Term × Term)) : Term → Term → Bool
  | .app f as, .app g bs =>
      f == g && as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ rel)
  | _, _ => false

/-- Whether `p` follows from `rel` by a single `Cong` rule. Reflexivity's side
condition is `p ∈ candidates terms`, which is where this is used. -/
def stepAdds (terms : Finset Term) (rel : Finset (Term × Term)) (p : Term × Term) : Bool :=
  decide (p.1 = p.2) || decide ((p.2, p.1) ∈ rel)
    || decide (∃ m ∈ terms, (p.1, m) ∈ rel ∧ (m, p.2) ∈ rel)
    || congrPair rel p.1 p.2

/-- One round of closure. -/
def congStep (terms : Finset Term) (rel : Finset (Term × Term)) : Finset (Term × Term) :=
  rel ∪ (candidates terms).filter fun p => stepAdds terms rel p

/-- Iterate `congStep` to a fixpoint. -/
def closure (terms : Finset Term) (rel : Finset (Term × Term))
    (h : rel ⊆ candidates terms) : Finset (Term × Term) :=
  if _hfix : congStep terms rel = rel then rel
  else closure terms (congStep terms rel) (Finset.union_subset h (Finset.filter_subset _ _))
  termination_by (candidates terms).card - rel.card
  decreasing_by
    have hss : rel ⊂ congStep terms rel :=
      ssubset_of_subset_of_ne Finset.subset_union_left (Ne.symm _hfix)
    have h1 : rel.card < (congStep terms rel).card := Finset.card_lt_card hss
    have h2 : (congStep terms rel).card ≤ (candidates terms).card :=
      Finset.card_le_card (Finset.union_subset h (Finset.filter_subset _ _))
    omega

/-- `closure` with the candidate restriction imposed rather than assumed, so that it
needs no proof argument. On a well-formed input the restriction removes nothing. -/
def closureTotal (terms : Finset Term) (rel : Finset (Term × Term)) : Finset (Term × Term) :=
  closure terms ((candidates terms).filter (· ∈ rel)) (Finset.filter_subset _ _)

end Egglog
