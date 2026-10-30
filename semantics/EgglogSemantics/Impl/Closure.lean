import Mathlib.Data.Finset.Prod
import EgglogSemantics.Spec.Congruence

/-!
# A decidable congruence closure

`Cong` is a predicate, so nothing in the semantics computes it. This computes it for a
finite, subterm-closed term set, which is what an executable interpreter needs
and what lets a ported test case be discharged by `decide` rather than
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

/-! ### Reading transitivity off the relation

`stepAdds` looks for `Cong.trans`'s middle term by scanning the candidate universe:
`∃ m ∈ terms, (p.1, m) ∈ rel ∧ (m, p.2) ∈ rel` walks all of `terms` and tests two
memberships at each, and `congStep` asks it once per pair of `terms ×ˢ terms`. A `Finset`
is a list quotient, so a membership test is a linear scan and a pass costs
`|terms|³ · |rel|` — the run's whole cost on an encoded program, where every rebuild
firing mints another proof term and `terms` grows every round while the classes stay tiny.

`rel` already holds the middle terms: the pairs `(p.1, m)` are its entries with `p.1` in
the left column, so one scan of it offers exactly the `m` worth testing, and a class is
one or two terms wide. A pass drops to `|terms|² · |rel|`, which at 127 terms is 15.4 s of
closure against 0.5 s.

`stepAddsFast` is that reading and `congStepFast` is `congStep` over it. Neither
`stepAdds` nor `congStep` moves, so every theorem in `Proofs/Closure.lean` keeps its
statement and its proof, and the `csimp` below is what points compiled code at the pair. -/
/-- Whether the entry `q` of `rel` witnesses `Cong.trans` for `p`: it starts where `p`
does, its right column is a term the closure may mention, and `rel` carries that column on
to where `p` ends.

A `Bool` rather than a conjunction of `Prop`s because `&&` short-circuits, where
`Decidable`'s `And` instance takes both decisions as arguments and so tests every column
of every entry. -/
def transWitness (terms : Finset Term) (rel : Finset (Term × Term)) (p q : Term × Term) :
    Bool :=
  (q.1 == p.1) && decide (q.2 ∈ terms) && decide ((q.2, p.2) ∈ rel)

/-- `stepAdds` with the middle term read off `rel` instead of searched for in `terms`. -/
def stepAddsFast (terms : Finset Term) (rel : Finset (Term × Term)) (p : Term × Term) :
    Bool :=
  decide (p.1 = p.2) || decide ((p.2, p.1) ∈ rel)
    || decide (∃ q ∈ rel, transWitness terms rel p q = true)
    || congrPair rel p.1 p.2

/-- **The two agree on the nose.** The middle terms `rel` offers are the middle terms
`terms` holds: an accepted `m` gives the entry `(p.1, m)`, an accepted entry the term
`q.2`. -/
theorem stepAddsFast_eq (terms : Finset Term) (rel : Finset (Term × Term))
    (p : Term × Term) : stepAddsFast terms rel p = stepAdds terms rel p := by
  have hmid : decide (∃ q ∈ rel, transWitness terms rel p q = true)
      = decide (∃ m ∈ terms, (p.1, m) ∈ rel ∧ (m, p.2) ∈ rel) := by
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨q, hq, hw⟩ := h
      simp only [transWitness, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
      obtain ⟨⟨h1, h2⟩, h3⟩ := hw
      refine ⟨q.2, h2, ?_, h3⟩
      rw [show (p.1, q.2) = q from Prod.ext h1.symm rfl]
      exact hq
    · obtain ⟨m, hm, h1, h2⟩ := h
      refine ⟨(p.1, m), h1, ?_⟩
      simp only [transWitness, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨trivial, hm⟩, h2⟩
  simp only [stepAddsFast, stepAdds, hmid]

/-- One round of closure, over `stepAddsFast`. -/
def congStepFast (terms : Finset Term) (rel : Finset (Term × Term)) :
    Finset (Term × Term) :=
  rel ∪ (candidates terms).filter fun p => stepAddsFast terms rel p

theorem congStepFast_eq (terms : Finset Term) (rel : Finset (Term × Term)) :
    congStepFast terms rel = congStep terms rel := by
  ext p
  simp only [congStepFast, congStep, Finset.mem_union, Finset.mem_filter, stepAddsFast_eq]

/-- **What points compiled code at the fast pass.** It sits here because `csimp` rewrites
the declarations compiled *after* it, and `closure` — the only caller — is just below. -/
@[csimp] theorem congStep_eq_fast : @congStep = @congStepFast := by
  funext terms rel
  exact (congStepFast_eq terms rel).symm

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
