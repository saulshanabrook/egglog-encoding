import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Syntax

/-!
# Ground terms

The Redex `Term`:

```
Term = number | (constructor Term ...)
```

A term is its own identity — there are no e-class ids on this side of the
encoding, and the e-graph is a set of terms plus a congruence relation over them.

`Term` nests `List Term`, so the recursor Lean derives carries a second motive
over `List Term`. `Term.recTerm` repackages it as ordinary structural induction
with the hypothesis available for every argument.
-/

namespace Egglog
/-- A ground term. -/
inductive Term where
  | lit : Lit → Term
  | app : FnName → List Term → Term

namespace Term
mutual

/-- Decidable equality, written by hand because no `deriving` handler sees through the
`List Term` nesting. The relational semantics needs none of this; a `Finset`-based
executable interpreter does (`PLAN.md`, M10). -/
def decEq : (s t : Term) → Decidable (s = t)
  | .lit l₁, .lit l₂ =>
    if h : l₁ = l₂ then .isTrue (by rw [h]) else .isFalse (by simp [h])
  | .lit _, .app _ _ => .isFalse (by simp)
  | .app _ _, .lit _ => .isFalse (by simp)
  | .app f₁ as₁, .app f₂ as₂ =>
    if hf : f₁ = f₂ then
      match decEqList as₁ as₂ with
      | .isTrue ha => .isTrue (by rw [hf, ha])
      | .isFalse ha => .isFalse (by simp [ha])
    else .isFalse (by simp [hf])

/-- `decEq` over argument lists. -/
def decEqList : (as bs : List Term) → Decidable (as = bs)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by simp)
  | _ :: _, [] => .isFalse (by simp)
  | a :: as, b :: bs =>
    match decEq a b with
    | .isTrue hab =>
      match decEqList as bs with
      | .isTrue h => .isTrue (by rw [hab, h])
      | .isFalse h => .isFalse (by simp [h])
    | .isFalse hab => .isFalse (by simp [hab])

end

instance : DecidableEq Term := decEq

/-- `IsSubterm s t` holds when `s` occurs in `t`, including `s = t`. This is the
"presence of children" axiom of the Redex `Congruence-Reduction`, which there adds
every child of a present term to the term set. -/
inductive IsSubterm : Term → Term → Prop where
  | refl (t : Term) : IsSubterm t t
  | arg {s a : Term} {f : FnName} {args : List Term} :
      a ∈ args → IsSubterm s a → IsSubterm s (.app f args)

/-- The subterms of `t`, as a set. -/
def subterms (t : Term) : Set Term := {s | IsSubterm s t}

mutual

/-- `subterms` as a list, for the executable interpreter. `mem_subtermList` is the
bridge to the relation. -/
def subtermList : Term → List Term
  | .lit l => [.lit l]
  | .app f args => .app f args :: subtermListL args

/-- `subtermList` over an argument list. -/
def subtermListL : List Term → List Term
  | [] => []
  | t :: ts => subtermList t ++ subtermListL ts

end

/-- `subterms` as a `Finset`. -/
def subtermsF (t : Term) : Finset Term := t.subtermList.toFinset

end Term
/-! ### Rows

A database maps each function's key tuple to its value columns. For a constructor there
is one value column and it holds the application itself, which is what makes congruence
and the functional dependency one rule (`Cong.fd`). -/
/-- One tuple of one function's table: `fn args… ↦ out…`.

`out` is a *list*, one entry per value column. egglog's tables are multi-column and the
encoding depends on it — `@UF_<Sort>` carries a parent *and* a proof. -/
@[ext]
structure Row where
  fn : FnName
  args : List Term
  out : List Term
  deriving DecidableEq

namespace Term
/-- The constructor rows of `t`: one per application among its subterms, each mapping
its own children to itself.

Only a *constructor* application ever occurs inside a `Term` — a `:merge` function's
application evaluates to its recorded output — so this needs no signature. -/
def ctorRows (t : Term) : Set Row :=
  {r | r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ t.subterms}

/-- `ctorRows` as a list, for the executable interpreter. -/
def ctorRowList (t : Term) : List Row :=
  t.subtermList.filterMap fun s =>
    match s with
    | .app f as => some ⟨f, as, [.app f as]⟩
    | .lit _ => none

end Term
end Egglog
