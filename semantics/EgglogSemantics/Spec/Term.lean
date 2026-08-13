import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Syntax

/-!
# Ground terms

What an expression evaluates to, and what the database holds:

```
Term = number | (constructor Term ...)
```

A term is its own identity: there are no e-class ids, and the e-graph is a set of terms
plus a congruence relation over them.
-/

namespace Egglog
/-- A ground term. -/
inductive Term where
  | lit : Lit → Term
  | app : FnName → List Term → Term

namespace Term
mutual

/-- Decidable equality. -/
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

/-- `t` is a base value. egglog's `union` requires an eq-sort and so rejects one;
`evalAction` reads this to refuse the same. -/
def isLit : Term → Bool
  | .lit _ => true
  | .app _ _ => false

/-- `s` occurs in `t`, including `s = t`. -/
inductive IsSubterm : Term → Term → Prop where
  | refl (t : Term) : IsSubterm t t
  | arg {s a : Term} {f : FnName} {args : List Term} :
      a ∈ args → IsSubterm s a → IsSubterm s (.app f args)

/-- The subterms of `t`, as a set. -/
def subterms (t : Term) : Set Term := {s | IsSubterm s t}

mutual

/-- `subterms` as a list, in **reverse creation order**: `t`, then its arguments right to
left, each preceded by its own subterms. The order is load-bearing. -/
def subtermList : Term → List Term
  | .lit l => [.lit l]
  | .app f args => .app f args :: subtermListL args

/-- `subtermList` over an argument list, **later arguments first**: a later argument is the
newer term. -/
def subtermListL : List Term → List Term
  | [] => []
  | t :: ts => subtermListL ts ++ subtermList t

end

end Term
/-! ### The term order

`ordering-min`/`ordering-max` are primitives a `:merge` body calls, and `Term.blt` is the
order they read. -/
mutual

/-- A total order on terms: literals below applications, then by argument count, then by
name, then lexicographically. -/
def Term.blt : Term → Term → Bool
  | .lit (.int m), .lit (.int n) => decide (m < n)
  | .lit _, .app _ _ => true
  | .app _ _, .lit _ => false
  | .app f as, .app g bs =>
      if as.length ≠ bs.length then decide (as.length < bs.length)
      else if f ≠ g then decide (f < g)
      else Term.bltList as bs

/-- `Term.blt` lexicographically over argument lists. -/
def Term.bltList : List Term → List Term → Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then Term.bltList as bs else Term.blt a b

end

/-- egglog's `ordering-min`. -/
def Term.orderingMin (s t : Term) : Term := if Term.blt s t then s else t

/-- egglog's `ordering-max`. -/
def Term.orderingMax (s t : Term) : Term := if Term.blt s t then t else s

/-! ### Primitives -/
/-- The primitives this fragment has. A primitive is applied as `Expr.app` of a reserved
name, not by a constructor of its own. -/
inductive Prim where
  | orderingMin
  | orderingMax
  /-- egglog's `i64` `min`. -/
  | intMin
  /-- egglog's `i64` `max`. -/
  | intMax
  deriving DecidableEq, Repr

/-- The reserved names; a user function of the same name is shadowed. -/
def Prim.ofName : FnName → Option Prim
  | "ordering-min" => some .orderingMin
  | "ordering-max" => some .orderingMax
  | "min" => some .intMin
  | "max" => some .intMax
  | _ => none

/-- A primitive's meaning. `none` for the wrong arity, and for `min`/`max` also for a
non-literal operand. -/
def Prim.apply : Prim → List Term → Option Term
  | .orderingMin, [s, t] => some (Term.orderingMin s t)
  | .orderingMax, [s, t] => some (Term.orderingMax s t)
  | .intMin, [.lit (.int m), .lit (.int n)] => some (.lit (.int (min m n)))
  | .intMax, [.lit (.int m), .lit (.int n)] => some (.lit (.int (max m n)))
  | _, _ => none

end Egglog
