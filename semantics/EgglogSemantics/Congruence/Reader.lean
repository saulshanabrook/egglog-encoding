import EgglogSemantics.Congruence.Read
import EgglogSemantics.Impl.Interp

/-!
# Reading the congruence target, computed

A source term is represented by recursively joining view rows on its children's ids. Two
terms are equivalent when they have a common resulting id. The link to `ViewRepr` belongs
with the compiler proofs.
-/

namespace Egglog.Congruence

/-- Pointwise membership: `ks` picks, per column, one of the ids that column's child was
given. `false` at unequal lengths, which is what makes a view row of the wrong width no
row at all. -/
def memAll : List (List Term) → List Term → Bool
  | [], [] => true
  | r :: rs, k :: ks => decide (k ∈ r) && memAll rs ks
  | _, _ => false

/-- The id a view row gives the source application `f a…`, or `none` where the term is
not one: the head has to be `f`'s view, the width the key plus the single id column, and
the key columns ids of the children, which `rs` carries. -/
def viewIdOf (rs : List (List Term)) (f : FnName) (n : Nat) : Term → Option Term
  | .app g cs =>
      if g = viewName f ∧ cs.length = n + 1 ∧ memAll rs (cs.take n) = true then
        (cs.drop n).head?
      else none
  | .lit _ => none

mutual

/-- The ids the target gives a source term. A literal is its own id and nothing else's:
`encodeBuild` emits no view for a literal, so a literal never keys a view row. -/
def viewReprsF (d : FDatabase) : Term → List Term
  | .lit l => [Term.lit l]
  | .app f as => d.terms.filterMap (viewIdOf (viewReprsListF d as) f as.length)

/-- `viewReprsF` over an argument list, one id list per column. -/
def viewReprsListF (d : FDatabase) : List Term → List (List Term)
  | [] => []
  | t :: ts => viewReprsF d t :: viewReprsListF d ts

end

/-- `SameClass`, computed: one id the target gives both terms. -/
def sameClassF (d : FDatabase) (a b : Term) : Bool :=
  (viewReprsF d a).any fun e => decide (e ∈ viewReprsF d b)

end Egglog.Congruence
