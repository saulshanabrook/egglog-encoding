import EgglogSemantics.Congruence.Read
import EgglogSemantics.Impl.Interp

/-!
# Reading the congruence target, computed

A source term is read by joining the applications the target holds with the live
union-find edges of their children, recursively on its own children. Two terms are
equivalent when each reads to exactly one id and the ids agree. The link to `Repr` belongs
with the compiler proofs.
-/

namespace Egglog.Congruence

/-- The parents the live union-find edges give a key. -/
def parentsF (d : FDatabase) (k : Term) : List Term :=
  d.terms.filterMap fun t => match t with
    | .app g [k', p] => if g == ufName && k' == k && !d.subsumed.contains t then some p else none
    | _ => none

/-- Pointwise: each child has a live edge to one of the ids its column was given. `false`
at unequal lengths, which is what makes an application of the wrong width no match. -/
def edgesInto (d : FDatabase) : List (List Term) → List Term → Bool
  | [], [] => true
  | r :: rs, b :: bs => (parentsF d b).any (fun p => decide (p ∈ r)) && edgesInto d rs bs
  | _, _ => false

mutual

/-- The ids the target gives a source term. A literal is its own id and nothing else's. -/
def reprsF (d : FDatabase) : Term → List Term
  | .lit l => [Term.lit l]
  | .app f as =>
      let rs := reprsListF d as
      d.terms.flatMap fun t => match t with
        | .app g bs => if g == f && edgesInto d rs bs then parentsF d t else []
        | .lit _ => []

/-- `reprsF` over an argument list, one id list per column. -/
def reprsListF (d : FDatabase) : List Term → List (List Term)
  | [] => []
  | t :: ts => reprsF d t :: reprsListF d ts

end

/-- The id of a source term, when the target gives it exactly one. At a rebuild fixpoint
every key has one live edge and the congruence rule has merged the roots of all
applications with the same child parents, so every held term has an id; several readings
mean a rebuild the target did not finish. -/
def idF (d : FDatabase) (t : Term) : Option Term :=
  match (reprsF d t).dedup with
  | [e] => some e
  | _ => none

/-- `SameClass`, computed: both terms have an id, and it is the same one. -/
def sameClassF (d : FDatabase) (a b : Term) : Bool :=
  match idF d a, idF d b with
  | some x, some y => x == y
  | _, _ => false

end Egglog.Congruence
