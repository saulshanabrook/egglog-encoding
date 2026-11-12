import EgglogSemantics.Spec.Step
import EgglogSemantics.Source.Names

/-! The mathematical observation of the congruence target. A source application is read
by joining its children's ids with the applications the target holds, through the live
union-find edges of their children; the id is the parent the application's own live edge
names. This definition uses only mathematical databases and does not depend on an
executable interpreter. Held applications remain readable here when subsumed: `Repr`
describes equality, while compiled query atoms enforce liveness. -/

namespace Egglog.Congruence

/-- A live union-find edge from `a` to `b`: the target holds the row and has not subsumed
it, up to congruent spelling. -/
def Edge (d : Database) (a b : Term) : Prop := Term.app ufName [a, b] ∈ d.live

mutual

/-- Read one id per source subterm. A literal is its own id. An application's id is the
parent of a held application of the same constructor whose children's parents are the
children's ids. -/
inductive Repr (d : Database) : Term → Term → Prop where
  | lit {l : Lit} : Repr d (.lit l) (.lit l)
  | app {f : FnName} {as bs rs : List Term} {e : Term} :
      ReprList d as rs → Term.app f bs ∈ d.terms → List.Forall₂ (Edge d) bs rs →
      Edge d (.app f bs) e → Repr d (.app f as) e

/-- Pointwise reading. -/
inductive ReprList (d : Database) : List Term → List Term → Prop where
  | nil : ReprList d [] []
  | cons {a e : Term} {as es : List Term} :
      Repr d a e → ReprList d as es → ReprList d (a :: as) (e :: es)

end

end Egglog.Congruence
