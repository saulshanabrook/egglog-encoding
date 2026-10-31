import EgglogSemantics.Spec.Step
import EgglogSemantics.Source.Names

/-! The mathematical observation of the congruence target. A source application is read
by joining its children's ids with the applications the target holds, through the live
union-find edges of their children; the id is the parent the application's own live edge
names. This definition uses only mathematical databases and does not depend on an
executable interpreter. -/

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

/-- The id of a term: its one reading. Rebuilding compresses every edge to a root and
merges the roots of applications with the same child parents, so at a rebuild fixpoint
every held term has an id and the reading needs no UF walk. -/
def Id (d : Database) (t e : Term) : Prop :=
  Repr d t e ∧ ∀ e', Repr d t e' → e' = e

/-- Two terms with the same id. -/
def SameClass (d : Database) (a b : Term) : Prop :=
  ∃ e, Id d a e ∧ Id d b e

theorem SameClass.symm {d : Database} {a b : Term} (h : SameClass d a b) :
    SameClass d b a := ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩

end Egglog.Congruence
