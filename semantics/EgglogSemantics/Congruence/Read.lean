import EgglogSemantics.Spec.Step
import EgglogSemantics.Source.Names

/-! The mathematical observation of the congruence target. Source applications are
read by joining their children's ids with view rows, which are constructor applications
the target holds. This definition uses only mathematical databases and does not depend on
an executable interpreter. -/

namespace Egglog.Congruence

/-- A held view row of `f` with child ids `es` and id `e`, up to congruent spelling. -/
def ViewRow (d : Database) (f : FnName) (es : List Term) (e : Term) : Prop :=
  Cong d (.app (viewName f) (es ++ [e])) (.app (viewName f) (es ++ [e]))

mutual

/-- Read one id per source subterm from the view tables. -/
inductive ViewRepr (d : Database) : Term → Term → Prop where
  | lit {l : Lit} : ViewRepr d (.lit l) (.lit l)
  | app {f : FnName} {as es : List Term} {e : Term} :
      ViewReprList d as es → ViewRow d f es e → ViewRepr d (.app f as) e

/-- Pointwise view representation. -/
inductive ViewReprList (d : Database) : List Term → List Term → Prop where
  | nil : ViewReprList d [] []
  | cons {a e : Term} {as es : List Term} :
      ViewRepr d a e → ViewReprList d as es → ViewReprList d (a :: as) (e :: es)

end

/-- Rebuilding propagates parent edges into views, so the reading needs no UF walk. -/
def SameClass (d : Database) (a b : Term) : Prop :=
  ∃ e, ViewRepr d a e ∧ ViewRepr d b e

theorem SameClass.symm {d : Database} {a b : Term} (h : SameClass d a b) :
    SameClass d b a := ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩

end Egglog.Congruence
