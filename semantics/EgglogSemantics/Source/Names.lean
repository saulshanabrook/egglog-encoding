import EgglogSemantics.Spec.Syntax
import EgglogSemantics.Spec.Term

/-! Names shared by the encoding passes. -/

namespace Egglog

/-! ### Names -/
/-- The union-find table. The modelled language has one eq-sort, so where egglog emits
`@UF_<Sort>` per sort there is one table here. -/
def ufName : FnName := "@UF"

/-- The canonical node view of source constructor `f`, an optimization of the congruence
pass: its key is the tuple of child leaders and its last column the leader of the node. -/
def viewName (f : FnName) : FnName := "@" ++ f ++ "View"

/-- The index of the canonical node views: a row per view row and column, relating the view
row, as a term, to each value it mentions. -/
def hasChildName : FnName := "@HasChild"

/-- The `n`th generated variable. -/
def freshVar (n : Nat) : Var := "@v" ++ toString n

/-- **A generated variable is in the generated namespace.** -/
theorem atPrefix_freshVar (n : Nat) : "@".isPrefixOf (freshVar n) = true := by
  rw [freshVar, String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@v").toList = ['@', 'v'] from by decide]
  exact ⟨'v' :: (toString n).toList, rfl⟩

end Egglog
