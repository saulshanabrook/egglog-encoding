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

/-- The node relation of source constructor `f`: `@Node_f(a₁, …, aₙ, f(a₁, …, aₙ))` records a
held application and its children. Unlike the application's own row it is never subsumed,
so the congruence rule still reads a subsumed node. -/
def nodeName (f : FnName) : FnName := "@Node" ++ f

/-- The subsumption marker of source constructor `f`: `@Sub_f(a₁, …, aₙ)` records that the
source subsumed the spelling `f(a₁, …, aₙ)`. -/
def subName (f : FnName) : FnName := "@Sub" ++ f

/-- The `n`th generated variable. -/
def freshVar (n : Nat) : Var := "@v" ++ toString n

/-- **A generated variable is in the generated namespace.** -/
theorem atPrefix_freshVar (n : Nat) : "@".isPrefixOf (freshVar n) = true := by
  rw [freshVar, String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@v").toList = ['@', 'v'] from by decide]
  exact ⟨'v' :: (toString n).toList, rfl⟩

theorem atPrefix_nodeName (f : FnName) : "@".isPrefixOf (nodeName f) = true := by
  rw [nodeName, String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@Node").toList = ['@', 'N', 'o', 'd', 'e'] from by decide]
  exact ⟨'N' :: 'o' :: 'd' :: 'e' :: f.toList, rfl⟩

theorem atPrefix_subName (f : FnName) : "@".isPrefixOf (subName f) = true := by
  rw [subName, String.isPrefixOf, String.startsWith_string_iff, String.toList_append,
    show ("@Sub").toList = ['@', 'S', 'u', 'b'] from by decide]
  exact ⟨'S' :: 'u' :: 'b' :: f.toList, rfl⟩

theorem nodeName_inj {f g : FnName} (h : nodeName f = nodeName g) : f = g := by
  have h2 := congrArg String.toList h
  rw [nodeName, nodeName, String.toList_append, String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_left h2)

theorem subName_inj {f g : FnName} (h : subName f = subName g) : f = g := by
  have h2 := congrArg String.toList h
  rw [subName, subName, String.toList_append, String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_left h2)

theorem nodeName_ne_ufName (f : FnName) : nodeName f ≠ ufName := by
  intro h
  have h2 := congrArg String.toList h
  rw [nodeName, ufName, String.toList_append,
    show ("@Node").toList = ['@', 'N', 'o', 'd', 'e'] from by decide,
    show ("@UF").toList = ['@', 'U', 'F'] from by decide] at h2
  cases h2

theorem subName_ne_ufName (f : FnName) : subName f ≠ ufName := by
  intro h
  have h2 := congrArg String.toList h
  rw [subName, ufName, String.toList_append,
    show ("@Sub").toList = ['@', 'S', 'u', 'b'] from by decide,
    show ("@UF").toList = ['@', 'U', 'F'] from by decide] at h2
  cases h2

theorem subName_ne_nodeName (f g : FnName) : subName f ≠ nodeName g := by
  intro h
  have h2 := congrArg String.toList h
  rw [subName, nodeName, String.toList_append, String.toList_append,
    show ("@Sub").toList = ['@', 'S', 'u', 'b'] from by decide,
    show ("@Node").toList = ['@', 'N', 'o', 'd', 'e'] from by decide] at h2
  cases h2

end Egglog
