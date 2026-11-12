import EgglogSemantics.Slotted.Encode.Query
import EgglogSemantics.Slotted.Spec.Step

/-!
# Premises of slotted pass correctness

These are source-language obligations for phase 3, not a simulation or a proof of the pass.
`WellBound` checks the fields a binder annotation names; `PayloadConsistent` describes the
inferred layout; `Scoped` allows only query-bound variables and fresh action slots. The
paper's renaming assumption is `Commutes`: a source round commutes, up to slotted meaning,
with a permutation of names that fixes concrete constants and literal query slots.
Action-only slots remain fresh choices. The parser substitutes globals into rules.
This assumption mentions no target state.
-/

namespace Egglog.Slotted.Pass

open Encode

/-- Every application has in-range binding annotations and slots at binding positions. -/
def WellBound (bind : Binders) (P : Egglog.Program) : Prop :=
  ∀ fa ∈ Encode.Program.apps P, ∀ ji ∈ bind fa.1,
    ji.1 < fa.2.length ∧ ji.2 < fa.2.length ∧
      ∃ e, fa.2[ji.1]? = some e ∧ (slotRef e).isSome = true

/-- A payload column holds a literal or a non-slot variable; a binder never covers it. -/
def PayloadConsistent (bind : Binders) (P : Egglog.Program) : Prop :=
  let L := Layout.ofProgram bind P
  ∀ fa ∈ Encode.Program.apps P, ∀ je ∈ fa.2.zipIdx,
    L.column fa.1 je.2 = .payload →
      (je.1.isLit = true ∨ ∃ v, je.1 = .var v ∧ isSlotVar v = false) ∧
      ∀ ji ∈ bind fa.1, ji.2 ≠ je.2

/-- Action variables are query-bound, except for fresh slot variables. -/
def Scoped (P : Egglog.Program) : Prop :=
  ∀ r ∈ P.rules, ∀ v ∈ r.actions.flatMap actionVars,
    v ∈ r.query.vars ∨ isSlotVar v = true

/-- A bijection of names that preserves which strings denote slots. -/
structure NamePermutation where
  names : Slot ≃ Slot
  slots : ∀ s, isSlotName (names s) = isSlotName s

mutual

/-- Uniformly rename slot leaves, including bound names. A bijection cannot capture. -/
def renameTerm (ρ : NamePermutation) : Term → Term
  | .lit l => .lit l
  | .app f args =>
    if isSlotApp f args then .slot (ρ.names f) else .app f (renameTerms ρ args)

def renameTerms (ρ : NamePermutation) : List Term → List Term
  | [] => []
  | t :: ts => renameTerm ρ t :: renameTerms ρ ts

end

/-- The image of the equations and subsumptions under a uniform renaming. -/
def renameDatabase (ρ : NamePermutation) (db : Database) : Database :=
  { eqs := (fun p => (renameTerm ρ p.1, renameTerm ρ p.2)) '' db.eqs,
    subsumed := renameTerm ρ '' db.subsumed }

/-- A permutation fixes concrete slot terms and literal query slots. Action-only slots
remain fresh choices and need not be fixed. -/
def FixesConstants (ρ : NamePermutation) (r : Rule) : Prop :=
  (∀ fa ∈ r.query.flatMap Encode.Pattern.apps ++ r.actions.flatMap Encode.Action.apps,
    isSlotName fa.1 = true → fa.2 = [] → ρ.names fa.1 = fa.1) ∧
  (∀ v ∈ r.query.vars, isSlotVar v = true → ρ.names v = v)

/-- Consistently renaming a match only renames the facts it produces: the paper's source
rule assumption, stated for the complete round (including all choices of fresh slots). -/
def Commutes (bind : Binders) (r : Rule) : Prop :=
  ∀ ρ : NamePermutation, FixesConstants ρ r → ∀ db : Database,
    SameMeaning' bind (SRunRules bind [r] (renameDatabase ρ db))
      (renameDatabase ρ (SRunRules bind [r] db))

/-- The semantic and source-layout premises of phase 3. Successful compilation separately
checks namespace separation, arities, ordering, supported operations, keyed queries and
variable roles. No component assumes anything about the compiled program's behavior. -/
structure Premises (P : Slotted.Program) : Prop where
  binders : P.binders.WF
  wellBound : WellBound P.binders P.plain
  payloads : PayloadConsistent P.binders P.plain
  headScope : Scoped P.plain
  equivariant : ∀ r ∈ P.plain.rules, Commutes P.binders r

end Egglog.Slotted.Pass
