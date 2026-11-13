import EgglogSemantics.Slotted.Spec.Match

/-!
# Slotted actions

Actions evaluate as in the plain semantics, under the match's substitution extended with
fresh names: a slot variable that the actions mention and the query does not bind is a slot
"used only in actions" and receives a fresh name, distinct from the other fresh names and from
every slot name of the match. Every such choice is a result of the round; the choices differ
by a renaming of fresh slots, so they have one slotted meaning.
-/

namespace Egglog.Slotted

/-- The variables an action mentions. -/
def actionVars : Action → List Var
  | .expr e => e.vars
  | .union e₁ e₂ => e₁.vars ∪ e₂.vars
  | .subsume _ es => Expr.varsList es

/-- The slot variables of the actions that the query does not bind. -/
def freshVars (r : Rule) : List Var :=
  ((r.actions.flatMap actionVars).filter fun v => isSlotVar v && v ∉ r.query.vars).dedup

/-- `ν` binds exactly the action-only slot variables of `r`, to pairwise distinct slots that
occur in no value of the match `σ`. -/
def FreshSlots (r : Rule) (σ ν : Env) : Prop :=
  (Env.dom ν).Perm (freshVars r) ∧
  (∀ b ∈ ν, ∃ s, isSlotName s = true ∧ b.2 = Term.slot s ∧ ∀ c ∈ σ, s ∉ allSlots c.2) ∧
  (∀ b ∈ ν, ∀ c ∈ ν, b.2 = c.2 → b.1 = c.1)

/-- `G ⊕_{νσ} H`: the head under the match extended with the fresh names, `evalActions`. -/
def evalActions' (σ ν : Env) (db : Database) (H : List Action) : Option Database :=
  evalActions (ν ++ σ) db H

end Egglog.Slotted
