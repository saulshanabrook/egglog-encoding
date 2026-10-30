import EgglogSemantics.Spec.Step

/-!
# Sequential readings

Not part of the specification. The interpreter and many proofs run actions one at a time
and read a round as a union of rule results. `Proofs/Writes.lean` relates each reading to
its definition in `Spec/Eval.lean` and `Spec/Step.lean`.
-/

namespace Egglog

/-- Run one action under a substitution. A delete is applied in the current state, whereas
a round applies every delete before every write and reads spellings in the pre-state; the
two readings agree for heads that neither assert an equation before a delete nor delete a
row they also write. The proofs use delete-free heads. -/
def evalAction (σ : Env) (db : Database) : Action → Option Database
  | .expr e => (e.eval σ).map fun t => db.addTerm t
  | .union e₁ e₂ =>
      (e₁.eval σ).bind fun t₁ =>
        (e₂.eval σ).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some (db.addEq t₁ t₂)
  | .delete e => (e.eval σ).map fun t => db.deleteRows {t}

/-- Run the actions in order, threading the database through. -/
def evalActions (σ : Env) (db : Database) : List Action → Option Database
  | [] => some db
  | a :: as => (evalAction σ db a).bind fun db' => evalActions σ db' as

/-- The databases one rule contributes, one per substitution satisfying its query. -/
def RuleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ, ValidQuerySubst db r.query σ ∧ evalActions σ db r.actions = some d}

/-- A state whose next round of `rs` preserves its meaning. -/
def RunSaturated (rs : List Rule) (d : Database) : Prop := d.SameMeaning (RunRules rs d)

end Egglog
