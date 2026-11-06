import EgglogSemantics.Spec.Step

/-!
# Set-valued readings

Not part of the specification. The proofs read an action as the facts it adds, a round as
the pre-state plus the union of the firings' facts, and a rule as the set of states its
firings produce. `Proofs/Writes.lean` relates each reading to `evalAction` and `RunRules`.
-/

namespace Egglog

/-- The equations an action asserts, undefined exactly when `evalAction` is. -/
def Action.write (σ : Env) : Action → Option (Set (Term × Term))
  | .expr e => (e.eval σ).map fun t => {(t, t)}
  | .union e₁ e₂ =>
      (e₁.eval σ).bind fun t₁ =>
        (e₂.eval σ).bind fun t₂ =>
          if t₁.isLit || t₂.isLit then none else some {(t₁, t₂)}
  | .subsume f es => (Expr.evalList es σ).map fun ts => {(.app f ts, .app f ts)}

/-- The rows an action subsumes: the row of a subsume, and nothing for the others. -/
def Action.mark (σ : Env) : Action → Option (Set Term)
  | .subsume f es => (Expr.evalList es σ).map fun ts => {.app f ts}
  | a => (a.write σ).map fun _ => ∅

/-- The equations asserted by a head, defined when every action's are. -/
def Action.writes (σ : Env) : List Action → Option (Set (Term × Term))
  | [] => some ∅
  | a :: as => (a.write σ).bind fun W => (Action.writes σ as).map (W ∪ ·)

/-- The rows subsumed by a head, defined exactly when its writes are. -/
def Action.marks (σ : Env) : List Action → Option (Set Term)
  | [] => some ∅
  | a :: as => (a.mark σ).bind fun X => (Action.marks σ as).map (X ∪ ·)

/-- The equations every rule of `rs` writes on every substitution satisfying its query in
the pre-state. -/
def RunWrites (rs : List Rule) (db : Database) : Set (Term × Term) :=
  ⋃₀ {W | ∃ r ∈ rs, ∃ σ, QueryMatches db r.query σ ∧ Action.writes σ r.actions = some W}

/-- The rows every rule of `rs` subsumes on those substitutions. -/
def RunMarks (rs : List Rule) (db : Database) : Set Term :=
  ⋃₀ {X | ∃ r ∈ rs, ∃ σ, QueryMatches db r.query σ ∧ Action.marks σ r.actions = some X}

/-- The databases one rule contributes, one per substitution satisfying its query. -/
def RuleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ, ValidQuerySubst db r.query σ ∧ evalActions σ db r.actions = some d}

/-- A state whose next round of `rs` preserves its meaning. -/
def RunSaturated (rs : List Rule) (d : Database) : Prop := d.SameMeaning (RunRules rs d)

end Egglog
