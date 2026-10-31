import EgglogSemantics.Source.Domain

/-! Static well-formedness for the source language. These conditions are separate from the
compiler's supported fragment and from whether a check is true. -/

namespace Egglog

instance (r : Rule) (Γ : Scope) : Decidable (r.Scoped Γ) :=
  inferInstanceAs (Decidable ((∀ p ∈ r.query, p.Scoped) ∧
    Actions.Scoped r.actions (Query.bind r.query Γ)))

instance (S : Schedule) (Γ : Scope) : Decidable (S.Scoped Γ) :=
  inferInstanceAs (Decidable (∀ r ∈ S.rules, r.Scoped Γ))

instance (P : Program) (Γ : Scope) : Decidable (Program.Scoped P Γ) :=
  inferInstanceAs (Decidable (P.schedule.Scoped Γ ∧ ∀ p ∈ P.check, p.Scoped))

/-- The paper's static premise, used together with `Program.Fragment`: every rule and
check is scoped, with head variables bound by the query, and every name is applied at one
arity. These are syntactic conditions: a check need not be true for its program to be well
formed. -/
@[blueprint "def:wellformed"
  (title := /-- Static well-formedness -/)
  (statement := /-- Rules and the final check are scoped, with head variables bound by
  the query, and every name is applied at one arity. These are syntactic conditions: the
  check need not be true for its program to be well formed. -/)]
def Program.WellFormed (P : Program) : Prop := WellScoped P ∧ P.AritiesAgree

instance (P : Program) : Decidable P.WellFormed :=
  inferInstanceAs (Decidable (Program.Scoped P [] ∧ P.AritiesAgree))

end Egglog
