import EgglogSemantics.Spec.Term
import Mathlib.Data.Set.Finite.Basic

namespace Egglog.Term

/-- Terms over a fixed vocabulary; depth and constructor arity remain unrestricted. -/
inductive UsesVocabulary (names : Set FnName) (literals : Set Lit) : Term → Prop where
  | lit {l : Lit} : l ∈ literals → UsesVocabulary names literals (.lit l)
  | app {f : FnName} {args : List Term} : f ∈ names →
      (∀ a ∈ args, UsesVocabulary names literals a) →
      UsesVocabulary names literals (.app f args)

/-- The paper uses these properties, leaving the concrete tie-break to `Term.blt`. -/
@[blueprint "def:order"
  (title := /-- Term order -/)
  (statement := /-- The model's fixed term order $\prec$ is strict and total, extends the
  orders on numbers and on strings with numbers below strings, and has every proper
  subterm smaller than its enclosing term. For every fixed finite
  vocabulary $V$ and bound $t$, the set $\{s\in T(V)\mid s\prec t\}$ is finite.
  The expression $\min(s,t)$ selects the smaller operand.
  Finite lower sets are required only within a fixed finite vocabulary.
  The model's concrete order compares node counts first and breaks ties structurally. -/)]
structure AdmissibleOrder (lt : Term → Term → Prop) : Prop where
  irrefl : ∀ t, ¬ lt t t
  trans : ∀ s t u, lt s t → lt t u → lt s u
  total : ∀ s t, s ≠ t → lt s t ∨ lt t s
  subterm : ∀ s t, IsSubterm s t → s ≠ t → lt s t
  literals : ∀ m n, lt (.lit (.int m)) (.lit (.int n)) ↔ m < n
  strings : ∀ a b, lt (.lit (.str a)) (.lit (.str b)) ↔ a < b
  numbersFirst : ∀ n a, lt (.lit (.int n)) (.lit (.str a))
  finiteLower : ∀ (names : Set FnName) (literals : Set Lit),
    names.Finite → literals.Finite → ∀ t,
      {s | UsesVocabulary names literals s ∧ lt s t}.Finite

end Egglog.Term
