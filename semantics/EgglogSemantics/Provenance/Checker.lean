import EgglogSemantics.Provenance.Format
import EgglogSemantics.Spec.Scope

/-! Intermediate certificates for union-free relational programs, before source lifting.
Every premise of a firing is an established fact: a row, or a subterm of one. -/

namespace Egglog.Provenance

/-- The facts one action produces: a written row and its subterms. A delete produces none,
and a union is outside the relational language. -/
def actionFacts (σ : Env) : Action → Option (List Term)
  | .expr e => do
      let t ← e.eval σ
      some t.subtermList
  | .delete e => do
      let _ ← e.eval σ
      some []
  | .union _ _ => none

def actionsFacts (σ : Env) : List Action → Option (List Term)
  | [] => some []
  | a :: as => do
      let fs ← actionFacts σ a
      let rest ← actionsFacts σ as
      some (fs ++ rest)

def unionFree (P : Program) : Bool := P.rules.all fun r =>
  r.actions.all fun a => match a with | .union _ _ => false | _ => true

/-- `t` is a subterm of an established fact. -/
def supported (premises : List Term) (t : Term) : Bool :=
  premises.any fun p => decide (t ∈ p.subtermList)

/-- A row premise's fact is its instance. An equality premise's fact is the common value of
its sides. A disequality premise's fact is one of its sides; both sides are established and
differ. -/
def premiseMatches (σ : Env) (premises : List Term) (p : Pattern) (fact : Term) : Bool :=
  match p with
  | .expr e => e.eval σ == some fact
  | .eq a b => a.eval σ == some fact && b.eval σ == some fact
  | .ne a b =>
      match a.eval σ, b.eval σ with
      | some x, some y =>
          (x == fact || y == fact) && x != y && supported premises x && supported premises y
      | _, _ => false

def premisesMatch (σ : Env) (premises : List Term) : Query → List Term → Bool
  | [], [] => true
  | p :: ps, t :: ts => premiseMatches σ premises p t && premisesMatch σ premises ps ts
  | _, _ => false

def ruleFacts (r : Rule) (σ : Env) (premises : List Term) : Option (List Term) := do
  if decide ((Env.dom σ).Perm r.query.vars) &&
      σ.all (fun b => supported premises b.2) &&
      premisesMatch σ premises r.query premises then
    actionsFacts σ r.actions
  else none

/-- The root node's justification, against the facts its subproofs state. -/
def checkReason (P : Program) : Proof → Bool
  | .rule t i σ ps => (do
      let r ← P.rules[i]?
      let facts ← ruleFacts r σ (ps.map Proof.fact)
      some (decide (t ∈ facts))).getD false
  | .subterm t parent => decide (t ∈ parent.fact.subtermList)

mutual

/-- Every node is valid. -/
def valid (P : Program) : Proof → Bool
  | .rule t i σ ps => allValid P ps && checkReason P (.rule t i σ ps)
  | .subterm t p => valid P p && checkReason P (.subterm t p)

def allValid (P : Program) : List Proof → Bool
  | [] => true
  | p :: ps => valid P p && allValid P ps

end

/-- Check a proof about the compiled relational program, which has no `union`. This is an
intermediate step: source proofs are checked by `SourceProof.check` against the original
program, unions included. -/
def check (P : Program) (pf : Proof) : Option Term := do
  if !unionFree P then none else
    if valid P pf then some pf.fact else none

end Egglog.Provenance
