import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Term

/-!
# The database

One assertion set stores equations and reflexive facts. A row of a relation is a held
application; deleting it removes its reflexive assertion and keeps its columns.
-/

namespace Egglog
/-- Variable bindings, innermost first. -/
abbrev Env := List (Var × Term)

namespace Env
/-- The first binding for `v`, if any. -/
def lookup (v : Var) : Env → Option Term
  | [] => none
  | (w, t) :: rest => if v = w then some t else lookup v rest

/-- The variables bound by `σ`, in order. -/
def dom (σ : Env) : List Var := σ.map Prod.fst

/-- Environments no `lookup` can tell apart. -/
def Agree (σ₁ σ₂ : Env) : Prop := ∀ v, lookup v σ₁ = lookup v σ₂

end Env

/-- Egglog's global state: equations and reflexive facts, not closed under congruence. -/
@[ext, blueprint "def:state"
  (statement := /-- \(E\subseteq\{(s,t)\mid s,t\in\mathit{Term}\}\) -/)
  (latexEnv := "paperfragment")]
structure Database where
  eqs : Set (Term × Term)

namespace Database
/-- The initial database. -/
def empty : Database where
  eqs := ∅

/-- Assert that `t` exists; congruence supplies subterm existence. -/
def addTerm (t : Term) (db : Database) : Database :=
  { db with eqs := insert (t, t) db.eqs }

def addTerms (ts : List Term) (db : Database) : Database :=
  ts.foldl (fun d t => d.addTerm t) db

/-- Assert `a = b`; congruence supplies endpoint and subterm existence. -/
def addEq (a b : Term) (db : Database) : Database :=
  { db with eqs := insert (a, b) db.eqs }

/-- Assert a set of equations. -/
def addEqs (ps : Set (Term × Term)) (db : Database) : Database :=
  { db with eqs := db.eqs ∪ ps }

/-- Union in a whole family of databases at once. -/
def sUnion (db : Database) (S : Set Database) : Database :=
  { eqs := db.eqs ∪ ⋃ d ∈ S, d.eqs }

/-- `d₁`'s equalities are among `d₂`'s. -/
structure Contained (d₁ d₂ : Database) : Prop where
  eqs : d₁.eqs ⊆ d₂.eqs

end Database
end Egglog
