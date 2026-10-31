import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Term

/-!
# The e-graph

One assertion set stores equations and reflexive facts, and a second set names the rows
that have been subsumed. A row of a relation is a held application; subsuming it keeps it
and its columns and stops every query from matching it.
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

/-- Egglog's global state, the e-graph `G = (E, X)`: equations and reflexive facts `E`, not
closed under congruence, and the subsumed rows `X`. -/
@[ext, blueprint "def:state"
  (statement := /--
  \(G=(E,X)\qquad E\subseteq\mathit{Term}\times\mathit{Term}\qquad X\subseteq\mathit{Term}\)
  -/)
  (latexEnv := "paperfragment")]
structure Database where
  eqs : Set (Term × Term)
  subsumed : Set Term

namespace Database
/-- The initial database. -/
def empty : Database where
  eqs := ∅
  subsumed := ∅

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

/-- Mark a set of rows subsumed. -/
def addSubsumed (X : Set Term) (db : Database) : Database :=
  { db with subsumed := db.subsumed ∪ X }

/-- The e-graph with subsumption forgotten, `(E, ∅)`: what a check sees. -/
def forgetSubsumed (db : Database) : Database :=
  { db with subsumed := ∅ }

/-- Union in a whole family of databases at once. -/
def sUnion (db : Database) (S : Set Database) : Database :=
  { eqs := db.eqs ∪ ⋃ d ∈ S, d.eqs, subsumed := db.subsumed ∪ ⋃ d ∈ S, d.subsumed }

/-- `d₁`'s equalities and subsumed rows are among `d₂`'s. -/
structure Contained (d₁ d₂ : Database) : Prop where
  eqs : d₁.eqs ⊆ d₂.eqs
  subsumed : d₁.subsumed ⊆ d₂.subsumed

end Database
end Egglog
