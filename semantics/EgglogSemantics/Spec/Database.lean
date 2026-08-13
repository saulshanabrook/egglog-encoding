import Mathlib.Data.Set.Lattice
import EgglogSemantics.Spec.Term

/-!
# The database

The global state: the equalities the program has asserted, the global bindings, the rules,
and the declarations. There is no separate term set — the equation `t = t` records that `t`
was built, and `Database.terms` is the terms that are self-equal. It is the *endpoints* of
`eqs`, not its diagonal: asserting `1 = 2` alone holds both, by `symm` and `trans`. The two
coincide exactly under `WF.eqsRefl`, which is what that field is for. A function's table
lives there too: a merge function's entry at the key `a…` with value columns `v…` is the
term `f(a…, v…)`, and a constructor's entry is `f(a…)`.
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
/-- Egglog's global state. -/
@[ext]
structure Database where
  /-- The declared functions. Written only by `Cmd.decl`. -/
  sig : Signature
  /-- The *asserted* equalities: `union`s, and a reflexive `t = t` per term built. Not
  closed under congruence, and never shrinks. -/
  eqs : Set (Term × Term)
  /-- Global bindings, extended by a top-level `let`. -/
  env : Env
  /-- The rules, run by `Cmd.run`. -/
  rules : Set Rule

namespace Database
/-- The initial database. -/
def empty : Database where
  sig := fun _ => none
  eqs := ∅
  env := []
  rules := ∅

/-- Record `t` and all of its subterms, each by its reflexive equation. -/
def addTerm (t : Term) (db : Database) : Database :=
  { db with eqs := db.eqs ∪ {(s, s) | s ∈ t.subterms} }

def addTerms (ts : List Term) (db : Database) : Database :=
  ts.foldl (fun d t => d.addTerm t) db

/-- Assert `a = b`, recording both terms. -/
def addEq (a b : Term) (db : Database) : Database :=
  let d := (db.addTerm a).addTerm b
  { d with eqs := insert (a, b) d.eqs }

/-- Union in a whole family of databases at once, taking `sig`, `env` and `rules` from
`db`. -/
def sUnion (db : Database) (S : Set Database) : Database :=
  { db with eqs := db.eqs ∪ ⋃ d ∈ S, d.eqs }

/-- Databases that differ only in an environment no `lookup` can tell apart. -/
structure EnvAgree (d₁ d₂ : Database) : Prop where
  sig : d₁.sig = d₂.sig
  eqs : d₁.eqs = d₂.eqs
  rules : d₁.rules = d₂.rules
  env : Env.Agree d₁.env d₂.env

/-- `d₁`'s equalities are among `d₂`'s; the other fields are ignored. -/
structure Contained (d₁ d₂ : Database) : Prop where
  eqs : d₁.eqs ⊆ d₂.eqs

end Database
end Egglog
