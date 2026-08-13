import Mathlib.Data.List.Forall2
import EgglogSemantics.Spec.Database

/-!
# Congruence

`Cong db a b` says `a = b` is derivable in `db`: an **inductive predicate** over the
asserted equalities, not a set of pairs the state carries.
-/

namespace Egglog
mutual

/-- The congruence closure of `db`'s asserted equalities. A **partial equivalence
relation**: symmetric and transitive, but reflexive only where an equation makes it so. -/
inductive Cong (db : Database) : Term → Term → Prop where
  | assert {a b : Term} : (a, b) ∈ db.eqs → Cong db a b
  | symm {a b : Term} : Cong db a b → Cong db b a
  | trans {a b c : Term} : Cong db a b → Cong db b c → Cong db a c
  | congr {f : FnName} {as bs : List Term} :
      Cong db (.app f as) (.app f as) → Cong db (.app f bs) (.app f bs) →
      CongList db as bs → Cong db (.app f as) (.app f bs)

/-- Pointwise `Cong` over argument lists. -/
inductive CongList (db : Database) : List Term → List Term → Prop where
  | nil : CongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      Cong db a b → CongList db as bs → CongList db (a :: as) (b :: bs)

end

/-- The terms `db` holds: a term is present exactly when it is self-equal. -/
def Database.terms (db : Database) : Set Term := {t | Cong db t t}

/-- Both sides of a derivable equation are present. -/
theorem eqsInTerms_free {db : Database} {a b : Term} (h : Cong db a b) :
    a ∈ db.terms ∧ b ∈ db.terms := ⟨h.trans h.symm, h.symm.trans h⟩

/-- Every application the database holds is a **declared** function's entry: its head is
declared, and it carries that declaration's `entryWidth` children. -/
def Database.DeclaredTerms (db : Database) : Prop :=
  ∀ f as, Term.app f as ∈ db.terms → ∃ d, db.sig f = some d ∧ as.length = d.entryWidth

/-- No asserted equation puts a literal beside anything but itself: `evalAction` refuses a
`union` on a literal and `addTerm` writes only reflexive pairs. `Cong.eq_of_isLit` reads it
back as "a literal's class is a singleton", which is what makes `Prim.apply` stable. -/
def Database.LitsIsolated (db : Database) : Prop :=
  ∀ p ∈ db.eqs, p.1.isLit ∨ p.2.isLit → p.1 = p.2

/-- The database invariants: it records the diagonal of what it holds, holds the children
of every term it holds, binds its variables to terms it holds, and isolates literals.

`eqsRefl` is what makes "the term is present" and "the equation `t = t` is asserted"
interchangeable. Without it a term can be present by `symm`/`trans` alone, and then
`addTerm` on a term already held is not the identity — so a self-collision, which always
applies, would still change the state and nothing would be `MergeSaturated`. -/
structure Database.WF (db : Database) : Prop where
  eqsRefl : ∀ t ∈ db.terms, (t, t) ∈ db.eqs
  subtermClosed : ∀ t ∈ db.terms, t.subterms ⊆ db.terms
  envInTerms : ∀ b ∈ db.env, b.2 ∈ db.terms
  litsIsolated : db.LitsIsolated

/-- `db` plus the terms `ts`, used to relate a term the database may not hold — a pattern
instance, say — to one it does. It records that each of `ts` exists and **adds no equation
between distinct terms**, so it can relate `a` to `b` only for a reason `db` already had. -/
def Database.withOperands (db : Database) (ts : List Term) : Database := db.addTerms ts

@[inherit_doc Database.withOperands] def CongOn
    (db : Database) (ts : List Term) (a b : Term) : Prop := Cong (db.withOperands ts) a b

/-- **Every equation `d₁` records `d₂` records up to congruence.** The witness `q` is one
of `d₂`'s own equations, or the clause says nothing: `withOperands` alone makes `p` hold. -/
structure Database.Recorded (d₁ d₂ : Database) : Prop where
  eqs : ∀ p ∈ d₁.eqs, ∃ q ∈ d₂.eqs,
    CongOn d₂ [p.1, p.2] p.1 q.1 ∧ CongOn d₂ [p.1, p.2] p.2 q.2

end Egglog
