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
@[blueprint "def:congruence"
  (statement := /--
  \begin{mathpar}
  \ir{Direct}{(s,t)\in E}{s\sim_E t}
  \and
  \ir{Sym}{s\sim_E t}{t\sim_E s}
  \and
  \ir{Trans}{s\sim_E t\\t\sim_E u}{s\sim_E u}
  \and
  \ir{Child}{f(s_1,\ldots,s_n)\sim_E f(s_1,\ldots,s_n)}{s_i\sim_E s_i}
  \and
  \ir{Cong}{f(s_1,\ldots,s_n)\sim_E f(s_1,\ldots,s_n)\\\forall i.\ s_i\sim_E t_i}
    {f(s_1,\ldots,s_n)\sim_E f(t_1,\ldots,t_n)}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
inductive Cong (db : Database) : Term → Term → Prop where
  | direct {a b : Term} : (a, b) ∈ db.eqs → Cong db a b
  /-- A child of an existing application exists; by induction, so does every subterm. -/
  | child {f : FnName} {as : List Term} {s : Term} :
      Cong db (.app f as) (.app f as) → s ∈ as → Cong db s s
  | symm {a b : Term} : Cong db a b → Cong db b a
  | trans {a b c : Term} : Cong db a b → Cong db b c → Cong db a c
  | congr {f : FnName} {as bs : List Term} :
      Cong db (.app f as) (.app f as) →
      CongList db as bs → Cong db (.app f as) (.app f bs)

/-- Pointwise `Cong` over argument lists. -/
inductive CongList (db : Database) : List Term → List Term → Prop where
  | nil : CongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      Cong db a b → CongList db as bs → CongList db (a :: as) (b :: bs)

end

/-- Terms explicitly occurring in the store, including subterms. -/
@[blueprint "def:stored-terms"
  (statement := /--
  \[
  \operatorname{terms}(E)\triangleq
    \bigcup_{(s,t)\in E}
      \bigl(\operatorname{subterms}(s)\cup\operatorname{subterms}(t)\bigr)
  \]
  -/)
  (latexEnv := "paperfragment")]
def Database.terms (db : Database) : Set Term :=
  {t | ∃ p ∈ db.eqs, t ∈ p.1.subterms ∨ t ∈ p.2.subterms}

/-- Literals only occur beside themselves in asserted equations. -/
def Database.LitsIsolated (db : Database) : Prop :=
  ∀ p ∈ db.eqs, p.1.isLit ∨ p.2.isLit → p.1 = p.2

/-- Literals have singleton equivalence classes. -/
structure Database.WF (db : Database) : Prop where
  litsIsolated : db.LitsIsolated

/-- Two spellings of one row: the same head over congruent children. -/
def Database.SameRow (db : Database) (s t : Term) : Prop :=
  ∃ f as bs, s = .app f as ∧ t = .app f bs ∧ CongList db as bs

/-- The terms a query may look up: everything that exists, in any spelling, except the
subsumed rows, in any spelling. Subsuming `f(s̄)` subsumes every `f(t̄)` with `t̄ ~ s̄`,
as egglog keeps a row subsumed when canonicalization merges it with another. -/
@[blueprint "def:live"
  (statement := /--
  \[
  \operatorname{live}(E,X)\triangleq
    \{\,t\mid t\sim_E t\,\}\setminus
    \{\,f(t_1,\ldots,t_n)\mid f(s_1,\ldots,s_n)\in X,\ \forall i.\ s_i\sim_E t_i\,\}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Database.live (db : Database) : Set Term :=
  {t | Cong db t t ∧ ¬ ∃ u ∈ db.subsumed, db.SameRow t u}

/-- States agree on semantic equality and on the live terms: the paper's `G ≡ G'`. -/
@[blueprint "def:equiv"
  (statement := /--
  \[
  (E,X)\equiv(E',X')\ \triangleq\
    {\sim_E}={\sim_{E'}}\ \wedge\ \operatorname{live}(E,X)=\operatorname{live}(E',X')
  \]
  -/)
  (latexEnv := "paperfragment")]
structure Database.SameMeaning (d₁ d₂ : Database) : Prop where
  congr : ∀ a b, Cong d₁ a b ↔ Cong d₂ a b
  live : ∀ t, t ∈ d₁.live ↔ t ∈ d₂.live

end Egglog
