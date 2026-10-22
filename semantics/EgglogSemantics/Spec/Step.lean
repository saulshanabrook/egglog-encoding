import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# Steps

A run fires the rules it names once against the current state, applying all their
deletions before all their writes. Saturation repeats runs until one leaves congruence
unchanged; it need not terminate. A program's outcome is its final check.
-/

namespace Egglog
/-! ### Deleting rows -/
/-- The immediate children of a term: the columns of a row. -/
def Term.children : Term → List Term
  | .lit _ => []
  | .app _ as => as

/-- Two spellings of one row: the same head over congruent children. -/
def Database.SameRow (db : Database) (s t : Term) : Prop :=
  ∃ f as bs, s = .app f as ∧ t = .app f bs ∧ CongList db as bs

/-- The rows `X` names, in every spelling the state holds: a held `f(s̄)` is deleted when
some `f(t̄) ∈ X` has congruent children. -/
def Database.deletedRows (X : Set Term) (db : Database) : Set Term :=
  {r | (r, r) ∈ db.eqs ∧ ∃ t ∈ X, db.SameRow r t}

/-- The reflexive facts of the deleted rows: the paper's `R`, a subset of `E`.
`Proofs/Deletes.lean` shows `deleteRows` is `(E \ R) ∪ …` in these terms. -/
def Database.deletedFacts (X : Set Term) (db : Database) : Set (Term × Term) :=
  {p | p ∈ db.eqs ∧ p.1 = p.2 ∧ p.1 ∈ db.deletedRows X}

/-- Remove every held spelling of each row in `X`, re-asserting their column values. A row
that another assertion still forces to exist, as a subterm or an equation endpoint, stays
represented; compiled programs never delete such a row. Deleting an absent row changes
nothing. -/
@[blueprint "def:delete"
  (statement := /--
  \[
  \begin{gathered}
  E\ominus X\triangleq(E\setminus R)\ \cup\ \{(s_i,s_i)\mid (f(\bar s),f(\bar s))\in R\}\\[.3em]
  \text{where}\quad
  R=\{\,(f(\bar s),f(\bar s))\in E\mid \exists f(\bar t)\in X.\ \bar s\sim_E\bar t\,\}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Database.deleteRows (X : Set Term) (db : Database) : Database :=
  { db with eqs := (db.eqs \ {p | p.1 = p.2 ∧ p.1 ∈ db.deletedRows X}) ∪
      {p | ∃ r ∈ db.deletedRows X, ∃ c ∈ r.children, p = (c, c)} }

/-! ### Rounds and saturation -/
/-- The equations every rule of `rs` writes on every substitution satisfying its query in
the pre-state. -/
def RunWrites (rs : List Rule) (db : Database) : Set (Term × Term) :=
  ⋃₀ {W | ∃ r ∈ rs, ∃ σ, QueryMatches db r.query σ ∧ Action.writes σ r.actions = some W}

/-- The rows every rule of `rs` deletes on those substitutions. -/
def RunErases (rs : List Rule) (db : Database) : Set Term :=
  ⋃₀ {X | ∃ r ∈ rs, ∃ σ, QueryMatches db r.query σ ∧ Action.erases σ r.actions = some X}

/-- `⟨run ρ̄, E⟩ ⇓ E'`: every rule of `ρ̄` fires on every substitution satisfying its query
in the pre-state. All deletions are applied first and then all writes, so a row that one
firing deletes and another writes survives, as in egglog, whose table merge removes before
it inserts. -/
@[blueprint "def:round"
  (statement := /--
  \[
  \begin{gathered}
  \ir{Run}{}{\langle\kw{run}\ \bar\rho,E\rangle\Downarrow(E\ominus\mathcal X)\cup\mathcal W}\\[.6em]
  \text{where}\quad
  \mathcal W=\bigcup\{\writes A\mid(Q\Rightarrow A)\in\bar\rho,\ E,\sigma\models Q\},\quad
  \mathcal X=\bigcup\{\erases A\mid(Q\Rightarrow A)\in\bar\rho,\ E,\sigma\models Q\}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def RunRules (rs : List Rule) (db : Database) : Database :=
  (db.deleteRows (RunErases rs db)).addEqs (RunWrites rs db)

/-- `⟨saturate ρ̄, E⟩ ⇓ E'`: run `ρ̄` until a run leaves congruence unchanged, returning
that run's result. Redundant spellings and rows that are replaced do not prevent
saturation. -/
@[blueprint "def:saturation"
  (statement := /--
\[
  \ir{Fixpoint}{\langle\kw{run}\ \bar\rho,E\rangle\Downarrow E'\\{\sim_E}={\sim_{E'}}}
    {\langle\kw{saturate}\ \bar\rho,E\rangle\Downarrow E'}
  \qquad
  \ir{Repeat}{\langle\kw{run}\ \bar\rho,E\rangle\Downarrow E_1\\{\sim_E}\ne{\sim_{E_1}}\\
    \langle\kw{saturate}\ \bar\rho,E_1\rangle\Downarrow E'}
    {\langle\kw{saturate}\ \bar\rho,E\rangle\Downarrow E'}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive SaturateReach (rs : List Rule) : Database → Database → Prop where
  | fixpoint {db : Database} :
      Cong db = Cong (RunRules rs db) → SaturateReach rs db (RunRules rs db)
  | again {db d : Database} :
      Cong db ≠ Cong (RunRules rs db) → SaturateReach rs (RunRules rs db) d →
      SaturateReach rs db d

/-! ### Commands and programs -/
/-- Successful command execution. -/
def CmdStep (db : Database) : Cmd → Database → Prop
  | .run rs, db' => db' = RunRules rs db
  | .saturate rs, db' => SaturateReach rs db db'

/-- Run the commands in order. -/
inductive ProgramStep : Database → List Cmd → Database → Prop where
  | nil {db : Database} : ProgramStep db [] db
  | cons {db d d' : Database} {c : Cmd} {cs : List Cmd} :
      CmdStep db c d → ProgramStep d cs d' → ProgramStep db (c :: cs) d'

/-- The outcome of a finite execution: the final check held, or it failed. The final state
is not part of the outcome. Divergence and interpreter fuel exhaustion are not outcomes. -/
inductive Result where
  | ok
  | checkFailed
  deriving DecidableEq

/-- The observation compared by compiler correctness. -/
def Result.succeeded : Result → Bool
  | .ok => true
  | .checkFailed => false

/-- Program evaluation: the commands in order, then the final check decides the outcome.
Running `P` from the empty state is `Eval Database.empty P`. -/
@[blueprint "def:behavior"
  (statement := /--
  \[
  \ir{Check}{E,\sigma\models Q}{\langle\kw{check}\ Q,E\rangle\Downarrow\kw{ok}}\quad
  \ir{Fail}{\nexists\sigma.\ E,\sigma\models Q}{\langle\kw{check}\ Q,E\rangle\Downarrow\kw{error}}\quad
  \ir{Next}{\langle C,E\rangle\Downarrow E_1\\\langle P,E_1\rangle\Downarrow o}
    {\langle C;P,E\rangle\Downarrow o}
  \qquad o\in\{\kw{ok},\kw{error}\}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive Eval : Database → Program → Result → Prop where
  | ok {db d : Database} {P : Program} :
      ProgramStep db P.commands d → QueryHolds d P.check → Eval db P .ok
  | checkFailed {db d : Database} {P : Program} :
      ProgramStep db P.commands d → ¬ QueryHolds d P.check → Eval db P .checkFailed

end Egglog
