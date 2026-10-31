import Mathlib.Logic.Relation
import EgglogSemantics.Spec.Match

/-!
# Steps

A run fires the rules it names once against the current state and adds every firing's
result. Nothing is removed, so the firings commute. A saturation repeats its
schedule until a pass leaves the meaning of the state unchanged; it need not terminate. A
program's outcome is its final check.
-/

namespace Egglog
/-! ### Rounds and saturation -/
/-- `⟨run R, G⟩ ⇓ G'`, the round: every rule of `R` fires on every substitution satisfying
its query in the pre-state, and the result is the pre-state together with every firing's
result. Nothing is removed, so the firings commute. -/
@[blueprint "def:round"
  (statement := /--
  \[
  \ir{Run}{G'=G\cup\bigcup\{\,G\oplus_\sigma H\mid(Q\Rightarrow H)\in R,\ G,\sigma\models Q\,\}}
    {\langle\kw{run}\ R,G\rangle\Downarrow G'}
  \]
  -/)
  (latexEnv := "paperfragment")]
def RunRules (rs : List Rule) (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ rs, ∃ σ, QueryMatches db r.query σ ∧ evalActions σ db r.actions = some d}

/-- `⟨S, G⟩ ⇓ G'`: a run is one round; a sequence threads the state; a saturation repeats
its schedule until a pass changes neither congruence nor the live terms, returning that
pass's result. Redundant spellings do not prevent saturation. -/
@[blueprint "def:saturation"
  (statement := /--
  \begin{mathpar}
  \ir{Seq}{\langle S_1,G\rangle\Downarrow G_1\\\langle S_2,G_1\rangle\Downarrow G'}
    {\langle S_1;S_2,G\rangle\Downarrow G'}
  \and
  \ir{Fixpoint}{\langle S,G\rangle\Downarrow G'\\G\equiv G'}
    {\langle\kw{saturate}\ S,G\rangle\Downarrow G'}
  \and
  \ir{Repeat}{\langle S,G\rangle\Downarrow G_1\\G\not\equiv G_1\\
    \langle\kw{saturate}\ S,G_1\rangle\Downarrow G'}
    {\langle\kw{saturate}\ S,G\rangle\Downarrow G'}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
inductive Reach : Database → Schedule → Database → Prop where
  | run {db : Database} {rs : List Rule} : Reach db (.run rs) (RunRules rs db)
  | seq {db d d' : Database} {S₁ S₂ : Schedule} :
      Reach db S₁ d → Reach d S₂ d' → Reach db (.seq S₁ S₂) d'
  | fixpoint {db d : Database} {S : Schedule} :
      Reach db S d → db.SameMeaning d → Reach db (.saturate S) d
  | again {db d d' : Database} {S : Schedule} :
      Reach db S d → ¬ db.SameMeaning d → Reach d (.saturate S) d' →
      Reach db (.saturate S) d'

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

/-- Program evaluation: the schedule, then the final check decides the outcome. A check
sees subsumed rows, as egglog's `check` does (`check_facts` queries with
`include_subsumed`), so it runs against the final e-graph with subsumption forgotten.
Running `P` from the empty state is `Eval Database.empty P`. -/
@[blueprint "def:behavior"
  (statement := /--
  \begin{mathpar}
  \ir{Ok}{\langle S,G\rangle\Downarrow(E',X')\\(E',\emptyset),\sigma\models Q}
    {\langle S;\kw{check}\ Q,G\rangle\Downarrow\kw{ok}}
  \and
  \ir{Error}{\langle S,G\rangle\Downarrow(E',X')\\\nexists\sigma.\ (E',\emptyset),\sigma\models Q}
    {\langle S;\kw{check}\ Q,G\rangle\Downarrow\kw{error}}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
inductive Eval : Database → Program → Result → Prop where
  | ok {db d : Database} {P : Program} :
      Reach db P.schedule d → QueryHolds d.forgetSubsumed P.check → Eval db P .ok
  | checkFailed {db d : Database} {P : Program} :
      Reach db P.schedule d → ¬ QueryHolds d.forgetSubsumed P.check → Eval db P .checkFailed

end Egglog
