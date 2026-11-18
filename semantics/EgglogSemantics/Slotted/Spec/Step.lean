import EgglogSemantics.Spec.Step
import EgglogSemantics.Slotted.Spec.Eval

/-!
# Slotted rounds, schedules, and outcomes

The plain `Reach` and `Eval` over the slotted round: every rule fires on every slotted match,
under every choice of fresh names for its action-only slots, and a saturation repeats until a
pass preserves the slotted meaning of the state. A slotted program is a plain program with a
binder signature; its outcome is what phase 2 compares with the plain outcome of the compiled
program.
-/

namespace Egglog.Slotted

/-- `⟨run R, G⟩ ⇓ G'`, the slotted round: the pre-state together with every firing's result,
over the slotted matches and every choice of fresh action slots. -/
@[blueprint "def:slotted-round"
  (statement := /--
  \[
  \ir{Run'}{G'=G\cup\bigcup\{\,G\oplus_{\nu\sigma}H\mid(Q\Rightarrow H)\in R,\
    G,\sigma\models Q,\
    \nu:\operatorname{PS}(H)\setminus\operatorname{PS}(Q)\rightarrowtail
      \text{slots fresh for }\sigma\,\}}
    {\langle\kw{run}\ R,G\rangle\Downarrow G'}
  \]
  -/)
  (latexEnv := "paperfragment")]
def SRunRules (bind : Binders) (rs : List Rule) (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ rs, ∃ σ ν, SQueryMatches bind db r.query σ ∧ FreshSlots r σ ν ∧
    evalActions' σ ν db r.actions = some d}

/-- `⟨S, G⟩ ⇓ G'` with slotted rounds and the slotted fixpoint test. -/
inductive SReach (bind : Binders) : Database → Schedule → Database → Prop where
  | run {db : Database} {rs : List Rule} : SReach bind db (.run rs) (SRunRules bind rs db)
  | seq {db d d' : Database} {S₁ S₂ : Schedule} :
      SReach bind db S₁ d → SReach bind d S₂ d' → SReach bind db (.seq S₁ S₂) d'
  | fixpoint {db d : Database} {S : Schedule} :
      SReach bind db S d → SameMeaning' bind db d → SReach bind db (.saturate S) d
  | again {db d d' : Database} {S : Schedule} :
      SReach bind db S d → ¬ SameMeaning' bind db d → SReach bind d (.saturate S) d' →
      SReach bind db (.saturate S) d'

/-- Slotted program evaluation: the schedule, then the final check as a slotted query. -/
inductive SEval (bind : Binders) : Database → Egglog.Program → Result → Prop where
  | ok {db d : Database} {P : Egglog.Program} :
      SReach bind db P.schedule d → SQueryHolds bind d P.check → SEval bind db P .ok
  | checkFailed {db d : Database} {P : Egglog.Program} :
      SReach bind db P.schedule d → ¬ SQueryHolds bind d P.check → SEval bind db P .checkFailed

/-- A slotted program: a plain program with its binder signature. -/
structure Program where
  plain : Egglog.Program
  binders : Binders

/-- The outcome of a slotted program from the empty state: the source side of the slotted
pass's correctness statement. -/
def Program.Eval (P : Program) (o : Result) : Prop := SEval P.binders Database.empty P.plain o

end Egglog.Slotted
