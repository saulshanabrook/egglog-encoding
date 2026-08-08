import EgglogSemantics.Spec.Match

/-!
# Running commands and programs

Ports the Redex `Command-Reduction` and `Egglog-Reduction`.

The Redex needs two reduction relations because `(run)` picks a set of
substitutions nondeterministically and then unions the results. Here the database's
components are `Set`s, so that union is expressible directly and `runRules` is a
function; `runProgram` is then a plain fold and the semantics is deterministic.

Two consequences of that:

* The Redex `skip` command, which only exists to let `Command-Reduction` signal
  completion to `Egglog-Reduction`, is gone.
* `restore-congruence` between commands is gone, because congruence is the
  predicate `Cong` rather than a set the state has to carry (see `PLAN.md`).

`runRules` is noncomputable: the set of matching substitutions is carved out by a
predicate, not enumerated. An executable interpreter is `PLAN.md`'s M10.
-/

namespace Egglog
/-- The databases one rule contributes, one per substitution satisfying its query.

This is the Redex `Eval-Actions`, whose `U_d` over the results is taken by
`runRules`. Substitutions whose actions get stuck contribute nothing, which cannot
happen for a well-scoped rule (`Scope.lean`). -/
def ruleResults (db : Database) (r : Rule) : Set Database :=
  {d | ∃ σ, ValidQuerySubst db r.query σ ∧ evalLocalActions db r.actions σ = some d}

/-- The Redex `(run)` case of `Command-Reduction`.

Every rule fires on every substitution satisfying its query *in the pre-state*, and
all the results are unioned in. Rules therefore cannot see each other's output
within one `run`. -/
noncomputable def runRules (db : Database) : Database :=
  db.sUnion {d | ∃ r ∈ db.rules, d ∈ ruleResults db r}

/-- The Redex `Command-Reduction`. -/
noncomputable def stepCmd (db : Database) : Cmd → Option Database
  | .action a => evalAction db a
  | .rule r => some { db with rules := insert r db.rules }
  | .run => some (runRules db)
  | .decl f d => some { db with sig := Function.update db.sig f (some d) }

/-- The Redex `Egglog-Reduction`: run the commands in order. -/
noncomputable def runProgram (db : Database) : Program → Option Database
  | [] => some db
  | c :: cs => (stepCmd db c).bind fun db' => runProgram db' cs

/-- Run a whole program from the initial database. -/
noncomputable def run (p : Program) : Option Database := runProgram Database.empty p

/-! ### Rounds

The Redex `(run)` is exactly one round, and its to-do list carries "add schedules".
`runRounds` is egglog's `(run n)`; `Cmd.run` is `n = 1`. Nothing in the command
language reaches these yet — they exist because comparing this semantics against
egglog means comparing at round boundaries, and because egglog's `saturate` is what
the encoding's rebuild schedule relies on. -/
/-- `runRules` iterated `n` times: egglog's `(run n)`. -/
noncomputable def runRounds : Nat → Database → Database
  | 0, db => db
  | n + 1, db => runRounds n (runRules db)

/-- A database no round can add to. Egglog's `saturate` runs until this holds; it need
not ever hold, which is why it is a predicate rather than a fixpoint operator. -/
def Saturated (db : Database) : Prop := runRules db = db

end Egglog
