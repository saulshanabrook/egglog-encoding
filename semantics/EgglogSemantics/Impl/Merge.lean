import EgglogSemantics.Impl.Interp
import EgglogSemantics.Spec.Merge

/-!
# An executable interpreter for the M9 semantics

`Impl/Interp.lean` runs the constructor-only fragment. This runs `Spec/Merge.lean`, so
that `:merge` programs can be differentially tested against egglog — which is the only
check that M9's design matches the real system rather than matching itself.

`execM` at the bottom is the composed entry point, and it is what
`Program.expectedSizes` runs. Until it existed, `Impl/Interp.lean`'s `exec` was — and
that evaluates with `Expr.eval` and never calls `mergeRound`, so everything in this file
except `keyRowCount` had **no differential coverage at all**. A passing suite said nothing
about the merge implementation.

Three things differ from `Impl/Interp.lean`, all forced by the spec being *relational*.

**The refinement weakens to reachability.** `exec_toDatabase` says the constructor
interpreter computes exactly the spec's answer. Here the spec admits several, so the
statement is `ProgramStep d.toDatabase p (exec p).toDatabase` — the interpreter's
result is one the spec reaches. `Proofs/Merge.lean` states it.

**The merge phase is one pass, not a fixpoint.** `mergeRound` fires each collision among
the pre-pass rows once and is structurally terminating, which is sound because `RunStep`
is `MergeClosure` with no `MergeSaturated` requirement — a prefix of the closure is a
reachable state. Saturation is *now* reachable, since `min` and `max` became `Prim`s and
merging is an idempotent join again; `mergeSaturateF` says what switching to it would
buy and cost.

**A lookup has to pick.** `Expr.MEval`'s `lookup` reads any recorded output; `execExpr`
takes the first. `MERGE.md`, "Why the reader over-approximates", is why the spec does
not pin this and why an interpreter must. It is also where the model and egglog are now
known to diverge, since a superseded row is still readable here — `MERGE.md`, "What the
widening and the composed interpreter found", has the repro.

The congruence closure is *unchanged*. `MCong.fd` fires only at `.union` functions, and
a `.union` function's rows are exactly the constructor rows `Impl/Closure.lean` already
sees through `terms`; a `:merge` function's rows contribute nothing to `MCong`. So
`closureF` needs no `fd` disjunct as long as every declared function is `.merge` or
`.noMerge`, which is `Proofs/Merge.lean`'s `closureF_ok`.
-/

namespace Egglog
namespace FDatabase
/-- Whether two key tuples are congruent. `Impl/Interp.lean`'s `congrTuple`, which the
tuple-destructure pattern also uses. -/
abbrev congrKeys : Finset (Term × Term) → List Term → List Term → Bool :=
  FDatabase.congrTuple

/-- `Database.Out`, computed: every output recorded at a key congruent to `as`. -/
def outs (d : FDatabase) (f : FnName) (as : List Term) : List (List Term) :=
  let cl := d.closureF
  d.rows.filterMap fun r =>
    if r.fn = f && congrKeys cl as r.args then some r.out else none

end FDatabase
/-! ### Evaluation

`Expr.MEval`, computed. The `lookup` case takes the *first* recorded output, which is
the interpreter's pick; the spec allows any. -/
mutual

/-- `Expr.MEval`, computed. -/
def FDatabase.execExpr (d : FDatabase) (σ : Env) : Expr → Option Term
  | .lit l => some (.lit l)
  | .var v => Env.lookup v σ
  | .app f args =>
    (FDatabase.execExprList d σ args).bind fun ts =>
      match Prim.ofName f with
      | some p => p.apply ts
      | none =>
        match d.sig.mergeOf f with
        | .union => some (.app f ts)
        | _ => match d.outs f ts with
               | [v] :: _ => some v
               | _ => none

/-- `execExpr` over an argument list. -/
def FDatabase.execExprList (d : FDatabase) (σ : Env) : List Expr → Option (List Term)
  | [] => some []
  | e :: es => (d.execExpr σ e).bind fun t => (d.execExprList σ es).map (t :: ·)

end

/-! ### Actions -/
/-- `MDatabase.ActionStep`, computed. -/
def FDatabase.execAction (d : FDatabase) : Action → Option FDatabase
  | .expr e => (d.execExpr d.env e).map fun t => d.addTerm t
  | .letBind v e => (d.execExpr d.env e).map fun t =>
      { d.addTerm t with env := (v, t) :: d.env }
  | .union e₁ e₂ => (d.execExpr d.env e₁).bind fun t₁ =>
      (d.execExpr d.env e₂).map fun t₂ => d.addEq t₁ t₂
  | .set f args out => (d.execExprList d.env args).bind fun ts =>
      (d.execExprList d.env out).map fun vs => d.addRow f ts vs

/-- `MDatabase.ActionsStep`, computed. -/
def FDatabase.execActions (d : FDatabase) : List Action → Option FDatabase
  | [] => some d
  | a :: as => (d.execAction a).bind fun d' => d'.execActions as

/-! ### The merge phase

**This is where `Impl/` stops being append-only, and deliberately.** `Spec/` stays
append-only — the M11 safety invariant needs neither termination nor confluence precisely
because nothing is removed, and the encoding depends on "nothing is ever removed from it,
which lets proofs refer to terms after they leave the e-graph". A *reference
implementation* has a different job: egglog's merge replaces the row, so an append-only
`Impl/` is faithful to our spec and unfaithful to the system the spec is a model of. The
contract between the two therefore weakens from an equality to a containment — the
implementation may find *fewer* results, never more — which is the safe direction, since
every property M11 cares about is positive in the state.

**What "superseded" means here: the two rows the merge combined.** After the body has run
and the combined row is computed, `r₁` and `r₂` are dropped and the combined row is
written at `r₁`'s key. Nothing else is ever removed:

* **never a term and never an equality** — only `rows` is filtered;
* **never a row of a `.union` function** — the filter runs only inside the `.merge` branch,
  and `r₁.fn = r₂.fn` is that function;
* **never a row of a `.noMerge` function** — same reason, and it matters: `:no-merge` is
  how the proof encoding declares its proof nodes (`… → Unit :no-merge`, deliberately so
  two structurally equal proofs are never merged), and deleting one would delete a proof.

`Proofs/Merge.lean`'s `mergeRound_confined` is that paragraph, machine-checked.

Two mechanical consequences. Rows are filtered **before** the combined row is added, so an
idempotent merge that re-derives a row it already had keeps it rather than deleting what it
just wrote. And a firing now checks that both rows are still **present**, because
`mergeRound`'s loop ranges over the pre-pass row list and an earlier firing may already
have removed one — without the check a deleted row would be resurrected.

Saturation becomes genuinely reachable rather than approximated: two rows at one key class
become one, so the pair that fired is gone and the pass converges. -/
/-- One `:merge` firing on a named pair of rows, if it applies.

The signature is consulted *before* the congruence check, which is not cosmetic: the
check computes `closureF`, and `mergeRound` calls this once per ordered pair of rows, so
testing the cheap condition first is what keeps a constructor-only database from paying
a closure per pair. Same result either way — a `.union` or `.noMerge` function has no
body to run. -/
def FDatabase.mergeOneWith (cl : Finset (Term × Term)) (d : FDatabase) (r₁ r₂ : Row) :
    Option FDatabase :=
  match d.sig.mergeOf r₁.fn with
  | .merge body res =>
    if r₁.fn = r₂.fn && congrKeys cl r₁.args r₂.args
        && d.rows.contains r₁ && d.rows.contains r₂ then
      (FDatabase.execActions { d with env := mergeEnv r₁.out r₂.out } body).bind
        fun e => (e.execExprList e.env res).map fun vs =>
          let e' := { e with rows := e.rows.filter fun r => r ≠ r₁ && r ≠ r₂ }
          { e'.addRow r₁.fn r₁.args vs with env := d.env, rules := d.rules }
    else none
  | _ => none

/-- `mergeOneWith` at `d`'s own closure. -/
def FDatabase.mergeOne (d : FDatabase) (r₁ r₂ : Row) : Option FDatabase :=
  FDatabase.mergeOneWith d.closureF d r₁ r₂

/-- Whether any row belongs to a function with a `:merge` body — the cheap test that
keeps a constructor-only database out of the closure entirely. -/
def FDatabase.hasMergeRow (d : FDatabase) : Bool :=
  d.rows.any fun r => match d.sig.mergeOf r.fn with
    | .merge _ _ => true
    | _ => false

/-- One pass of the merge phase: every ordered pair of *distinct* rows present when the
pass began, fired once, left to right.

**Not** saturation. Structurally terminating, so it needs neither fuel nor a termination
witness, and sound because `RunStep` is `MergeClosure` with no `MergeSaturated`
requirement — a prefix of the closure is still a reachable state.

Two ways this fires a strict subset of what `MergeStep` allows, both deliberate and both
sound for the same reason.

**Self-collisions are skipped.** `MergeStep` has no `a ≠ b` guard, on purpose: without it
the spec would *under*-approximate egglog (`MERGE.md`, "No guard on the collision"). An
interpreter is under no such obligation — firing fewer steps still lands on a reachable
state — and egglog merges a retained row against an incoming staged one, so it never
self-merges either. What they produce is a row `MCong` already derives, so nothing is
lost.

**The inner loop ranges over the pre-pass rows**, not the accumulator, so a pass is a
fixed `n²` firings. Ranging over the accumulator would feed each pass its own output for
the same reason.

**The congruence closure is computed once per pass**, not once per pair, which is what
makes a pass affordable — `closureF` is a fixpoint over `terms ×ˢ terms` and `n²` of them
timed out difftest cases that had run in seconds. Rows added during the pass are therefore
compared against the *pre-pass* closure and a collision they create fires on the next
pass, which is again firing fewer steps. A constructor-only database skips the closure
altogether (`hasMergeRow`), so the 70 constructor cases pay a linear scan per action and
nothing else.

-/
def FDatabase.mergeRound (d : FDatabase) : FDatabase :=
  if !d.hasMergeRow then d else
    let cl := d.closureF
    d.rows.foldl (fun acc r₁ =>
      d.rows.foldl (fun acc' r₂ =>
        if r₁ == r₂ then acc'
        else match FDatabase.mergeOneWith cl acc' r₁ r₂ with
          | some acc'' => acc''
          | none => acc') acc) d

/-! ### Running -/
/-- Whether a merge pass changed anything. Compares the decidable fields; `sig` is a
function and `env`/`rules` a merge cannot touch. -/
def FDatabase.settled (d : FDatabase) : Bool :=
  let e := d.mergeRound
  e.terms == d.terms && e.rows == d.rows && e.eqs == d.eqs

/-- Merge saturation, for the record. Takes a **termination witness**, not fuel: being
undefined for a signature whose merges diverge is what egglog does too, where fuel would
return a half-merged database and present it as an answer. Not used by `execCmd`, which
runs one pass — see `mergeRound`. -/
def FDatabase.MergeRel (x y : FDatabase) : Prop :=
  y.mergeRound = x ∧ ¬ y.settled = true

def FDatabase.mergeSaturate (d : FDatabase) (h : Acc FDatabase.MergeRel d) :
    FDatabase :=
  Acc.rec (motive := fun _ _ => FDatabase)
    (fun x _ ih => if he : x.settled = true then x else ih x.mergeRound ⟨rfl, he⟩) h

/-- Merge saturation bounded by fuel that **fails** rather than returning a prefix.

egglog's `merge_all` runs to a fixed point (`free_join/mod.rs:546-628`), so this is the
faithful shape, and it is now *reachable*: while `min` and `max` were ordinary names a
`:merge (min old new)` body built the term `min(5, 3)` rather than computing `3`, merging
was non-idempotent by construction, `settled` was never reached, and each pass squared the
row set. Making them `Prim`s fixed that.

This **is** what `execCmdM` runs, and it has to be, now that a rule can read a value: a
single pass leaves `k` rows at a key class as `k - 1` when three or more collide, and a
value read would see the survivors. Deleting the combined rows is what makes it converge —
the pair that fired is gone, so a pass strictly shrinks the class until one row is left.

Returning `none` rather than a prefix is what keeps this outside `MERGE.md`'s objection to
fuel ("returns a wrong answer where *no answer* is correct"): a merge that really does
diverge makes `execM` `none`, which the difftest prints as `STUCK` and reports as a
mismatch, rather than silently presenting a half-merged state as the answer. -/
def FDatabase.mergeSaturateF : Nat → FDatabase → Option FDatabase
  | 0, d => if d.settled then some d else none
  | n + 1, d => if d.settled then some d else FDatabase.mergeSaturateF n d.mergeRound

/-- Passes `execM` allows before declaring a merge divergent. A pass strictly shrinks the
rows at every key class that collided, so this is a bound on the largest such class rather
than on the run. -/
def mergeFuel : Nat := 64

/-! ### E-matching, over `Expr.MEval`

`Impl/Interp.lean`'s `patternHolds` evaluates a pattern with `Expr.eval`, which builds an
application for *every* name. That is right for the constructor fragment and wrong here:
a body mentioning a `:merge` function has to read its row, and the tuple destructure
`Pattern.values` has no `Expr.eval` reading at all.

The congruence closure is unchanged. `MCong.fd` fires only at a `.union` function, whose
rows are exactly the constructor rows `closureF` already sees through `terms`, so
`closureF` decides `MCong` too — `Proofs/Merge.lean`'s `closureF_ok`. -/
/-- `MValidSubst`, computed. `patternHolds` with `execExpr` in place of `Expr.eval`. -/
def FDatabase.patternHoldsM (d : FDatabase) (p : Pattern) (σ : Env) : Bool :=
  match p with
  | .values vs f as =>
    match d.execExprList (d.env ++ σ) vs, d.execExprList (d.env ++ σ) as with
    | some us, some ts =>
      let cl := d.closureF
      d.rows.any fun r =>
        decide (r.fn = f) && congrKeys cl ts r.args && congrKeys cl us r.out
    | _, _ => false
  | .expr e =>
    match d.execExpr (d.env ++ σ) e with
    | none => false
    | some t =>
      let cl := (d.addTerm t).closureF
      decide (∃ w ∈ d.terms, (w, t) ∈ cl)
  | .eq e₁ e₂ =>
    match d.execExpr (d.env ++ σ) e₁, d.execExpr (d.env ++ σ) e₂ with
    | some t₁, some t₂ =>
      let cl := ((d.addTerm t₁).addTerm t₂).closureF
      decide ((t₁, t₂) ∈ cl) && decide (∃ w ∈ d.terms, (w, t₁) ∈ cl)
    | _, _ => false

/-- `matchQuery`, over `patternHoldsM`. The enumerator is unchanged: it assigns the
query's free variables to terms the database holds and restricts to each pattern. -/
def FDatabase.matchQueryM (d : FDatabase) (q : Query) : List Env :=
  (assignments d.terms (Query.freeVars q d.env)).filter fun σ =>
    q.all fun p => d.patternHoldsM p (Env.canon (p.freeVars d.env) σ)

/-! ### Running

`Impl/Interp.lean`'s `exec` evaluates with `Expr.eval` and never calls `mergeRound`, so
before this the merge implementation had **no** differential coverage at all: `mergeOne`,
`mergeRound`, `execActions` and `execExpr`'s lookup branch were unreachable from
`Program.expectedSizes`. `execM` is the composition that reaches them. -/
/-- `RuleResults`, computed: one firing, unioned into the accumulator. -/
def FDatabase.fireIntoM (d : FDatabase) (r : Rule) (acc : FDatabase) (σ : Env) :
    FDatabase :=
  match (FDatabase.execActions { d with env := d.env ++ σ } r.actions).map
      (fun d' => { d' with env := d.env, rules := d.rules }) with
  | some d' => acc.union d'
  | none => acc

/-- Every firing of `r`, unioned into `acc`. -/
def FDatabase.fireRuleM (d : FDatabase) (acc : FDatabase) (r : Rule) : FDatabase :=
  (d.matchQueryM r.query).foldl (d.fireIntoM r) acc

/-- `RunRules`, computed: every rule on every matching substitution, all read off the
pre-state. The merge phase is deliberately *not* here — egglog defers it until every rule
has been searched, so no rule sees another's merged value within a round. -/
def FDatabase.execRunRulesM (d : FDatabase) : FDatabase := d.rules.foldl d.fireRuleM d

/-- `CmdStep`, computed.

Both `.action` and `.run` end in a merge phase, which is egglog's shape and not a choice:
top-level actions go through the same staging path as a rule head, so **each top-level
`set` is its own merge phase** (`src/lib.rs:1490-1512`). Without that, the three top-level
`set`s of a difftest case would collide only at the next `(run)`.

The phase runs to a **fixpoint**, as `merge_all` does, which is only possible because the
implementation deletes the rows it merged — `mergeRound`'s docstring has that argument. -/
def FDatabase.execCmdM (d : FDatabase) : Cmd → Option FDatabase
  | .action a => (d.execAction a).bind (FDatabase.mergeSaturateF mergeFuel)
  | .rule r => some { d with rules := r :: d.rules }
  | .run => FDatabase.mergeSaturateF mergeFuel d.execRunRulesM
  | .decl f dc => some { d with sig := Function.update d.sig f (some dc) }

/-- `ProgramStep`, computed. -/
def FDatabase.execProgramM (d : FDatabase) : Program → Option FDatabase
  | [] => some d
  | c :: cs => (d.execCmdM c).bind fun d' => d'.execProgramM cs

/-- Run a program from the initial database, under the M9 semantics.

On the constructor fragment this agrees with `Impl/Interp.lean`'s `exec`: `execExpr` at a
`.union` function is `Expr.eval`, no constructor name resolves as a primitive, and with no
`.merge` function `mergeOne` never fires, so every merge phase is the identity. It differs
exactly where M9 does — a `:merge` function's application is a lookup, and a round ends
with `merge_all`. -/
def execM (p : Program) : Option FDatabase := FDatabase.empty.execProgramM p

/-! ### Row counts

`(print-size)` reports one row per distinct *canonical key tuple*, so this counts
congruence classes of keys — not rows and not values.

That is what makes the difftest work without the interpreter saturating merges. A merge
step writes its combined row at a key that is already present, so it adds no key class;
a merge with an empty action block adds no row anywhere else either. The count is
therefore invariant under the merge phase, which `Proofs/Merge.lean`'s
`mergeRound_rowCount` states — and does not hold as stated; the counterexample is
recorded there. It is also why keeping every superseded output — the
over-approximation the whole design rests on — does not inflate the number: three
recorded values at one key are still one row. -/
/-- The key tuples of `d`'s `f`-rows. -/
def FDatabase.keyLists (d : FDatabase) (f : FnName) : List (List Term) :=
  d.rows.filterMap fun r => if r.fn = f then some r.args else none

/-- The number of rows egglog's table for `f` would hold: one per congruence class of
key tuples. Each key is mapped to its whole class and the distinct classes counted, so
no representative has to be chosen.

Generalizes `Impl/Interp.lean`'s `rowCount`, which reads applications out of `terms`.
The two agree on a constructor, since `addTerm` writes one row per application; this one
additionally counts a `:merge` function's table. -/
def FDatabase.keyRowCount (d : FDatabase) (f : FnName) : Nat :=
  let cl := d.closureF
  let keys := (d.keyLists f).toFinset
  (keys.image fun as => keys.filter fun bs => congrKeys cl as bs).card

end Egglog
