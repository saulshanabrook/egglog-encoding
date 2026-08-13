import EgglogSemantics.Impl.Interp
import EgglogSemantics.Spec.Step

/-!
# An executable interpreter for the M9 semantics

`Impl/Interp.lean` runs the constructor-only fragment. This runs `Spec/Step.lean`, so
that `:merge` programs can be differentially tested against egglog — which is the only
check that M9's design matches the real system rather than matching itself.

`execM` at the bottom is the composed entry point, and it is what
`Program.expectedSizes` runs. Until it existed, `Impl/Interp.lean`'s `exec` was — and
that evaluates with `Expr.eval` and never calls `mergeRound`, so everything in this file
except `keyRowCount` had **no differential coverage at all**. A passing suite said nothing
about the merge implementation.

Two things differ from `Impl/Interp.lean`, both forced by the spec being *relational*.

**The refinement weakens to reachability.** `exec_programStep` says the constructor
interpreter reaches exactly the states the spec does, in both directions. Here the spec
admits several, so only one direction survives: the interpreter's result is one the spec
reaches. `Proofs/Merge.lean`'s `execM_contained` states what is available instead, and it
is confined to `Program.NoSaturate` — `execRunRules_contained` is a *containment*, so the
interpreter settling does not witness a specification fixpoint, and that is what a
`Cmd.saturate` would need.

**The merge phase is a pass iterated to a fixpoint.** `mergeRound` is one pass — a rebuild, then
each collision among the pre-pass rows fired once, structurally terminating — and `execCmdM` runs
`mergeSaturateF` over it, as `merge_all` does. A single pass would also be sound, since `CmdStep`
ends in a `MergeClosure` with no `MergeSaturated` requirement and a prefix of the closure is a
reachable state; it is not *enough*, because a rule can read a value and one pass leaves three
colliding entries at a key class as two. Saturating terminates only because the pass deletes the
rows it merged — `mergeSaturateF` has the argument.

What no longer differs is **evaluation, e-matching or actions**: with reading confined to
the query, `Expr.eval` takes a signature and resolves primitives, so `Impl/Interp.lean`'s
`execAction`, `execActions` and `patternHolds` serve a `:merge` program unchanged and this
file adds only the merge phase and the round that runs it. The one place the interpreter
still chooses is `patternHolds`' row scan, which sees a superseded output where egglog
sees only the current one — `MERGE.md`, "What the widening and the composed interpreter
found", has the repro.

The congruence closure is *unchanged*, and needs no argument to stay so: `Cong` reads
`eqs` and no row at all, so `closureF` decides it whatever the index holds.
The functional dependency a constructor's table has is `Cong.congr` itself, a rule of the
relation, since a constructor's entry is its own application.

Entry terms do enter the closure, and inertly. A merge function's entry `f(a…, v…)` is
never a *subterm* of anything — `Expr.eval` builds no application of a merge function, so
every key and value column is a constructor term — so the pairs it adds relate entry terms
to entry terms and can never propagate down to a key. `congrKeys`, `canonTerm` and
`canonOf` therefore see exactly what they saw when entries were rows and nothing else.
-/

namespace Egglog
namespace FDatabase
/-- Whether two key tuples are congruent. `Impl/Interp.lean`'s `congrTuple`, which the
row atom `Pattern.values` also uses. -/
abbrev congrKeys : Finset (Term × Term) → List Term → List Term → Bool :=
  FDatabase.congrTuple

end FDatabase
/-! ### The merge phase

**This is where the *index* stops being append-only, and deliberately.** `Spec/` stays
append-only — the M11 safety invariant needs neither termination nor confluence precisely
because nothing is removed, and the encoding depends on "nothing is ever removed from it,
which lets proofs refer to terms after they leave the e-graph". A *reference
implementation* has a different job: egglog's merge replaces the row, and its rebuild
*moves* one, so a table that only grows is faithful to our spec and unfaithful to the
system the spec is a model of.

`FDatabase.rows` is where that happens, and `toDatabase` drops it, so the **denotation
stays append-only** whatever the index does: the entry terms `addRow` and
`mergeOneOriented` put in `terms` are never removed and never re-keyed. What the two
sides then differ by is which entries the implementation still *finds* — the contract is
`Spec/Congruence.lean`'s `Database.Recorded`, read through `Database.Out`, so the
implementation may find *fewer* results, never more. That is the safe direction, since
every property M11 cares about is positive in the state.

**What "superseded" means here: the two rows the merge combined.** After the body has run
and the combined row is computed, `r₁` — the row being inserted — is dropped from the
index, and `r₂` — the row already in the table — is overwritten in place by the combined
row, whose entry term is added beside the two it combined. A collision that changes no
value column skips the body and the overwrite, dropping `r₁` and leaving `r₂` exactly as
it stands (`noConflict`). Nothing else is ever removed:

* **never a term and never an equality** — only `rows` is rewritten;
* **never a constructor's row**, which the whole congruence argument rests on — the rewrite runs
  only inside the `.merge` branch and touches only `r₁` and `r₂`, whose function is that branch's;
* **never a row of a `.noMerge` function** — same reason, and it matters: `:no-merge` is
  how the proof encoding declares its proof nodes (`… → Unit :no-merge`, deliberately so
  two structurally equal proofs are never merged), and deleting one would delete a proof.

`Proofs/Merge.lean`'s `mergeRound_confined` is that paragraph, machine-checked.

One mechanical consequence: a firing checks that both rows are still **present**, because
`mergeRound`'s loop ranges over the pre-pass row list and an earlier firing may already
have removed one — without the check a deleted row would be resurrected.

Saturation becomes genuinely reachable rather than approximated: two rows at one key class
become one, so the pair that fired is gone and the pass converges. -/
/-- Whether the collision resolves to nothing, so that egglog runs no body at all.

egglog's `MergeFn` (`egglog-bridge/src/lib.rs`) computes an `unchanged_width`: the
declared `:internal-identity-vals` columns, or — for a merge with an **action block** —
*every* value column. When the resident row and the arriving row agree on those columns
the collision "is not a real value conflict", so the block's actions do not run and the
resident value columns are kept. That is the whole of this test, and both halves of it
are load-bearing.

**The comparison is on the values and says nothing about the keys.** Two rows at
*congruent but unequal* keys holding the same value are therefore a no-op there, where
whole-row equality — which is all `mergeRound` skips on — sees a firing pair. That
mismatch was a recorded divergence:

```
(function Log (Math) i64 :merge new)
(function Dist (Math) i64 :merge ((set (Log (L)) old) new))
(set (Dist (X)) 2) (set (Dist (Y)) 2) (union (X) (Y)) (run 1)
```

egglog answers `L 0, Log 0` and this model answered `L 1, Log 1`. The two agree again as
soon as any column differs, so this is all-or-nothing over the value tuple and not per
column — a width-2 body with one column equal and one different runs on both sides.

**The body must be non-empty.** A single-expression `:merge` does not short-circuit in
egglog and deliberately so, since it may be non-idempotent: `:merge (+ old new)` on two
rows both holding `2` still gives `4` there. `MergeSpec.merge body res` with `body = []`
is exactly that form, so the guard is `body ≠ []` and nothing else. The `let`-only block
form does take the skip, unobservably — such a body writes nothing and its result is
`min v v = v` either way.

**Firing less is always sound**, which is why this is a repair rather than a new fragment
boundary: `mergeRound` already fires a strict subset of `MergeStep`, and its contract is
containment in a state the closure reaches, not equality.

The one residual is eq-sorted value columns, which the difftest fragment does not draw:
egglog compares canonical e-class ids, so two congruent-but-unequal output terms are
unchanged there and distinct here, and the model would fire where egglog skips — the safe
direction again. -/
def FDatabase.noConflict (body : List Action) (r₁ r₂ : Row) : Bool :=
  !body.isEmpty && r₁.out == r₂.out

/-- One `:merge` firing on an *oriented* pair of rows, if it applies: `r₂` is the row
already in the table and `r₁` the one arriving, so the body runs under
`mergeEnv r₂.out r₁.out` — `old` from `r₂`, `new` from `r₁`, the opposite of the argument
order. `mergeOneWith` is what decides the orientation; nothing else should call this.

The signature is consulted *before* the congruence check, which is not cosmetic: the
check computes `closureF`, and `mergeRound` calls this once per ordered pair of rows, so
testing the cheap condition first is what keeps a constructor-only database from paying
a closure per pair. Same result either way — a constructor or a `.noMerge` function has
no body to run.

**The combined row takes `r₂`'s key and `r₂`'s slot**, and its entry term `f(r₂.args…,
vs…)` joins `terms`, which is what `MergeStep` records and the only part of the firing the
denotation sees. `r₁` is dropped and `r₂` is overwritten where it stands, rather than both
being dropped and the result prepended: in
egglog a merge leaves the existing table entry in place, so the survivor inherits the
resident row's key and its age, and a third row colliding with it later is the *newer*
one. Prepending instead made the survivor the youngest row of its class, which inverts
the next collision — `(set (Dist X) 1) (set (Dist Y) 2) (set (Dist Z) 3) (union X Y)
(union Y Z)` returns `3` under `:merge old` that way, where egglog returns `1`.

Writing at `r₂`'s key matches egglog's surviving key whenever `r₂` is the canonical-key
row, which is what `mergeOneWith` arranges when either row is. When *neither* is — a
third, older term in the class carries the canonical key and egglog re-inserts both rows
under it — egglog's survivor sits at a key no row here has, and this writes at `r₂`'s
instead. `Database.Out` reads a row from every congruent key, so nothing is lost until a
row appears at that third key later, which is the residual `MERGE.md` records.

**A collision that changes no value column runs no body.** `noConflict` is that test, and
`MERGE.md`'s "A collision that changes nothing runs no body" is the evidence. The firing
reduces to dropping `r₁`, which is what egglog's insert does with the row it did not have
to merge. -/
def FDatabase.mergeOneOriented (cl : Finset (Term × Term)) (d : FDatabase) (r₁ r₂ : Row) :
    Option FDatabase :=
  match d.sig.mergeOf r₁.fn with
  | some (.merge body res) =>
    if r₁.fn = r₂.fn && congrKeys cl r₁.args r₂.args
        && d.rows.contains r₁ && d.rows.contains r₂ then
      if FDatabase.noConflict body r₁ r₂ then
        some { d with rows := d.rows.filter fun r => r ≠ r₁ }
      else
        (execActions { d with env := mergeEnv r₂.out r₁.out } body).bind
          fun e => (Expr.evalList e.sig res e.env).map fun vs =>
            let e' := e.addTerm (.app r₂.fn (r₂.args ++ vs))
            { e' with
              rows := (e'.rows.filter fun r => r ≠ r₁).map fun r =>
                if r = r₂ then ⟨r₂.fn, r₂.args, vs⟩ else r,
              env := d.env, rules := d.rules }
    else none
  | _ => none

/-! ### Which colliding row is `old`

egglog's table insert calls the merge function as `merge_fn(cur, row)` — `cur` the row
already stored under that key, `row` the one arriving — and binds `old` to the first and
`new` to the second (`egglog/core-relations/src/table/mod.rs`, `SortedWritesTable`'s
`insert`). `old` is therefore not "the row written earlier"; it is **the row that is
already there**, and the two coincide only when nothing moved.

A rebuild moves rows. It re-canonicalizes every candidate row and stages a
remove-and-re-insert for exactly those the canonicalization changed
(`core-relations/src/table/rebuild.rs`), so the row whose key is *already* canonical is
left alone and is the one the others are inserted onto — it is `cur`, hence `old`,
however recently it was written. Canonical is least e-class id, because the union-find
unions by min id (`egglog/union-find/src/lib.rs`, "union by min id"), and ids are handed
out as terms are built, so the canonical member of a class is its **earliest-created**
term. That is what `Term.subtermList`'s order records and what `canonTerm` reads back.

Four shapes checked against the release binary, all with
`(function Dist (Math) i64 :merge new)` and read back with `(print-function Dist)`:

* `(set (Dist (K)) 3) (set (Dist (A)) 2) (union (A) (K))` keeps `2`, but the same three
  commands after a bare `(A)` — which creates `A` first — keep `3`. Insertion age is
  identical in the two; only which key is canonical changed, which is what rules the
  insertion-age reading out. The union's argument order changes nothing.
* `(P (K) (A))` before the two `set`s keeps `2`, and `(P (A) (K))` keeps `3`: the order
  the *arguments of one term* are created in decides it too.
* No union at all — `(set (Dist (K)) 3) (set (Dist (K)) 2)` — keeps `2`. No key moved,
  so the resident row is simply the earlier write and age does decide, which is the case
  the two readings agree on.
* Two rows and no canonical key among them: `(Z)` first, then `(set (Dist (K)) 3)`,
  `(set (Dist (A)) 2)` and both keys unioned into `(Z)`, keeps `2` under `:merge new` and
  `3` under `:merge old`. Both keys moved, so egglog stages both in table order and the
  earlier write is the one the other is merged onto — age, again, as the tie-break.

**What this still does not model** is allocation order the term list cannot see. A term
list position is fixed when the term is *first* added, which matches egglog for terms
built by actions and by rule heads in the order the interpreter runs them, but a round
that fires several rules is free to build terms in another order than egglog's; and
`ordering-min`/`ordering-max` continue to use the structural `Term.blt`, since a `Prim`
has no database to consult. `MERGE.md` records both. -/
/-- Whether `t` is the canonical member of its congruence class — no congruent term was
created before it — which is what makes egglog's rebuild leave a row keyed on `t` alone.

`ts` is `FDatabase.terms`, which `addTerm` prepends to, so the terms *after* `t` in `ts`
are exactly the ones created before it. A `t` the list does not hold counts as canonical,
vacuously; `addRow` puts every key term in `terms`, so a row's key never is one. -/
def FDatabase.canonTerm (cl : Finset (Term × Term)) (ts : List Term) (t : Term) : Bool :=
  ((ts.dropWhile (· != t)).drop 1).all fun u => u == t || !(decide ((t, u) ∈ cl))

/-- `canonTerm` on a key tuple: whether a row keyed here is the one egglog's rebuild
leaves in place. A key is canonical exactly when each column is. -/
def FDatabase.canonKey (cl : Finset (Term × Term)) (ts : List Term) (as : List Term) :
    Bool :=
  as.all (FDatabase.canonTerm cl ts)

/-! ### The rebuild

`canonTerm` says *whether* a row is the one egglog leaves in place. That is enough to
orient a collision between two rows the interpreter can see, and not enough when the
canonical key belongs to a third term carrying no row of its own:

```
(datatype Math (A) (B) (C) (Kept) (Lost))
(function Dist (Math) i64 :merge new)
(A) (set (Dist (B)) 1) (set (Dist (C)) 2) (union (C) (A)) (union (B) (A))
(rule ((= 1 (Dist (A)))) ((Kept)))  (rule ((= 2 (Dist (A)))) ((Lost)))
(run 1)
```

`A` is canonical and holds no row, so neither `Dist (B)` nor `Dist (C)` is at a canonical
key and `swapForCanon` declines to orient the pair. egglog answers `Kept`, and answers
`Lost` when the two `union`s are swapped, because `old` is the row **already at the
canonical key**: the first `union` re-keys `C`'s row onto `A`, where the second `union`
then finds it resident. Insertion age cannot see that — both `set`s happened before either
`union` — so the interpreter has to re-key too. `DiffTest.lean`'s `rekey-*` cases are the
four shapes, and `mrand-28` is what found it.

**What it does.** Rewrite every `:merge` row's key columns to their class's canonical
representative, drop the rows that become duplicates, and put the rows the rewrite
*moved* in front of the rows it left alone. All three parts are load-bearing:

* rewriting is what records, in the row itself, that the row has reached the canonical
  key, so a later collision there can tell resident from arriving;
* dropping duplicates is egglog's insert finding nothing to resolve — the arriving row
  goes away and the resident one keeps its place, which `List.dedup` does for free by
  keeping the *last* occurrence;
* moving is the age update. A re-keyed row was removed and re-inserted, so it is the
  arriving row and the one already at the canonical key is `old`. `mergeRound` reads age
  off the row list front-first, so "arriving" is "at the front", and the moved rows keep
  their relative order among themselves — egglog stages a rebuild's re-insertions in
  table order, so the earlier write is still the one the rest merge onto
  (`canon-none-old`).

**Key columns only.** egglog canonicalizes eq-sorted *value* columns as well — with
`(function Val (Math) Math :merge ((set (Fired (L)) 1) old))`, a second `(set (Val (K))
(V2))` after `(union (V1) (V2))` runs no body, where without the `union` it does. That
stays the residual `noConflict` records: `FnDecl` carries no sorts and `Tests/Egg.lean`
renders `i64` per output column, so no program the difftest can build has an eq-sorted
merge output, and re-keying values would put the implementation's rows outside
`Database.Out` — the relation `Spec/Congruence.lean`'s `Database.Recorded` reads them
through.

**Constructor rows are left alone**: a constructor has no value column, so `ctorRowList` emits
`⟨f, as, []⟩` and the term it indexes is the application `f(as)` itself. Re-keying one would put
it out of step with that term while buying nothing — congruence never reads a row, and
`Database.Out` reads a constructor's entry from every congruent key already. `.noMerge` rows are
left alone too; a `:no-merge` collision is a program error, not a resolution. -/
/-- The canonical member of `t`'s congruence class: the congruent term created *first*.

`ts` is `FDatabase.terms`, whose *tail* is the oldest part — `addTerm` prepends and
`List.dedup` keeps a repeated term's last occurrence, so a term's position is fixed when
it is first added. The last congruent entry is therefore the earliest-created one, which
is egglog's representative, its union-find unioning by min id.

`canonTerm` is the predicate this is the witness of: a term is canonical exactly when it
is its own representative. A term `ts` does not hold represents itself.

Written as a fold that keeps overwriting, so it is one pass and its result is visibly
either `t` or a congruent entry of `ts` — `Proofs/Merge.lean`'s `foldl_pick`. -/
def FDatabase.canonOf (cl : Finset (Term × Term)) (ts : List Term) (t : Term) : Term :=
  ts.foldl (fun acc u => if u == t || decide ((t, u) ∈ cl) then u else acc) t

/-- `canonOf` on a key tuple: the key egglog's rebuild leaves the row at. -/
def FDatabase.canonKeyOf (cl : Finset (Term × Term)) (ts : List Term) (as : List Term) :
    List Term :=
  as.map (FDatabase.canonOf cl ts)

/-- A row at its canonical key. Only a `.merge` function's rows move. -/
def FDatabase.rebuildRow (cl : Finset (Term × Term)) (d : FDatabase) (r : Row) : Row :=
  match d.sig.mergeOf r.fn with
  | some (.merge _ _) => ⟨r.fn, FDatabase.canonKeyOf cl d.terms r.args, r.out⟩
  | _ => r

/-- **egglog's rebuild**: every `:merge` row re-keyed onto its class's canonical key, the
re-keyed ones in front as the rows that just arrived, and duplicates dropped.

Takes the closure as an argument because `mergeRound` has already computed it and a
rebuild cannot change it — only `terms` and `eqs` feed `closureF`, and this writes
neither. Idempotent for the same reason: its output has every `:merge` key canonical and
no repeated row, so a second pass moves nothing. -/
def FDatabase.rebuild (cl : Finset (Term × Term)) (d : FDatabase) : FDatabase :=
  let tagged := d.rows.map fun r => (d.rebuildRow cl r, r)
  { d with rows :=
      ((tagged.filter fun p => p.1 != p.2).map Prod.fst
        ++ (tagged.filter fun p => p.1 == p.2).map Prod.fst).dedup }

/-- Whether the *first* row of the pair is the one already in the table, so that
`mergeOneWith` must hand `mergeOneOriented` the pair the other way round.

Guarded by `mergeOneOriented`'s own firing condition, and that is load-bearing twice
over. `mergeRound` asks this once per ordered pair of rows while `canonKey` scans
`terms` per key column, so the scan has to be confined to pairs that actually collide.
And a guard that is *weaker* than the firing condition would force `cl` where the firing
never does — `congrKeys` compares tuple lengths first, so a pair of different arities
never looks inside the closure — which is enough to put the whole congruence closure in
front of the kernel and stall the `decide` proofs in `Proofs/Lattice.lean`.

Equal keys need no scan either: they are canonical or not together, so age decides,
which is the argument order already. -/
def FDatabase.swapForCanon (cl : Finset (Term × Term)) (d : FDatabase) (r₁ r₂ : Row) :
    Bool :=
  match d.sig.mergeOf r₁.fn with
  | some (.merge _ _) =>
    r₁.args != r₂.args && r₁.fn == r₂.fn && congrKeys cl r₁.args r₂.args
      && FDatabase.canonKey cl d.terms r₁.args && !FDatabase.canonKey cl d.terms r₂.args
  | _ => false

/-- One `:merge` firing on a named pair of rows, if it applies, with `old` and `new`
bound the way egglog binds them.

`mergeOneOriented` does the work on a pair whose second element is the row already in
the table. This picks that pair. If exactly one of the two keys is canonical, its row is
the resident one and so is `old`, whichever was written first. Otherwise — the keys are
equal, or neither is canonical — the argument order decides, and `mergeRound` passes the
older row second, which is egglog's tie-break: rows it re-inserts arrive in table order,
so the oldest is the one the rest are merged onto.

Both orders are `MergeStep.collide` premises, so either choice refines the spec
(`Proofs/Merge.lean`, `mergeOneWith_mergeStep`); this is the one that agrees with the
binary. Getting it wrong is invisible to a commutative merge, which is why the suite
stayed green through two different wrong answers — first `old` and `new` swapped
outright, then bound by insertion age. `DiffTest.lean`'s `canon-*` cases pin it. -/
def FDatabase.mergeOneWith (cl : Finset (Term × Term)) (d : FDatabase) (r₁ r₂ : Row) :
    Option FDatabase :=
  if FDatabase.swapForCanon cl d r₁ r₂ then d.mergeOneOriented cl r₂ r₁
  else d.mergeOneOriented cl r₁ r₂

/-- `mergeOneWith` at `d`'s own closure. -/
def FDatabase.mergeOne (d : FDatabase) (r₁ r₂ : Row) : Option FDatabase :=
  FDatabase.mergeOneWith d.closureF d r₁ r₂

/-- Whether any row belongs to a function with a `:merge` body — the cheap test that
keeps a constructor-only database out of the closure entirely. -/
def FDatabase.hasMergeRow (d : FDatabase) : Bool :=
  d.rows.any fun r => match d.sig.mergeOf r.fn with
    | some (.merge _ _) => true
    | _ => false

/-- One pass of the merge phase: a **rebuild**, then every ordered pair of *distinct* rows
it leaves, fired once, left to right.

**The rebuild comes first and is part of the pass**, which is where egglog puts it: a
round canonicalizes the tables and then resolves what the canonicalization collided. Two
consequences the code depends on. The pairwise fold ranges over the *rebuilt* rows, so
every `:merge` key it compares is canonical and `congrKeys` mostly degenerates to
equality — `swapForCanon` is left in place for the rows a merge body writes during the
pass, which no rebuild has seen yet. And `settled` sees the rebuild, so a pass that only
re-keys still counts as progress and `mergeSaturateF` runs another; `rebuild` is
idempotent, so that terminates.

**Not** saturation. Structurally terminating, so it needs neither fuel nor a termination
witness, and sound because `CmdStep` ends in a `MergeClosure` with no `MergeSaturated`
requirement — a prefix of the closure is still a reachable state.

**Position in `rows` is insertion age, and the pair reaches `mergeOneWith` youngest
first.** `addRow` prepends, so the earlier of two rows in `d.rows` is the more recently
written one, and this scans from the front: the first firing of a key class has `r₁`
before `r₂` and therefore `r₁` newer. That is the tie-break `mergeOneWith` falls back on
when key canonicity does not decide, and it is the only thing the argument order means —
egglog binds `old` by canonicity first, so `mergeOneWith` may hand the pair on swapped.

Three ways this fires a strict subset of what `MergeStep` allows, all deliberate and all
sound for the same reason.

**A collision that changes no value column takes no step at all**, because egglog takes
none — `mergeOneOriented`'s `noConflict` drops the arriving row and runs nothing. This is
the one of the three that is about *fidelity* rather than about cost: over-firing here is
observable, since a body writes.

**Self-collisions are skipped.** `MergeStep` has no `a ≠ b` guard, on purpose: without it
the spec would *under*-approximate egglog (`MERGE.md`, "No guard on the collision"). An
interpreter is under no such obligation — firing fewer steps still lands on a reachable
state — and egglog merges a retained row against an incoming staged one, so it never
self-merges either. What they produce is a row `Cong` already derives, so nothing is
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
nothing else. -/
def FDatabase.mergeRound (d : FDatabase) : FDatabase :=
  if !d.hasMergeRow then d else
    let cl := d.closureF
    let e := FDatabase.rebuild cl d
    e.rows.foldl (fun acc r₁ =>
      e.rows.foldl (fun acc' r₂ =>
        if r₁ == r₂ then acc'
        else match FDatabase.mergeOneWith cl acc' r₁ r₂ with
          | some acc'' => acc''
          | none => acc') acc) e

/-! ### Running -/
/-- Whether a merge pass changed anything. Compares the decidable fields; `sig` is a
function and `env`/`rules` a merge cannot touch. -/
def FDatabase.settled (d : FDatabase) : Bool := d.sameData d.mergeRound

/-- Merge saturation, for the record. Takes a **termination witness**, not fuel: being
undefined for a signature whose merges diverge is what egglog does too, where fuel would
return a half-merged database and present it as an answer. Kept as the faithful shape;
`execCmdM` runs `mergeSaturateF` instead, which fails rather than returning a prefix. -/
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

/-! ### Running

`Impl/Interp.lean`'s `exec` never calls `mergeRound`, so before `execM` existed the merge
implementation had **no** differential coverage at all: `mergeOne` and `mergeRound` were
unreachable from `Program.expectedSizes`. `execM` is the composition that reaches them.

Everything below the merge phase is `Impl/Interp.lean`'s, unchanged. `patternHolds`
already resolves primitives in a row atom's operands, because `Expr.eval` does; and
`execRunRules` already reads every rule off the pre-state, which is where the merge phase
must *not* be — egglog defers it until every rule has been searched, so no rule sees
another's merged value within a round. -/
/-- One round of `R`: rule firing, then a merge phase run to a fixpoint. `Spec/Step.lean`'s
`RunStep`, computed.

The phase runs to a **fixpoint**, as `merge_all` does, which is only possible because the
implementation deletes the rows it merged — `mergeRound`'s docstring has that argument. -/
def FDatabase.runRoundM (R : RulesetName) (d : FDatabase) : Option FDatabase :=
  FDatabase.mergeSaturateF mergeFuel (execRunRules R d)

/-- Rounds of `R` until nothing changes: `Impl/Interp.lean`'s `runSaturateF` with a merge
phase inside each round. Two ways to fail — the merge phase of a round diverges, or the
rounds do. -/
def FDatabase.runSaturateM (R : RulesetName) : Nat → FDatabase → Option FDatabase
  | 0, d => (d.runRoundM R).bind fun e => if d.sameData e then some d else none
  | n + 1, d => (d.runRoundM R).bind fun e =>
      if d.sameData e then some d else FDatabase.runSaturateM R n e

/-- `CmdStep`, computed.

Both `.action` and a run end in a merge phase, which is egglog's shape and not a choice:
top-level actions go through the same staging path as a rule head, so **each top-level
`set` is its own merge phase** (`src/lib.rs:1490-1512`). Without that, the three top-level
`set`s of a difftest case would collide only at the next `(run 1)`. -/
def FDatabase.execCmdM (d : FDatabase) : Cmd → Option FDatabase
  | .action a => (execAction d a).bind (FDatabase.mergeSaturateF mergeFuel)
  | .rule r => some { d with rules := r :: d.rules }
  | .run R => d.runRoundM R
  | .saturate R => d.runSaturateM R runFuel
  | .decl f dc => some { d with sig := Function.update d.sig f (some dc) }

/-- `ProgramStep`, computed. -/
def FDatabase.execProgramM (d : FDatabase) : Program → Option FDatabase
  | [] => some d
  | c :: cs => (d.execCmdM c).bind fun d' => d'.execProgramM cs

/-- Run a program from the initial database, under the M9 semantics.

On the constructor fragment this is `Impl/Interp.lean`'s `exec`: the two share every
definition below the merge phase, and with no `.merge` function `mergeOne` never fires, so
every merge phase is the identity. It differs exactly where M9 does — each top-level
action and each round ends with `merge_all`. -/
def execM (p : Program) : Option FDatabase := FDatabase.empty.execProgramM p

/-! ### Row counts

`(print-size)` reports one row per distinct *canonical key tuple*, so this counts
congruence classes of keys — not rows and not values.

That is what makes the difftest comparable at all. A merge step writes its combined row at a
key that is already present, so it adds no key class; a merge with an empty action block adds
no row anywhere else either. The count should therefore be invariant under the merge phase —
but that is **not proved**: `mergeRound_rowCount` said it, was false as stated, and is deleted
with its counterexample at `Proofs/Merge.lean`'s deletion note. What holds is the same claim
with the merge result restricted to a term the database already holds, which every generated
case satisfies. It is also why keeping every superseded output — the over-approximation the
whole design rests on — does not inflate the number: three recorded values at one key are
still one row. -/
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
