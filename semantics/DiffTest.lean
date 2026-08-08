import EgglogSemantics.Tests.Egg

/-!
# Differential test case generator

Writes one `.egg` file and one `.expected` file per case. `scripts/difftest.sh` runs
egglog on the former and diffs its `(print-size)` output against the latter.

Two kinds of case, over two fragments. The **curated** ones are the Redex `test.rkt`
programs plus a few variations, so they are only as good as whoever picked them. The
**random** ones are generated from a seed by a fixed linear congruential stream, which is
what removes that selection bias — the `redex-check` analogue the Redex had and this port
did not. Each kind covers both the constructor fragment and M9's `:merge` functions.

One invocation writes one case, so that a generated program which happens to blow up
cannot take the rest of the run down with it; the script applies a timeout per case.

Cases use nullary constructors rather than literals, since egglog's `i64` is a distinct
primitive sort while `Term.lit` shares a sort with applications here (see `Egg.lean`).

**Nothing here may emit a program egglog rejects.** A rejected program is not a failing
case but a missing one, and a generator quietly producing unrunnable programs is the
failure mode this file is written against — it once cost 34 of 60 random cases, when the
fragment still allowed bare variables. `writeCase` checks the one rule the generator could
plausibly break, `set`'s.
-/

open Egglog

/-- A nullary constructor. -/
private def C (f : FnName) : Expr := .app f []

private def add (a b : Expr) : Expr := .app "Add" [a, b]

/-! ### Curated cases -/

private def commuteRule : Rule where
  query := [.expr (add (.var "a") (.var "b"))]
  actions := [.union (add (.var "a") (.var "b")) (add (.var "b") (.var "a"))]

private def swapRule : Rule where
  query := [.expr (add (.var "a") (.var "b"))]
  actions := [.expr (add (.var "b") (.var "a"))]

private def detectRule : Rule where
  query := [.eq (.app "Wrapper" [add (C "One") (C "Two")])
                (.app "Wrapper" [add (C "Two") (C "One")])]
  actions := [.expr (.app "Success" [])]

private def assocRule : Rule where
  query := [.expr (add (add (.var "a") (.var "b")) (.var "c"))]
  actions := [.union (add (add (.var "a") (.var "b")) (.var "c"))
                     (add (.var "a") (add (.var "b") (.var "c")))]

private def curated : List (String × Program) :=
  [ ("actions",
      [.action (.expr (add (C "One") (C "Two"))),
       .action (.union (C "One") (C "One")),
       .action (.letBind "$g" (add (C "Two") (C "Three"))),
       .action (.expr (.app "Wrapper" [.var "$g"]))]),
    ("swap-1", [.action (.expr (add (C "One") (C "Two"))), .rule swapRule, .run]),
    ("swap-2", [.action (.expr (add (C "One") (C "Two"))), .rule swapRule, .run, .run]),
    ("wrapper-1",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run]),
    ("wrapper-2",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run, .run]),
    ("wrapper-3",
      [.action (.expr (.app "Wrapper" [add (C "One") (C "Two")])),
       .rule commuteRule, .rule detectRule, .run, .run, .run]),
    ("assoc-1",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))), .rule assocRule, .run]),
    ("assoc-2",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))),
       .rule assocRule, .run, .run]),
    ("both-2",
      [.action (.expr (add (add (C "One") (C "Two")) (C "Three"))),
       .rule assocRule, .rule commuteRule, .run, .run]),
    ("seed-2", [.rule ⟨[], [.expr (add (C "One") (C "Two"))]⟩, .run, .run]) ]

/-! ### Random cases

A fixed signature — two nullary constructors, one unary, one binary — keeps every
generated program expressible in egglog, where one name may not be used at two arities.
Depths are small on purpose: a rule whose head builds a deep term grows the term set fast,
and the enumerator is |terms| ^ |vars|. -/

private def step (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- A number below `n`, and the advanced seed.

Read off the **high** bits. Bit `k` of a linear congruential generator with a
power-of-two modulus has period `2^(k+1)`, so `s % n` for a small `n` cycles almost
immediately: with `s % 4` every fourth draw agrees, and the merge cases were all emitting
the same `union` because of it. Discarding the low 16 bits is the usual fix. -/
private def pick (n : Nat) (s : Nat) : Nat × Nat :=
  let s := step s
  (s / 65536 % max n 1, s)

/-- A leaf: a nullary constructor, or one of `vars`. -/
private def genLeaf (vars : List Var) (s : Nat) : Expr × Nat :=
  let (i, s) := pick (2 + vars.length) s
  match i with
  | 0 => (C "A", s)
  | 1 => (C "B", s)
  | k => (.var (vars.getD (k - 2) "a"), s)

/-- A ground expression of depth at most `d`. -/
private def genGround : Nat → Nat → Expr × Nat
  | 0, s => genLeaf [] s
  | d + 1, s =>
    let (i, s) := pick 4 s
    match i with
    | 2 =>
      let (e, s) := genGround d s
      (.app "F" [e], s)
    | 3 =>
      let (e₁, s) := genGround d s
      let (e₂, s) := genGround d s
      (.app "G" [e₁, e₂], s)
    | _ => genLeaf [] s

/-- An expression of depth at most `d` whose leaves may be any of `vars`.

Weighted **towards building** rather than uniformly, at one leaf to two `F` to one `G`.
This is what a rule head is drawn from, so it is what decides whether a round's firings
grow the term set or just permute it: the cases worth having are the ones where a rule
matching everything builds a nested term and the next round matches that. Over the default
60 seeds the weighting takes the spread from 32 distinct row-count profiles to 38. -/
private def genOver (vars : List Var) : Nat → Nat → Expr × Nat
  | 0, s => genLeaf vars s
  | d + 1, s =>
    let (i, s) := pick 4 s
    match i with
    | 1 | 2 =>
      let (e, s) := genOver vars d s
      (.app "F" [e], s)
    | 3 =>
      let (e₁, s) := genOver vars d s
      let (e₂, s) := genOver vars d s
      (.app "G" [e₁, e₂], s)
    | _ => genLeaf vars s

/-- An expression whose top is a constructor application.

The model admits a bare variable as a query fact or as an `expr` action — it matches, or
adds, any term — where egglog's grammar does not. The fragment is therefore not a subset
of egglog's language, and the generator has to stay inside the overlap. -/
private def genApp (vars : List Var) (d : Nat) (s : Nat) : Expr × Nat :=
  -- Weighted away from a nullary top: `(A)` as a query matches at most one term, so a
  -- program full of them exercises almost nothing.
  let (i, s) := pick 6 s
  match i with
  | 0 => genLeaf [] s
  | 1 | 2 =>
    let (e, s) := genOver vars d s
    (.app "F" [e], s)
  | _ =>
    let (e₁, s) := genOver vars d s
    let (e₂, s) := genOver vars d s
    (.app "G" [e₁, e₂], s)

mutual

/-- Replace some subterms with variables. -/
private def abstractExpr (vars : List Var) : Expr → Nat → Expr × Nat
  | .app f args, s =>
    let (i, s) := pick 3 s
    match i, vars with
    | 0, v :: vs =>
      let (j, s) := pick (v :: vs).length s
      (.var ((v :: vs).getD j v), s)
    | _, _ =>
      let (args, s) := abstractArgs vars args s
      (.app f args, s)
  | e, s => (e, s)

private def abstractArgs (vars : List Var) : List Expr → Nat → List Expr × Nat
  | [], s => ([], s)
  | e :: es, s =>
    let (e, s) := abstractExpr vars e s
    let (es, s) := abstractArgs vars es s
    (e :: es, s)

end

/-- A pattern got by abstracting some subterms of `src` into variables, keeping `src`'s
root constructor.

Abstracting a term the program actually builds is what makes the rule fire: a freely
generated pattern of this shape almost never matches anything, which showed up as most
generated programs producing no rows beyond their seeded terms. Keeping the root is what
keeps it a legal egglog fact. -/
private def genPattern (vars : List Var) (src : Expr) (s : Nat) : Expr × Nat :=
  match src with
  | .app f args =>
    let (args, s) := abstractArgs vars args s
    (.app f args, s)
  | e => (e, s)

/-- A rule whose body is abstracted from `src`. The head is built only over variables the
body binds, so every generated program is well-scoped and neither engine rejects it. -/
private def genRule (src : Expr) (s : Nat) : Rule × Nat :=
  let (shape, s) := pick 3 s
  let (p, s) := genPattern ["a", "b"] src s
  match shape with
  | 0 =>
    -- one pattern, head builds a term
    let (a, s) := genApp p.vars 2 s
    (⟨[.expr p], [.expr a]⟩, s)
  | 1 =>
    -- one pattern, head unions two terms; `union` operands may be bare variables
    let (a₁, s) := genOver p.vars 2 s
    let (a₂, s) := genOver p.vars 2 s
    (⟨[.expr p], [.union a₁ a₂]⟩, s)
  | _ =>
    -- an equality body, so matching has to go through congruence
    let (q, s) := genPattern ["a", "b"] src s
    let (a, s) := genApp (p.vars ∪ q.vars) 2 s
    (⟨[.eq p q], [.expr a]⟩, s)

private def genProgram (s : Nat) : Program :=
  let (g₁, s) := genGround 2 s
  let (g₂, s) := genGround 3 s
  let (g₃, s) := genGround 3 s
  let (r₁, s) := genRule g₂ s
  let (r₂, s) := genRule g₃ s
  let (rounds, _) := pick 3 s
  -- The model keeps rules in a `Set` and so ignores a repeat; egglog panics on one.
  -- Compare the rendered form, there being no decidable equality on `Rule`.
  let rules := if r₁.toEgg = r₂.toEgg then [Cmd.rule r₁] else [Cmd.rule r₁, Cmd.rule r₂]
  [.action (.expr g₁), .action (.expr g₂), .action (.expr g₃)] ++ rules
    ++ List.replicate (rounds + 1) Cmd.run

/-! ### `:merge` cases (M9)

The first empirical check on M9. Every generated merge is a **join** — `min`/`max` on
`i64` — for a reason: our reads over-approximate, so a non-idempotent merge would give
extra firings and extra values, and a row-count difference would be this model's design
showing rather than a real bug.

Merge functions here are written and never read. A body atom reading one would bind the
variable to *any* recorded output, where egglog binds the current one, so the model would
fire more and build more. That is the fragment's boundary, and it is where the
over-approximation would first become observable.

`min-rebuild` is the case that matters: unioning the keys makes two `Dist` rows collide,
so egglog's table drops from two rows to one. It is the shape of
`egglog/tests/merge-during-rebuild.egg`, with nullary constructors in place of `(Node
i64)`. Row counts see it because they count *key classes*, which is also why the
interpreter need not saturate merges to predict them.
-/

private def dist (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [] [.app "min" [.var "old", .var "new"]] }

private def distMax (n : Nat) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [] [.app "max" [.var "old", .var "new"]] }

/-- The same join, written as egglog's **action block** — `let`-bind the combined value,
then return it.

Worth a case of its own because the emitter's block branch had never been exercised: all
seven original merge cases are `:merge (min old new)`, which takes the expression branch.
The block branch emitted two nested lists where egglog wants the actions and the result as
siblings, so every program using it was a parse error.

Bodies stay `let`-only. A body that `set`s a side table is where our over-approximation
becomes observable — a row collides with itself and both orders fire — so the side
table's row count would diverge by design rather than by defect. -/
private def distBlock (n : Nat) (op : FnName) : FnDecl :=
  { arity := n, outArity := 1,
    merge := .merge [.letBind "s" (.app op [.var "old", .var "new"])] [.var "s"] }

/-- `:no-merge`: a collision is an error rather than a resolution
(egglog panics with "Illegal merge attempted for function Dist"), so a case using it must
keep its keys distinct. Inert in the model, since `MergeStep` fires only on `.merge`. -/
private def distNoMerge (n : Nat) : FnDecl :=
  { arity := n, outArity := 1, merge := .noMerge }

private def num (n : Int) : Expr := .lit (.int n)

private def mset (f : FnName) (args : List Expr) (v : Int) : Cmd :=
  .action (.set f args [num v])

/-- A rule that copies a `Dist` entry onto the commuted key, so a merge fires from a rule
head as well as from a top-level action. -/
private def commuteDist : Rule where
  query := [.expr (.app "G" [.var "a", .var "b"])]
  actions := [.set "Dist" [.var "b", .var "a"] [num 9]]

/-! ### Multi-column outputs

`Row.out`, `Database.addRow`, `Database.Out` and `MergeSpec`'s result were multi-column
from the start; `Action.set` and `Pattern` were not, so a two-column row could be created
by a merge and never written or read. Both are now widened, and these are the cases that
exercise it — egglog's `(function f (Math) (i64 i64) …)`, `(set (f k) (values a b))` and
the tuple destructure `(= (values a b) (f k))`.

**What the oracle can and cannot see.** `(print-size)` reports one row per canonical *key*
tuple and is blind to value columns, so a row-count comparison validates that egglog
accepts the declaration, the two-column `set` and the destructure, and that the key classes
agree — it does not validate the merged values. `tuple-read` closes half of that gap
without a new oracle: its rule guards on *literal* value columns, so whether it fires is
observable in the count of the constructor its head builds. The other half — the merged
value after a real collision — is not observable through `print-size` at all, and needs
`(check (= (values …) …))`, which is a different oracle and a `Cmd.check` this fragment
does not have. -/
/-- A two-column merge function: `min` on column 0, `max` on column 1, which is what
`mergeEnvIdx`'s `old0`/`new0`/`old1`/`new1` naming is for. Emitted as
`(function Dist (Math…) (i64 i64) :merge (values (min old0 new0) (max old1 new1)))`. -/
private def distPair (n : Nat) : FnDecl :=
  { arity := n, outArity := 2,
    merge := .merge [] [.app "min" [.var "old0", .var "new0"],
                        .app "max" [.var "old1", .var "new1"]] }

private def pset (f : FnName) (args : List Expr) (v w : Int) : Cmd :=
  .action (.set f args [num v, num w])

/-- Reads a two-column row and builds a term from its *key*, gated on both value columns
being the literals written. Whether the rule fired is therefore visible in `Hit`'s row
count, which is what makes the value columns observable through `(print-size)`.

The keys are kept distinct so no merge ever fires on the guarded row. That is deliberate
and it is the fragment boundary `MERGE.md` draws: this model keeps every superseded output
where egglog deletes it, so after a collision a guard on the *pre-merge* value fires here
and not there. `MERGE.md`, "What the widening and the composed interpreter found", has the
minimal repro. -/
private def readPair : Rule where
  query := [.values [num 3, num 4] "Dist" [.var "k"]]
  actions := [.expr (.app "Hit" [.var "k"])]

/-! ### Reading a `:merge` function from a rule body

`MERGE.md` calls this the difftest fragment's boundary: every merge case so far *writes*
`Dist` and queries only constructors, so `Expr.MEval.lookup` — reachable through `execM`
from `MValidSubst.expr` — had **no coverage at all**. That is the shape of the `min`/`max`
bug: a path the suite exercised zero times while the pass count said everything was fine.

Reading an analysis function in a rule body is ordinary egglog. Three shapes, all checked
against the binary:

* `(rule ((Dist k)) …)` — existence. The value does not matter, so this agrees whatever
  the model does with superseded rows.
* `(rule ((= 3 (Dist k))) …)` — the value, with no collision. Also agrees.
* `(rule ((= 5 (Dist k))) …)` after a collision that merged `5` away — this is where
  keeping superseded rows shows. -/
/-- Existence: fires once per key class holding a row. -/
private def readExists : Rule where
  query := [.expr (.app "Dist" [.var "k"])]
  actions := [.expr (.app "Hit" [.var "k"])]

/-- The value: fires only where the recorded output is `3`. -/
private def readValue (v : Int) : Rule where
  query := [.eq (num v) (.app "Dist" [.var "k"])]
  actions := [.expr (.app "Hit" [.var "k"])]

/-- The two-column acceptance test's rule: guarded on the *pre-merge* value tuple. -/
private def readStale : Rule where
  query := [.values [num 5, num 1] "Dist" [.var "k"]]
  actions := [.expr (.app "Hit" [.var "k"])]

private def curatedMerge : List (String × Program) :=
  [ -- One key, three writes: min wins, and the table still holds one row.
    ("min-one",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       mset "Dist" [C "A"] 7]),
    -- Two distinct keys stay two rows.
    ("min-two",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 5, mset "Dist" [C "B"] 3]),
    -- `merge-during-rebuild`: unioning the keys collapses two rows into one.
    ("min-rebuild",
      [.decl "Dist" (dist 2),
       mset "Dist" [C "X", C "Y"] 1, mset "Dist" [C "A", C "B"] 2,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run]),
    -- The same collapse, with `max`.
    ("max-rebuild",
      [.decl "Dist" (distMax 2),
       mset "Dist" [C "X", C "Y"] 1, mset "Dist" [C "A", C "B"] 2,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run]),
    -- A congruence-driven collapse: the keys become equal through `G`, not directly.
    ("min-congr",
      [.decl "Dist" (dist 1),
       .action (.expr (.app "G" [C "A", C "B"])),
       .action (.expr (.app "G" [C "X", C "Y"])),
       mset "Dist" [.app "G" [C "A", C "B"]] 4,
       mset "Dist" [.app "G" [C "X", C "Y"]] 6,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run]),
    -- A rule head writing a row, so the merge fires from a firing rather than an action.
    ("min-rule",
      [.decl "Dist" (dist 2),
       .action (.expr (.app "G" [C "A", C "B"])),
       .action (.expr (.app "G" [C "B", C "A"])),
       mset "Dist" [C "B", C "A"] 2,
       .rule commuteDist, .run]),
    -- No merge fires at all: the declaration is inert, which the counts must show.
    ("min-inert",
      [.decl "Dist" (dist 1), .action (.expr (.app "F" [C "A"])),
       mset "Dist" [C "A"] 1]),
    -- `min-one` with the merge written as an action block, which is a different parse.
    ("min-block",
      [.decl "Dist" (distBlock 1 "min"), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       mset "Dist" [C "A"] 7]),
    -- An action block resolving a collision the keys only acquire through a union.
    ("max-block-rebuild",
      [.decl "Dist" (distBlock 2 "max"),
       mset "Dist" [C "X", C "Y"] 1, mset "Dist" [C "A", C "B"] 2,
       .action (.union (C "A") (C "X")), .action (.union (C "B") (C "Y")), .run]),
    -- `:no-merge`, with keys kept distinct so no collision is ever attempted.
    ("nomerge-two",
      [.decl "Dist" (distNoMerge 2), .action (.expr (.app "F" [C "A"])),
       mset "Dist" [C "A", C "B"] 1, mset "Dist" [C "B", C "A"] 2]),
    -- Two value columns, two distinct keys: the declaration, the `(values …)` merge and
    -- the two-column `set` all have to parse and typecheck for this to run at all.
    ("tuple-two",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 3 4, pset "Dist" [C "B"] 5 6]),
    -- The same, plus a collision on one key. Only the key classes are compared — see the
    -- note above on what `(print-size)` can see.
    ("tuple-merge",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 5 1, pset "Dist" [C "A"] 3 7,
       pset "Dist" [C "B"] 2 2]),
    -- A rule *reading* a two-column row through the destructure, gated on both value
    -- columns. `Hit` is 1 iff the read bound the columns the `set` wrote.
    ("tuple-read",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 3 4, pset "Dist" [C "B"] 5 6,
       .rule readPair, .run]),
    -- The destructure through congruent keys: `A` and `X` become one class, so the row
    -- written at `X` is readable at `A`.
    ("tuple-read-congr",
      [.decl "Dist" (distPair 1), pset "Dist" [C "X"] 3 4,
       .action (.expr (C "A")), .action (.union (C "A") (C "X")),
       .rule readPair, .run]),
    -- A rule body *reading* a single-column `:merge` function: existence only.
    ("read-exists",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 3, mset "Dist" [C "B"] 5,
       .rule readExists, .run]),
    -- The same, reading the value, with the keys distinct so no merge fires.
    ("read-value",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 3, mset "Dist" [C "B"] 5,
       .rule (readValue 3), .run]),
    -- **The acceptance test, single column.** `5` is merged away by `min`, so egglog's
    -- table no longer holds it and the rule must not fire.
    ("read-stale",
      [.decl "Dist" (dist 1), mset "Dist" [C "A"] 5, mset "Dist" [C "A"] 3,
       .rule (readValue 5), .run]),
    -- **The acceptance test, two columns.** The repro that was recorded in `MERGE.md` as
    -- a known divergence: egglog says `Hit 0`, and an append-only implementation says
    -- `Hit 1` because the superseded row is still readable.
    ("tuple-stale",
      [.decl "Dist" (distPair 1), pset "Dist" [C "A"] 5 1, pset "Dist" [C "A"] 3 7,
       .rule readStale, .run]) ]

/-! ### Random `:merge` cases

The curated merge cases are only as good as whoever picked them — the caveat the
constructor cases carried until they were randomized, and the same fix. These draw a
merge function's arity and its merge spec from the same seeded stream, write rows at
generated keys, and union constructors underneath those keys, which is what makes keys
collide and so what the counts actually discriminate on.

The fragment stays the one `MERGE.md` describes, and both narrowings are justified by the
model rather than by convenience:

* **Every drawn merge is a join** (`min`/`max`). A non-idempotent one diverges under our
  over-approximating reads *by design* — a row collides with itself, so `:merge (+ old
  new)` derives `2v`, `3v`, … — so a difference would be the design showing, not a bug.
* **Bodies are `let`-only.** A body that `set`s a side table would fire on self-collisions
  and in both orders, inflating that table's count against egglog's for the same reason.
* **Merge functions are written and never read**, since a body atom reading one binds any
  recorded output where egglog binds the current one.

Keys are eq-sorted and outputs are `i64`, as the curated cases already are. -/

/-- The merge specs the generator draws from: `min` and `max`, each in the expression form
and in the action-block form. -/
private def genMergeSpec (s : Nat) : MergeSpec × Nat :=
  let (i, s) := pick 4 s
  let combined : Expr := .app (if i % 2 == 0 then "min" else "max") [.var "old", .var "new"]
  if i < 2 then (.merge [] [combined], s)
  else (.merge [.letBind "s" combined] [.var "s"], s)

/-- `n` ground key expressions. Shallow: a key is a term like any other, so a deep one
inflates the term set the enumerator squares. -/
private def genKeys : Nat → Nat → List Expr × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (e, s) := genGround 1 s
    let (es, s) := genKeys k s
    (e :: es, s)

/-- `n` key expressions over `vars`, for a `set` in a rule head. A bare variable is fine
in an *argument* position — the ban is on a bare variable as a whole query fact or a whole
`expr` action, which is where egglog's grammar stops. -/
private def genKeysOver (vars : List Var) : Nat → Nat → List Expr × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (e, s) := genOver vars 1 s
    let (es, s) := genKeysOver vars k s
    (e :: es, s)

/-- A rule writing a `Dist` row, so a merge fires from a firing and not only from a
top-level action. The body is abstracted from a term the program builds, so it fires. -/
private def genMergeRule (arity : Nat) (src : Expr) (s : Nat) : Rule × Nat :=
  let (p, s) := genPattern ["a", "b"] src s
  let (ks, s) := genKeysOver p.vars arity s
  let (v, s) := pick 9 s
  (⟨[.expr p], [.set "Dist" ks [num v]]⟩, s)

/-- A rule *reading* `Dist` from its body, in one of the two shapes egglog offers for a
single-column function: the bare atom `(Dist k…)` (existence) or `(= v (Dist k…))` (the
value). Its head builds a `Hit`, so whether and how often it fired is visible in
`(print-size)`.

This is the path `MERGE.md` called the fragment boundary — "merge functions are written
and never read" — and leaving it there meant `Expr.MEval.lookup`, reachable through
`execM` from `MValidSubst.expr`, had **no** coverage. Reading an analysis function in a
rule body is ordinary egglog, so there was no reason for the boundary except that nothing
had run the merge implementation. -/
private def genMergeReadRule (arity : Nat) (src : Expr) (s : Nat) : Rule × Nat :=
  let (p, s) := genPattern ["a", "b"] src s
  let (ks, s) := genKeysOver p.vars arity s
  let (v, s) := pick 9 s
  let (shape, s) := pick 2 s
  let body : Query :=
    if shape = 0 then [.expr p, .expr (.app "Dist" ks)]
    else [.expr p, .eq (num v) (.app "Dist" ks)]
  (⟨body, [.expr (.app "Hit" [p])]⟩, s)

private def genMergeProgram (s : Nat) : Program :=
  let (a, s) := pick 2 s
  let arity := a + 1
  let (spec, s) := genMergeSpec s
  let (g, s) := genGround 2 s
  let (k₁, s) := genKeys arity s
  let (k₂, s) := genKeys arity s
  let (k₃, s) := genKeys arity s
  let (v₁, s) := pick 9 s
  let (v₂, s) := pick 9 s
  let (v₃, s) := pick 9 s
  let (u₁, s) := genGround 1 s
  let (u₂, s) := genGround 1 s
  let (r, s) := genMergeRule arity g s
  let (rr, s) := genMergeReadRule arity g s
  let (rounds, _) := pick 2 s
  [ .decl "Dist" { arity := arity, outArity := 1, merge := spec },
    .action (.expr g),
    .action (.set "Dist" k₁ [num v₁]),
    .action (.set "Dist" k₂ [num v₂]),
    .action (.set "Dist" k₃ [num v₃]),
    .action (.union u₁ u₂),
    .rule r, .rule rr ] ++ List.replicate (rounds + 1) Cmd.run

/-! ### Entry point -/

/-- Write one case, refusing outright to emit a program egglog would reject.

The one rule the generator can plausibly break is `set`'s: `(set (f args…) v)` is legal
only on a declared function, and is a *type* error on a constructor or a relation. A
rejected program is not a failing case but a missing one, and a generator that quietly
stops producing runnable programs is the failure this whole file is written against — so
the check is an abort, not a skip. `Program.illegalSets` states it. -/
private def writeCase (dir name : String) (p : Program) : IO Unit := do
  unless p.illegalSets.isEmpty do
    throw <| IO.userError
      s!"difftest: {name} sets {p.illegalSets}, which egglog rejects: only a function \
         declared with :merge or :no-merge may be set"
  IO.FS.writeFile s!"{dir}/{name}.egg" p.toEgg
  IO.FS.writeFile s!"{dir}/{name}.expected" p.expectedSizes

/-- `difftest <dir> curated` writes the curated cases, `difftest <dir> merge` the curated
`:merge` ones; `difftest <dir> seed <n>` writes one random constructor case named
`rand-<n>` and `difftest <dir> mergeseed <n>` one random `:merge` case named `mrand-<n>`.
The two random families are named apart so the script can report a profile distribution
for each — a collapsing distribution is how a generator that has stopped exercising
anything shows up, and a single pooled number would hide it. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [dir, "curated"] =>
    IO.FS.createDirAll dir
    for (name, p) in curated do writeCase dir name p
    IO.println s!"wrote {curated.length} curated cases"
    return 0
  | [dir, "merge"] =>
    IO.FS.createDirAll dir
    for (name, p) in curatedMerge do writeCase dir name p
    IO.println s!"wrote {curatedMerge.length} merge cases"
    return 0
  | [dir, "seed", n] =>
    match n.toNat? with
    | none => IO.eprintln s!"difftest: bad seed {n}"; return 1
    | some k =>
      IO.FS.createDirAll dir
      writeCase dir s!"rand-{n}" (genProgram (k + 1))
      return 0
  | [dir, "mergeseed", n] =>
    match n.toNat? with
    | none => IO.eprintln s!"difftest: bad seed {n}"; return 1
    | some k =>
      IO.FS.createDirAll dir
      writeCase dir s!"mrand-{n}" (genMergeProgram (k + 1))
      return 0
  | _ =>
    IO.eprintln "usage: difftest <dir> curated | merge | seed <n> | mergeseed <n>"
    return 1
