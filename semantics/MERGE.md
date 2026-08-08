# `:merge` functions (M9)

Design for generalizing the semantics from "every function is a constructor and
congruence is `Cong`" to "a function carries a `:merge`". Revises `PLAN.md`'s M9
section, which is kept for the record; where they disagree this document is current.

**Status.** The compatibility theorem is **proved**. `Spec/Merge.lean` and
`Impl/Merge.lean` are definitions; of the 22 theorems `Proofs/Merge.lean` originally left
unproved, 17 are now proved and 5 remain — `MergeStep.diamond_of_join`,
`RunStep.unique_of_confluent`, `execM_reachable`, `mergeRound_closure` and
`FDatabase.mergeRound_rowCount`. Four of the 22 statements were **wrong** and are recorded
where they are stated; see "What the widening and the composed interpreter found".
Curated `:merge` cases run in the differential test against real egglog alongside the
constructor cases. Nothing in M0–M10 changed except `MergeSpec` and `FnDecl` in
`Spec/Syntax.lean`, and later `Action.set` and `Pattern` for multi-column outputs.

Facts about egglog's real behaviour are cited to the Rust. Guesses are flagged
**[guess]**.

## The one-paragraph version

The state gains a **row set**: `⟨f, args, out⟩` says `f` records the value columns
`out` at `args`. For a constructor there is one column and it holds the application
itself, so `Database` embeds. Congruence and the functional
dependency then become *one inductive rule*, `MCong.fd`, and `Cong.congr` is that rule
read at constructor rows — the compatibility theorem. A `:merge` body is an action
list, so resolving a collision is a *step relation on databases*, `MergeStep`, not a
value combiner; both colliding rows survive, which is what keeps the state monotone.
Because a non-constructor application is a **lookup** and a key class can record
several outputs, `Expr.eval` becomes the relation `Expr.MEval`, and everything
downstream of it — actions, rule firing, `run` — becomes a relation too. That last
consequence is the biggest one and it was not in `PLAN.md`.

## The framing: invariants over a step relation

Everything below is shaped by what M11 actually needs. The headline theorem — *every
proof row the encoding writes is accepted by the checker* — is an **invariant** over
the step relation:

```lean
theorem invariant_of_step {I : MDatabase → Prop}
    (hstep : ∀ db c db', I db → CmdStep db c db' → I db')
    (hinit : I db) (h : ProgramStep db p db') : I db'
```

That is four lines and it is proved. An invariant needs **neither termination nor
confluence**: it holds at every reachable state, so a run that diverges satisfies it
throughout, and a run that merges in a different order satisfies it too.

So the spec is kept simple and **over-approximating**, and everything needed only to
match egglog *exactly* is moved out of the core into a hypothesis on the theorems that
want it. Concretely: a lookup reads *any* recorded output rather than the current one, a
round takes *any number* of merge steps rather than all of them, and a row collides with
itself. The spec therefore reaches every state egglog reaches, plus some egglog does not.

Over-approximation has to be **unconditional** to be worth anything. Any place the spec
under-approximates is a hole: egglog reaches a state the model never checks, so the
invariant does not transfer. That criterion is what removed the last side condition, the
`a ≠ b` collision guard — see "No guard on the collision". The design now has no
signature-level scope condition on the safety theorem at all.

Two things make this sound rather than merely convenient.

* **Append-only rows.** Term rows and proof rows are never deleted, from anything. So
  every recorded proof is valid and *stays* valid, and reading a stale one yields a
  different proof of the same fact — never an invalid one. The safety theorem needs no
  well-behavedness hypothesis at all.
* **Order-dependent merges are the user's fault.** A merge that is not a lattice join
  has no order-independent answer; egglog itself calls that "user-visible undefined
  behavior" (`egglog-backend-trait/src/lib.rs:46-48`). A semantics that declines to pin
  an order the programmer never specified is arguably the more honest one. This belongs
  beside `PLAN.md`'s naive-vs-seminaive note, and is recorded there too.

The two places that *do* need to match egglog — differential testing and M11's
simulation theorem — take `MergeSaturated` and a join condition as hypotheses.

## Representation

```lean
structure Row where
  fn : FnName
  args : List Term
  out : List Term                -- one entry per value column

structure MDatabase where
  sig   : Signature
  terms : Set Term
  rows  : Set Row                -- new
  eqs   : Set (Term × Term)
  env   : Env
  rules : Set Rule
```

`terms` stays. It is **not** derivable from `rows`: a literal is a term with no row,
and `MCong.refl`'s side condition — the thing that makes the e-matching witness bite —
reads `terms`. `eqs` stays too, because a `union` action relates two arbitrary terms
and is not a row.

Building a term writes its constructor rows:

```lean
def Term.ctorRows (t : Term) : Set Row :=
  {r | r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ t.subterms}
def MDatabase.build (t : Term) (db : MDatabase) : MDatabase :=
  { db with terms := db.terms ∪ t.subterms, rows := db.rows ∪ t.ctorRows }
```

`ctorRows` needs no signature because a `Term` only ever contains *constructor*
applications — `Expr.MEval` resolves a merge function's application to its recorded
output, so `(g 1)` never survives into a term. That is a small invariant with a lot of
weight; see "Base sorts" for where it is fragile.

The embedding is the M9-shaped view of an M2 database:

```lean
def Database.toM (db : Database) : MDatabase :=
  { …, rows := {r | r.out = [.app r.fn r.args] ∧ Term.app r.fn r.args ∈ db.terms} }
```

## Congruence is the functional dependency

`MCong` is `Cong` with the `congr` constructor **deleted** and one new constructor in
its place:

```lean
| fd {f : FnName} {as bs a b : List Term} {x y : Term} :
    ⟨f, as, a⟩ ∈ db.rows → ⟨f, bs, b⟩ ∈ db.rows →
    db.sig.mergeOf f = MergeSpec.union → MCongList db as bs →
    (x, y) ∈ a.zip b → MCong db x y
```

One rule, three readings:

* constructor rows, congruent keys → `Cong.congr`;
* constructor rows, *equal* keys → `Cong.refl` on an application;
* any `.union` function → "one key, one output" — the functional dependency.

The `zip` premise makes it per *column*, so a multi-column `.union` function equates
its outputs positionally. See "Multi-column outputs" for why that costs nothing.

The compatibility theorem, in `Proofs/Merge.lean`, **proved** — `#print axioms` reports
`propext` as its only axiom:

```lean
theorem mcong_iff_cong {db : Database} (hsig : db.sig.AllConstructors)
    (hrows : db.CtorRows) {a b : Term} : MCong db a b ↔ Cong db a b
```

#### What became of `mcong_toM_iff`

It was `MCong db.toM a b ↔ Cong db a b`, where `Database.toM` embedded an M2 database
into a separate `MDatabase`. Now that the two states are **one structure**, that
embedding is the identity and the theorem as stated would have no content — so the
hypothesis carries what the embedding used to:

```lean
def Database.CtorRows (db : Database) : Prop := db.rows = ctorRowsOf db.terms
```

`toM` produced exactly the constructor rows; `CtorRows` *says* the rows are exactly
those. The theorem's content, its proof (the same four `match` cases), and its axiom set
are unchanged — only the way the constructor-only fragment is named. `CtorRows` is true
of `Database.empty`, preserved by `addTerm` and `addEq`, and false as soon as a `set`
writes a `:merge` function's row, which is the right boundary.

Both directions are a `match`-recursion in a `mutual theorem` block, four lines each, with
the `fd`/`congr` case the only interesting one. One idiom was needed twice: `obtain ⟨rfl,
_⟩` on a row membership fails, because the row's `out` field appears under unreduced
projections (`{fn := f, args := as, out := a}.args`) so `subst` sees `a` occurring in its
own definition. Routing through `Database.toM_row_iff` — which is `Iff.rfl` but *states*
the reduced form — fixes it. That is the same class of trap as the `rw`-needs-a-bridge-lemma
one already recorded.

Two directions with different hypotheses, which is itself informative. `MCong → Cong`
holds for **any** signature, because a row of the embedding is a constructor row
whatever the signature says. `Cong → MCong` needs `AllConstructors`, which is what
licenses `fd`. Congruence is recovered as a derived rule rather than a constructor:

```lean
theorem MCong.congr (ha : Row.mk f as [.app f as] ∈ db.rows)
    (hb : Row.mk f bs [.app f bs] ∈ db.rows)
    (hsig : db.sig.mergeOf f = MergeSpec.union) (hl : MCongList db as bs) :
    MCong db (.app f as) (.app f bs) := .fd ha hb hsig hl (by simp)
```

`Signature.mergeOf` defaults an **undeclared** name to `.union`, so M0–M8 — where
nothing declares anything — is *literally* the all-constructors case rather than
merely analogous to it. That is the whole reason the theorem is a refactor licence
instead of a fresh development. There is a step-side companion,
`MergeStep.saturated_of_allConstructors`, also proved: with no `.merge` function there is
no collision to resolve, so a round is `MRunRules` and nothing else. Together the two say
M9 restricted to constructors is M0–M8 unchanged — no longer a conjecture, so the 2244
lines in `Proofs/` transport.

**A merge function's applications get no congruence at all.** `fd` requires `.union`.
Two `@UF_Math` rows with congruent keys do not make their parents equal *by
congruence*; they make them equal because the merge body says so, which is a step. A
`.union` collision is the only one whose whole effect is an equality between terms
that already exist, so it is the only one a relation can express. That is the line the
whole design is drawn along.

## Constraint (1): a `:merge` body is an action

This is the constraint that decides the shape, and it is real, not internal-only.

**What egglog does.** The AST is `GenericMerge { actions: GenericActions, result:
GenericExpr }` (`egglog-ast/src/generic_ast.rs:45-57`); the field on a declaration is
`merge: Option<GenericMerge<…>>` and is *required* (`src/ast/parse.rs:585-593`).
Parsing disambiguates syntactically: if the argument is a list whose head is itself a
list it is an action block, otherwise a bare result expression
(`src/ast/parse.rs:531-569`) — so `:merge (max old new)` stays an expression. `:on_merge`
was removed and this replaced it (`CHANGELOG.md:178`, `:42-46`). The action block
admits **exactly `let`, `set`, `union`**; anything else is rejected at lowering with
"action `{other}` is not supported inside a :merge block" (`src/lib.rs:1064-1067`). So
`panic` and `delete` are *not* available, and `set` into another table — or into the
function's own table (`src/lib.rs:1100-1106`) — is. There is a user-facing test,
`tests/merge-action-block.egg`. The union-find's block in `proof_encoding.md` is
ordinary surface syntax.

**The model.** `MergeSpec.merge` carries the pair, and the merge is a relation on
databases:

```lean
inductive MergeSpec where
  | union
  | merge : List RowAction → List Expr → MergeSpec   -- one expression per value column
  | noMerge

inductive MergeStep : MDatabase → MDatabase → Prop where
  | collide {db d f} {as bs a b vs : List Term} {body res} :
      ⟨f, as, a⟩ ∈ db.rows → ⟨f, bs, b⟩ ∈ db.rows → MCongList db as bs →
      db.sig.mergeOf f = MergeSpec.merge body res →
      MDatabase.RowActionsStep { db with env := mergeEnv a b } body d →
      Expr.MEvalList d d.env res vs →
      MergeStep db { d.addRow f as vs with env := db.env, rules := db.rules }
```

Points to review:

* **Nothing is removed.** `db.Contained` the result. The two colliding rows are still
  there afterwards. This is what keeps every monotonicity lemma alive, and it leaves
  the old rows' proofs available for the `@MergeRow` that names them.
* **No guard on the collision** — see the section of that name.
* **The combined row is written at key `as` only.** Reads go through `Out`, which
  quantifies over congruent keys, so the row is visible from `bs` too. This replaces
  egglog's rebuild-driven re-keying of rows: keys are compared up to congruence rather
  than canonicalized.
* **The env is `mergeEnv a b` and nothing else.** A merge body sees the two colliding
  rows' outputs and its own `let`s. Globals are desugared to nullary functions before
  the encoding, so they are lookups, not environment reads. egglog binds `old`/`new`
  for a single-output function and `old0`/`new0`/`old1`/… per value column for a tuple
  output (`src/typechecking.rs:1066-1077`), and `mergeEnv` does both. *Every* column is
  bound, not just the one being computed — `MergeFn::OldCol`/`NewCol` exist precisely
  because "a column's merge may reference any output column of the old row".
* **The body runs once, before any column is computed.** `RowActionsStep` produces `d`
  and every column of `res` is evaluated in `d`. egglog's order, not a choice: "Run the
  block's side effects once, before computing the merged values"
  (`egglog-bridge/src/lib.rs:1433`).
* **Both orders fire.** The two rows are premises in both orders, so a non-commutative
  merge relates `db` to two different results. Deliberate — see "the framing".
* **`RowAction` is a new type**, `Action` plus `set`. `RowAction.MergeLegal` records
  egglog's `{let, set, union}` restriction.

### Why not a value combiner

`PLAN.md` proposed defining the observable value as a merge-fold over the congruent
asserted rows and never having a step at all. That does not survive constraint (1),
for a specific reason worth writing down: **the union-find's merge is all side
effect**. Its value output is `ordering-min old new`, which a fold would get right —
and its `set` of the displaced edge, which is the entire content of the union-find's
transitivity, is invisible to any fold over values. Path compression would have
nothing to compress. The fold is lossy exactly where the encoding puts its meaning.

### One action language — done

An earlier draft had two, `Action` and `RowAction`, as a scope limit. They are now one:
`Action` gained `set` and `RowAction` is gone. M11 forced it — the encoding's *rules*
write `(set (@AddView b a) (values rewrite_var ()))`, so the target language of
`encode : Program → Program` needs `set` in rule heads.

The cost was about what was estimated: 24 match sites across 10 files. What was *not*
anticipated is that it drags the state with it — `evalAction`'s `set` case has nowhere
to put a row unless `Database` has one, so the syntax and state unifications are a
single step, not two.

egglog restricts a `:merge` body to `let`, `set`, `union` while a rule head also has
`panic`, `delete`, `subsume`, `extract` and bare expressions. `Action.MergeLegal`
records the restriction rather than a second type doing it.

## Constraint (2), continued: reading a table

A finding that did not survive first contact with the Rust and is not in `PLAN.md`.

`:default` was removed (`CHANGELOG.md:176`, #461). A missing row now behaves
differently in the two positions:

* **rule body** — `(f x)` is not a lookup at all, it is a join atom
  (`src/core.rs:629-639`). No row means no match, silently.
* **rule action, top-level action, or merge body** — it *is* a lookup. A constructor
  mints a fresh e-class (`DefaultVal::FreshId`); a custom function panics
  (`DefaultVal::Fail`, `src/lib.rs:1122-1125`, `egglog-bridge/src/rule.rs:658-672`).
  `tests/merge_read.egg` is the case.

So `Expr.eval : Expr → Env → Option Term` is no longer enough: evaluation reads the
database, and since a key class may record several outputs it is a **relation**.

```lean
inductive Expr.MEval (db : MDatabase) (σ : Env) : Expr → Term → Prop where
  | lit    : Expr.MEval db σ (.lit l) (.lit l)
  | var    : Env.lookup v σ = some t → Expr.MEval db σ (.var v) t
  | ctor   : Prim.ofName f = none → db.sig.mergeOf f = MergeSpec.union →
             Expr.MEvalList db σ args ts → Expr.MEval db σ (.app f args) (.app f ts)
  | lookup : Prim.ofName f = none → db.sig.mergeOf f ≠ MergeSpec.union →
             Expr.MEvalList db σ args ts → db.Out f ts v → Expr.MEval db σ (.app f args) v
  | prim   : Prim.ofName f = some p → Expr.MEvalList db σ args ts →
             p.apply ts = some v → Expr.MEval db σ (.app f args) v
```

### Why the reader over-approximates

`lookup` reads `Out` — *any* recorded output — rather than the current one. This was
the design's sharpest open question and it is now settled, in favour of
over-approximating, for two reasons.

**A "current value" usually does not exist.** Under `:merge old` (`merge a b = a`)
every recorded output absorbs, so a greatest element is not unique; under `:merge new`
(`= b`) none absorbs, so there is none. Both are ordinary: the encoding's own
`(function @<Sort>Proof (<Sort>) @Proof :merge old)` is the first, and egglog's tests
use `:merge new` widely (`luminal-llama.egg`, `factoring-multisets.egg`). egglog
resolves both by *insertion order*, which a `Set Row` cannot express and which the
`Set` representation was chosen to avoid.

**Over-approximating is sound for proof soundness**, for the append-only reason in
"the framing": reading a stale proof gives a different proof of the same fact, never an
invalid one.

`Current` survives as a derived definition, used only by differential testing and by
M11's simulation theorem — never by `MEval`:

```lean
def MDatabase.Current (db) (le : List Term → List Term → Prop) (f) (as) (vs) : Prop :=
  db.Out f as vs ∧ ∀ ws, db.Out f as ws → le ws vs
```

#### Why a maximum and not a fold

`PLAN.md` asks for the fold to be proved well defined "when the merge is a semilattice
join, using Mathlib's `SemilatticeSup`". A fold over a set is well defined only once the
combiner is proved **commutative and associative**; a greatest element is unique from
**antisymmetry alone**:

```lean
theorem MDatabase.current_unique (hanti : ∀ x y, le x y → le y x → x = y)
    (hv : db.Current le f as v) (hw : db.Current le f as w) : v = w
```

— a three-line proof, already discharged, with no `Finset.fold` well-definedness
argument anywhere. For a `SemilatticeSup` merge the greatest element *is* what the fold
computes, so nothing is lost. `le` is a parameter and not an instance because the order
is per function — one untyped `Term` carries every sort — and it orders whole rows,
since a multi-column merge can settle its columns jointly.

### Other consequences of relational evaluation

1. **`runProgram` stops being a function.** `RowActionStep`, `MRuleResults`,
   `RunStep`, `CmdStep` and `ProgramStep` in `Spec/Merge.lean` are all relations. This
   is no longer treated as a defect to be repaired by a determinism theorem; see "the
   framing".
2. **`Scope.lean` weakens.** `run_isSome` says a well-scoped program never gets stuck.
   With lookups, "never stuck" additionally requires every lookup to hit, which is not
   a scope property and not decidable statically — it is egglog's `Fail` panic. The
   M9 statement is the conditional one: a well-scoped program with no failing lookup
   runs to completion.
3. **`Expr.eval_agree` survives**, since `MEval` still reads the environment only
   through `lookup`.

### Primitives without churning `Expr`

`ordering-min`/`ordering-max` are `Expr.app` of a *reserved name*, resolved by
`Prim.ofName` ahead of the signature, rather than a new `Expr` constructor. Two reasons,
in order:

* It is what egglog does — a primitive lives in a table sharing a namespace with user
  functions, and shadows a user function of the same name.
* Adding an `Expr` constructor makes every existing `cases e` / `induction e` in
  `Proofs/Eval.lean`, `Proofs/Match.lean` and `Proofs/Interp.lean` non-exhaustive, which
  is an error rather than a `sorry`. M9 has nothing to say about any of those cases.

`Expr.eval` (the M2 function) therefore still treats `(ordering-min a b)` as building a
term. That is harmless because the two developments do not mix — `Expr.eval` is what
M0–M10 uses and `MEval` replaces it — but it *is* a latent trap the day `Database` is
replaced by `MDatabase`, and the fix at that point is to delete `Expr.eval`.

## The term order

One definition, two deliberately distinct jobs.

**(a) A spec primitive.** `ordering-min`/`ordering-max` are part of the *program* the
encoding writes, not an implementation detail: the union-find's merge body is literally
`(set (@UF_<S> (ordering-max old new)) (values (ordering-min old new) ()))`. M11 cannot
state `encode` without them. It is also where a termination witness comes from, since a
merge that keeps the smaller side descends.

**(b) An implementation tie-break.** `MergeStep` is non-deterministic in which collision
fires; the interpreter has to pick one, and ordering candidates by this makes the choice
deterministic. **The spec stays non-deterministic** — this is an `Impl/` choice only.

```lean
def Term.blt : Term → Term → Bool   -- literals, then arity, then name, then lex
def Term.orderingMin (s t : Term) : Term := if Term.blt s t then s else t
def Term.orderingMax (s t : Term) : Term := if Term.blt s t then t else s
```

Structural size before lexicographic, so "keep the smaller side" descends.
`Term.blt_linear` is stated and unproved.

egglog orders by *insertion* instead, so it picks a different class **representative**.
That is invisible to `(print-size)`, which counts one row per class, so differential
testing is unaffected.

## Multi-column outputs

egglog's tables are multi-column and the encoding depends on it: `@UF_<Sort>` carries a
parent *and* a proof, `@<C>View` an e-class and a proof. `Row.out : List Term`, with
`FnDecl.outArity` beside the key `arity`.

**The merge result is a `List Expr`, one per value column**, where the surface syntax
writes one tuple-valued `(values e₀ e₁ …)`. This follows the backend, which is already
per-column — `assert_eq!(resolved.len(), schema_math.n_vals(), "merge for {f} must have
one entry per value column")` (`egglog-bridge/src/lib.rs:1405`) — and it avoids putting
a tuple constructor into `Term`, which would make every existing `cases t` in the M10
proofs non-exhaustive, the same objection that kept primitives out of `Expr`. **Recorded
as a deviation from surface syntax**: a source program writes `(values …)` and the model
takes the list it denotes.

**`MCong.fd` is unaffected — the claim holds.** `fd` fires only at `.union`, and:

* A `.union` function is a source-program **constructor**, which has exactly one value
  column. `MergeFn::UnionId` is documented in the backend as "Use congruence to resolve
  FD conflicts" — it *is* `fd`.
* The **encoded** program has no `.union` function at all. `@UF_<Sort>` and `@<C>View`
  are `MergeFn::Block`s whose columns are expressions (`ordering-min old0 new0`, `()`),
  and they resolve congruence through the body's `set (@UF_Math …)` plus the `@UF`
  table. So in the target, congruence is **entirely simulated** — a clean thing to be
  able to state, and exactly the M11 simulation obligation.

`fd` was still generalized to fire per column (`(x, y) ∈ a.zip b`), which costs one
premise and makes the claim moot rather than load-bearing. It degenerates to the old
single-column rule under `Database.toM`.

### One place this is coarser than egglog

**A merge kind is per *function* here and per *column* there.** The backend has
`MergeFn::Columns(Vec<MergeFn>)`, so a single function may legally have `UnionId` on
column 0 and `Old` on column 1 — a mixed function that `MergeSpec` cannot express, since
`.union` / `.merge` / `.noMerge` is a choice for the whole function.

Nothing needs it today: the encoding's tables are uniformly `Block`s with expression
columns, and source constructors are single-column `UnionId`. The faithful shape, if it
is ever wanted, is

```lean
inductive ColumnMerge where | union | expr : Expr → ColumnMerge | noMerge
structure MergeSpec where
  actions : List RowAction     -- run once, before any column
  columns : List ColumnMerge   -- one per value column
```

under which `fd` fires on a column whose `ColumnMerge` is `.union` — i.e. `fd` would
gain a designated e-class column after all. Not done, because it would put a
per-column signature lookup into `MCong` for a case neither the source nor the target
language currently produces.

## Restrictions on `encode`'s domain (M11)

`encode` is defined only for source programs **whose functions have no `:merge` action
block**. This is intended and permanent, not a gap to close: the encoder rejects such a
program with `ProofEncodingUnsupportedReason::MergeActionBlock`, because "a `:merge`
action block runs actions before its result; the proof encoding only instruments the
merged value, so mark it unsupported rather than emit silently-incomplete proofs"
(`proof_encoding_helpers.rs:1088-1096`).

The asymmetry is deliberate and not a contradiction: the encoder *emits* merge action
blocks — `@UF_<Sort>` and `@<C>View` are exactly that shape — while declining to
*encode* one it is handed. It knows what its own blocks prove; it does not know what a
user's does.

A second restriction from the same check: `:no-merge` on an eq-sorted output is rejected
(`NoMergeEqSortFunction`).

## Constraint (3): monotonicity

Discharged by the representation, not by an argument. Asserted rows only accumulate; a
merge adds the combined row beside the two it combined; there is nothing to overwrite.
`MDatabase.Contained` gains a `rows` field and

```lean
theorem MergeStep.contained  (h : MergeStep d₁ d₂)   : d₁.Contained d₂
theorem CmdStep.contained    (h : CmdStep db c db')  : db.Contained db'
theorem ProgramStep.contained (h : ProgramStep db p db') : db.Contained db'
```

are what every M2–M8 lemma needs to transport. `MCong.mono` and `MDatabase.Out.mono`
follow.

`CmdStep.contained` is also the formal content of the hard constraint **never delete a
term row or a proof row**. The encoding depends on it directly — "Nothing is ever
removed from it, which lets proofs refer to terms after they leave the e-graph" — and
the invariant argument needs it, because everything the checker reads is *positive* in
the state, so once true it stays true. `delete` and `subsume` are outside the fragment
and, when they arrive, must not touch term or proof rows; the encoding already defers
them to marker relations and deletes only the *view* row, which is the shape to
preserve.

**What monotonicity costs.** egglog *deletes* the displaced row; the model keeps it. So
`Out` is a sound over-approximation: every value egglog computes is derivable here,
plus stale ones egglog has removed. For `@UF_<Sort>` that is not merely harmless but
right — any parent a term ever had is genuinely equal to it, which is exactly what
`Out.union_cong` says.

## Constraint (4): firing counts

**What egglog does.** Merges are *deferred*: rule execution stages rows into mutation
buffers, and `Database::run_rule_set` searches and applies every rule before calling
`merge_all` (`core-relations/src/free_join/execute.rs:653-655`). `merge_all` then runs
**to a fixed point** (`free_join/mod.rs:546-628`, `:686-689`) — a merge's own `set`
re-notifies and is picked up next iteration. Within one key, merging is a left fold in
staging (FIFO) order, and **the first row for a fresh key is inserted verbatim with no
merge call** (`table/mod.rs:715-790`, `:742-768`); in parallel mode the cross-buffer
order is not deterministic. Top-level actions go through the same path, so each
top-level `set` is its own merge phase (`src/lib.rs:1490-1512`).

### Saturation is a hypothesis, not a step

Merge closure is a *phase* of a round — congruence closure never needed one, being a
relation; merge closure changes state and does:

```lean
def RunStep (db db' : MDatabase) : Prop := MergeClosure (MRunRules db) db'
```

The deferral is faithful: no rule sees another's merged value within a round. But
`RunStep` deliberately does **not** require the closure to have saturated, and an
earlier draft that did was *wrong*, not merely strict:

```lean
def MergeSaturated (db : MDatabase) : Prop := ∀ db', ¬ MergeStep db db'    -- unsatisfiable
```

Nothing removes rows, so the two colliding rows are still present after the step and the
step applies again — forever. (With no guard on the collision, below, there is a second
independent reason: every row collides with itself, so a step always applies.) Under
that definition `CmdStep … .run` is vacuous for every program with a real merge
collision. The corrected form is "every step is the identity":

```lean
def MergeSaturated (db : MDatabase) : Prop := ∀ db', MergeStep db db' → db' = db
```

and it is **assumed by the theorems that need it** — simulation, and matching egglog's
row counts — rather than built into the step. This removes termination from the spec
entirely, which is what the invariant framing buys.

### No guard on the collision

`MCongList` is reflexive, so a row collides with **itself**, and `MergeStep` has no
`a ≠ b` side condition to stop it.

An earlier draft had one. The reasoning was that egglog merges a *retained* row against
an *incoming staged* one and so never self-merges, and that a state relation — two rows
in a `Set` — cannot see how often a value was staged, so it should not fire on `a = b`.
That reasoning is about *matching* egglog, and it made the guard the one
**under**-approximation in an otherwise over-approximating design. Under-approximation
is the unsafe direction: it leaves egglog reaching states the model never checks, so the
safety invariant does not transfer to real egglog.

Without the guard the model covers egglog unconditionally. Where a function has
`:internal-identity-vals` set, egglog skips a re-`set` of an equal value and the model
fires anyway; where it is not set, egglog fires on the re-`set` and the model fires
spontaneously. Over-approximate either way. **The safety theorem therefore needs no
scope condition on the signature at all** — no `merge (x, x) = x`, no
identity-guardedness hypothesis.

Two consequences, both intended.

**Idempotent merges gain vacuous rows, not divergence.** The union-find's body on a
self-collision is `(set (@UF_<S> (ordering-max p p)) (values (ordering-min p p) ()))` —
a reflexive self-edge. `MCong` derives only `p = p`, already true by `refl`. In proof
mode it writes extra proofs of `p = p`, which are *valid*, so the invariant is
untouched. And they are not observable: egglog's `print-size` filters
`internal_hidden || internal_let` and reports a view under its `term_constructor` name,
which is exactly why `files.rs` shares one snapshot between normal and term-encoded
runs — so `@UF_*` and `@*View` never appear in a diff. `MergeStep.self_id` states the
fixpoint: a body that adds nothing and returns the output it was given makes the step
the identity, which is what keeps `MergeSaturated` reachable.

**`:merge (+ old new)` diverges.** The self-collision derives `2v`, `3v`, … forever,
where egglog with a single `set` merges nothing. This is the intended reading and not a
defect: such a program's egglog result is insertion-order dependent, so there is no
fixpoint for a semantics to denote, and diverging is more honest than inventing an
answer. Same "the user's fault" framing as order-dependent merges generally — egglog
documents that a merge must define a lattice (`src/ast/mod.rs:803-808`) and never checks
it. The two changes are coupled: this is workable only because `MergeSaturated` is the
"no step *changes* anything" form, under which `ordering-min` self-merges saturate and
`+` correctly does not.

Where this leaves naive vs seminaive: `PLAN.md`'s note that they "genuinely diverge"
for a non-idempotent merge is right about egglog and does not apply to this model,
because this model has no firing count at all.

### `:internal-identity-vals`, deferred

In full (`egglog-bridge/src/lib.rs:1412-1478`): compare the first `k` **value** columns
by raw equality; if they agree, skip the action block entirely, keep the *old* value in
every column including the payload, and leave the row untouched with its old timestamp
so seminaive does not re-fire. The encoding's use is identity column = e-class, payload
= proof: a collision agreeing on the e-class keeps the existing proof. Contract: only
valid when `merge (x, x) = x` (`egglog-bridge/src/lib.rs:227-231`).

The count is a `Nat` and not a `Bool` because it marks a **prefix** of the value
columns: `:internal-identity-vals 1` on `(Math) (Math @Proof)` marks the parent column
identity and the proof column not, so re-setting the same parent with a *different*
proof keeps the old row and its old proof. The comparison is
`cur[id_lo .. id_lo + k] == new[id_lo .. id_lo + k]`, and when it holds every column —
payload included — takes the old value.

**`identityVals` stays out of `FnDecl`.** With the collision guard gone it is not a
soundness concern, and the `print-size` filtering above means it is not a
difftest-fidelity concern either. It becomes relevant only if `encode`'s output is ever
rendered to `.egg` and run in real egglog, which is not the plan now — that is the
trigger to revisit. `Row.out` is now a list, so the distinction is at least
*expressible*; what is missing is only the marker itself.

## Constraint (5): base sorts

**Not done, deliberately.** `Lit` is still `Int` only and `Term` is still untyped. What
the design does instead:

* The FD's key comparison is `MCongList`, which compares every argument position by
  congruence. On a base-sorted argument congruence degenerates to equality, since a
  base value is never unioned. So the sort discipline is **not needed for the FD to be
  correct** — only for typing. That is why M9 can land without it.
* `MDatabase.WF.rowsInTerms` requires a row's *arguments* and *output* to be terms, but
  **not its key application** `.app f args`. For a `:merge` function that application
  is a key, not a value: it has no e-class and cannot be unioned. With one untyped
  `Term` nothing else prevents it being written as a term.
* `MDatabase.ArityOk` is stated and unused — the decidable half of the discipline.

The proposed shape when it is done, which is where the Redex's `no-type` finally dies:

```lean
inductive Sort where | eq : String → Sort | i64 | str | unit
structure FnDecl where
  inputs : List Sort
  output : Sort
  merge  : MergeSpec
```

with `Scope` becoming `List (Var × Sort)` and `Expr.Scoped` a typing judgment. Two
side conditions the sorts would buy: `.union` requires an eq-sorted output (egglog
rejects `:no-merge` on an eq-sort output under the term encoding,
`proof_encoding_helpers.rs:1067-1086`), and `Term.ctorRows` needing no signature
becomes a theorem instead of an invariant maintained by inspection.

`Lit` also wants `.str` and `.unit` before M11 — `@Rule_<k>` carries a rule *name* and
the no-proof column is `Unit`. Cheap (`Lit` has `deriving DecidableEq`, and `Egg.lean`
gains two render cases), and independent of everything above, so it was left out to
keep this diff about one thing.

## Constraint (6): termination

Out of the spec entirely. `MergeClosure := Relation.ReflTransGen MergeStep`, no
fixpoint, no measure, and — after the change above — no saturation requirement anywhere
in `Spec/`. The reason merge closure has no measure is sharper than "merges may not
terminate": **a merge body can build terms**, so the candidate universe grows as the
closure runs. That is exactly what `Impl/Closure.lean`'s `closure` relies on not
happening — its well-founded measure is `(candidates terms).card - rel.card` over a
*fixed* `terms`.

The congruence closure itself is fine. Generalizing `stepAdds` with an `fd` disjunct
keeps `terms` and `rows` fixed while it runs, so `closure` stays well-founded and the
FD is decidable. It is only the *merge* loop that has no measure.

## The executable layer

`Impl/Merge.lean` runs the M9 semantics; `Tests/EggMerge.lean` renders an `MProgram` as
`.egg`; `DiffTest.lean` writes seven `:merge` cases. **77 cases pass** — the 70
constructor ones unchanged and 7 new.

Four things differ from `Impl/Interp.lean`, and each is a design decision rather than an
implementation detail.

**The refinement weakens to reachability.** The spec admits several results, so
`execM_reachable` says the interpreter lands on one the spec reaches, not on *the* one.
Nothing stronger is available and nothing stronger is wanted: pinning a single result
means pinning the merge order, which is what the semantics deliberately declines to do.

**The merge phase is one pass, not a fixpoint.** `mergeRound` fires every collision it
can see once. Structurally terminating, so no fuel and no accessibility argument — and
sound *because* `RunStep` is `MergeClosure` with no `MergeSaturated` requirement, so a
prefix of the closure is still a reachable state. Dropping saturation from `RunStep` paid
for itself here immediately. `mergeSaturate` is defined beside it, taking a termination
witness (`Acc`) rather than fuel, and is not what `execCmd` runs.

**A lookup has to pick.** `execExpr` takes the first recorded output. The spec allows
any; an interpreter cannot.

**The congruence closure is unchanged.** `MCong.fd` fires only at `.union` functions, and
a `.union` function's rows are exactly the constructor rows `Impl/Closure.lean` already
sees through `terms`; a `:merge` function's rows contribute nothing to `MCong`. So
`closureF` reuses `closureTotal` verbatim, which `closureF_ok` states. That was not
obvious in advance and is worth keeping in mind for M11 — it says the FD machinery adds
nothing to *decide* as long as no user function is `.union`.

### Row counts survive, and why that matters

`rowCount` counts congruence classes of **key tuples**. Two consequences, both load-bearing
and both now deliberate rather than accidental (`mergeRound_rowCount`):

* A merge step writes its combined row at a key already present, so it adds no key class.
  A merge with an empty action block writes nothing anywhere else. The count is therefore
  invariant under the merge phase — which is exactly why the interpreter can run one pass
  instead of saturating and still predict egglog's answer.
* Keeping every superseded output — the over-approximation the whole design rests on —
  does not inflate the number. Three recorded values at one key are still one row.

### The difftest fragment

Deliberately narrow, and the narrowness is the interesting part.

* **Every generated merge is a join** (`min`/`max` on `i64`). A non-idempotent merge would
  give extra firings and extra values under our over-approximating reads, so a row-count
  difference would be this model's design showing rather than a real bug.
* **Merge functions are written and never read.** A body atom reading one binds the
  variable to *any* recorded output where egglog binds the current one, so the model would
  fire more and build more. This is the fragment's boundary and the first place the
  over-approximation becomes observable. It is also the one thing the difftest therefore
  does *not* validate.
* **Outputs are `i64`, keys are eq-sorted.** egglog typechecks a `(function …)`
  declaration, so a merge function needs a real output sort — this is where sorts finally
  bite. An eq-sorted output would dodge the base sort but then `ordering-min` must render,
  and `Term.blt` is *structural* where egglog's is by insertion order, so the two would
  pick different representatives. Row counts would survive that; nothing else would.
  Keeping keys eq-sorted also keeps `Term.lit` out of constructor arguments, so `Egg.lean`'s
  standing literal mismatch stays out of the way.

The case that matters is `min-rebuild`, the shape of `egglog/tests/merge-during-rebuild.egg`:
two `Dist` rows whose keys are then unioned, so egglog's table drops from two rows to one.
`min-congr` does the same collapse through congruence rather than a direct union, and
`min-rule` writes a row from a rule head. These discriminate — a model that ignored key
congruence would predict 2 where egglog says 1.

### Still unbuilt

* **Two evaluators.** `Expr.eval`/`evalAction`/`stepCmd`/`runProgram` (functions) and
  `Expr.MEval`/`ActionStep`/`CmdStep`/`ProgramStep` (relations) both run over the one
  `Database` and the one `Action`. `Expr.MEval_of_eval` is stated as the guard against
  drift. Collapsing them is `PLAN.md`'s **M12**, deliberately deferred: it is where the
  cost is (~1000–1400 lines of `Option` algebra become existentials), and it weakens
  `exec_toDatabase` from an equality to reachability unless `ProgramStep` is first proved
  deterministic under `AllConstructors`.
* **`Cong` and `MCong` still coexist**, now over the one `Database`. `mcong_iff_cong` is
  the theorem that licenses deleting `Cong` and renaming; what it costs is rerouting
  `Cong.congr'`, `Cong.le` and `mem_closure_iff` through `CtorRows`.
* **`Database.RowsWF`** is stated outside `WF`. Putting it in would make every `WF`
  construction carry a subterm-transitivity argument for no current payoff; it belongs in
  `WF` once something reads it.
* **`Lit` is still `Int` only**, so `.str` and `.unit` are still missing — which is what a
  proof column's `Unit` and `@Rule_<k>`'s rule name need. `min` and `max` are no longer on
  this list; see below.

## What the widening and the composed interpreter found

Two changes, and what each turned up.

**`Action.set` takes a `List Expr` and `Pattern` gained `values`.** `Row.out`,
`Database.addRow`, `Database.Out` and `MergeSpec`'s result were multi-column from the
start; `Action.set` and the pattern language were not, so a multi-column row could be
*created* by a merge and never written or read, which is what `CHECKER.md` called the one
blocker on M11's proof column. The read side is egglog's **tuple destructure**
`(= (values v…) (f a…))`, and it is the only way egglog offers to read a value column
other than the first: a tuple-output function cannot be evaluated as an expression
(`eval_resolved_expr` panics on `values`) and cannot be extracted, whose error message
says "Read its columns in a rule with `(= (values ...) (f ...))` instead". `MEval.lookup`
therefore *stays* single-column, which is faithful rather than a limitation.

**`Program.expectedSizes` now runs a composed M9 `execProgramM`.** It ran
`Impl/Interp.lean`'s `exec`, which evaluates with `Expr.eval` and never calls
`mergeRound`, so `mergeOne`, `mergeRound`, `execActions`, `execExpr`'s lookup branch and
the destructure had **zero** differential coverage — the suite's pass count said nothing
about the merge implementation. It does now.

**`min` and `max` had to become primitives.** `Prim.ofName` knew only
`ordering-min`/`ordering-max`, so a `:merge (min old new)` body — the shape every merge
case uses, and the shape `tests/interval.egg` and `tests/merge-during-rebuild.egg` use —
built the *term* `min(5, 3)` where egglog computes `3`. That was invisible while nothing
ran the merge phase, and three things went wrong the moment something did. No state was
ever `MergeSaturated`, so `mergeSaturateF` returned `none` for every case with a real
collision. Each pass wrote a genuinely new value at every colliding key, so the row set
squared per pass and **12 of 30 generated merge cases timed out**. And a rule reading a
merged value got a term where egglog has a number. Adding `Prim.intMin`/`intMax` on
`Lit.int` fixed all three: the suite went from 102 passed / 12 skipped to **114 passed, 0
failed, 0 skipped**, and saturation became reachable again (`execCmdM` still runs one pass,
for the reason in `mergeSaturateF`'s docstring). This is the sharpest thing the coverage
gap was hiding: the difftest's merge cases were *generated* correctly and *predicted*
by a merge implementation that had never been run.

**`Impl/` now deletes superseded merge rows; `Spec/` does not.** The two were both
append-only, and the contract between them was an *equality* — which is what forced `Impl/`
to be append-only in the first place. That made the reference implementation faithful to
this model and **unfaithful to egglog**, which replaces the row, and the divergence below
is what that costs. `Spec/` stays append-only: the M11 safety theorem is an invariant over
`MergeStep` and needs neither termination nor confluence precisely because nothing is
removed, and the encoding depends on the same property. `Impl/Merge.lean`'s merge phase
drops the two rows it combined, and nothing else — never a term, never an equality, never a
row of a `.union` function (constructor rows, which the whole congruence argument rests on)
and never a row of a `.noMerge` function (which is how the encoding declares its proof
nodes, so deleting one would delete a proof). `Proofs/Merge.lean`'s
`FDatabase.mergeRound_confined` is that sentence, machine-checked.

The contract therefore **splits** rather than weakens:

* *Soundness* is now a containment — the implementation finds **fewer** results, never
  more, which is the safe direction because everything M11 reads is positive in the state.
  `MValidSubst.mono` is the half that makes "fewer rows" mean "fewer matches"; `MCong`,
  `MCongList`, `Database.Out` and `Expr.MEval` are all monotone already. `execM_contained`
  is the top-level statement, unproved for the same reason `execM_reachable` is.
* *Completeness*, so containment is not vacuous, is two statements. On the constructor
  fragment the existing **equality** stands untouched: no row belongs to a `.merge`
  function, so `hasMergeRow` is false and the pass is the identity
  (`FDatabase.mergeRound_eq_self`), which is why `exec_toDatabase` is outside the blast
  radius entirely. On **lattice** merges the implementation holds the `Current` value at
  each key class — exactly what `Current` was defined for. For a non-lattice merge
  `Current` does not exist and nothing is claimed.

Two statements became **false** and are corrected where they stand:
`Impl/Merge.lean`'s result is no longer `MergeClosure`-reachable (`mergeRound_closure`), and
neither is `execM`'s (`execM_reachable` now applies to `exec` only, which has no merge
phase). Both are false in the *harmless* direction — the implementation is smaller than
anything the spec reaches, not different from it.

Saturation is a consequence rather than a hope: deleting the pair that fired makes a pass
strictly shrink each colliding key class, so `mergeSaturateF` terminates and `execCmdM`
runs the merge phase to a fixpoint as `merge_all` does.

**The over-approximation was observable, and is now gone.** `MERGE.md` has always said
the model keeps every superseded output where egglog deletes it, and that this is sound
because rows are append-only. Until a rule could read a value column, no oracle could see
it. Now one can, and it diverges — minimal repro, machine-checked both ways:

```
(function Dist (Math) (i64 i64) :merge (values (min old0 new0) (max old1 new1)))
(set (Dist (A)) (values 5 1))
(set (Dist (A)) (values 3 7))
(rule ((= (values 5 1) (Dist k))) ((Hit k)))
(run 1)
```

egglog reports `Hit 0`: the merge replaced the row and `(5, 1)` is gone. An append-only
implementation reports `Hit 1`, because the superseded row is still there and the
destructure reads it. It is now a difftest case (`tuple-stale`, with the single-column
`read-stale` beside it) and **it agrees**. The *specification* still says `Hit 1` is
reachable, and that is deliberate: **this is the design showing through, not a defect** — it is the over-approximation argued for under
"Why the reader over-approximates", and it is in the safe direction, since a stale row is a
row that really was written. What changed is only which side of the `Spec`/`Impl` line it
lives on: the specification still admits it, and the reference implementation no longer
does.

**The read path had no coverage at all**, which is how this stayed invisible. This
document's own fragment boundary — "merge functions are written and never read" — meant
`Expr.MEval.lookup`, reachable through `execM` from `MValidSubst.expr`, was exercised zero
times. The generator now emits a rule reading `Dist` in both shapes egglog offers,
`(Dist k…)` and `(= v (Dist k…))`, and there are curated `read-exists` / `read-value` /
`read-stale` cases. One finding from the before-measurement is worth keeping: the
single-column `read-stale` **agreed even before the deletion**, and for the wrong reason —
`execExpr` takes the *first* recorded output and `FDatabase.addRow` prepends, so the row it
picked happened to be the merged one. The tuple destructure searches all rows and exposed
what the single-column read was hiding. An agreement that rests on list order is not
evidence of anything, which is the same lesson as `min`/`max`.

## What was rejected

* **Merge as a value combiner `Term → Term → Term`.** Dies on the union-find's `set`;
  see "Why not a value combiner".
* **The observable value as a fold over asserted rows** (`PLAN.md` M9 §3), for the same
  reason: the side effects live only in the closure, not in the asserted rows. What
  survives is `Current`, and only for difftest and simulation.
* **A `Current`-reading `MEval`.** Proposed and retracted: `Current` does not exist for
  `:merge old` or `:merge new`, both of which are common. See "Why the reader
  over-approximates".
* **Saturation inside `RunStep`.** Unsatisfiable as first written, and unnecessary once
  the safety theorem is an invariant.
* **The `a ≠ b` collision guard**, and with it a `merge (x, x) = x` or
  identity-guardedness hypothesis on the safety theorem. All three bought a soundness
  gap rather than closing one; see "No guard on the collision".
* **Fuel-bounded merge saturation in `Impl/`.** Returns a wrong answer where "no answer"
  is correct.
* **Overwriting the row.** Breaks `Contained` and with it every M2–M8 lemma.
* **Keeping `Cong.congr` alongside `fd`.** Two rules for one fact; the compatibility
  theorem is what shows the second is redundant, and keeping it would make that
  theorem vacuous.
* **An `Expr` constructor for primitives**, and a tuple constructor in `Term` for
  multi-column outputs. Both would make existing `cases` in the M10 proofs
  non-exhaustive; reserved names and a `List` respectively match egglog and cost no
  churn.
* **Per-column merge kinds.** Faithful to the backend's `MergeFn::Columns`, but neither
  the source nor the target language currently produces a mixed function; see "One place
  this is coarser than egglog".
* **A fresh-id / e-class-id representation on this side.** M11 adds ids to the *target*
  configuration only; the source semantics keeps terms as their own identity.
  `PLAN.md` is right about this and nothing in M9 pressures it.
* **In-place surgery on `Database`.** `MDatabase` is a separate structure and
  `Database.toM` an embedding, so the compatibility theorem is a statement relating
  two things rather than an assertion that a refactor was safe. Once it is proved, the
  migration is to delete `Database` and rename.

## Open questions

1. **Is `MergeStep` confluent for a join merge?** `MergeStep.diamond_of_join` is stated
   and **[guess]** — a merge body that writes to a *third* table can plausibly break the
   diamond even when the value combiner is a join, since the third table's own merge
   sees a different pair depending on the order. **Demoted**: no safety theorem needs
   it. It buys one thing, strengthening M10's refinement from "the interpreter's result
   is spec-reachable" to an equality.

2. **Redeclaration.** `Cmd.decl` is `Function.update`, so a program can change a
   function's `:merge` after rows exist, silently changing what the existing rows mean.
   egglog forbids redeclaration. Should `WellScoped`?

3. **`Signature.mergeOf` defaults undeclared names to `.union`.** This is what makes
   `AllConstructors` cover M0–M8 exactly, and it is load-bearing for the compatibility
   theorem. But egglog requires every function to be declared. Keep the default and
   note it, or add a `Declared` hypothesis and re-state M0–M8's theorems under it?
