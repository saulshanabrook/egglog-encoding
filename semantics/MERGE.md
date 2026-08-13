# `:merge` functions (M9)

Generalizes the semantics from "every function is a constructor and congruence is `Cong`" to "a
function carries a `:merge`". Revises `PLAN.md`'s M9 section; where they disagree this is current.
Facts about egglog are cited to the Rust; guesses are flagged **[guess]**.

A function's table lives in the terms: a merge function's entry at the key `a…` with value columns
`v…` **is** the term `f(a…, v…)`, and a constructor's entry is `f(a…)`. What that adds to
congruence is the **functional dependency**, which comes out as `Cong.congr` — a rule of the one
congruence relation, at no cost, rather than a second relation or a theorem under hypotheses. A
`:merge` body is an action list, so resolving a collision is a step relation on databases,
`MergeStep`, not a value combiner; command stepping becomes a relation with it. That last
consequence was not in `PLAN.md`.

**Three shapes this file argued for, and their fates.** Congruence as an inductive `fd` rule over a
second relation `MCong`, with a compatibility theorem `mcong_iff_cong` — **retired**, first for a
theorem `Cong.fd` and then for `Cong.congr` itself. Evaluation as a relation `Expr.MEval`, because
a non-constructor application was a lookup — **retired** when reading became the query atom
`Pattern.values`, after which `Expr.eval` needs nothing of the database but its signature and is a
function again. And a **row set** in the state, `⟨f, args, out⟩` — **retired** for entry terms;
`Row` survives in `Impl/` as a private table index and nowhere else. The sections below are the
design record; where they reason about `MCong`, `Expr.MEval` or `Database.rows`, the reasoning is
about a shape the development no longer has, and each such section says so.

**Status.** `make lean-difftest` is **166 passed / 0 failed / 0 skipped**, 66 of those curated
`:merge` cases, and `execM_eq_exec` is `sorryAx`-free, so those cases bear on `Spec/` and not only
on the interpreter. `Proofs/Merge.lean` has **no `sorry`s**: `execM_contained` is proved, under one
new hypothesis `p.UnionFree`. The difftest corpus does **not** satisfy that hypothesis — it writes
`Action.union` at 54 sites — so the tested programs are strictly more than the proved ones. That
gap is `PLAN.md`, "What is covered, and what is not", and it is what to read before quoting 166/0
as evidence about a theorem.

**The five defective M9 statements are deleted, not carried as `sorry`s.**
`MergeStep.diamond_of_join`, `execM_current_of_lattice`, `mergeRound_closure` and
`FDatabase.mergeRound_rowCount` went as statements, each with its defect written up where it stood
(`Proofs/Merge.lean`, "Known-broken statements, removed" and "Two statements removed rather than
carried"); the fifth went with `RunStep` itself, whose job is now `CmdStep` at `.run`. Only
`execM_current_of_lattice` has compiled refutations, in `Proofs/Lattice.lean` — the other three
are argued at the deletion notes.

## The framing: invariants over a step relation

M11's headline theorem — *every proof row the encoding writes is accepted by the checker* — is an
**invariant** over the step relation, and that shapes everything below:

```lean
theorem invariant_of_step {I : Database → Prop}
    (hstep : ∀ db c db', I db → CmdStep db c db' → I db')
    (hinit : I db) (h : ProgramStep db p db') : I db'
```

Four lines. An invariant needs **neither termination nor confluence**: it holds at every
reachable state, so a diverging run satisfies it throughout and so does a differently-ordered one.

So the spec is **over-approximating**, and matching egglog exactly is a hypothesis on the theorems
that want it. A lookup reads *any* recorded output; a round takes *any number* of merge steps; a
row collides with itself. The spec reaches every state egglog reaches, plus some it does not.
Over-approximation must be **unconditional**: any under-approximation is a hole, since egglog then
reaches a state the model never checks and the invariant does not transfer. That criterion removed
the last side condition, the `a ≠ b` collision guard. Two things make this sound rather than
merely convenient.

* **Append-only.** In `Spec/`, `eqs` only grows, so a term or proof entry once recorded is
  recorded forever: every recorded proof is valid and *stays* valid, and a stale one is a
  different proof of the same fact, never an invalid one. The safety theorem needs no
  well-behavedness hypothesis at all.
* **Order-dependent merges are the user's fault.** A merge that is not a lattice join has no
  order-independent answer; egglog calls that "user-visible undefined behavior"
  (`egglog-backend-trait/src/lib.rs:46-48`) and documents that a merge must define a lattice
  (`src/ast/mod.rs:803-808`) without ever checking it.

Differential testing and M11's simulation theorem, the two places that *do* need to match egglog,
take `MergeSaturated` and a join condition as hypotheses.

## Representation

The M9 state is `Database` itself, which is four fields — `sig`, `eqs`, `env`, `rules`. There is
no separate `MDatabase` and no `Database.toM`: an earlier draft had both, which kept the
compatibility theorem a statement relating two things rather than an assertion that a refactor was
safe; merging them turned a statement relating two state types into one relating two relations
over the same state — which is what made it possible to then delete the second relation outright.
M9 then added `rows : Set Row` beside a `terms` field, and **both are gone again**. A function's
table is in the terms:

* a **merge function**'s entry at key `a…` with value columns `v…` is the term `f(a…, v…)`;
* a **constructor**'s entry is `f(a…)` — the key alone, no value appended.

**Why a constructor's value is not appended.** A constructor's value *is* its own application, so
appending it would write `f(as ++ [f as])`. That resurrects `Term.ctorRows` under another name, and
worse, it makes the width invariant unstatable: `f(as)` and `f(as ++ [f as])` would both be
present, one head at two widths, and no per-name width predicate can hold of both. Leaving the
constructor entry bare is what lets `FnDecl.entryWidth` be a *function of the declaration* —
`arity` for a constructor, `arity + outArity` for a merge function — and `Database.DeclaredTerms`
then says every application the database holds has its declaration's head and its declaration's
width. That predicate is what replaced `Database.CtorTerms`, and it is the invariant a `set` on a
constructor would break (`PLAN.md`, "The front end's six checks").

**Why the entries do not need a set of their own.** `eqs` already carries existence: `t = t`
records that `t` was built, `Database.terms` is `{t | Cong db t t}`, and `addTerm` writes one
reflexive equation per subterm. So recording an entry is recording a term, `union` and `set` become
the same kind of write, and the state has one growing component instead of three. It also removes
the question a row set kept raising — whether `terms` is derivable from `rows`, and what to do
about a literal, which is a term with no row.

## Congruence is the functional dependency

This started as a second relation and ended as **nothing at all**, which is the best outcome the
question had. `MCong` was `Cong` with `congr` deleted and an `fd` constructor in its place — two
rows of one function with congruent keys, outputs equated column by column, guarded on the function
being a constructor — plus a compatibility theorem `mcong_iff_cong` licensing the transport of
every M2–M8 result. That became a theorem `Cong.fd` under one hypothesis, the shape of a
constructor's rows. Then the rows went away, and with them the hypothesis and the theorem.

**It is `Cong.congr`.** A constructor's entry is the term `f(a…)` itself, so two entries with
congruent keys are two applications of one head with congruent arguments, and

```lean
| congr : Cong db (.app f as) (.app f as) → Cong db (.app f bs) (.app f bs) →
          CongList db as bs → Cong db (.app f as) (.app f bs)
```

*is* "one key, one output". No premise about a row's shape, nothing to discharge, no state
invariant standing behind it. The two self-congruence premises are the "both applications are
present" side conditions, and under the `eqs`-only design they are literally membership.

**What that cost, tracked honestly.** The old `Cong.fd` fired at *any* constructor row, including
one a `set` had written; `Cong.congr` fires only on entries the database actually holds. The
difference is exactly the program `Action.SetLegal` forbids — `(set (f) (c)) (set (f) (d))` on a
declared constructor `f`, which was the whole gap between `Cong` and `MCong`. Under entry terms
that program does not reach a state at all: the width is wrong for a constructor and
`DeclaredTerms` excludes it. So the chain that existed only to discharge `fd`'s hypothesis —
`Database.CtorRows`, `CtorRows.fd_hyp`, `ProgramStep.ctorRows`, `Database.CtorFragment` — is
deleted rather than ported.

**A merge function's applications still get no congruence at all**, and this is the line the whole
design is drawn along. `congr` needs both applications present, and it equates *applications*, not
a key with a value; two `@UF_Math` entries with congruent keys make their parents equal because the
merge body says so, which is a **step**. A constructor collision is the only one whose whole effect
is an equality between terms that already exist, hence the only one a relation can express.

**Declaration is required** (`Signature.IsCtor` is `∃ d, sig f = some d ∧ d.merge = none`), so an
undeclared name is not a constructor and M0–M8 is the all-constructors case only for programs that
*declare* their constructors — which is what `Tests/Examples.lean` and `DiffTest.lean` do, and what
egglog requires anyway. The hypothesis that carries it is a state invariant — now
`Database.DeclaredTerms` — and not a fact about the signature alone: `Signature.AllConstructors`
says nothing *is* a merge function, which does not imply that the applications the database holds
are constructors'. `MergeStep.saturated_of_allConstructors` is the step-side companion: with no
`.merge` function there is no collision, so a round is `RunRules` and nothing else. Together they
say M9-on-constructors is M0–M8 unchanged, so all of `Proofs/` transports.

## Constraint (1): a `:merge` body is an action

**What egglog does.** The AST is `GenericMerge { actions: GenericActions, result: GenericExpr }`
(`egglog-ast/src/generic_ast.rs:45-57`); the declaration field is `merge: Option<GenericMerge<…>>`
and is *required* (`src/ast/parse.rs:585-593`). Parsing disambiguates syntactically — a list whose
head is itself a list is an action block, otherwise a bare result expression
(`src/ast/parse.rs:531-569`), so `:merge (max old new)` stays an expression. `:on_merge` was
removed and this replaced it (`CHANGELOG.md:178`, `:42-46`). The block admits **exactly `let`,
`set`, `union`**; anything else is rejected at lowering with "action `{other}` is not supported
inside a :merge block" (`src/lib.rs:1064-1067`). So `panic` and `delete` are *not* available, and
`set` into another table — or into the function's own (`src/lib.rs:1100-1106`) — is. There is a
user-facing test, `tests/merge-action-block.egg`; the union-find's block in `proof_encoding.md` is
ordinary surface syntax.

`MergeSpec.merge : List Action → List Expr → MergeSpec` carries the pair, one expression per value
column, and the merge is a relation on databases:

```lean
inductive MergeStep : Database → Database → Prop where
  | collide {db d f decl} {as bs a b vs : List Term} {body res} :
      db.sig f = some decl → decl.merge = some (.merge body res) →
      as.length = decl.arity → bs.length = decl.arity →
      Term.app f (as ++ a) ∈ db.terms → Term.app f (bs ++ b) ∈ db.terms →
      CongList db as bs →
      evalActions { db with env := mergeEnv a b } body = some d →
      Expr.evalList d.sig res d.env = some vs →
      MergeStep db { d.addTerm (.app f (as ++ vs)) with env := db.env, rules := db.rules }
```

* **The `arity` premises are load-bearing, not typing.** An entry is now one flat term, so
  `f(A, 1)` splits into key and value columns three ways and **only the declaration knows which**.
  Without `as.length = decl.arity` the rule may take the split `key = []`, under which every entry
  of `f` is congruent-keyed with every other and the trigger fires on all of them. So
  `FnDecl.arity` is semantically load-bearing, which its docstring used to deny — it is what
  recovers the key/value boundary that a row type used to carry in its shape.
  `Database.NoMergeOk` carries the same two premises for the same reason.
* **Nothing is removed** — `db.Contained` the result, both colliding entries survive. That keeps
  every monotonicity lemma alive and leaves the old entries' proofs available for the `@MergeRow`
  naming them. **No guard on the collision** either; see the section of that name.
* **The combined entry is written at key `as` only.** Reads go through `Out`, which quantifies over
  congruent keys, so it is visible from `bs` too. This replaces egglog's rebuild-driven re-keying:
  keys are compared up to congruence rather than canonicalized.
* **The env is `mergeEnv a b` and nothing else** — the two outputs plus the body's `let`s. egglog
  binds `old`/`new` for a single-output function and `old0`/`new0`/`old1`/… per value column for a
  tuple output (`src/typechecking.rs:1066-1077`), and `mergeEnv` does both. *Every* column is
  bound, not just the one being computed: `MergeFn::OldCol`/`NewCol` exist precisely because "a
  column's merge may reference any output column of the old row". Globals desugar to nullary
  functions, so they are lookups, not environment reads.
* **The body runs once, before any column is computed** — `evalActions` produces `d` and every
  column of `res` is evaluated in `d`. egglog's order, not a choice: "Run the block's side effects
  once, before computing the merged values" (`egglog-bridge/src/lib.rs:1433`).
* **Both orders fire**, so a non-commutative merge relates `db` to two different results.

**Why not a value combiner.** `PLAN.md` proposed the observable value as a merge-fold over the
congruent asserted rows, no step at all. That dies here because **the union-find's merge is all
side effect**: its value output is `ordering-min old new`, which a fold gets right, but its `set`
of the displaced edge — the entire content of the union-find's transitivity — is invisible to any
fold over values, so path compression would have nothing to compress.

**One action language.** `Action` and `RowAction` were two types and are now one, forced by M11:
the encoding's rules write `(set (@AddView b a) (values rewrite_var ()))`, so `encode`'s target
language needs `set` in rule heads. Cost as estimated, ~24 match sites across 10 files; not
anticipated was that it drags the state with it, since `evalAction`'s `set` case has nowhere to put
a row unless `Database` has one. egglog restricts a `:merge` body to `let, set, union` while a rule
head also has `panic`, `delete`, `subsume`, `extract` and bare expressions. That difference is
recorded here rather than as a second type or a predicate — nothing in the model consumed the
predicate, since `MergeSpec.merge` already carries whatever body the declaration was given.

## Constraint (2): reading a table

`:default` was removed (`CHANGELOG.md:176`, #461), so a missing row behaves differently in the two
positions: in a **rule body** `(f x)` is not a lookup but a join atom (`src/core.rs:629-639`), so
no row means no match, silently; in a **rule action, top-level action or merge body** it *is* a
lookup, where a constructor mints a fresh e-class (`DefaultVal::FreshId`) and a custom function
panics (`DefaultVal::Fail`, `src/lib.rs:1122-1125`, `egglog-bridge/src/rule.rs:658-672`) —
`tests/merge_read.egg`.

**This section's conclusion is superseded**, and the paragraph above is what survives it: the
record of *why* the model's restriction is a restriction and not a simplification. It concluded
that evaluation must therefore be a relation `Expr.MEval` reading `Database.Out`. The model instead
**forbids the lookup** — reading is the query atom `Pattern.values` and nothing else (`PLAN.md`,
"Reading is a query atom") — so `Expr.eval` is a function of the signature alone and the whole
`MEval` family is gone. The step relations stayed relations for an unrelated reason, the merge
phase; and `programStep_isSome` needs `Program.Evaluable` beside `WellScoped`, because `Expr.eval`
returns `none` at a lookup and at a mis-sorted primitive.

### Why the reader over-approximates

The one read that remains — the row atom, and `Database.Out` beneath it — takes *any* recorded
output rather than the current one, for two reasons.

**A "current value" usually does not exist.** Under `:merge old` (`merge a b = a`) every recorded
output absorbs, so a greatest element is not unique; under `:merge new` none absorbs, so there is
none. Both are ordinary: the encoding's own `(function @<Sort>Proof (<Sort>) @Proof :merge old)`
is the first, and egglog's tests use `:merge new` widely (`luminal-llama.egg`,
`factoring-multisets.egg`). egglog resolves both by *insertion order*, which a `Set Row` cannot
express and which the `Set` was chosen to avoid. **And over-approximating is sound for proof
soundness**, for the append-only reason above.

#### Why a maximum and not a fold

`Database.Current` survives as a derived definition,
`db.Out f as vs ∧ ∀ ws, db.Out f as ws → le ws vs`, used only by difftest and M11's simulation
theorem — never by evaluation. `PLAN.md` wanted the *fold* proved well defined "when the merge is a
semilattice join, using Mathlib's `SemilatticeSup`", but a fold over a set is well defined only
once the combiner is proved commutative and associative, whereas a greatest element is unique from
**antisymmetry alone** (`Database.current_unique`, three lines, no `Finset.fold` argument
anywhere), and for a `SemilatticeSup` merge the greatest element *is* what the fold
computes. `le` is a parameter rather than an instance because the order is per function — one
untyped `Term` carries every sort — and it orders whole rows, since a multi-column merge can
settle its columns jointly.

### Primitives without churning `Expr`

`ordering-min`/`ordering-max`/`min`/`max` are `Expr.app` of a *reserved name* resolved by
`Prim.ofName` ahead of the signature, not a new `Expr` constructor. It is what egglog does (a
primitive shares a namespace with user functions and shadows one of the same name), and a new
`Expr` constructor would make every existing `cases e` in `Proofs/Eval.lean`, `Proofs/Match.lean`
and `Proofs/Interp.lean` non-exhaustive, an error rather than a `sorry`. While two evaluators
coexisted, only one of them resolved reserved names, and `execM_reachable` carried a
`Program.NoPrim` hypothesis to keep them apart; with one evaluator that hypothesis is gone.

`min`/`max` are in `Prim.ofName` for the same reason, and the three things that went wrong before
they were — non-idempotent merging, a row set that squared per pass, and a rule reading a term
where egglog has a number — are under "What the widening and the composed interpreter found".

## The term order

One definition, two deliberately distinct jobs. **(a) A spec primitive**:
`ordering-min`/`ordering-max` are part of the *program* the encoding writes — egglog's union-find
merge body is `(set (@UF_<S> (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))`, and
`Encoding/Encode.lean`'s `mergeBody` is that at one value column, the proof column not being
emitted. Either way M11 cannot state `encode` without them, and they are where a termination
witness comes from, since a merge that keeps the smaller side descends. **(b) An implementation tie-break**:
`MergeStep` is non-deterministic in which collision fires, and ordering candidates by `Term.blt` —
literals, then arity, then name, then lex, with `orderingMin`/`orderingMax` defined from it —
makes the interpreter's choice deterministic. **The spec stays non-deterministic**; this is an
`Impl/` choice only. Structural size before lexicographic, so "keep the smaller side" descends;
`Term.blt_linear` follows from `blt_asymm`/`blt_total`/`blt_trans`.

### The representative deviation

**`Term.blt` keeps a deterministic structural order and does not model egglog's allocation order**,
and it is not invisible to `(print-size)`: the repros below differ in row counts. It is worse than a
fidelity gap, since the operator is not congruence-stable and that blocks a proof — and, as the
subsection at the end shows, it is not the *order* that is at fault.

Scope: this is about `ordering-min`/`ordering-max`, and *not* about which of two colliding rows is
`old`. That one is allocation order too, and `Impl/` does model it by reading `FDatabase.terms`'
order — "`old` is the row at the canonical key". The same repair is unavailable here, and not for
want of a database to read: handing the operator one changes nothing, as the subsection below
proves.

egglog's `ordering-min`/`ordering-max` compare the `Value` word a term is stored as
(`egglog/src/lib.rs`, `add_primitive!(&mut eg, "ordering-min" = |a: #, b: #| -> # { if a < b { a }
else { b } })`), and a `Value` is a `u32` **id handed out in allocation order** within a session.
`Term.blt` compares structure. So the two pick different class **representatives**, deliberately —
matching egglog would mean threading a session-wide allocation counter through `Database`, which
would not buy congruence-stability anyway.

The invisibility claim holds only under two side conditions, and both are routinely violated: the
merge function must never be **read**, and its representative must never be used as a **key**. The
proof encoding does both — it keys `@UF_<Sort>` on `(ordering-max old0 new0)`. Two repros, run
against `target/release/egglog`:

**(a) An eq-sorted merge, read back.** With `(function UF (Math) Math :merge (ordering-min old
new))`, `(set (UF (A)) (Y))`, `(set (UF (B)) (X))`, `(union (A) (B))` and rules
`(rule ((= (X) (UF k))) ((HitX)))` / `(rule ((= (Y) (UF k))) ((HitY)))`, egglog prints
`(HitX 0) (HitY 1)` — it keeps `Y`, the term created first. This model keeps `X`, because
`"X" < "Y"` structurally, and predicts `(HitX 1) (HitY 0)`. Swapping the two `set`s so `X` is
written first makes egglog keep `X`, so egglog's choice is **order-driven where this one is
name-driven**. Row counts see it: `HitX` and `HitY` differ.

**(b) A negative `i64`.** With `(function D (Math) i64 :merge (ordering-min old new))`,
`(set (D (A)) -1)`, `(set (D (A)) 1)` and `(rule ((= -1 (D k))) ((Hit k)))`, egglog settles on `1`
and prints `(Hit 0)`; this model settles on `-1` and predicts `(Hit 1)`. The mechanism is the same
allocation order: an `i64` in `[0, 2³¹)` is stored *unboxed* as itself, and every other `i64` —
negative or `≥ 2³¹` — is interned and stored as `2³¹ + index` with `index` handed out in order of
first interning (`egglog/core-relations/src/base_values/`, `impl_medium_base_value!` and
`BaseInternTable::intern`). So `1` sorts below `-1`, and between two *interned* literals egglog's
answer is not even a function of the two numbers — it depends on which the session saw first.

#### It is not the order: **no** choice operator is stable

The cheapest witness first: after `(union (f 1) (g 1))`, `orderingMin (f 1) (f 2) = f 1` while
`orderingMin (g 1) (f 2) = f 2`, so replacing an operand by a congruent one gives a non-congruent
answer. That kills "a run under a congruent environment records the run under the original", which
two of the three `Recorded` transports spend — and is why they are proved under a condition that
makes congruent-but-distinct impossible instead.

**Superseding everything that treated this as a defect of `Term.blt`.** The obstruction is not the
order and not the missing database: it is that a choice operator has to commit to a **side**, and
`Recorded` lets a congruence identify any two non-literal terms. The condition the transports would
otherwise need is *stability*: for `A.Recorded C` with both states well formed, on arguments `C`
sees as congruent, evaluation in the specification's `A` and in the implementation's `C` must give
congruent answers. Stated at the strongest hypothesis (bare `Cong C`) and the weakest conclusion
(`CongOn C`), so refuting it refutes every weaker reading. Against it — machine-checked and
`sorryAx`-free. The names below live in **probe files outside the repository**, at
`.claude/jobs/0f6e77e4/tmp/Choice{1,2,3}.lean`; they still compile, but nothing in `lake build`
checks them and they import each other, so `LEAN_PATH` must include that directory. **They stay
out of the tree by decision, not by omission**: they justify the *shape* of a hypothesis rather
than supporting a theorem, so nothing breaks if they rot, and the write-ups here are detailed
enough to re-derive them.

* **The general impossibility** (`no_stable_choice`). No operator that answers with something
  congruent to one of its arguments and makes the same choice on `(x, y)` as on `(y, x)` is
  stable. The condition is not vacuous — projections and constants satisfy it (`fst_stable`,
  `const_stable`) — but a union-find parent chosen by argument *position* is not a parent, since
  `MergeStep.collide` fires on the two colliding entries in either order and would write both
  `@UF(y) ↦ x` and `@UF(x) ↦ y`. Symmetry up to congruence, which is all a union-find needs, is
  refuted too. `orderingMin_not_stable` then refutes today's operator **from its shape**, so
  swapping `Term.blt` for e-class ids changes nothing.
* **A database argument buys nothing.** The impossibility is proved of operators that *take* a
  `Database`, so neither the allocation counter above nor a new operator baked into the language is
  a way out. A database-aware `Expr.eval` would also stop being computable, so `Impl/` would
  compute a different function and would need exactly the condition just refuted.
* **Class-min fails, and the reason is the shape of the refinement** (`cmin_not_stable`). Picking
  the least member of the argument's congruence class *is* a function of the classes **within one
  database** — `cmin_congr` gets the answers literally equal, not merely congruent — which is why
  it looks like the fix and why egglog's e-class-id order is stable *in one run*. The refinement
  compares two databases: `C` holds terms `A` never built, so a class of `C` is a larger set, its
  minimum can be a term `A` has never seen, and that term can sit on the far side of the other
  argument and flip which class the operator answers from. A class minimum also need not **exist**
  — `Term.blt` orders by an unbounded integer over a `Set`.

**One caveat, recorded as unverified rather than proved.** The refuting state pair — built at a
hand-made witness operator, `Choice3` — was never exhibited as *reachable* by a program. What is
refuted is the stability condition at an arbitrary pair of states, which is what the transports
quantify over and so is enough for them; it is not a program whose contract breaks.

`min`/`max` broke the same lemma for a second and **separable** reason, matching on `Lit`; that
half is **closed** — `evalAction` refuses a `union` on a literal, so a literal's class is a
singleton and `Prim.apply_cong` follows. The `ordering-*` half is what is left, and nothing closes
it.

**Consequence.** The deviation is a hypothesis of any future simulation theorem against real
egglog **and** an obstruction inside this development. `Term.blt` cannot leave `Spec/`, because
`encode` is unstatable without the two primitives ("The term order", above), and there is no better
operator to move to. So the development **sidesteps the question** instead: `execM_contained` takes
`p.UnionFree`, under which every reachable state is diagonal, nothing is congruent-but-distinct, and
no choice operator is ever asked to be stable. Restricting the transported positions to
ordering-free expressions is the *other* repair and is the second arm being added now; it reaches
`RuleResults.mono_recorded`, and — **recorded as structural reasoning, not as a proof** — is
believed not to reach `MergeStep.transport_recorded`, whose `mergeEnv` is built from value columns
`Recorded` may move before any expression is evaluated. No ordering-free counterexample to that
lemma was built. Only a union-find-free encoding retires the primitives and with them both halves
of this; the *encoded* fragment escapes by yet another route, `ENCODING.md`.

## Multi-column outputs

egglog's tables are multi-column and the encoding depends on it: `@UF_<Sort>` carries a parent
*and* a proof, `@<C>View` an e-class and a proof. Hence `FnDecl.outArity` beside the key `arity`,
and an entry term whose children are the key followed by **all** the value columns —
`f(a…, v…)`, with `outArity` of them. Where a row type carried the split in its shape, the term
carries it in `FnDecl.entryWidth` and the two `arity` premises on `MergeStep`.

**The merge result is a `List Expr`, one per value column**, where surface syntax writes one
tuple-valued `(values e₀ e₁ …)`. This follows the backend, already per column —
`assert_eq!(resolved.len(), schema_math.n_vals(), "merge for {f} must have one entry per value
column")` (`egglog-bridge/src/lib.rs:1405`) — and avoids a tuple constructor in `Term`, which would
make every existing `cases t` in the M10 proofs non-exhaustive. **Recorded as a deviation from
surface syntax**: a source program writes `(values …)` and the model takes the list it denotes.

**Reading a column other than the first is `Pattern.values`**, egglog's tuple destructure
`(= (values v…) (f a…))`, and it is the *only* way egglog offers: a tuple-output function cannot
be evaluated as an expression (`eval_resolved_expr` panics on `values`, `exec_state.rs:293`) and
cannot be extracted, whose error message says "Read its columns in a rule with `(= (values ...)
({0} ...))` instead" (`typechecking.rs:1639`). egglog recognizes the shape inside an ordinary `=`
fact, in either argument order, and lowers it to the atom `f(a…, v…)` (`match_tuple_destructure`,
`ast/mod.rs:1770`). Since every read is an atom, the destructure is now the model's **only** read,
generalized to any width, and `Expr.MEval.lookup` is gone — see `PLAN.md`, "Reading is a query
atom". The historical passages below that mention `MEval.lookup` or `execExpr`'s lookup branch
describe the state before that change.

**Multiple columns and the functional dependency never interact.** The dependency is `Cong.congr`,
which fires at a constructor, and a constructor has exactly one value column — its own application,
which is why its entry appends nothing. `MergeFn::UnionId` is documented in the backend as "Use
congruence to resolve FD conflicts", so it *is* that rule. The **encoded** program has no
constructor tables of that kind at all: `@UF_<Sort>` and `@<C>View` are `MergeFn::Block`s whose
columns are expressions (`ordering-min old0 new0`, `()`), resolving congruence through the body's
`set (@UF_Math …)` plus the `@UF` table — so in the target, congruence is **entirely simulated**,
exactly the M11 simulation obligation.

**One place this is coarser than egglog.** A merge kind is per *function* here and per *column*
there: `MergeFn::Columns(Vec<MergeFn>)` lets one function have `UnionId` on column 0 and `Old` on
column 1, which `MergeSpec` cannot express. Nothing needs it — the encoding's tables are uniformly
`Block`s with expression columns, source constructors single-column `UnionId`. The faithful shape
would be a per-column merge kind beside a single `actions` list run once before any column, under
which the functional dependency holds of a column and not of a function. Not done: it would put a
per-column signature lookup into the congruence rule for a case neither language produces.

## Restrictions on `encode`'s domain (M11)

`encode` is defined only for source programs **whose functions have no `:merge` action block**,
permanently rather than as a gap to close: the encoder itself rejects such a program with
`ProofEncodingUnsupportedReason::MergeActionBlock`, because "a `:merge` action block runs actions
before its result; the proof encoding only instruments the merged value, so mark it unsupported
rather than emit silently-incomplete proofs" (`proof_encoding_helpers.rs:1088-1096`). Not a
contradiction with the encoder *emitting* such blocks — `@UF_<Sort>` and `@<C>View` are exactly
that shape — since it knows what its own blocks prove and not what a user's does. Same check also
rejects `:no-merge` on an eq-sorted output (`NoMergeEqSortFunction`).

## Constraint (3): monotonicity

Discharged by the representation: in `Spec/` asserted equations only accumulate, a merge adds the
combined entry beside the two it combined, and there is nothing to overwrite. `Database.Contained`
is now a **single** field, `eqs ⊆ eqs` — the term and row clauses it used to carry are that clause,
since existence and entries both live in `eqs`. `MergeStep.contained`, `CmdStep.contained` and
`ProgramStep.contained` are what every M2–M8 lemma needs to transport; `Cong.mono` and
`Database.Out.mono` follow, and `Cong.mono` carries `Contained` and nothing else.

`CmdStep.contained` is also the formal content of the hard constraint **never delete a term or a
proof entry**, on which the encoding depends directly ("Nothing is ever removed from it, which lets
proofs refer to terms after they leave the e-graph"). `delete` and `subsume` are outside the
fragment and, when they arrive, must not touch term or proof entries; the encoding already defers
them to marker relations and deletes only the *view* entry.

### Why `Recorded` is weaker than `Contained`, and weaker than it was

`Database.Recorded` is the containment an implementation that **re-keys** can satisfy, and the
refinement chain cannot run on `Contained` alone. That is now **proved rather than asserted**, and
it bites inside a *single* merge round rather than only across commands:
`mergeRound_contained_needs_recorded` exhibits a state satisfying both of `mergeRound_contained`'s
own premises — `FDatabase.Inv` and `Signature.MergesLegal` — whose one pass reaches a database
that **no** merge closure from that same state contains. The two sides start out literally equal,
so the gap is not an artifact of an already-weakened relation.

**The rebuild is not what moves the denotation, and text blaming it is imprecise.**
`rebuild_toDatabase` is `rfl`: a rebuild writes `rows`, which `toDatabase` drops. What moves the
denotation is the merge write *after* it. `rebuild` re-keys a `:merge` row onto its class's
canonical member — the oldest congruent term — and `mergeOneOriented` then writes the combined
**entry term** at that rebuilt key, into `terms`. `MergeStep.collide` may write only where an
entry already sits, at one of the two colliding keys, and it is symmetric, so both of its choices
are ruled out at once. When the canonical key belongs to a **third, older term carrying no
entry**, the implementation writes where no specification run can.

The witness is minimal: `(A) (B) (C)` nullary and `(function Dist (Math) i64 :merge new)`, with
`(A)` built first so that it is canonical and carries no `Dist` entry; then `set (Dist B) 1`,
`set (Dist C) 2`, `union C A`, `union B A`. One implementation pass writes `Dist(A, 2)`, and
`spec_never_distA` shows no `ProgramStep` on that program ever reaches a state holding any
`Dist(A, …)`. Kernel-checked: the sealed well-founded `closure` is replaced by a proved
description of it, thirteen pairs, after which the pass reduces and `decide` goes through. These
two live with the refutations under "The representative deviation", in probe files outside the
repository — they compile, nothing in `lake build` checks them, and this description is what a
reader of the tree alone has.

**Both witnesses `union`**, and they have to: re-keying moves a key only where congruence relates
two terms, and only a `union` puts two distinct terms in one class. So the programs that show
`Recorded` is necessary are exactly the ones `execM_contained`'s `p.UnionFree` excludes — on the
fragment the theorem covers, its conclusion is a `Contained` claim wearing `Recorded`'s clothes.
`Recorded` stays in the statement because it is what the second arm will need, not because the
first arm needs it.

It used to be three clauses — `terms ⊆ terms`, a row clause through `Out`, and `eqs ⊆ eqs`. It is
**one** now, and uniformly weakened: every `p ∈ d₁.eqs` is matched by *some* `q ∈ d₂.eqs` whose two
endpoints are `CongOn`-congruent to `p`'s. So a term of `d₁` is no longer a term of `d₂` — it is
congruent to one — and a lemma along `Recorded` cannot conclude `Cong d₂ a b` on the nose.

The weakening is forced, not chosen. `Cong` **cannot state** the old row clause: `Cong.congr`
requires both applications to be present, and the whole point is that the specification never built
the implementation's re-keyed entry. `CongOn` can, because it adds the operands first. And it goes
through `CongOn` for the same reason everywhere rather than only at entries, because there is no
longer a row clause to treat specially.

Checked non-vacuous rather than assumed so: the only database `Recorded` in the empty one is a
database with no equations at all (`Proofs/Counterexamples.lean`'s `recorded_empty`). That check
is worth repeating on anything else phrased through `CongOn` — `ENCODING.md`'s second finding is a
statement of exactly this shape that turned out to say nothing.

**Where it is not weaker at all — and this is the case the development now runs on.** On a recorder
whose asserted pairs are *all reflexive* (`Database.Diag`) nothing is congruent-but-distinct for a
re-keying to hide behind, so `d₁.Recorded d₂` yields `d₁.Contained d₂` outright. That was the probe
`recorded_iff_subset`; it is a library theorem now, `Database.Recorded.contained_of_diag`, and it is
what both surviving `Recorded` transports are proved by. Two fragments never leave such a state: a
program with no `Action.union`, which is `execM_contained`'s `p.UnionFree`, and an encoded program,
which is `ENCODING.md`'s reason to restate M11 rather than abandon it.

**`Recorded` is transitive, and what it took is worth recording.** The obstacle is the `CongOn`:
composing two hops leaves a derivation in `d₃` extended by the *middle* database's terms, which
`Recorded` gives no reason to be terms of `d₃`. What removes the extension is **conservativity** —
adding reflexive equations for terms a database does not hold cannot relate two terms it does —
proved through a `Quot (Cong db)` model, roughly 315 lines. Not the congruence-closure-completeness
induction that was predicted, and it is what `Cong.mono_recorded` needs too, pinned to the ambient
`trans` actually uses. The price is two `WF` premises on `trans`, discharged locally at both call
sites. Conservativity does **not** rescue the three transports:
`Database.Out` and `MergeStep.collide`'s `CongList` premise want *bare* `Cong` at `d₂`, and
conservativity discharges the ambient only when both endpoints are already terms of `d₂`, which
`Recorded` does not supply — the key `d₁` searched at need not be a term of `d₂` at all. What
closed them instead was diagonality, below, for two of the three; the third,
`Database.Out.mono_recorded`, is **deleted as false in every form that keeps the value columns**,
and its consumers now take the `Out` facts their caller already maintains as premises.

**What monotonicity costs.** egglog *deletes* the displaced row and `Spec/` keeps it, so `Out` is a
sound over-approximation: every value egglog computes is derivable here, plus stale ones it has
removed. For `@UF_<Sort>` that is not merely harmless but right: any parent a term ever had is
genuinely equal to it. (`Out.union_cong` used to be named here as the lemma saying so; it was
never ported, and nothing needs it.)

## Constraint (4): firing counts

**What egglog does.** Merges are *deferred*: rule execution stages rows into mutation buffers, and
`Database::run_rule_set` searches and applies every rule before calling `merge_all`
(`core-relations/src/free_join/execute.rs:653-655`). `merge_all` then runs **to a fixed point**
(`free_join/mod.rs:546-628`, `:686-689`) — a merge's own `set` re-notifies and is picked up next
iteration. Within one key, merging is a left fold in staging (FIFO) order, and **the first row for
a fresh key is inserted verbatim with no merge call** (`table/mod.rs:715-790`, `:742-768`); in
parallel mode the cross-buffer order is not deterministic. Top-level actions take the same path, so
each top-level `set` is its own merge phase (`src/lib.rs:1490-1512`).

### Saturation is a hypothesis, not a step

Merge closure is a *phase* of a command — `CmdStep` is `cmdEffect` then `MergeClosure`, so at
`.run` it is `RunRules` then the closure — and the deferral is faithful: no rule sees another's
merged value within a round. But `CmdStep` deliberately does **not** require the closure to have
saturated, and an earlier draft that did was *wrong*, not merely strict: `∀ db', ¬ MergeStep db db'`
is **unsatisfiable**, because nothing is removed, so both colliding entries are still present after
the step and it applies again — forever. (With no guard on the collision there is a second,
independent reason: every entry collides with itself.) Under that definition `CmdStep … .run` is
vacuous for every program with a real merge collision. The corrected form is "every step is the
identity",
`MergeSaturated db := ∀ db', MergeStep db db' → db' = db`, **assumed by the theorems that need it**
— simulation, and matching egglog's row counts — rather than built into the step. This removes
termination from the spec entirely, which is what the invariant framing buys.

### No guard on the collision

`CongList` is reflexive on terms the database holds, so an entry collides with **itself**, and
`MergeStep` has no `a ≠ b` side condition to stop it. An earlier draft had one, reasoning that
egglog merges a *retained* row against an *incoming staged* one and so never self-merges, and that
a state relation cannot see how often a value was staged. That reasoning is about *matching* egglog, and
it made the guard the one **under**-approximation in an otherwise over-approximating design, the
unsafe direction: it leaves egglog reaching states the model never checks, so the safety invariant
does not transfer to real egglog.

Without the guard the model covers egglog unconditionally. egglog skips a collision that changes no
value column whenever the function declares `:internal-identity-vals` **or** its `:merge` carries an
action block, and fires on it otherwise; `MergeStep` fires either way, and on the self-collision
egglog never even sees. Over-approximate in every case. **The safety theorem therefore needs no
scope condition on the signature at all** — no `merge (x, x) = x`, no identity-guardedness
hypothesis. (`Impl/` does take the skip, because it has to predict row counts and a `:merge` body
*writes*; that is `FDatabase.noConflict`, and firing fewer steps is what its containment contract
allows. See "A collision that changes nothing runs no body" below.)

~~Congruence **monotonicity** does need a signature condition, and it is not optional.~~
**Superseded, and this is where the second congruence relation cost the most.** `MCong.fd` fired
only where the signature said "constructor", so a redeclaration destroyed a derivation while adding
nothing, and the monotonicity lemmas had to carry `d₁.sig = d₂.sig`. `Cong` reads `eqs` and nothing
else, so `Cong.mono`, `CongList.mono` and `Database.Out.mono` carry only `Database.Contained`, the
counterexample that used to sit here is provably false and deleted, and `CmdStep.mono_recorded` and
`ProgramStep.mono_recorded` lost their `Cmd.DeclFresh` hypothesis.

Two consequences, both intended.

**Idempotent merges gain vacuous entries, not divergence.** The union-find's body on a
self-collision is `(set (@UF_<S> (ordering-max p p)) (values (ordering-min p p) ()))`, a reflexive
self-edge; `Cong` derives only `p = p`, which already holds because `p` is present. In proof mode it
writes extra proofs of `p = p`, which are *valid* — and not observable, because egglog's
`print-size` filters `internal_hidden || internal_let` and reports a view under its
`term_constructor` name, which is exactly why `files.rs` shares one snapshot between normal and
term-encoded runs, so `@UF_*` and `@*View` never appear in a diff. `MergeStep.self_id` states the
fixpoint: a body that adds nothing and returns the output it was given makes the step the identity,
which keeps `MergeSaturated` reachable.

**That fixpoint is exactly what `Database.WF.eqsRefl` exists for**, and it is worth seeing why,
because the invariant looks like bookkeeping and is not. `MergeStep` ends in `addTerm`, which writes
reflexive equations. If a term can be present *without* `(t,t) ∈ eqs` — reachable by `symm` and
`trans` from a non-reflexive pair, so `eqs = {(a,b)}` with `a ≠ b` is such a state — then `addTerm`
on a term the database already holds is **not** the identity, the self-collision that always applies
changes the state, and nothing is `MergeSaturated` however settled it looks. With `eqsRefl` in `WF`,
"the term is present" and "the equation `t = t` is asserted" are interchangeable and `self_id` can
conclude database equality again.

**`:merge (+ old new)` diverges.** The self-collision derives `2v`, `3v`, … forever, where egglog
with a single `set` merges nothing. Intended: such a program's egglog result is insertion-order
dependent, so there is no fixpoint to denote and diverging is more honest than inventing an answer.
The two changes are coupled — this works only because `MergeSaturated` is the "no step *changes*
anything" form, under which `ordering-min` self-merges saturate and `+` correctly does not.
`PLAN.md`'s note that naive and seminaive "genuinely diverge" for a non-idempotent merge is right
about egglog and does not apply here, since this model has no firing count at all.

### `:internal-identity-vals`, and the skip that is now the default

In full (`egglog-bridge/src/lib.rs`, `MergeFn`): compare the first `k` **value** columns by raw
equality; if they agree, skip the action block entirely, keep the *old* value in every column
including the payload, and leave the row untouched with its old timestamp so seminaive does not
re-fire. The encoding's use is identity column = e-class, payload = proof, so a collision agreeing
on the e-class keeps the existing proof. Contract: only valid when `merge (x, x) = x`
(`egglog-bridge/src/lib.rs:227-231`). The count is a `Nat` and not a `Bool` because it marks a
**prefix** of the value columns — `:internal-identity-vals 1` on `(Math) (Math @Proof)` marks the
parent column identity and the proof column not, so re-setting the same parent with a *different*
proof keeps the old row and its old proof. The comparison is
`cur[id_lo .. id_lo + k] == new[id_lo .. id_lo + k]`, and when it holds every column, payload
included, takes the old value.

**Since `20d1461` (issue #59) the undeclared case is not "no skip".** `unchanged_width` is now
`n_identity_vals.or_else(|| (!actions.is_empty()).then(n_vals))`: a `:merge` with an **action
block** and no declaration takes the same skip over *every* value column. A single-expression
`:merge` still never short-circuits, deliberately — it may be non-idempotent, and `:merge (+ old
new)` on two rows holding `2` gives `4` on both this binary and upstream.

**That made the skip a difftest-fidelity concern, and this file said it was not.** The earlier
conclusion here — "the `print-size` filtering above means it is not a difftest-fidelity concern
either" — was about the *declared* form, which only the encoding's own views use and which
`print-size` hides. It does not survive the generalization: the difftest generates ordinary
`:merge` action blocks, they now skip by default, and comparing whole *rows* rather than value
columns cost a real divergence (recorded below). `Impl/Merge.lean`'s `FDatabase.noConflict` is the
model of the default form.

**`identityVals` stays out of `FnDecl`**, now for a narrower reason: what is left unmodelled is the
*prefix* — `k < n_vals`, where the payload columns may differ and the row is still kept. Nothing in
the difftest fragment declares it, and the trigger to revisit is unchanged: rendering `encode`'s
output to `.egg` and running it in real egglog.

### `:no-merge` collisions, out of scope

The other deliberate gap on this constraint, and the one where the model is **looser** than egglog
rather than stricter. A `:no-merge` collision is a *program error egglog rejects at runtime*, and
this model does not model runtime rejection: there is no error state for a step to enter, and the
model should not try to cover the whole egglog language. `Database.NoMergeOk` states the condition
and **nothing consumes it**; `Impl/Merge.lean` does not check it either, and `MergeStep` fires only
on `.merge`, so a `.noMerge` collision is simply inert here.

Confirmed against the binary: `(function Dist (Math) i64 :no-merge)`, `(set (Dist (A)) 1)`,
`(set (Dist (B)) 2)`, `(union (A) (B))` gives `[ERROR] Panic: Illegal merge attempted for function
Dist` and exits 1, where this model silently keeps both rows and predicts `Dist 1`. With **equal**
values the two agree — the same program with both values `1` prints `(A 1) (B 1) (Dist 1)` and the
model predicts the same — so it is exactly the conflicting-value case that is scoped out, which is
why the difftest's `:no-merge` cases keep their keys distinct.

`MergeSpec.noMerge` itself stays. Scoping out the *collision behaviour* is not "drop the
constructor": the proof encoding declares its proof nodes with `:no-merge` (`Encoding/Encode.lean`'s
`termDecl`), and `Impl/Merge.lean`'s merge phase turns on a `.noMerge` row never being deleted,
"deleting one would delete a proof".

## Constraint (5): base sorts

**Not done, deliberately.** `Lit` is still `Int` only and `Term` is still untyped. Instead:

* The FD's key comparison is `CongList`, comparing every argument position by congruence. On a
  base-sorted argument congruence degenerates to equality, since a base value is never unioned, so
  the sort discipline is **not needed for the FD to be correct** — only for typing. That is why M9
  can land without it.
* **An entry term is not a value, and only the untypedness lets it be one.** `f(a…, v…)` names no
  e-class and cannot be unioned; it is a table row wearing a term's clothes. A sort discipline would
  say so. Untyped, the only defence is to keep the two apart wherever it matters, which is one
  place: `Impl/Interp.lean`'s `valueTerms` filters merge-function entries out of the matcher's
  assignment universe, so no variable is ever bound to one. `Spec/`'s `ValidEnv` does not forbid the
  binding, which is why that filter is a refinement rather than an equality.
* **The signature is now needed where it was not.** `Term.ctorRowList` — the entries a term
  contributes to `Impl/`'s index — takes a `Signature` argument, because `addTerm` now sees merge
  functions' applications and synthesising a constructor row for one would give that name a second,
  bogus key class. The old claim that it needs no signature rested on "a `Term` only ever contains
  constructor applications", which entry terms falsify. Under sorts this would be a typing fact
  rather than a filter.
* The **arity** half of the discipline is done and separable from the sort half; arity needs no
  sorts, which is why it landed first. It now exists in three places, and the three are *not* one
  definition — a drift risk worth naming.
  - `Impl/Check.lean`'s `arityOk` and `Spec/Scope.lean`'s `WidthOk` — the `Bool` the difftest
    enforces before writing a case, and the front end's sixth check. `PLAN.md`, "Arity checking",
    has what each demands and where they can drift.
  - `Proofs/Merge.lean` carries `Action.SetWidthOk` — `WidthOk`'s `set` clause and nothing else —
    bundled with `SetLegal` into `Action.WriteLegal`, and that is what funds `IndexOk.width` and
    `MergeStep.collide`'s two `arity` premises. Substituting `Spec/`'s check is **not** a drop-in:
    `WidthOk` also constrains applications inside expressions, and that half is not preserved by
    `Function.update` at a fresh name — an action applying an undeclared `f` satisfies it vacuously
    and stops the moment `f` is declared — which makes `Action.WriteLegal.update` false, and
    `WriteLegal.update` funds the containment chain. Repairing it needs a "this action does not
    mention `f`" clause threaded through `ProgramLegal`, i.e. a redesign, not an edit.

  The state-level counterpart is `Database.DeclaredTerms`, "every application the database holds
  has its declaration's head and width". `SetLegal` and `WidthOk` are what keep it true of what a
  `set` writes — `SetLegal` decides *which* width an entry is held to and `WidthOk` supplies the
  counts, and alone neither says anything — but it still sits **outside** `Database.WF`, so it is
  assumed where needed rather than carried. Putting it in `WF` needs preservation lemmas through
  `evalAction` and `MergeStep`, and is the remaining follow-on.

The shape once sorts land, where the model's single untyped `Term` finally dies, is
`Sort := eq String | i64 | str | unit` with `FnDecl` carrying `inputs`/`output`/`merge`, `Scope`
becoming `List (Var × Sort)` and `Expr.Scoped` a typing judgment. Two side conditions the sorts
would buy: a constructor requires an eq-sorted output (egglog rejects `:no-merge` on an eq-sort output
under the term encoding, `proof_encoding_helpers.rs:1067-1086`), and telling an entry term from a
value becomes a typing fact rather than a filter. `Lit` also wants
`.str` and `.unit` before M11 — `@Rule_<k>` carries a rule *name* and the no-proof column is
`Unit` — which is cheap and independent of everything above.

## Constraint (6): termination

Out of the spec entirely: `MergeClosure := Relation.ReflTransGen MergeStep`, no fixpoint, no
measure, no saturation requirement anywhere in `Spec/`. The reason is sharper than "merges may not
terminate": **a merge body can build terms**, so the candidate universe grows as the closure runs —
exactly what `Impl/Closure.lean`'s `closure` relies on not happening, its well-founded measure
being `(candidates terms).card - rel.card` over a *fixed* `terms`. The congruence closure is fine:
`terms` and `eqs` are fixed while it runs, and the functional dependency adds no step to it at
all, since it is a rule of `Cong` over terms already there. Only the *merge* loop has no measure.

## The executable layer

`Impl/Merge.lean` runs the M9 semantics, `Tests/Egg.lean` renders a `Program` as `.egg`, and
`DiffTest.lean` writes the cases. Four things differ from `Impl/Interp.lean`, each a design
decision, and `Impl/Merge.lean`'s header repeats them.

**The contract is containment, not equality**, because `Impl/` deletes — see the next section.

**`mergeRound` is one pass and `execCmdM` iterates it to a fixpoint**, as `merge_all` does. One
pass alone is sound *because* `CmdStep` carries no `MergeSaturated` requirement, so a prefix of the
closure is a reachable state; but it is not enough now that a rule can read a value, since one pass
leaves three colliding entries at a key class as two. There are **two** saturators and they are not
interchangeable: `mergeSaturate` takes a termination witness (`Acc`) and is the faithful shape,
kept for the record; `mergeSaturateF` takes fuel and is what `execCmdM` actually runs. Fuel is
allowed here only because it **fails rather than returning a prefix** — a divergent merge makes
`execM` `none`, which the difftest reports as `STUCK` and a mismatch. That is what keeps it outside
this file's own objection to fuel ("returns a wrong answer where *no answer* is correct"), and the
distinction is worth keeping straight: the objection is to fuel that *answers*.

**A read has to pick**: `patternHolds`' row scan sees a superseded output where the spec allows any,
and where egglog sees only the current one.

**The congruence closure is unchanged**, and for a reason that needs no side condition: `Cong` reads
`eqs` alone, so `closureF` is `closureTotal` over the terms and equations whatever the row index
holds (`mem_closureF_iff`, which lost its well-formedness hypothesis with the rows). The functional
dependency adds nothing to decide.

### Row counts survive, and why that matters

`keyRowCount` counts congruence classes of **key tuples**, and that count is invariant under the
merge phase — the argument is at its definition in `Impl/Merge.lean`, and it is why the difftest
can compare row counts at all.

What belongs here is that the invariance is **not proved**. `FDatabase.mergeRound_rowCount` stated
it and was false as stated — `addRow` inserts the *result's* terms with their index rows, so a
merge whose result builds an application adds a key class to a different function's table — and is
deleted, with the counterexample at the deletion note. What the difftest relies on is that
statement with `hpure` strengthened to "the merge result is a term the database already holds",
which every generated case satisfies, results being `i64` literals. Nobody has proved that one.

### The difftest fragment

Deliberately narrow, and the narrowness is the interesting part.

* **Every generated merge is idempotent** (`min`, `max`, `old`, `new` on `i64`). A non-idempotent
  one would give extra firings and extra values under our over-approximating reads, so a row-count
  difference would be this model's design showing rather than a real bug. **Non-commutative is a
  different question**, and excluding `old`/`new` on this bullet's reasoning was a mistake: they are
  idempotent and, unlike `+`, completely determined in egglog. While every generated merge was
  commutative, nothing could see which colliding row the model called `old` — see below.
* **Generated merge bodies are `let`-only.** A body that `set`s a side table would fire on
  self-collisions and in both orders, inflating that table's count for the same reason.
* ~~**Merge functions are written and never read.**~~ **No longer true, and it agrees.** This was
  the fragment's boundary, on the reasoning that a body atom reading a merge function binds *any*
  recorded output where egglog binds the current one. What closed it is `Impl/` deleting the rows a
  merge combined: the reference implementation now holds only the merged value, so a read sees what
  egglog sees. Reads are generated in both shapes egglog offers — `(Dist k…)` and `(= v (Dist k…))`
  — biased towards a key and a value the program actually writes, which took the reads that fire
  from 6 of 30 cases to 17 of 30; curated `read-exists` / `read-value` / `read-stale` /
  `read-congr` / `read-value-congr` / `read-nomerge` / `read-copy` sit beside them. Every one
  agrees. The *specification* still admits the stale read, which is the design showing rather than a
  defect.
* **Outputs are `i64`, keys are eq-sorted.** egglog typechecks a `(function …)` declaration, so a
  merge function needs a real output sort — this is where sorts finally bite. An eq-sorted output
  would dodge the base sort, but then `ordering-min` must render, and `Term.blt` is *structural*
  where egglog's is by allocation order, so the two would pick different representatives. **Row
  counts would not survive that** — repro (a) of "The representative deviation" is exactly this
  shape, an eq-sorted `ordering-min` merge read back by a rule, and its `Hit` counts differ.
  Eq-sorted keys also keep `Term.lit` out of constructor arguments, so `Egg.lean`'s standing
  literal mismatch stays out of the way.

The case that matters is `min-rebuild`, the shape of `egglog/tests/merge-during-rebuild.egg`: two
`Dist` rows whose keys are then unioned, so egglog's table drops from two rows to one. `min-congr`
does the same collapse through congruence rather than a direct union, and `min-rule` writes a row
from a rule head. These discriminate — a model that ignored key congruence would predict 2 where
egglog says 1.

## What the widening and the composed interpreter found

**`Action.set` takes a `List Expr` and `Pattern` gained `values`** — the state side was
multi-column from the start and the write and read sides were not, so a multi-column entry could be
*created* by a merge and never written or read. That was `CHECKER.md`'s one blocker on M11's proof
column; "Multi-column outputs", above, is the design.

**`Program.expectedSizes` now runs a composed M9 `execProgramM`.** It ran `Impl/Interp.lean`'s
`exec`, which evaluates with `Expr.eval` and never calls `mergeRound`, so `mergeOne`, `mergeRound`,
`execActions`, `execExpr`'s lookup branch and the destructure had **zero** differential coverage —
the suite's pass count said nothing about the merge implementation.

**`min` and `max` had to become primitives.** `Prim.ofName` knew only
`ordering-min`/`ordering-max`, so a `:merge (min old new)` body — the shape every merge case uses,
and the shape `tests/interval.egg` and `tests/merge-during-rebuild.egg` use — built the *term*
`min(5, 3)` where egglog computes `3`. Invisible while nothing ran the merge phase, and three
things went wrong the moment something did: no state was ever `MergeSaturated`, so `mergeSaturateF`
returned `none` for every case with a real collision; each pass wrote a genuinely new value at
every colliding key, so the row set squared per pass and **12 of 30 generated merge cases timed
out**; and a rule reading a merged value got a term where egglog has a number. `Prim.intMin`/
`intMax` on `Lit.int` fixed all three — 102 passed / 12 skipped became 114 / 0 / 0 — and saturation
became reachable again. The sharpest thing the coverage gap was hiding: the merge cases were
*generated* correctly and *predicted* by a merge implementation that had never been run.

**`Impl/` now deletes superseded merge rows; `Spec/` does not.** Both were append-only and the
contract between them was an *equality*, which is what forced `Impl/` to be append-only — making
the reference implementation faithful to this model and **unfaithful to egglog**, which replaces
the row. `Spec/` stays append-only, since the M11 safety invariant needs neither termination nor
confluence precisely because nothing is removed. `Impl/Merge.lean`'s merge phase drops the two rows
it combined and nothing else — never a term, never an equality, never a constructor row (which the
whole congruence argument rests on) and never a row of a `.noMerge`
function (how the encoding declares its proof nodes, so deleting one would delete a proof);
`FDatabase.mergeRound_confined` is that sentence, as a statement. Saturation then follows rather
than being hoped for: deleting the pair that fired strictly shrinks each colliding key class, so
`mergeSaturateF` terminates.

The contract **splits** rather than weakens. *Soundness* is a containment — the implementation
finds **fewer** results, never more, the safe direction because everything M11 reads is positive in
the state; `ValidSubst.mono` makes "fewer rows" mean "fewer matches", and `Cong`, `CongList` and
`Database.Out` are monotone already. `execM_contained` is the top-level statement.
*Completeness*, so containment is not vacuous, was to be two statements, and **only the first
survives**. On the constructor fragment the existing **equality** stands untouched, since no row
belongs to a `.merge` function, so `hasMergeRow` is false, the pass is the identity
(`FDatabase.mergeRound_eq_self`) and `exec_programStep` is outside the blast radius. On **lattice**
merges the implementation was to hold the `Current` value at each key class —
`execM_current_of_lattice`, false as stated and now deleted, so **nothing machine-checked says the
merge interpreter finds anything at all**; difftest is what rules out a degenerate one. For a
non-lattice merge `Current` does not exist and nothing was ever claimed.

`execM_reachable` applies to `exec` only, under `Program.CtorDecls` alone, whose necessity is
`Falsity.exec_programStep_needs_ctorDecls`: a `:merge` declaration lets an entry collide with
itself, so the specification reaches two states where the interpreter returns one (the witness is
in `Proofs/Counterexamples.lean`). `Program.SetLegal` used to sit beside it and is gone — what it maintained was `Database.CtorRows`,
which the refinement stopped reading when congruence did, and which is now deleted outright. What
replaced it on `execM_contained` is `FDatabase.ProgramLegal`, checked at the state each command
reaches rather than on the syntax: the legal-`set` clause got the column widths beside it
(`Action.WriteLegal`), declarations must name something the state does not mention
(`FDatabase.Unused`, since redeclaring `g` `:merge` after `g ()` exists moves `g`'s rows between
`IndexOk`'s clauses), and every declared `:merge` body obeys the discipline
(`Signature.MergesLegal`, which patches a real gap — `Cmd.SetLegal (.decl _ _)` is `True`, so
`Program.SetLegal` says nothing about a merge body).

**The over-approximation was observable, and `Impl/` no longer shows it.** Until a rule could read
a value column, no oracle could see that the model keeps every superseded output where egglog
deletes it. Now one can — minimal repro, machine-checked both ways:

```
(function Dist (Math) (i64 i64) :merge (values (min old0 new0) (max old1 new1)))
(set (Dist (A)) (values 5 1))
(set (Dist (A)) (values 3 7))
(rule ((= (values 5 1) (Dist k))) ((Hit k)))
(run 1)
```

egglog reports `Hit 0`: the merge replaced the row and `(5, 1)` is gone. An append-only
implementation reports `Hit 1`, because the superseded row is still there and the destructure reads
it. It is now a difftest case (`tuple-stale`, with the single-column `read-stale` beside it) and
**it agrees**. The *specification* still says `Hit 1` is reachable, deliberately: **this is the
design showing through, not a defect** — the over-approximation argued for under "Why the reader
over-approximates", in the safe direction, since a stale row is a row that really was written. What
changed is only which side of the `Spec`/`Impl` line it lives on.

**`old` and `new` were bound backwards, and nothing saw it**: `genMergeSpec` drew `min` and `max`
only, which are commutative, and `(print-size)` cannot see a value at all. It now draws `:merge old`
and `:merge new`, with eight curated cases pinning the four shapes. The fix got the *direction*
right and the *rule* wrong, and is subsumed by the next section.

### `old` is the row at the canonical key, and insertion age is only the tie-break

Every case the previous fix added agrees with both readings, so nothing caught it. **`old` is not
the row written earlier. It is the row already in the table.** egglog's insert calls the merge
function as `merge_fn(cur, row)` — `cur`
the stored row, `row` the arriving one — and binds `old` to the first
(`egglog/core-relations/src/table/mod.rs`, `SortedWritesTable::insert`). Nothing there mentions
age. A rebuild is what separates the two: it re-canonicalizes each candidate row and stages a
remove-and-re-insert for exactly those the canonicalization changed
(`egglog/core-relations/src/table/rebuild.rs`), so the row whose key is *already canonical* is
never moved and is therefore `cur`, however recently it was written, while every row whose key
moved arrives as `new`. Canonical is least e-class id, since the union-find unions **by min id**
(`egglog/union-find/src/lib.rs`), and ids are handed out as terms are built — so the canonical
member of a class is the term created first. Age decides only when no key moved (two `set`s at one
key) or when *no* row holds the canonical key (the rebuild stages them all, in table order).

Minimized against `target/release/egglog`, all `(function Dist (Math) i64 :merge new)`:

| program | egglog | what it rules out |
| --- | --- | --- |
| `(set (Dist (K)) 3) (set (Dist (A)) 2) (union (A) (K))` | `2` | — |
| the same after a bare `(A)`, so `A` exists first | `3` | insertion age: identical, answer flipped |
| `(P (K) (A))` before the two `set`s | `2` | — |
| `(P (A) (K))` before the two `set`s | `3` | argument order within one term decides too |
| `(set (Dist (K)) 3) (set (Dist (K)) 2)`, no union | `2` | canonicity alone: no key moved, age decides |
| `(Z)` first, both keys unioned into `(Z)` | `2` (`3` under `old`) | canonicity alone: neither key canonical |

Swapping the `union`'s arguments changes nothing, which is min-id and not argument order.

**`Impl/` matches this; `Spec/` neither can nor needs to.** `MergeStep.collide` takes the two rows
as premises in *both* orders, so either binding is a legal step and `mergeOneWith_mergeStep` is
indifferent to the choice — matching egglog is an implementation question, not a change to the
semantics. `Database.terms` is a `Set` and has no order to read canonicity from; `FDatabase.terms`
is a list that `addTerm` prepends to, so a position in it is an age, exactly as a position in
`rows` is. `FDatabase.canonTerm` reads canonicity off that list and `swapForCanon` orients the pair
before `mergeOneOriented` runs. Two consequences worth naming:

* **`Term.subtermList` is ordered, and load-bearing.** It now lists a term, then its arguments
  **right to left**, so that prepending it puts the first-built argument last — egglog builds an
  application's arguments left to right. Reversing it back fails `canon-arg-left`/`canon-arg-right`.
  Every other consumer goes through `mem_subtermList` and cannot see the order.
* **`swapForCanon` is guarded by the firing condition.** A weaker guard forces the congruence
  closure on pairs whose arities differ — `congrTuple` compares lengths before looking inside `cl` —
  which is enough to stall the kernel on `Proofs/Lattice.lean`'s `decide` proofs.

Six curated cases (`canon-old`, `canon-new`, `canon-arg-left`, `canon-arg-right`,
`canon-none-old`, `canon-none-new`) pin the table above, the last three being shapes where the two
readings agree, so the agreement cannot rot silently. Disabling the orientation fails three of
them; reversing `subtermList` fails two.

**What is still not modelled.** A term's list position is fixed when it is *first* added, which
tracks egglog for terms built by actions and by rule heads in the order the interpreter runs them.
A round firing several rules may build terms in another order than egglog does, and nothing here
pins that. Two further residuals, both inherited from "quantifying over congruent keys rather than
re-keying rows":

* When neither colliding key is canonical, egglog's survivor sits at the canonical key and this
  model's sits at one of the two colliding keys, which is the only place `MergeStep.collide` can
  write. Invisible to `Database.Out`, which reads a row from every congruent key — and **not**
  invisible to containment: the entry term the implementation writes at that third key is one no
  specification run holds. That is the whole reason the refinement runs on `Recorded`, and it is
  proved, not conjectured — "Why `Recorded` is weaker than `Contained`".
* `ordering-min`/`ordering-max` keep using the structural `Term.blt` — "The representative
  deviation", where the reason no repair exists turned out **not** to be the missing database.

**The read path had no coverage at all**, which is how this stayed invisible: the lookup branch,
reachable through `execM` from a pattern's `expr` case, was exercised zero times. One finding from
the before-measurement is worth keeping — the single-column `read-stale` **agreed even before the
deletion**, and for the wrong reason: the evaluator took the *first* recorded output and
`FDatabase.addRow` prepends, so the row it picked happened to be the merged one. The tuple
destructure searches all rows and exposed what the single-column read was hiding. An agreement that
rests on list order is not evidence of anything, the same lesson as `min`/`max`. (That branch is
gone: reads are the query atom now, and `patternHolds`' row scan is the one place the interpreter
still chooses.)

### A collision that changes nothing runs no body

`mergeRound` skipped a pair only when the two rows were **equal**, `r₁ == r₂`. egglog skips when
the two rows' **value columns** are equal and says nothing about their keys. The gap between the
two is exactly one shape — *congruent but unequal keys holding the same value* — and it is only
observable through a body that writes, which is why it survived until writing bodies were
generated:

```
(datatype Math (L) (X) (Y))
(function Log (Math) i64 :merge new)
(function Dist (Math) i64 :merge ((set (Log (L)) old) new))
(set (Dist (X)) 2) (set (Dist (Y)) 2) (union (X) (Y)) (run 1) (print-size)
```

egglog answers `L 0, Log 0`; the model answered `L 1, Log 1`. With a `union` body instead, egglog
answers `W 2` and the model answered `W 1`. Minimized against `target/release/egglog`, with the
controls that pin the trigger to *equal values at unequal keys*:

| program | egglog | model, before | what it fixes the trigger to |
| --- | --- | --- | --- |
| the repro above | `L 0, Log 0` | `L 1, Log 1` | the divergence |
| second value `3` instead of `2` | `L 1, Log 1` | `L 1, Log 1` | not "a rebuild collision"; the values must agree (this is `merge-body-set-rebuild`) |
| `(set (Dist (K)) 2)` twice, one key | `L 0, Log 0` | `L 0, Log 0` | not "equal values"; at one key the model dedups the rows, which is the case issue #59 fixed |
| width 2, one column equal, one not | `L 1, Log 1` | `L 1, Log 1` | all-or-nothing over the whole value tuple, not per column |
| three rows, two equal plus one different | `L 1, Log 1` | `L 1, Log 1` | a real conflict elsewhere in the class still fires |
| `:merge (+ old new)`, both rows `2` | `4` | — | a single-expression `:merge` does **not** short-circuit; `20d1461` records that as an explicit decision |

**The fix is in `Impl/`, not `Spec/`.** `FDatabase.noConflict body r₁ r₂` is `body ≠ [] &&
r₁.out == r₂.out`, and `mergeOneOriented` takes it as a branch that drops `r₁` and leaves `r₂` where
it stands, running neither `execActions` nor the result expressions. `Spec/Step.lean` is untouched:
`MergeStep` still fires on the collision, which keeps it over-approximating in the safe direction —
the model **over-fired**, and firing fewer steps is precisely what `mergeRound`'s contract permits.

**Drop `r₁`, not "no-op entirely".** Both agree on the repro and on every control above, because a
key class whose rows *all* hold one value has nothing to observe and a class with any disagreement
collapses through the pairs that do fire. Dropping is still the right one: it is what egglog's
insert does — the arriving row is discarded and only the resident row remains in the table — and it
is what keeps `mergeRound`'s convergence argument true as stated ("a pass strictly shrinks the rows
at every key class that collided"), which a branch that removed nothing would break.

**One proof statement had to weaken**, and only these two: `mergeOneOriented_mergeStep` and
`mergeOneWith_mergeStep` concluded `∃ D', MergeStep D D' ∧ …` and now conclude
`∃ D', MergeClosure D D' ∧ …`. A skipped collision takes **no** specification step, and no step is
available to take instead: the implementation never evaluates the body, so `MergeStep.collide`'s
`evalActions` and `Expr.evalList` premises are not in hand and in general do not hold — nothing
scope-checks a merge body, so one with a free variable makes `evalActions` fail while the skip still
fires. Zero-or-one steps is `MergeClosure`. Everything downstream is verbatim unchanged:
`mergeRound_contained` consumed the step with `ReflTransGen.tail` and now consumes the closure with
`.trans`, and `execM_contained` and `execM_reachable` are as they were.

Four curated cases pin it — `merge-body-noop-rebuild` (the repro), `merge-body-noop-union` (the
skip seen as an equality that was never asserted), `merge-body-noop-partial` (width 2, one column
moving, so the block must still run) and `merge-body-noop-three` (a real conflict inside a class
that also contains a no-op pair). Reverting the fix fails the first two.

**This unblocks drawing writing merge bodies at random**, which `genMergeSpec` stopped short of for
exactly this reason. Widening it is a separate change.

## The merge phase runs between commands

Every command now ends in one:

```lean
def CmdStep (db) (c) (db') : Prop := ∃ d, cmdEffect db c = some d ∧ MergeClosure d db'
```

It started as a leg on the `.action` constructor. Without *that*, the specification could not
reach the states `execM` reaches, and `execM_contained` was **false**. Checked against the release
binary, with no `(run)` anywhere:

```
(function f () i64 :merge (max old new))  (set (f) 1)  (set (f) 2)
→ (print-size f) = 1,   (f) -> 2
```

Swapping the merge gives `old` → 1, `new` → 2, `min` → 1, `max` → 2, so the merge *function* really
runs at the second `set` rather than last-write-wins. `print-size` and `print-function` are both
`&self` and cannot rebuild, so nothing else is doing it. The path is `lib.rs:2101` → `eval_actions`
(`lib.rs:1490`), which compiles a bare action into a one-rule run and calls `run_rules` at
`lib.rs:1508`; every rule-set run ends in `merge_all` (`core-relations/.../execute.rs:654`).

**The implementation was faithful all along; the specification was the side that was wrong.** That
is the case for keeping differential testing ahead of proof work — no amount of proving `Impl/`
against `Spec/` would have found this.

The consequence this section used to flag — that the fix landed in the relational `CmdStep` and not
in the functional `stepCmd`, so the two disagreed off the constructor fragment — is **resolved**:
the whole functional half was deleted, and `CmdStep` is the only command stepping there is.

### Why *every* command, and what it cost the front end

Making the closure uniform is what let `CmdStep` stop being an inductive and become the one-line
`def` above, and it deleted `RunStep` along the way. It is only sound because both extra cases are
neutral, and one of them was not until the front end changed.

* **`.rule` is neutral outright.** A merge step commutes with a rules update, since `Cong` reads
  `eqs` alone; the closure after the command reaches nothing a closure before it does not.
* **`.decl` is neutral only given `MergeDeclared`.** Declaring `g` with `:merge` result `(f)`,
  where `f` is undeclared, is a program in which **no merge step exists before the declaration and
  one exists after** — the declaration *creates* the step, so it cannot be relocated earlier. That
  is not a soundness hole to be argued away; it is a program the model was accepting and **egglog
  rejects**, because egglog typechecks a `:merge` expression at declaration time
  (`typechecking.rs:809`). So the fix belongs in the front end, and it is `Spec/Scope.lean`'s fifth
  check.

**The `set` head clause of `MergeDeclared` is load-bearing, not decoration.** A `set` head is not
in `Expr.fns` and `evalAction` never consults the signature for it, so without the separate
`sig f ≠ none` conjunct a body `(set (f 0) 1)` on an undeclared `f` is admitted; two such bodies
plant colliding entries during the closure, and the declaration then turns them into a merge step
that no pre-state closure reaches.

Two facts carry the neutrality argument, both compiled in `Scratch/CmdMergePhase.lean`:
`MergeDeclared` plus `DeclsFresh` put the fresh name outside every *existing* merge body, so bodies
evaluate identically before and after the declaration; and `DeclaredTerms` plus `WF` give
`Avoids f db` — no term of `db` mentions `f` — preserved across the whole closure, which is needed
because step *k* could otherwise plant an `f`-headed entry for step *k+1*. `decl_enables_merge` is
kept as the justification for the check rather than deleted, beside `db₀_not_sigMergeDeclared`
recording why it no longer contradicts `declStep_iff`.

**This is a fidelity gap difftest could not have found**, which is worth noting because difftest
found the original one. The difftest only runs programs egglog compiles, so a program egglog
*rejects* is invisible to it by construction — the whole class of "we accept what egglog refuses"
bugs is outside its reach, and reading the typechecker is the only way in.

## What was rejected

| rejected | why |
| --- | --- |
| Merge as a value combiner `Term → Term → Term`, and the observable value as a fold over asserted rows (`PLAN.md` M9 §3) | the union-find's side effects live only in the closure, not in the asserted rows; what survives is `Current`, for difftest and simulation only |
| A `Current`-reading evaluator | `Current` does not exist for `:merge old` or `:merge new`, both common |
| Saturation inside the step relation | unsatisfiable as first written, and unnecessary once the safety theorem is an invariant |
| The `a ≠ b` collision guard, and with it a `merge (x, x) = x` or identity-guardedness hypothesis on the safety theorem | all three bought a soundness gap rather than closing one |
| Fuel-bounded merge saturation that **returns a prefix** | presents a wrong answer where "no answer" is correct. Fuel that returns `none` is fine and is what `Impl/` runs |
| Overwriting the entry in `Spec/`, and a second congruence relation carrying `fd` as a rule | the first breaks `Contained` and every M2–M8 lemma; the second turned out to be `Cong.congr` once a constructor's entry was its own application |
| A row set in `Spec/` | it duplicated what the terms already say, and made the entry-width invariant harder to state than the thing it was guarding |
| An `Expr` constructor for primitives, and a tuple constructor in `Term` | both make existing `cases` in the M10 proofs non-exhaustive; reserved names and a `List` match egglog and cost no churn |
| A fresh-id / e-class-id representation on this side | M11 adds ids to the *target* configuration only; the source keeps terms as their own identity, and `PLAN.md` is right about this |

## Open questions

1. **`Matches.values` is split-blind and e-class-blind.** Two defects in one atom, both in `Spec/`
   and neither fixable in `Impl/`.

   *Split-blind*: the atom's conclusion is a single term `f(ts ++ us)`, so `.values [b] f [a]` and
   `.values [] f [a, b]` are the **same** condition, though the declaration distinguishes them and
   `FnDecl.arity` is exactly what says where the key ends. `Impl/`'s row scan does fix a split,
   which is why the two disagreed until `patternHolds` was made to dispatch on the signature
   (`a820494`): a merge function takes the row scan, since the index is what says which recorded
   entry is current, and everything else reads the entry term directly. That repair makes them
   agree; it does not make `Matches.values` say what the declaration means.

   *E-class-blind*: egglog reads a constructor's `(= v (f a b))` as binding `v` to the **e-class**
   of `f(a, b)`, where the model reads the term `f(a, b, v)` — one child too wide for a
   constructor, so `DeclaredTerms` forbids it and `Pattern.arityOk` rejects the atom. Binding a
   constructor's value is the `.eq` atom here, because the value *is* the application.

   **Invisible today**, which is why it is deferred rather than urgent: `Encoding/Encode.lean`
   emits `.values` only for merge functions (`@UF` and the views), and the difftest emits no
   constructor read at all. The answer is a signature-aware `Matches.values`, which is a change to
   a frozen file, so it waits for a reason to make it.
2. **Is `MergeStep` confluent for a join merge?** It was `MergeStep.diamond_of_join`, **[guess]**,
   whose `hjoin` is self-contradictory so the statement was *unconditional* local confluence —
   which nevertheless looks true, since a step's effect does not depend on the ambient state. The
   statement is deleted; what survives is `evalActions_mono`, "the weak but sufficient form of what
   `diamond_of_join` wants", and `Proofs/Merge.lean`'s "Transporting a step" says what exactness
   would need. **Demoted**: no safety theorem needs it. It buys one thing, strengthening M10's
   refinement from "spec-reachable" to an equality.
3. **Settled: `ordering-min`/`ordering-max` are congruence-unstable, and no operator repairs it.**
   The question was whether a better choice — e-class ids, a class minimum, a database-aware
   primitive, a new operator baked into the language — would restore the stability two of the
   `Recorded` transports want. **None does**, and the refutation is from the shape of a choice
   operator rather than from `Term.blt`: "The representative deviation", above. What closed the
   transports was not an operator but a condition on the *program* — `p.UnionFree`, under which
   nothing is congruent-but-distinct and stability is never asked for. The encoded fragment gets
   the same collapse for free (`ENCODING.md`), and restricting the transported positions to
   ordering-free expressions is the remaining arm.
4. **Settled: `WellScoped` should not carry `DeclsFresh`, and the checks are not bundled at all.**
   The question was whether the static check forbidding a redeclaration belongs inside `WellScoped`
   or beside it. The reason it looked urgent is gone: `CmdStep.mono_recorded`'s `.decl` case needed
   `Cmd.DeclFresh` only because `MCong.fd` read the signature, and `Cong` does not, so both
   `mono_recorded` lemmas dropped the hypothesis and its counterexample is provably false.
   The other half of the old answer — that a `Check` record ran the checks over one walk, so the
   sharing bundling would buy was already there — is **superseded**: `Check` is deleted and
   `Spec/Scope.lean` writes its checks out directly, because nothing was ever generic over the
   record (`PLAN.md`, "The front end's six checks"). That strengthens the conclusion rather than
   weakening it. They stay separate predicates because the theorems take different subsets, and
   `MergeDeclared` shows why bundling would have been actively wrong: it is asked of the signature
   *after* `sigBind` where `DeclsFresh` is asked before, so one walk could not have carried both.
   What still wants the freshness check is the width invariant `Database.DeclaredTerms`: `Cmd.decl`
   is `Function.update`, so the dynamics allow a redeclaration to change what the signature says
   about a name the state already holds terms of. `FDatabase.ProgramLegal` carries the stronger
   `Cmd.DeclUnused`, from which `ProgramLegal.declsFresh` recovers `Program.DeclsFresh`.
5. **Settled: declaration is required.** `Signature.IsCtor` asks for a declaration, so `Expr.eval`
   gets stuck on an undeclared name and `Program.Evaluable` is declare-before-use for free. What it
   cost is that `AllConstructors` no longer implies that the applications the database holds are
   constructors', which is carried as the state invariant `Database.DeclaredTerms` instead.
