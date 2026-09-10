Rewrites an egglog program to use an encoding for equality tracking, optionally including proof tracking.

# Overview

The job of the term encoding is to *remove all calls to union* in the egglog
program. Egglog's built-in congruence and rebuilding are replaced by an explicit
per-sort union-find and per-constructor view tables, maintained by ordinary
rules. Every equality then has a rule firing behind it, which is what makes
proof tracking possible at all.

The transformation is triggered when an `EGraph` is created with
[`EGraph::new_with_term_encoding`](crate::EGraph::new_with_term_encoding) (no
proofs), [`EGraph::new_with_proofs`](crate::EGraph::new_with_proofs), or by
converting an existing one via
[`EGraph::with_term_encoding_enabled`](crate::EGraph::with_term_encoding_enabled).
The same table shapes are used either way: union-find and view rows carry a
proof column that is `()` (of sort `Unit`) with proofs off and a real `@Proof`
with them on.

This document has two parts.
[**The equality encoding**](#the-equality-encoding) is the tables, actions,
queries, and maintenance rules; its snippets are all shown with proofs off.
[**Proofs**](#proofs) is what fills the proof column. A proof row records how an
equality was derived and what it was derived from, never the equality itself;
proof conversion computes that afterwards. For a rule head the row records less
still — a *skeleton* naming the firing — which is the second of the two layers
that part is told in.

The running example throughout is:

```text
(datatype Math (Add Math Math) (Num i64))
(Add (Num 1) (Num 2))
(rewrite (Add a b) (Add b a))
(run 1)
(check (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))
(delete (Add (Num 1) (Num 2)))
```

Generated names keep the `@` prefix the encoding gives them (`@UF_Math`), but
the fresh variables it numbers `@pv0`, `@pv1`, … are renamed to something
readable.

# The equality encoding

## Union-find

```text
(sort Math :internal-uf @UF_Math)
(function @UF_Math (Math) (Math Unit)
    :merge ((set (@UF_Math (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
            (values (ordering-min old0 new0) ()))
    :unextractable :internal-hidden :internal-identity-vals 1)
```

`@UF_<Sort>` maps each term to its parent, plus the proof column. A term with no
row is its own representative, so the lookup is identity-on-miss. To union `a`
and `b` the encoding runs
`(set (@UF_<Sort> (ordering-max a b)) (values (ordering-min a b) ()))`. If the
key already had a different parent, the `:merge` block keeps the smaller of the
two parents and `set`s the larger parent's edge to the smaller one (both are
equal to the key). `ordering-max`/`ordering-min` impose an arbitrary but
deterministic order (by insertion), so the parent choice is stable.

`:internal-identity-vals 1` marks the first value column (the parent) as the one
that decides whether a re-`set` is a change, so re-setting an existing edge leaves
the row untouched, skips the `:merge` block, and does not re-stage the same union
forever. It makes re-writes idempotent; it is *not* a key, and many rows can point
at one parent.

## The view

A constructor becomes an e-node table — its **view** — plus a rebuild index:

```text
(function Add (Math Math) (Math Unit)
    :merge ((set (@UF_Math (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
            (values (ordering-min old0 new0) ()))
    :internal-view constructor :internal-identity-vals 1)
(index @AddOcc_Math Add (any 0 1 2))
```

The view keeps the function's name: the encoding rewrites the declaration rather
than adding a table beside it. What changes is the shape — the functional
dependency `children -> (eclass, proof)` over a term's *canonicalized* children.
Two rows that collide on the same children are congruent, so the `:merge`
resolves congruence directly: it keeps the smaller e-class and unions the two in
`@UF_<Sort>`, and no separate congruence rule is needed.

## Building a term

Evaluating a constructor application takes a fresh e-class and interns the
application into its view. Top level `(Add (Num 1) (Num 2))` lowers to:

```text
(let n1 (get-fresh! "Math"))
(let n1_can (set-if-empty-Num! 1 n1 ()))
…                                                       ;; the same for (Num 2)
(let ab (get-fresh! "Math"))
(let ab_can (set-if-empty-Add! n1_can n2_can ab ()))
```

`set-if-empty-<F>!` interns the application and returns the view's *existing*
e-class if the term was already there, so `ab_can` is always canonical. A parent
is built over its children's canonical ids, which is what keeps views canonical.
A freshly minted term needs no `@UF_<Sort>` row — identity-on-miss makes it its
own representative.

## Union in a rule

A `union` of two e-classes writes one `@UF_<Sort>` edge from the larger endpoint
to the smaller, using the `ordering-max`/`ordering-min` convention above. Each
operand that is itself a term is built first, to obtain its e-class.

Building an operand and then unioning it away wastes an e-class id and its
`@UF_<Sort>` edge. When a `union` operand is a freshly built constructor term,
the encoder instead builds it *directly into* the other operand's e-class. Two
passes over the head implement this (both in [`crate::proofs::proof_head`]):

1. **Normalize** — lift every constructor-application `union` operand into a
   `let`, so inline `(union (Add a b) (Add b a))` and let-bound
   `(let l (Add a b)) (let r (Add b a)) (union l r)` become the same shape.
2. **Construct-into** — for `(union l r)` where an operand is a
   constructor-`let`, pick the other operand as the *target* (built normally)
   and build the constructor-`let` operand (the *guest*) into the target's
   e-class, dropping the explicit union.

The running example's `rewrite` matches `(Add a b)` into `rewrite_var` and builds
`(Add b a)` as a guest into it:

```text
(rule ((= (values e p) (Add a b))
       (= rewrite_var e))
      ((set (Add b a) (values rewrite_var ())))
        :name "(rewrite (Add a b) (Add b a))")
```

No fresh e-class and no `@UF_Math` edge: the view is `set` to point at the
target, so `(Add b a)` *is* `rewrite_var`. If `(Add b a)` already exists under a
different e-class, the plain `set` collides on the children key and the view's
congruence `:merge` unions the two — exactly the edge the explicit union would
have produced. The guest's variable is bound to the target's e-class, so a later
use in the same head shares it.

Only one operand needs to be a constructor application; a `union` of two matched
variables keeps the plain `@UF_<Sort>` edge.

## Delete and subsume

Both build their argument's children first, and both touch only the view. A
proof already written about a deleted row still stands, since it names the row's
position in the program rather than reading the row.

`(delete (Add (Num 1) (Num 2)))` deletes the view row in the action:

```text
(delete (Add n1_can n2_can))
```

No extra deferral is added. A `delete` is staged into a mutation buffer and
applied when the batch commits, and a table's commit applies
its removals *before* its insertions, so a row another rule inserts in the same
batch outlives the delete. That is the uninstrumented meaning of `delete`, and
lowering it directly is what preserves it.

Subsumption *is* deferred, through a marker row:

```text
(set (@to_subsume_Add n1_can n2_can) ())
```

which `@subsume_ruleset` consumes during maintenance:

```text
(rule ((@to_subsume_Add c0_ c1_)
       (= (values e pf) (Add c0_ c1_)))
      ((subsume (Add c0_ c1_)))
        :ruleset @subsume_ruleset :name "@subsume_rule")
```

The marker outlives the row: rebuilding re-keys a view row by inserting it at its
canonical children, and that insert carries no subsumed bit, so only a marker
that is itself re-keyed keeps the row subsumed (see
[Keeping the view canonical](#keeping-the-view-canonical)).

Almost no program subsumes, so `@to_subsume_<Constructor>` and its rules are
declared on first use rather than with the constructor. Commands arrive one at a
time — the `subsume` may be many batches after the `datatype` — so the encoder
emits the declarations ahead of the command that needs them, and remembers which
constructors it has covered in the e-graph's own state, where `push`/`pop` roll
the memo back together with the declarations it tracks.

The marker is a plain `Unit` relation keyed on the children, with no minted id
and no `:internal-term-node`, so extraction never reads it as a term.

# Queries

All queries — rule bodies, `check`, and `prove` — read the **view**. A view read
binds both the e-class and the proof column:

```text
(= (values e p) (Add a b))
```

A nested term flattens into one view read per subterm, joined on shared e-class
variables. The running example's `check` expands to:

```text
(check (= (values e1 p1) (Num 1))
       (= (values e2 p2) (Num 2))
       (= (values e3 p3) (Add e1 e2))
       (= (values e4 p4) (Num 2))
       (= (values e5 p5) (Num 1))
       (= (values e6 p6) (Add e4 e5))
       (= e3 e6))
```

that is, that the representatives of `(Add (Num 1) (Num 2))` and
`(Add (Num 2) (Num 1))` are the same e-class. A plain `check` discards the proof
columns; a rule body or `prove` composes them (see
[Body premises](#body-premises)).

# Rebuilding

Between the original program's commands, the encoding runs maintenance rules that
restore the invariants egglog would otherwise maintain during rebuilding:

```text
(ruleset @parent)               ;; path compression on the union-find
(ruleset @rebuilding)           ;; re-canonicalize view rows; resolve congruence
(ruleset @rebuilding_cleanup)   ;; drop rows merged away
(ruleset @subsume_ruleset)      ;; apply subsumption markers

(run-schedule
    (seq (saturate (seq (run @rebuilding_cleanup)
                        (saturate (seq (run @parent)))
                        (run @rebuilding)))
         (run @subsume_ruleset)))
```

A command that only builds and interns terms — a `let`, a `set`, a top-level
expression over non-container sorts — merges no e-classes and defers no work, so
no maintenance runs after it. Everything else is followed by the schedule above.

## Path compression

The only union-find rule flattens `a -> b -> c` chains to `a -> c`:

```text
(rule ((= (values b pb) (@UF_Math a))
       (= (values c pc) (@UF_Math b))
       (!= b c))
      ((set (@UF_Math a) (values c ())))
        :ruleset @parent :name "@uf_path_compress")
```

## Keeping the view canonical

Each view gets one *rebuild index* per distinct eq-sort among its columns,
covering that sort's children **and** the e-class:

```text
(index @AddOcc_Math Add (any 0 1 2))
```

`@AddOcc_Math` is an ordinary declared index: for every view row and every listed
column, that column's value followed by the whole row. It answers "which rows
mention this term", which is what a rebuild needs and what a native rebuild finds
through its own such index.

One rule per sort then drives the rebuild from a `@UF_<Sort>` edge rather than by
matching the view:

```text
(rule ((= (values leader plf) (@UF_Math follower))
       (!= follower leader)
       (@AddOcc_Math follower c0_ c1_ e2_ pf))
      ((let c0_canon_ (@UF_Math_canon c0_ c0_))
       (let c1_canon_ (@UF_Math_canon c1_ c1_))
       (let e2_canon_ (@UF_Math_canon e2_ e2_))
       (delete (Add c0_ c1_))
       (set (Add c0_canon_ c1_canon_) (values e2_canon_ ())))
        :ruleset @rebuilding :unsafe-seminaive :name "@rebuild_rule" :internal-include-subsumed)
```

The index atom binds the whole row, so nothing else need be read, and the action
re-canonicalizes *every* eq-sort column at once — including the e-class, which
therefore needs no rule of its own. One firing yields the fully canonical row, so
two children moving in the same iteration fire twice with the same result rather
than each leaving a differently half-rewritten row behind. `@UF_<Sort>_canon` is
the row's leader column read by term, with the term itself as the fallback, so a
column already at its leader canonicalizes to itself.

The row is deleted before being re-inserted, because when only the e-class moved
the canonical key equals the old one. Reading `@UF_<Sort>` in the action is what
makes the rule `:unsafe-seminaive`; the driving `@UF_<Sort>` delta in the body is
what makes that read sound.

Container columns are not indexed — they carry no `@UF_<Sort>` row to drive a
lookup — and keep the `:naive` rule in [Containers](#containers). Subsumption
markers (`@to_subsume_<Constructor>`) are re-keyed to their leaders by their own
per-column rules, so a subsumed row stays subsumed after its children move.

# Globals

*Before the term encoding*, [`crate::ast::remove_globals`] desugars every global
variable to a nullary function, so execution need not treat them specially:

```text
(let g1 (Add (Num 1) (Num 2)))
```

becomes

```text
(function g1 () Math :internal-let)
(set (g1) (Add (Num 1) (Num 2)))
```

and references to `g1` become the lookup `(g1)`. The encoding then treats
`:internal-let` like a nullary constructor: it gets an FD view
`g1 : () -> (Math, proof)` with the congruence `:merge`, a rebuild index, and
rebuild rules like any other function. Because the definition is a `set` and not
a `union`, a global adds no e-class merge of its own.

The pass also appends a lookup fact to the body of every rule whose *head*
mentions a global, so the head can read the global's current value. Those facts
are premises like any other.

# Containers

Container sorts (`Vec`, `Set`, `Map`, `MultiSet`, `Pair`) are never unioned
directly, so they get **no** union-find tables. A container is instead
recanonicalized structurally when its elements' e-classes change. For

```text
(datatype Math (Num i64))
(sort MathVec (Vec Math))
(constructor Wrap (MathVec) Math)
```

the `MathVec` argument of `Wrap` is a container column, so it is canonicalized by
the per-container *rebuild primitive* the encoding registers on the sort
(`@container_rebuild`, with `@container_rebuild_proof` beside it in proof mode):

```text
(rule ((= (values e pf) (Wrap c0_))
       (= c0_canon_ (@container_rebuild c0_))
       (!= c0_ c0_canon_))
      ((set (Wrap c0_canon_) (values e ()))
       (delete (Wrap c0_)))
        :ruleset @rebuilding :naive :name "@rebuild_rule" :internal-include-subsumed)
```

The primitive clones the container, remaps each element to its union-find leader,
and re-interns it. Because it reads the elements' `@UF_<E>` tables rather than
joining a tracked table, the rule is `:naive`: an element becoming equal to
another produces no delta on the container's own view row, so the rule must
rescan the view each round. Nested containers (e.g. `(Vec (Vec Math))`) rebuild
by recursing through container-typed elements. The e-class column of `Wrap`
is an ordinary eq-sort column and gets the indexed rule from
[Keeping the view canonical](#keeping-the-view-canonical).

See [`crate::proofs::proof_container_rebuild`] for the rebuild primitives, and
[Container proofs](#container-proofs) for what they put in the proof column.

# Proofs

A proof in the e-graph is a *raw proof*: a justification, plus references to the
proofs it is built from. It does not carry the equality it proves. Proof
conversion turns each one into a
[`Proof`](crate::proofs::proof_format::Proof) — the same justification paired
with the [`Proposition`](crate::proofs::proof_format::Proposition) `t1 = t2` it
proves (see [`crate::proofs::proof_format`]). The checker reads propositions;
the e-graph never stores one.

Conversion computes each proposition from what the raw node references. A node
references other proofs, or a *position* in the program that conversion can
evaluate:

| Raw node | Names | Conversion computes the equality by |
| --- | --- | --- |
| `@Rule_<k>` / `@RuleLink` | the rule, and which of the head's proofs this is | replaying the head — see the two layers below |
| `@FiatUnion` | a global action | evaluating that action's two operands |
| `@FiatTerm` | a global action and one of its nodes | evaluating that node |
| `@ProjPrim_<k>` | the rule and the index of a call in its body | resolving that specialized primitive, deriving its unique container argument from the input/output sorts, running its validator, and projecting along the term path from that argument to the result |
| `@MergeIdx` / `@MergeRow` | a function and a subexpression of its merge body | running the merge body on the premise outputs |
| `@Trans`, `@Sym`, `@Congr`, `@Proj`, … | only other proofs | composing their conclusions |

Each action inside `(fail …)` is instrumented as one local block inside the
wrapper. General `fail` execution restores its e-graph snapshot after either a
command fails or every command succeeds, so none of its transient proof rows
can escape and the proof checker ignores its actions. The common single-`check`
form is read-only and runs without taking a snapshot. `prove` and `prove-exists`
are disallowed inside `fail`; otherwise the wrapper adds no proof-specific
restriction to a command the term/proof encoding already supports. Proof mode
does not currently support `output`, whether or not it is inside `fail`.

The separate top-level `(extract e)` case for a term not already present remains
open ([issue #80](https://github.com/saulshanabrook/egglog-encoding/issues/80)).

Two raw nodes are desugared during conversion rather than kept as proof nodes of
their own. `@ProjPrim_<k>` becomes a chain of one or more `@Proj` steps from the
resolved call's unique typed container argument to the position its validator's
result occupies, and `@CongrAll` becomes the positional `@Congr` steps it stands
for, expanded against the term.

With proofs enabled the encoding first emits a header defining the format (see
[`crate::proofs::proof_format`] and `proof_encoding_helpers.rs`): the `@Proof`
sort and the proof-node relations `@RuleLink`, `@MergeIdx`, `@MergeRow`,
`@Trans`, `@Sym`, `@Congr`, `@CongrAll`, `@Proj`, `@ContainerNormalize`,
`@Eval`, `@FiatUnion`, `@FiatTerm` — each a `(function … Unit :no-merge)`, not a
constructor, so a proof node is a fresh id plus a row, both written by that
relation's `mint-<Relation>!`. Three further families have their shape fixed by
the site rather than by the format, so each is declared where it is first needed
rather than in the header: `@Rule_<k>`, a rule proof carrying its `k` body
premises inline; `@Packed_<k>`, one row standing for a whole composition over
`k` proofs (see [Packed rows](#packed-rows)); and `@ProjPrim_<k>`, a body call
reading an element out of a container, carrying a proof per argument.

The union-find and view proof columns become real:

```text
(function @UF_Math (Math) (Math @Proof) :merge (… @Packed_2 "trans_sym_p0_p1" …) …)
(function Add (Math Math) (Math @Proof) :merge (… @Packed_2 "trans_p0_sym_p1" …) …)
```

If term `k` has parent `p`, `(@UF_Math k)` returns `(values p proof)` where
`proof` proves `k = p` — the key on the left. A view row's proof runs the other
way, `eclass = f(children)`.

The rest of this part is [reflexive anchors](#reflexive-anchors) and then the two
layers, which are how a *rule head* uses the reference-and-convert split above.
[**Layer 1**](#layer-1-building-the-proof-as-the-rule-runs) is a rule that builds
each proof as it goes; it is the specification.
[**Layer 2**](#layer-2-proof-skeletons) is what the encoder actually emits: a
skeleton naming the firing, from which conversion recovers layer 1's proof.
Everything after those two — body premises, rebuild rows, merge collisions,
containers — is stated against layer 1.

## Reflexive anchors

A proof of `t = t` is not free: the checker reads a reflexive equality over an
eq-sort or container term as a claim that the term *exists*. Inside a rule body
there is no action to name, so `@FiatTerm` will not do either (it names a
top-level action, and a plain `@Fiat_<Sort>` is reserved for literals and
value-constructor terms). Every such anchor is instead **projected out of a row
proof already in scope**. A view
row's proof states an equality whose right-hand side is the row's term, so:

* a term the row mentions as a child is `@Proj(row, i)`;
* an element a body call read out of a container, whose position in the term
  form is not known at the site, is `@ProjPrim_<k>(rule, body index, arg
  proofs…)`, which conversion resolves by finding that specialized call's unique
  typed container argument, running its validator, and projecting the result
  from that argument through one or more positional steps.

That covers every anchor the encoding wants: the reflexive base a container
rebuild composes from, and a rule body's eq-sort or container variable. Which
row anchors a body variable is only known once the whole body is walked, so the
anchor's row is written where the composition reading it lands — and a
composition that drops it as reflexive writes none at all. A body's equalities
join the variables they relate into one anchor class, so an element read bound to
a variable is anchored through the read.

**A value the query computed is not anchored at all.** Every one of the sources
above is a row the database holds, and a container a body primitive built is in
no row — so neither it nor anything read out of it can be projected. There is no
congruence route either: `@Congr`/`@CongrAll` rewrite a child of a term a proof
already mentions, so they cannot introduce the container's term in the first
place.

Such a value only matters where a premise reads its anchor. A fact's premise
composes `Sym(left)` with `right` and drops whichever side proves `t = t`, so an
equality reads its right-hand anchor exactly when its left-hand proof is itself
reflexive — a variable, or another primitive's result, but not a term the query
builds. Anywhere else the anchor goes unread and is never written: a view atom's
argument, the right-hand side of a built term, or a value some other atom
anchors after all. Proof support rejects a rule whose premises do read one (see
[`crate::ProofEncodingUnsupportedReason`]), covering both a container a body
primitive built and an eq-sort value a primitive produced without being handed a
container to read it out of. A head that mints no row reads no premise either;
proof support does not model that, and rejects those rules too.

## Layer 1: building the proof as the rule runs

Layer 1 keeps the proof and the row together: alongside every row a rule head
writes, it writes the proof of the equality that row asserts, composing
`@Congr`, `@Trans`, and `@Sym` into rows as it goes. **The encoder does not do
this for a rule head** — the snippets in this section are illustrative, not
dumps. It is still the design layer 2 is an optimization of, and the encoder
runs exactly this composition wherever there is no rule head to replay (see
[Where layer 1 is still emitted](#where-layer-1-is-still-emitted)).

Three things force its shape.

**A built subterm needs two nodes.** The proof of the shape a head wrote has to
be stated over the term as written, over its children's *as-built* ids; call that
the **natural** node `t`. But a parent must be built over its children's
representatives to keep views canonical, so the same term is minted again over
**canonical children** as `t'`, even when no child moved. `t` is deliberately
never interned, so the view's congruence can never move it. This is why proof
mode mints a node for a construct-into guest where the term encoding alone writes
the guest's row straight onto the target's e-class.

**The step from `t` to `t'` is congruence.** Each child that was built and then
interned carries a *connector* proof `child_natural = child_eclass`; one `@Congr`
per such child turns the head's own conclusion `t = t` into `t = t'`.

**Interning `t'` is not determined by the head.** `set-if-empty` returns the
view's representative `t''`, which may be some other term entirely if that shape
was already present. The view row's proof — `t'' = t'` — is the one fact about
the firing that the head's syntax does not fix. Call it the level's **bridge**.
Composing it gives the level's connector, `t = t''`, which the level above uses
as its `@Congr` step.

For the running example's `rewrite`, whose two children come straight from the
body and whose result is a construct-into guest, layer 1 would emit five proofs
(illustrative: `@Trans`/`@Sym` are spelled as calls rather than as mints, and
`rule-proof` stands for whatever names a proof the firing concludes):

```text
(let ba (get-fresh! "Math"))                     ;; the natural node
(let own  (rule-proof rule_name prems))      ;; ba = ba, the head's own conclusion
(let edge (rule-proof rule_name prems))      ;; rewrite_var = ba, the dropped union
(let view (@Trans edge own))                 ;; rewrite_var = (Add b a), the view row
(let back (@Sym view))
(let conn (@Trans own back))                 ;; ba = rewrite_var, the connector
(set (Add b a) (values rewrite_var view))
```

The compositions are not written per site. They are four operations over
proofs — `canonicalize`, `reflexive`, `connect`, and `guest_view` in
[`crate::proofs::proof_head`] — that say, respectively: apply one `@Congr` per
built child, turning `t = t` into `t = t'`; turn `t = t'` into `t' = t'`; join a
term to the e-class it interned into; and state a guest's view row from the
dropped union's edge. Walking a head bottom-up and applying those four is the
whole of layer 1.

### A nested term, level by level

The example above has one level. What the three forces cost becomes visible when
a head builds a term over a term. Take

```text
(let f (Neg (Add a (Add b c))))
(union rewrite_var f)
```

with `a`, `b`, `c` matched by the body. Flatten it first, so every constructor
application is its own action and every operand is a variable:

```text
(let d (Add b c))
(let e (Add a d))
(let f (Neg e))
(union rewrite_var f)
```

Now walk it bottom-up, carrying at each level a proof from the id the head built
to the canonical id the view interned. That proof is what lets the *next* level
up use canonical children while still concluding something about the term as
written. `set-if-empty` below is the primitive that returns a view's existing
representative, or installs the given id and proof when the shape is new.

**`(let d (Add b c))`.** Both children are body variables, already canonical, so
there is no congruence step — the natural node is the only one built:

```text
(let d (get-fresh! "Math"))
(let d-prf (rule-proof rule_name prems))              ;; d = d
(let (values d' d-to-d'-prf) (set-if-empty (Add b c) d d-prf))
```

**`(let e (Add a d))`.** The child `d` moved, so this level needs both nodes. The
natural node is over `d`; the canonical one over `d'`; `@Congr` at the child's
position carries the first to the second:

```text
(let e (get-fresh! "Math"))
(let e-prf (rule-proof rule_name prems))              ;; e = e

(let e' (get-fresh! "Math"))                             ;; the same term over canonical children
(let e-to-e'-prf (@Congr e-prf 1 d-to-d'-prf))        ;; e = e'
(let e'-prf (@Trans (@Sym e-to-e'-prf) e-to-e'-prf))  ;; e' = e'

(let (values e'' e'-to-e''-prf) (set-if-empty (Add a d') e' e'-prf))
(let e-to-e''-prf (@Trans e-to-e'-prf e'-to-e''-prf)) ;; e = e'', for the level above
```

**`(let f (Neg e))`.** Identical shape, one level up, with `e-to-e''-prf` as the
congruence step:

```text
(let f (get-fresh! "Math"))
(let f-prf (rule-proof rule_name prems))              ;; f = f

(let f' (get-fresh! "Math"))
(let f-to-f'-prf (@Congr f-prf 0 e-to-e''-prf))       ;; f = f'
(let f'-prf (@Trans (@Sym f-to-f'-prf) f-to-f'-prf))  ;; f' = f'

(let (values f'' f'-to-f''-prf) (set-if-empty (Neg e'') f' f'-prf))
(let f-to-f''-prf (@Trans f-to-f'-prf f'-to-f''-prf)) ;; f = f''
```

**`(union rewrite_var f)`.** The union is stated over the term as written, then
carried to the representative the view actually holds:

```text
(let rewrite_var-to-f (rule-proof rule_name prems))                    ;; rewrite_var = f
(let rewrite_var-to-f'' (@Trans rewrite_var-to-f f-to-f''-prf))
(set (@UF_Math rewrite_var) (values f'' rewrite_var-to-f''))
```

Three levels, and only four rows outlive the firing: the three view rows and the
`@UF_Math` edge. Everything else is proof — two nodes per level where a child
moved, plus a `@Congr`, a `@Sym` and two `@Trans` to thread them. That ratio is
what [layer 2](#layer-2-proof-skeletons) removes: the walk above is a function of
the head and the substitution, so it need not be written into the database at
all.

The walk is the specification of the proof at every layer-1 site, but not of the
rows written there: where the encoder runs this walk itself, each `@Congr`,
`@Sym` and `@Trans` above is a node of one [packed row](#packed-rows) rather than
a row of its own.

## Layer 2: proof skeletons

Layer 1 composes a proof for every step of the walk. Almost none of them are ever
read: a proof is only wanted if someone later asks to explain a specific fact.
Layer 2 keeps the same walk but writes a row only where the *e-graph itself must
store a proof* — a view row's proof column, a `@UF` edge's proof column. Each
such row is a **skeleton**: it names the rule that fired, the premise proofs it
fired on, and *which* proof of that head it is.

The original rule head is then the **format** of the proof. Given the skeleton,
proof conversion replays the head under the firing's substitution, applies the
same four operations, and arrives at exactly the proof layer 1 would have
written. Layer 2 is correct because of that: same proof, computed later.

### Columns

One walk of a head produces a flat array of proofs, in a fixed order — an
action's operands before the action, a term's children before the term. A proof
is named by nothing but its position in that array, its **column**. Each position
claims a fixed run:

| position | columns |
| --- | --- |
| a term the head builds | own conclusion, that conclusion over canonical children, the connector |
| a construct-into guest | own conclusion, the dropped `union`'s edge, the view row it writes, the connector |
| any other call | own conclusion |
| a `union` | its equality, then the union-find edge in each direction |
| a `set` | its row |

A position whose head produces no proof still holds its column, so the numbering
follows the walk rather than what either side emits. The table above is
[`crate::proofs::proof_head`]'s `HeadPosition`, and one walk of the head turns it
into a `HeadLayout`: the encoder claims a position's run as it lowers, and
`Firing` fills the same run as it rebuilds the array, so a row's column indexes
straight into the result.

The column and the premises are the whole conclusion: they fix the firing, and
conversion replays the head from there.

### Bridges

The bridge — which e-class a subterm interned into — is the one thing conversion
cannot recompute, so the skeleton carries it. A row written before the head
interns anything carries the body premises inline as `@Rule_<k>`, `k` counting
only the premises the encoding records (see [Body premises](#body-premises)).
Every row after that is a `@RuleLink`, naming the row written just before the
newest interning — which carries the premises and every earlier bridge — plus
that interning's bridge. Chaining keeps a row's width constant no matter how
deep the head is.

So a row carries exactly the bridges the head had recorded when it wrote the row,
and the replay takes them one at a time: it reaches the column the row names, and
then asks for one bridge more than the row has. Running out is what tells the
replay it has gone as far as this row can say anything about, and it is the only
thing that stops it.

### The running example

The `rewrite`'s head builds one guest over two matched variables. It writes two
proof rows:

```text
(rule ((= (values e p) (Add a b))
       (= rewrite_var e))
      ((let rule_name "(rewrite (Add a b) (Add b a))")
       (let ba (get-fresh! "Math"))
       (let view (mint-@Rule_1! rule_name p 2))
       (set (Add b a) (values rewrite_var view)))
        :name "(rewrite (Add a b) (Add b a))" :unsafe-seminaive)
```

Column 2 is the guest's view row. Columns 0, 1 and 3 — the natural node's own
conclusion, the dropped union's edge, and the connector — are in the array, but
nothing stores them, so no row is written. Those three plus the intermediate
`@Sym` are the four rows layer 1 wrote above and layer 2 does not.

A nested head chains. For

```text
(rule ((Seed r)) ((union r (Add (Num 1) (Num 2)))))
```

the walk numbers `(Num 1)` at columns 0–2, `(Num 2)` at 3–5, and the guest
`(Add …)` at 6–9, and the head writes three rows:

```text
(let num1_pf1   (mint-@Rule_1! rule_name prems 1))       ;; (Num 1) over canonical children
(let num1_e     (set-if-empty-Num! 1 …))
(let num1_bridge (view-proof-Num 1 …))
(let num2_pf1   (mint-@RuleLink! num1_pf1 num1_bridge 4))
(let num2_e     (set-if-empty-Num! 2 …))
(let num2_bridge (view-proof-Num 2 …))
(let add_view   (mint-@RuleLink! num2_pf1 num2_bridge 8))
(set (Add num1_e num2_e) (values r add_view))
```

The last row carries both bridges, reached through the chain. Layer 1's walk of
the same head names seventeen proofs: four conclusions and thirteen composition
steps. Three rows against seventeen is the whole point of the layer.

Row counts per firing, proof rows only (not the view or `@UF` write beside them):
a flat rewrite **1**, the nested head above **3**, a view rebuild **1**, a merge
collision **1**.

A `union` of two matched variables builds nothing, so it needs one row — but
which endpoint the `@UF` edge is stated from is only known once the ids are
compared. Its column is therefore an expression, not a literal:

```text
(let edge (mint-@Rule_1! rule_name prems (proof-of-max x 1 y 2)))
(set (@UF_Math (ordering-max x y)) (values (ordering-min x y) edge))
```

`proof-of-max` picks between the two orientations' columns by the same value
ordering as `ordering-max`.

## Where layer 1 is still emitted

Layer 2 needs a rule head to use as the format. Where there is none, the encoder
applies the same four operations itself and writes the composition out. The
operations are written once, over the `ProofAlgebra` trait in
[`crate::proofs::proof_head`], and implemented twice: for the encoder, where a
"proof" is the name of an emitted variable, and for proof conversion, where it is
a node in the proof store. Those are one algebra run at two times — while
lowering, or while replaying a skeleton — which is exactly the difference between
the layers.

**Top-level actions.** A top-level action has no column to name, so the encoder
composes, and each term it builds is justified by a `@FiatTerm` naming where that
term is written — which global action, and which node of it. For the running
example's `(Add (Num 1) (Num 2))` at top level the whole composition is one
[packed row](#packed-rows) — `add_own` is the `@FiatTerm` conclusion and
`num*_bridge` the two children's view-row proofs:

```text
(let add_canon (mint-@Packed_3!
        "trans_sym_congr_congr_p0_0_sym_p1_1_sym_p2_congr_congr_p0_0_sym_p1_1_sym_p2"
        add_own num1_bridge num2_bridge))
```

Four `@Proof` rows for that one expression: the three `@FiatTerm` conclusions and
that one row. A fiat is composed from nothing, so it cannot be a hole of a
skeleton and stays a row of its own. The row count is also already reduced by
dropping steps the encoder knows are reflexive — `(Num 1)`'s own conclusion is
its canonical one, so neither `Num` level composes anything.

**Merge bodies and maintenance rules.** A custom function's `:merge`, the
path-compression rule, and the container rebuild rule are all code the encoder
wrote rather than a user head, so they compose too: path compression emits
`@Trans` of the two edge proofs, and the container rebuild emits a `@Congr` onto
the view row.

### Body premises

A rule body's premise proofs are also composed, not recorded, since a body has no
column either. A nested pattern reads one view per subterm, and the fact's proof
is the outermost view's proof with a `@Congr` for each child that carries its own
subproof. That chain is emitted lazily, as one packed row, at the point the
premise is first read — which is inside the rule's *action* list. They are the
body's proofs, not proofs of anything the head concludes.

A **container side condition** is the exception: a fact a container-producing
primitive determines from bound variables — `(= v (vec-of e))`, `(= (set-of a)
(set-of b))`, or a bare `(vec-of e)` guard — has no premise to state, so it
carries the bare `@Eval` marker and the checker re-evaluates it against the rule
body instead. The encoder and the checker share one gate so they cannot drift.

A **base-value fact** is stated by no column at all. Its premise is a reflexive
`@Fiat_<Sort>` over a literal — a guard like `(> n 0)`, or an equality between two base
values such as the `(= len n)` a custom function's output leaves behind — and the
value is a function of the fact and the bindings the body already made, so
conversion re-evaluates it rather than reading a row. The `@Rule_<k>` a firing
writes then has one fewer column, and the row it would have named is never
minted. This is one gate over the body, taken in order (a fact is only
recomputable once one of its sides reads nothing but already-bound variables),
shared by the encoder and proof conversion.

A value read *out of* a container keeps a real premise, stated from the
container's own [anchor](#reflexive-anchors): `(= e (vec-get v 1))` and
`(= (vec-get v 0) (vec-get v 1))` are both `@ProjPrim_<k>` naming the reading
call, standing on whichever row anchors `v`. That is why the container has to be one the database holds — a
container the query built anchors nothing, and the rule is rejected rather than
encoded.

## Packed rows

Wherever [layer 1 is emitted](#where-layer-1-is-still-emitted), the composition's
shape is fixed by the site rather than discovered at run time, so one row stands
for the whole of it.

A site with no rule head to replay says what its row stands for by writing a
**skeleton** — a proof term over the row's other columns, spelled into the first
one in prefix order: `sym`, `trans`, `congr`, `proj`, `p<n>` for the proof in
column n, and a bare number for a congruence's or projection's child position.
Unpacking reads the skeleton back off that column and substitutes the rest into
it, so there is one statement of the composition rather than one at each end. A
column may be named twice — `trans_sym_p0_p0` is `reflexive`, `t' = t'` from the
one proof of `t = t'` — and is then carried once, or named not at all, when the
step it carries turned out to prove nothing. Every other column is a proof, so
the constructor is a function of their count alone: `@Packed_<k>`.

The encoder composes over proof *names*, so it holds each `@Sym`, `@Trans` and
`@Congr` back as a tree and writes the row where a statement reads the name. Two
things bound what one row spells. A composition nothing reads is never written at
all — the connector of a top-level term nobody builds on, for instance. And the
connector a built term hands its parent gets a row of its own, rather than being
spelled into every row above it, whenever the term's own children moved: a
level's row then spells its own children's steps and no deeper term's, so the row
is a function of the term's arity rather than of its size.

**A view rebuild** writes one row whose columns are the row proof, then each
canonicalized column's step proof, then the e-class's own step when the view's
output is an e-class. In proof mode the rebuild rule of
[Keeping the view canonical](#keeping-the-view-canonical) reads a step proof per
column and packs them:

```text
(let c0_canon_ (@UF_Math_canon c0_ c0_))
(let c0_step (@UF_Math_canon_proof c0_ pf))
… same for c1_ and e2_ …
(let s1 (drop-reflexive-step "trans_sym_p3_congr_congr_p0_0_p1_1_p2" 1 c0_ c0_canon_))
… same for columns 2 and 3 …
(let out (mint-@Packed_4! s3 pf c0_step c1_step e2_step))
```

`@UF_<Sort>_canon_proof` supplies each step's proof, or the fallback when the
column has no `@UF` row. A column that did not move proves `t = t`, so it
contributes nothing: rather than anchor it — a row per column, dropped again by
the proof simplifier — the fallback is the row proof itself and
`drop-reflexive-step` narrows the spelling until it names only the columns whose
two values differ. A column the spelling does not name is carried but never
read. The e-class's step composes on the left rather than at a child position,
since an e-class can equal one of its own children's terms.

**A merge collision** — two rows colliding on one key in a `@UF` or view
`:merge` — writes one packed row for the edge it displaces.
`proof-of-max`/`proof-of-min` pair each carried proof with the larger and smaller
side. The two share an endpoint, and which endpoint decides which of them the
composition reverses; either way it proves `larger = smaller`. The union-find's
carried proofs share their left-hand side, spelling `trans_sym_p0_p1`, and the
view's their right, spelling `trans_p0_sym_p1`.

**A custom function's view merge** writes one `@MergeRow` naming the function and
the two colliding rows' proofs; the conclusion is recovered by running the merge
body on the premise outputs. Constructor subterms inside the merge body get
`@MergeIdx` rows, indexed pre-order over the body so conversion can evaluate the
matching subexpression.

## Container proofs

A container's term form is the s-expr of its constructor — `(vec-of e0 e1 …)`,
`(pair a b)`, `(map-of k0 v0 …)`. The rebuild rule hands the primitive the
container's [reflexive anchor](#reflexive-anchors), projected out of the row
being rebuilt; a chain of congruence steps over the changed elements, anchored
there, proves `old = new` and folds into the view's congruence step like an
eq-sort child's `@UF` proof.

The chain uses `@CongrAll` — replace every child equal to `a` by `b` — rather
than positional `@Congr`, because the enclosing term's child order is not the
order the primitive sees elements in. A *nested* container needs no anchor of
its own: `@CongrAll` is expanded against the term during conversion, which
follows container children to the same depth the value rebuild does and knows
each child's position there. So the primitive folds one `@CongrAll` per changed
eq-sort element, at any depth, onto the outer anchor. Conversion desugars each
into positional `@Congr` steps against the actual term, canonicalizing a
rewritten child before the step that puts it back.

For reordering or merging containers (`Set`, `Map`, `MultiSet`) the term after
those steps can be out of order or hold duplicates, so a `@ContainerNormalize`
step canonicalizes it — sort plus dedup for sets, sort for multisets, sort plus
last-write-wins for maps. It is emitted on every rebuild, and the proof simplifier
drops it wherever it is the identity (always, for `Vec` and `Pair`).

A container is built over its elements' **natural** ids, not their deduped
e-classes: a deduped id can extract to a different syntactic shape, which would
break the rule-head check for the container's proof. Each element's
`natural -> (deduped, connector)` edge goes into the element's ordinary
`@UF_<E>`, so the standard rebuild and path compression canonicalize the natural
like any other stale term. That edge's proof column is the element's connector,
which is therefore one of the few connectors a rule head does write a row for.
