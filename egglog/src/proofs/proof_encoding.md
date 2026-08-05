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
[**Proofs**](#proofs) is what fills the proof column, told in two layers: an
encoding that builds each proof as the rule runs, and the *skeleton* the encoder
actually emits, which records just enough for proof conversion to rebuild that
same proof afterwards.

The running example throughout is:

```text
(datatype Math (Add Math Math) (Num i64))
(Add (Num 1) (Num 2))
(rewrite (Add a b) (Add b a))
(run 1)
(check (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))
(delete (Add (Num 1) (Num 2)))
```

Generated names keep the `@` prefix the encoding gives them (`@AddView`), but
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

## Term relation and view

Each constructor expands to a **term relation**, a **view**, a rebuild index,
and deferred-deletion helpers:

```text
(function Add (Math Math Math) Unit :no-merge :unextractable :internal-hidden :internal-term-node)
(function @AddView (Math Math) (Math Unit)
    :merge ((set (@UF_Math (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
            (values (ordering-min old0 new0) ()))
    :internal-term-constructor Add :internal-identity-vals 1)
(index @AddOcc_Math @AddView (any 0 1 2))
(function @to_delete_Add (Math Math) Unit :no-merge :unextractable :internal-hidden)
(function @to_subsume_Add (Math Math) Unit :no-merge :unextractable :internal-hidden)
```

The term relation `Add(child0, child1, eclass)` stores every application as a row
whose last column is the term's own id, minted with `get-fresh!`. Nothing is ever
removed from it, which lets proofs refer to terms after they leave the e-graph.
`:internal-term-node` marks its rows as term nodes for proof extraction.

The **view** is the functional dependency `children -> (eclass, proof)` over a
term's *canonicalized* children. Two view rows that collide on the same children
are congruent, so the view's `:merge` resolves congruence directly — it keeps the
smaller e-class and unions the two in `@UF_<Sort>`, and no separate congruence
rule is needed. All queries read the view; the term relation is write-only after
creation. The two deferred-deletion helpers are plain `Unit` relations keyed on
the children, with no minted id and no `:internal-term-node`, so extraction never
reads them as terms.

## Building a term

Evaluating a constructor application mints an id, writes the term-relation row,
and interns the application into its view. Top level `(Add (Num 1) (Num 2))`
lowers to:

```text
(let n1 (get-fresh! "Math"))
(set (Num 1 n1) ())
(let n1_can (set-if-empty-@NumView! 1 n1 ()))
…                                                       ;; the same for (Num 2)
(let ab (get-fresh! "Math"))
(set (Add n1_can n2_can ab) ())
(let ab_can (set-if-empty-@AddView! n1_can n2_can ab ()))
```

`set-if-empty-<View>!` interns the application and returns the view's *existing*
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
(rule ((= (values e p) (@AddView a b))
       (= rewrite_var e))
      ((set (Add b a rewrite_var) ())
       (set (@AddView b a) (values rewrite_var ())))
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

Deletions and subsumptions are deferred. `(delete (Add (Num 1) (Num 2)))` builds
its argument's children and then records a marker row:

```text
(set (@to_delete_Add n1_can n2_can) ())
```

which `@delete_subsume_ruleset` consumes during maintenance:

```text
(rule ((@to_delete_Add c0_ c1_)
       (= (values e pf) (@AddView c0_ c1_)))
      ((delete (@AddView c0_ c1_))
       (delete (@to_delete_Add c0_ c1_)))
        :ruleset @delete_subsume_ruleset :name "@delete_rule")
```

with a `:subsume` sibling for `@to_subsume_Add`. Only the view is deleted or
subsumed; the term relation is never queried, so keeping its rows lets proofs
still refer to deleted terms.

# Queries

All queries — rule bodies, `check`, and `prove` — read the **view**, never the
term relation. A view read binds both the e-class and the proof column:

```text
(= (values e p) (@AddView a b))
```

A nested term flattens into one view read per subterm, joined on shared e-class
variables. The running example's `check` expands to:

```text
(check (= (values e1 p1) (@NumView 1))
       (= (values e2 p2) (@NumView 2))
       (= (values e3 p3) (@AddView e1 e2))
       (= (values e4 p4) (@NumView 2))
       (= (values e5 p5) (@NumView 1))
       (= (values e6 p6) (@AddView e4 e5))
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
(ruleset @delete_subsume_ruleset)

(run-schedule
    (seq (saturate (seq (run @rebuilding_cleanup)
                        (saturate (seq (run @parent)))
                        (run @rebuilding)))
         (run @delete_subsume_ruleset)))
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
(index @AddOcc_Math @AddView (any 0 1 2))
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
       (delete (@AddView c0_ c1_))
       (set (@AddView c0_canon_ c1_canon_) (values e2_canon_ ())))
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
variable to a nullary function, so the backend need not treat them specially:

```text
(let g1 (Add (Num 1) (Num 2)))
```

becomes

```text
(function g1 () Math :internal-let)
(set (g1) (Add (Num 1) (Num 2)))
```

and references to `g1` become the lookup `(g1)`. The encoding then treats
`:internal-let` like a nullary constructor: it gets a term relation, an FD view
`@g1View : () -> (Math, proof)` with the congruence `:merge`, a rebuild index, and
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
(rule ((= (values e pf) (@WrapView c0_))
       (= c0_canon_ (@container_rebuild c0_))
       (!= c0_ c0_canon_))
      ((set (@WrapView c0_canon_) (values e ()))
       (delete (@WrapView c0_)))
        :ruleset @rebuilding :naive :name "@rebuild_rule" :internal-include-subsumed)
```

The primitive clones the container, remaps each element to its union-find leader,
and re-interns it. Because it reads the elements' `@UF_<E>` tables rather than
joining a tracked table, the rule is `:naive`: an element becoming equal to
another produces no delta on the container's own view row, so the rule must
rescan the view each round. Nested containers (e.g. `(Vec (Vec Math))`) rebuild
by recursing through container-typed elements. The e-class column of `@WrapView`
is an ordinary eq-sort column and gets the indexed rule from
[Keeping the view canonical](#keeping-the-view-canonical).

See [`crate::proofs::proof_container_rebuild`] for the rebuild primitives, and
[Container proofs](#container-proofs) for what they put in the proof column.

# Proofs

With proofs enabled, the encoding first emits a header defining the proof format
(see [`crate::proofs::proof_format`] and `proof_encoding_helpers.rs`): the
`@Proof` and `@Ast` sorts, one `@Ast<Sort>` per sort, and the proof-node
relations `@Fiat`, `@RuleLink`, `@MergeIdx`, `@MergeRow`, `@Trans`, `@Sym`,
`@Congr`, `@CongrAll`, `@ContainerNormalize`, `@Eval` — each a
`(function … Unit :no-merge)`, not a constructor, so a proof node is a fresh id
plus a row. Two further families have their column count fixed by the site rather
than by the format, so each shape is declared just before the commands needing
it: `@Rule_<k>`, a rule proof carrying its `k` body premises inline, and
`@Packed_<k>`, one row standing for a whole composition over `k` proofs (see
[Packed rows](#packed-rows)).

Each sort also gets `(function @<Sort>Proof (<Sort>) @Proof :merge old)`,
recording for each term `t` a proof of `t = t` (oldest kept), and the union-find
and view proof columns become real:

```text
(function @UF_Math (Math) (Math @Proof) :merge (… @Packed_2 "trans_sym_p0_p1" …) …)
(function @AddView (Math Math) (Math @Proof) :merge (… @Packed_2 "trans_p0_sym_p1" …) …)
```

If term `k` has parent `p`, `(@UF_Math k)` returns `(values p proof)` where
`proof` proves `k = p` — the key on the left. A view row's proof runs the other
way, `eclass = f(children)`.

The rest of this part is the two layers.
[**Layer 1**](#layer-1-building-the-proof-as-the-rule-runs) is a rule that builds
each proof as it goes; it is the specification.
[**Layer 2**](#layer-2-proof-skeletons) is what the encoder emits for a rule
head: a skeleton naming the firing, from which proof conversion recovers layer
1's proof. Everything after those two — body premises, rebuild rows, merge
collisions, containers — is stated against layer 1.

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
(illustrative: each proof node is one `let` rather than a `get-fresh!` plus a
row, and `rule-proof` stands for whatever names a proof the firing concludes):

```text
(let ba (get-fresh! "Math"))                 ;; the natural node
(set (Add b a ba) ())
(let own  (rule-proof rule_name prems))      ;; ba = ba, the head's own conclusion
(let edge (rule-proof rule_name prems))      ;; rewrite_var = ba, the dropped union
(let view (@Trans edge own))                 ;; rewrite_var = (Add b a), the view row
(let back (@Sym view))
(let conn (@Trans own back))                 ;; ba = rewrite_var, the connector
(set (@MathProof ba) own)
(set (@AddView b a) (values rewrite_var view))
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
(set (Add b c d) ())
(let d-prf (rule-proof rule_name prems))              ;; d = d
(let (values d' d-to-d'-prf) (set-if-empty (@AddView b c) d d-prf))
```

**`(let e (Add a d))`.** The child `d` moved, so this level needs both nodes. The
natural node is over `d`; the canonical one over `d'`; `@Congr` at the child's
position carries the first to the second:

```text
(let e (get-fresh! "Math"))
(set (Add a d e) ())
(let e-prf (rule-proof rule_name prems))              ;; e = e

(let e' (get-fresh! "Math"))                          ;; the same term over canonical children
(set (Add a d' e') ())
(let e-to-e'-prf (@Congr e-prf 1 d-to-d'-prf))        ;; e = e'
(let e'-prf (@Trans (@Sym e-to-e'-prf) e-to-e'-prf))  ;; e' = e'

(let (values e'' e'-to-e''-prf) (set-if-empty (@AddView a d') e' e'-prf))
(let e-to-e''-prf (@Trans e-to-e'-prf e'-to-e''-prf)) ;; e = e'', for the level above
```

**`(let f (Neg e))`.** Identical shape, one level up, with `e-to-e''-prf` as the
congruence step:

```text
(let f (get-fresh! "Math"))
(set (Neg e f) ())
(let f-prf (rule-proof rule_name prems))              ;; f = f

(let f' (get-fresh! "Math"))
(set (Neg e'' f') ())
(let f-to-f'-prf (@Congr f-prf 0 e-to-e''-prf))       ;; f = f'
(let f'-prf (@Trans (@Sym f-to-f'-prf) f-to-f'-prf))  ;; f' = f'

(let (values f'' f'-to-f''-prf) (set-if-empty (@NegView e'') f' f'-prf))
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
store a proof* — a view row's proof column, a `@UF` edge's proof column, a
`@<Sort>Proof` entry. Each such row is a **skeleton**: it names the rule that
fired, the premise proofs it fired on, and *which* proof of that head it is.

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

A rule proof stores no terms at all. The column, plus the premises, is the whole
conclusion.

### Bridges

The bridge — which e-class a subterm interned into — is the one thing conversion
cannot recompute, so the skeleton carries it. A row written before the head
interns anything carries the body premises inline as `@Rule_<k>`. Every row after
that is a `@RuleLink`, naming the row written just before the newest interning —
which carries the premises and every earlier bridge — plus that interning's
bridge. Chaining keeps a row's width constant no matter how deep the head is.

So a row carries exactly the bridges the head had recorded when it wrote the row,
and the replay takes them one at a time: it reaches the column the row names, and
then asks for one bridge more than the row has. Running out is what tells the
replay it has gone as far as this row can say anything about, and it is the only
thing that stops it.

### The running example

The `rewrite`'s head builds one guest over two matched variables. It writes two
proof rows:

```text
(rule ((= (values e p) (@AddView a b))
       (= rewrite_var e))
      ((let rule_name "(rewrite (Add a b) (Add b a))")
       (let ba (get-fresh! "Math"))
       (set (Add b a ba) ())
       (let own (get-fresh! "@Proof"))
       (set (@Rule_1 rule_name p 0 own) ())
       (set (@MathProof ba) own)
       (let view (get-fresh! "@Proof"))
       (set (@Rule_1 rule_name p 2 view) ())
       (set (@AddView b a) (values rewrite_var view)))
        :name "(rewrite (Add a b) (Add b a))" :unsafe-seminaive)
```

Column 0 is the natural node's own conclusion, stored in `@MathProof`; column 2
is the guest's view row. Columns 1 and 3 — the dropped union's edge and the
connector — are in the array, but nothing stores them, so no row is written.
Those two plus the intermediate `@Sym` are the three rows layer 1 wrote above and
layer 2 does not.

A nested head chains. For

```text
(rule ((Seed r)) ((union r (Add (Num 1) (Num 2)))))
```

the walk numbers `(Num 1)` at columns 0–2, `(Num 2)` at 3–5, and the guest
`(Add …)` at 6–9, and the head writes six rows (term rows and the `get-fresh!`
binding each proof variable elided):

```text
(set (@Rule_1   rule_name prems 0 num1_pf0) ())      ;; (Num 1) as written
(set (@Rule_1   rule_name prems 1 num1_pf1) ())      ;; …over canonical children
(let num1_e     (set-if-empty-@NumView! 1 …))
(let num1_bridge (view-proof-@NumView 1 …))
(set (@RuleLink num1_pf1 num1_bridge 3 num2_pf0) ())
(set (@RuleLink num1_pf1 num1_bridge 4 num2_pf1) ())
(let num2_e     (set-if-empty-@NumView! 2 …))
(let num2_bridge (view-proof-@NumView 2 …))
(set (@RuleLink num2_pf1 num2_bridge 6 add_pf0) ())  ;; (Add …) as written
(set (@RuleLink num2_pf1 num2_bridge 8 add_view) ())
(set (@AddView num1_e num2_e) (values r add_view))
```

The last row carries both bridges, reached through the chain. Column 3 is an own
conclusion, which composes nothing, so it does not use the bridge it carries — but
carry it it must, or the replay would stop one interning short of it. Layer 1's
walk of the same head names seventeen proofs: four conclusions and thirteen
composition steps. Six rows against seventeen is the whole point of the layer.

Row counts per firing, proof rows only (not the view or `@UF` write beside them):
a flat rewrite **2**, the nested head above **6**, a view rebuild **1**, a merge
collision **1**.

A `union` of two matched variables builds nothing, so it needs one row — but
which endpoint the `@UF` edge is stated from is only known once the ids are
compared. Its column is therefore an expression, not a literal:

```text
(set (@Rule_1 rule_name prems (proof-of-max x 1 y 2) edge) ())
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

**Top-level actions.** A top-level action is justified by `@Fiat` and has no
column to name, so the encoder composes. For the running example's
`(Add (Num 1) (Num 2))` at top level the whole composition is one
[packed row](#packed-rows) — `add_own` is the `@Fiat` conclusion and
`num*_bridge` the two children's view-row proofs:

```text
(set (@Packed_3 "trans_sym_congr_congr_p0_0_sym_p1_1_sym_p2_congr_congr_p0_0_sym_p1_1_sym_p2"
        add_own num1_bridge num2_bridge add_canon) ())
```

Four `@Proof` rows (plus six `@Ast` rows) for that one expression: the three
`@Fiat` conclusions and that one row. A `@Fiat` is composed from nothing, so it
cannot be a hole of a skeleton and stays a row of its own; the `@Ast` rows are
its endpoints. The row count is also already reduced by dropping steps the
encoder knows are reflexive — `(Num 1)`'s own conclusion is its canonical one, so
neither `Num` level composes anything.

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

## Packed rows

Wherever [layer 1 is emitted](#where-layer-1-is-still-emitted), the composition's
shape is fixed by the site rather than discovered at run time, so one row stands
for the whole of it.

A site with no rule head to replay says what its row stands for by writing a
**skeleton** — a proof term over the row's other columns, spelled into the first
one in prefix order: `sym`, `trans`, `congr`, `p<n>` for the proof in column n,
and a bare number for a congruence's child position. Unpacking reads the skeleton
back off that column and substitutes the rest into it, so there is one statement
of the composition rather than one at each end. A column may be named twice —
`trans_sym_p0_p0` is `reflexive`, `t' = t'` from the one proof of `t = t'` — and
is then carried once. Every other column is a proof, so the constructor is a
function of their count alone: `@Packed_<k>`.

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
(let c0_term (@MathProof c0_))
(let c0_step (@UF_Math_canon_proof c0_ c0_term))
… same for c1_ and e2_ …
(set (@Packed_4 "trans_sym_p3_congr_congr_p0_0_p1_1_p2"
        pf c0_step c1_step e2_step out) ())
```

`@UF_<Sort>_canon_proof` supplies each step's proof, reflexive for a column that
did not move. The e-class's step composes on the left rather than at a child
position, since an e-class can equal one of its own children's terms.

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
`(pair a b)`, `(map-of k0 v0 …)`. Every container sort gets a `@<Sort>Proof`
table holding a reflexive `container = container` proof, set at creation. A chain
of congruence steps over the changed elements, anchored there, proves `old = new`
and folds into the view's congruence step like an eq-sort child's `@UF` proof.

The chain uses `@CongrAll` — replace every child equal to `a` by `b` — rather
than positional `@Congr`, because the rebuild primitive sees elements in *value*
order while the term form orders children canonically. `@CongrAll` exists only in
the raw e-graph proof; conversion desugars it into positional `@Congr` steps
computed against the actual term.

For reordering or merging containers (`Set`, `Map`, `MultiSet`) the term after
those steps can be out of order or hold duplicates, so a `@ContainerNormalize`
step canonicalizes it — sort plus dedup for sets, sort for multisets, sort plus
last-write-wins for maps. It is emitted on every rebuild, and the proof simplifier
drops it wherever it is the identity (always, for `Vec` and `Pair`).

A container is built over its elements' **natural** ids, not their deduped
e-classes: a deduped id can extract to a different syntactic shape, which would
break the rule-head check for the container's term proof. Each element's
`natural -> (deduped, connector)` edge goes into the element's ordinary
`@UF_<E>`, so the standard rebuild and path compression canonicalize the natural
like any other stale term. That edge's proof column is the element's connector,
which is therefore one of the few connectors a rule head does write a row for.
