Rewrites an egglog program to use an encoding for equality tracking, optionally including proof tracking.

# Term Encoding

The job of the term encoding is to *remove all calls to union* in the egglog program.
This makes proof production easier, since all equality reasoning is explicit and
  can be instrumented with proof tracking.
The term encoding adds an explicit union-find structure per sort, and maintains it via
  rules that run during scheduled maintenance.
The union-find for a sort is a function `UF_<Sort>` that maps each term to its
  parent; a term with no entry is its own representative.
Unioning two terms is a `set` making one the parent of the other; the function's `:merge`
  resolves the case where the term already had a different parent.
For efficiency, every constructor becomes two tables:
  a term table that stores the actual terms, and a view table mapping canonicalized
  children to the e-class representative (the leader term).
The encoding uses the same shapes with and without proof tracking:
  union-find and view rows carry a proof column, which is `()` (of sort `Unit`)
  when proofs are off.
The term encoding enables proof tracking, done at the
  same time in this file.
The encoding keeps the operational semantics equivalent to the standard encoding (for the
subset of commands that are currently supported).

The transformation is triggered when an `EGraph` is created with
[`EGraph::new_with_term_encoding`](crate::EGraph::new_with_term_encoding) or
converted via [`EGraph::with_term_encoding_enabled`](crate::EGraph::with_term_encoding_enabled).

Consider a tiny program that defines a pure arithmetic helper and checks a fact about it:

```text
(sort Math)
(constructor Add (i64 i64) Math)
(Add 1 2)
(rule ((Add a b))
      ((union (Add a b) (Add b a)))
     :name "commutativity")
(run 1)
(check (= (Add 1 2) (Add 2 1)))

(delete (Add 1 2))
```

Lowering the program with the term encoding expands to a bunch of new egglog, which we'll show (most of) in pieces.

```text
(ruleset parent)
(ruleset rebuilding)
(ruleset rebuilding_cleanup)
(ruleset delete_subsume_ruleset)
```

*The new rulesets* orchestrate path compression on the per-sort union-find (`parent`),
rebuild-time congruence (`rebuilding` + `rebuilding_cleanup`), and deferred deletions/subsumptions (`delete_subsume_ruleset`).

```text
(run-schedule
    (seq
       (saturate
          rebuilding_cleanup ;; clean up merged rows
          (saturate parent) ;; flatten union-find chains via path compression
          rebuilding) ;; find new equalities via congruence
       delete_subsume_ruleset)) ;; process deletions/subsumptions
```

*In-between* the original program's commands, the term encoding
  runs these rulesets to maintain egglog's invariants.

```text
(sort Math :internal-uf UF_Math)
(function UF_Math (Math) (Math Unit)
    :merge ((set (UF_Math (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
            (values (ordering-min old0 new0) ()))
    :unextractable :internal-hidden :internal-identity-vals 1)
(rule ((= (values b pb) (UF_Math a))
       (= (values c pc) (UF_Math b))
       (!= b c))
      ((set (UF_Math a) (values c ())))
        :ruleset parent :name "uf_path_compress")
```

*The union-find* for each sort is the function `UF_<Sort>`, mapping each term to its parent
  (plus the proof column, `()` here).
A term with no row is its own representative, so `UF_<Sort>` acts as an identity-on-miss lookup.
To union `a` and `b`, the encoding runs
  `(set (UF_<Sort> (ordering-max a b)) (values (ordering-min a b) ()))`.
If the key already had a different parent, the `:merge` action block runs:
  the key keeps the smaller of the two parents (the merge result),
  and the `set` in the block unions the larger parent with the smaller one,
  since both are equal to the key.
The `:internal-identity-vals 1` annotation marks the parent column as the row's identity:
  a merge whose parent is unchanged keeps the existing row without running the block.
Without it, re-setting an existing edge would run the block and stage the same union
  again, forever.

*Union-find rules:*
The only maintenance rule is path compression (in the `parent` ruleset), which flattens
  `a -> b -> c` chains to `a -> c`.
We use the `ordering-max` and `ordering-min` egglog primitives
  to define an arbitrary ordering on terms based on insertion order,
  so that we can deterministically choose which term becomes the parent
  in the union-find structure.


```text
(sort view)
(constructor Add (i64 i64) Math :unextractable :internal-hidden)
(function AddView (i64 i64) (Math Unit)
    :merge ((set (UF_Math (ordering-max old0 new0)) (values (ordering-min old0 new0) ()))
            (values (ordering-min old0 new0) ()))
    :internal-term-constructor Add :internal-identity-vals 1)
(constructor to_delete_Add (i64 i64) view :internal-hidden)
(constructor to_subsume_Add (i64 i64) view :internal-hidden)
```

Each constructor in the original program is expanded to
  a term table (`Add`), a view table (`AddView`), and helpers for deferred deletion/subsumption
  (`to_delete_Add`, `to_subsume_Add`).
The view table maps a term's canonicalized children to `(values eclass proof)`:
  the representative term for its e-class, plus the proof column.
A canonicalized term has representative terms for its children.
Two view rows conflicting on the same children are congruent, so the view's `:merge`
  resolves congruence directly: it keeps the smaller e-class and unions the two
  e-classes in `UF_<Sort>` — no congruence rule is needed.
The view tables are kept up to date during rebuilding.

```text
(rule ((= (values v4 v5) (AddView c0 c1))
       (= (values v6 v7) (UF_Math v4))
       (!= v4 v6))
      ((set (AddView c0 c1) (values v6 ())))
        :ruleset rebuilding :name "rebuild_rule" :internal-include-subsumed)
```

For each constructor, we add rebuild rules that keep the view canonical,
  *fanned out* one per eq-sort column.
`Add`'s `i64` children are not eq-sorts, so its only rebuild rule updates the e-class:
  when the e-class has a `UF_<Sort>` parent, the rule re-sets the row with the leader
  (the view's `:merge` keeps the smaller).
A rule for an eq-sort child instead re-keys the row: it `set`s the view at the
  canonicalized children and deletes the stale row.
Because `UF_<Sort>` has no row for a canonical term (identity-on-miss), a column already at its
  leader simply doesn't match, so no self-loops or default lookups are needed.

## Rebuild indexes

Rather than fan out one rebuild rule per eq-sort child column, the encoding rebuilds a
  view's eq-sort children with a *single* rule driven by a `UF_<Sort>` edge, mirroring how
  a native rebuild iterates the e-nodes that reference a changed e-class.
This needs a materialized *rebuild index* per child eq-sort — a term→row map — so that,
  given a term that just gained a leader, the rule finds the rows containing it by key
  lookup instead of scanning the view.
Consider a constructor with two eq-sort children:

```text
(constructor Cons (Math Math) Math)
(function ConsIndex_Math (Math Math Math) Unit :merge old :internal-hidden :unextractable)
```

`ConsIndex_Math` holds, for each view row `(ConsView c0 c1)` and each eq-sort child, an
  entry `(<child> c0 c1)`: the referenced child first, then the row's key. The encoding
  writes these entries wherever it writes the view and deletes them wherever it deletes a
  view row, keeping the index in sync (subsumption keeps the row, so it leaves the index
  alone).
The index is a `:merge` function rather than a relation so that a `set` and a `delete` of
  the same index key in one rebuild round resolve exactly as the view's own `set`/`delete`
  do; a plain relation resolves that conflict differently and can drift out of sync with
  the view under concurrent re-keying.

The single rebuild rule is driven by the `UF_<Sort>` edge and the index alone; it reads
  the view row's `(eclass, proof)` on the *right-hand side* with per-value-column read
  primitives (`ConsView_col0` / `ConsView_col1`) rather than joining the view in the body.
  It then canonicalizes *every* eq-sort child in its action with the `uf_canon` primitive
  (the child's `UF_<Sort>` leader, or the child itself when it has no row — the
  identity-on-miss lookup a plain fact can't express):

```text
(rule ((= (values leader pf) (UF_Math follower))
       (!= follower leader)
       (ConsIndex_Math follower c0 c1))
      ((let e  (ConsView_col0 c0 c1))
       (let vp (ConsView_col1 c0 c1))
       (let nc0 (uf_canon c0))
       (let nc1 (uf_canon c1))
       (set (ConsView nc0 nc1) (values e ()))
       (set (ConsIndex_Math nc0 nc0 nc1) ()) (set (ConsIndex_Math nc1 nc0 nc1) ())
       (delete (ConsView c0 c1))
       (delete (ConsIndex_Math c0 c0 c1)) (delete (ConsIndex_Math c1 c0 c1)))
       :ruleset rebuilding :unsafe-seminaive :name "rebuild_rule" :internal-include-subsumed)
```

Keeping the view out of the body matters for performance: joining the tuple view there
  roughly doubles the rebuild's cost per firing, whereas the RHS reads are direct keyed
  lookups. `uf_canon` and the view reads touch tables in the action, so the rule is
  `:unsafe-seminaive`; the driving `UF_<Sort>` delta and the index make those reads sound
  (every child that changes produces a delta the rule fires on). The `(!= follower leader)`
  guard is required: it keeps the rule from re-keying a row to itself when `follower` is
  already its own leader, a no-op the fixpoint would otherwise never stop repeating. In
  proof mode the action folds one `Congr` step per child onto the view proof; reflexive
  (unchanged) children drop in the proof simplifier. A constructor view keeps a separate
  rule for its eclass *value* (the view `:merge` rewrites it without ever seeing the row
  key, so it cannot be indexed); container columns rebuild structurally rather than through
  `UF_<Sort>`.

```text
(function v3 () Math :no-merge :unextractable :internal-let)
(set (v3) (Add 1 2))
(set (AddView 1 2) (values (v3) ()))
```

Above is the desugaring for `(Add 1 2)`.
We add to both view and term tables whenever we evaluate
  a constructor or function application.
The new term needs no `UF_<Sort>` entry: with identity-on-miss, a term with no row is already
  its own representative.
It's straightforward except for global variables.
Since global variables are not allowed after this pass,
  we use functions with no arguments to represent them
  (see globals section below).


```text
(rule ((= (values v5 v6) (AddView a b)))
      ((let v7 (Add a b))
       (set (AddView a b) (values v7 ()))
       (let v8 (Add b a))
       (set (AddView b a) (values v8 ()))
       (set (UF_Math (ordering-max v7 v8)) (values (ordering-min v7 v8) ())))
       :name "commutativity")
```

Here we have the instrumented commutativity rule.
The query uses the view table to find the canonical e-node.
The actions add to the term and view tables, then add an equality to the union-find.
We add the equality with a `set` on `UF_<Sort>`, using the `ordering-max` and
  `ordering-min` egglog primitives to deterministically choose the parent.




```text
(check (= (values v9 v10) (AddView 1 2))
       (= (values v11 v12) (AddView 2 1))
       (= v9 v11))
```

All queries use the view tables, including check commands.
This query checks that the e-class representatives for `(Add 1 2)` and `(Add 2 1)` are equal,
  ensuring they share the same e-class.

```text
(rule ((to_delete_Add c0 c1)
       (= (values e pf) (AddView c0 c1)))
      ((delete (AddView c0 c1))
       (delete (to_delete_Add c0 c1)))
        :ruleset delete_subsume_ruleset :name "delete_rule")
(rule ((to_subsume_Add c0 c1)
       (= (values e pf) (AddView c0 c1)))
      ((subsume (AddView c0 c1)))
        :ruleset delete_subsume_ruleset :name "delete_rule_subsume")

(to_delete_Add 1 2)
```

Finally, deletions and subsumptions are deferred via helper tables.
For every constructor, we add a `to_delete_<Constructor>` and `to_subsume_<Constructor>` table.
When a deletion or subsumption is requested, we add to these tables.
During rebuilding, we process these tables to actually delete or subsume the requested terms.
View functions support subsumption (via the `:internal-term-constructor` annotation).
We only need to delete or subsume from the view tables,
  since the term tables are not used for queries.
This has the added benefit of allowing us to keep terms around
  for proof tracking even after they are deleted from the e-graph.


# Globals

*Before the term encoding*, egglog desugars all global
  variables to constructors with the `proof_global_remover.rs` pass.
This makes the encoding simpler and makes it so the backend
  need not worry about globals.
The above program doesn't have any global variables, so it stays the same.
A different program like this one:
```text
(sort Math)
(constructor Add (i64 i64) Math)
(let g1 (Add 1 2))
(rule ((= g1 (Add 2 3))
      ((Add 3 4))))
```

Would desugar to this before term encoding:
```text
(sort Math)
(constructor Add (i64 i64) Math)
(constructor g1 () Math)
(union (g1) (Add 1 2))
(rule ((= (g1) (Add 2 3)))
      ((Add 3 4)))
```



# Proof Tracking

During term encoding, if proof tracking is enabled,
  we also instrument the program to track proofs of equalities.
We'll continue with our example from above, showing the additions
  for proof tracking.

Original program snippet is

```text
(sort Math)
(constructor Add (i64 i64) Math)
(Add 1 2)
(rule ((Add a b))
      ((union (Add a b) (Add b a)))
     :name "commutativity")
(run 1)
(check (= (Add 1 2) (Add 2 1)))
```


The encoding with proof tracking adds a proof header before the rest of the program.
The header defines the proof format corresponding to [`RawProof`](crate::proofs::RawProof) in Rust.
See the proof header in `proof_encoding_helpers.rs` for details.

```text
(function MathProof (Math) Proof :merge old :unextractable :internal-hidden)
```

Every sort gets a proof table storing
  a proof for that term.
The proof proves a proposition `t = t` for
  input term `t`.
We store the oldest proof currently.

When proof tracking is enabled, the union-find keeps the same shape, but its proof
column carries a real `Proof` instead of `()`:

```text
(function UF_Math (Math) (Math Proof)
    :merge ((let hi_pf_ (proof-of-max old0 old1 new0 new1))
            (let lo_pf_ (proof-of-min old0 old1 new0 new1))
            (set (UF_Math (ordering-max old0 new0))
                 (values (ordering-min old0 new0) (Trans (Sym hi_pf_) lo_pf_)))
            (values (ordering-min old0 new0) lo_pf_))
    :unextractable :internal-hidden :internal-identity-vals 1)
```

If term `k` has parent `p`, `(UF_Math k)` returns `(values p proof)` where `proof`
proves `k = p` (the key on the left). The `:merge` is the term-mode merge with the
proofs riding along: `proof-of-min`/`proof-of-max` return the proof paired with the
smaller/larger parent, the displaced edge stores `Trans (Sym hi_pf_) lo_pf_`
(proving `larger parent = smaller parent`), and the smaller parent keeps its own
proof. Path compression flattens chains via `Trans`.


Similarly, the constructor view's proof column carries a proof of the row itself:

```text
(function AddView (i64 i64) (Math Proof)
    :merge ((let hi_pf_ (proof-of-max old0 old1 new0 new1))
            (let lo_pf_ (proof-of-min old0 old1 new0 new1))
            (set (UF_Math (ordering-max old0 new0))
                 (values (ordering-min old0 new0) (Trans hi_pf_ (Sym lo_pf_))))
            (values (ordering-min old0 new0) lo_pf_))
    :internal-term-constructor Add :internal-identity-vals 1)
```

The `proof` in `(values eclass proof)` proves `eclass = f(children)` (the eclass on
the left), which is why the `Trans`/`Sym` composition is flipped relative to the
union-find's.


```text
(rule (;; query the view for its eclass and proof (proof that eclass = (Add a b))
       (= (values v11 v12) (AddView a b)))
      (;; proof list, one per line of the original query
       (let v13 (PCons v12 (PNil)))

       (let v14 (Add a b))
       ;; Proof that Add a b = Add a b
       (let v15 (Rule "commutativity" v13 (AstMath v14) (AstMath v14)))
       ;; Set the proof for Add a b
       (set (MathProof v14) v15)
       ;; Update the FD view: children -> (eclass, proof)
       (set (AddView a b) (values v14 v15))

       (let v16 (Add b a))
       ;; Proof that Add b a = Add b a
       (let v17 (Rule "commutativity" v13 (AstMath v16) (AstMath v16)))
       (set (MathProof v16) v17)
       (set (AddView b a) (values v16 v17))

       ;; Union (Add a b) and (Add b a), storing a proof of their equality.
       (set (UF_Math (ordering-max v14 v16))
            (values (ordering-min v14 v16)
                    (Rule "commutativity" v13 (AstMath (ordering-max v14 v16)) (AstMath (ordering-min v14 v16))))))
         :name "commutativity")
```

Instrumented rules with proof tracking query the view function directly
  (since the proof is its output column), then construct proofs for each action.
The structure is the same as term mode — view and UF updates both use `set` —
  but the values stored carry `Proof` terms instead of `()`.
For nested terms, congruence proofs are built to ensure
  the proof terms match the original queries.

# Containers

Container sorts (`Vec`, `Set`, `Map`, `MultiSet`, `Pair`) are never unioned
directly, so they get **no** union-find tables. Instead a container is
recanonicalized structurally when its elements' e-classes change. Take:

```text
(datatype Math (Num i64))
(sort MathVec (Vec Math))
(constructor Wrap (MathVec) Math)
```

The `MathVec` argument of `Wrap` is a container column, so its rebuild rule
canonicalizes it with a per-container *rebuild primitive* the encoding registers
(here `MathVec_rebuild`); the e-class column gets the usual `UF_Math` rule:

```text
(rule ((= (values e pf) (WrapView c0))
       (= c0_rebuilt (MathVec_rebuild c0))
       (!= c0 c0_rebuilt))
      ((set (WrapView c0_rebuilt) (values e ()))
       (delete (WrapView c0)))
       :ruleset rebuilding :naive :name "rebuild_rule" :internal-include-subsumed)
```

The primitive clones the container, remaps each element to its union-find leader,
and re-interns it. Because it reads the elements' `UF_<E>` tables rather than
joining a tracked table, the rule is marked `:naive`: an element becoming equal
to another produces no delta on the container's own view row, so the rule must
rescan the view each round. Nested containers (e.g. `(Vec (Vec Math))`) rebuild
by recursing through container-typed elements.

**Proofs.** A container's term form is the s-expr of its constructor —
`(vec-of e0 e1 …)`, `(pair a b)`, `(map-of k0 v0 …)` — so the generic `Congr`
machinery applies unchanged. Every container sort gets a reflexive `<Sort>Proof`
table (a `container = container` proof, set at creation); a `Congr` chain over
the changed elements, anchored there, proves `old = new` and folds into the
view's congruence step like an eq-sort child's UF proof.

For reordering/merging containers (`Set`, `Map`, `MultiSet`) the element-wise
`Congr` term can be out of order or hold duplicates, so a `ContainerNormalize`
step (see [`crate::proofs::proof_format`]) canonicalizes it — sort + dedup for
sets, sort for multisets, sort + last-write-wins for maps. It is emitted on every
rebuild and dropped by the proof simplifier wherever it is the identity (always
for `Vec` / `Pair`). Maps use a flat `(map-of k0 v0 …)` form so this works like
the other containers.

See [`crate::proofs::proof_container_rebuild`] for the rebuild primitives.
