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
  variables to nullary functions with the `remove_globals.rs` pass.
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
(function g1 () Math :internal-let)
(set (g1) (Add 1 2))
(rule ((= (g1) (Add 2 3)))
      ((Add 3 4)))
```
The global is a nullary `:internal-let` function `set` to its value (no
`union` at the top level), so it gets a view table and rebuild rules like any
other function; references to `g1` become the lookup `(g1)`.



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
The snippet above is schematic (it inlines term creation as `(Add a b)`); the
  next section shows what building a term actually lowers to, and how congruence
  proofs thread canonical ids through a nested term.

# Building nested terms in actions

The commutativity rule above builds only flat, one-level terms. A rule (or a
top-level action) that builds a *nested* term has to do two things at once:
insert every subterm into its term relation and view using **canonical child
ids**, and thread a proof from the term *as the rule built it* to its canonical
form, so the final `union` records a correct equality proof.

We trace this rule end to end:

```text
(rule ((Seed a b c rewrite_var))
      ((union rewrite_var (Neg (Add a (Add b c))))))
```

The action first **flattens** to one constructor application per step:

```text
(let d (Add b c))
(let e (Add a d))
(let f (Neg e))
(union rewrite_var f)
```

The body match binds `a b c rewrite_var` and produces the rule's premise proof,
which is collected into a one-element proof list `prems = (PCons body_proof (PNil))`.
Every proof minted below is justified by `(Rule rule_name prems lhs rhs)`.

Two building blocks recur. Term, AST, and proof nodes are all *relations*, so a
new node is a fresh id (`get-fresh!`) plus a row `set` (shown here inlined, e.g.
`(Rule …)` stands for "mint a fresh proof id and `set` the `Rule` row for it").
A constructor application is interned into its FD view with
`set-if-empty-<View>!`, which returns the view's **existing** e-class if the term
was already there — so the id flowing up to the parent is always canonical.
Because a child may thus dedup to a *different* id than the one we built with, we
carry a **connector** proof `built_id = canonical_id` and rewrite that child in
the parent with `Congr`.

## Line 1 — `(let d (Add b c))`

`b` and `c` come straight from the body match, so they are already canonical and
`d` needs no `Congr`.

```text
;; the term at its natural id, and its `d_nat = d_nat` rule proof
(let d_nat (get-fresh! "Math"))
(set (Add b c d_nat) ())
(let d_prf (Rule rule_name prems (AstMath d_nat) (AstMath d_nat)))
(set (MathProof d_nat) d_prf)

;; intern (Add b c) into the view; `d` is the canonical e-class it returns
(let d_seed (get-fresh! "Math"))
(set (Add b c d_seed) ())
(set (MathProof d_seed) (Trans (Sym d_prf) d_prf))       ;; reflexive seed proof
(let d (set-if-empty-AddView! b c d_seed (Trans (Sym d_prf) d_prf)))
(let d_view_prf (view-proof-AddView b c …))              ;; proves `d = Add b c`

;; connector `d_nat = d`, used when `d` is a child of the next term
(let d_nat_to_d (Trans d_prf (Sym d_view_prf)))
```

The minted `d_nat` stays as its own row (never written into the view), so its
`Rule` proof keeps pointing at the shape the rule head wrote; `set-if-empty`
seeds a *separate* node and returns the canonical `d`.

## Line 2 — `(let e (Add a d))`

`d` was canonicalized in line 1, so the natural `e = Add(a, d_nat)` must be
rewritten to `Add(a, d)` before interning. That is the `Congr` at child index 1.

```text
;; natural e over the natural child d_nat
(let e_nat (get-fresh! "Math"))
(set (Add a d_nat e_nat) ())
(let e_prf (Rule rule_name prems (AstMath e_nat) (AstMath e_nat)))
(set (MathProof e_nat) e_prf)

;; rewrite child 1 (d_nat -> d): proves `e_nat = Add a d`
(let e_nat_to_ad (Congr e_prf 1 d_nat_to_d))

;; intern (Add a d) over the canonical child d; `e` is the returned e-class
(let e_seed (get-fresh! "Math"))
(set (Add a d e_seed) ())
(set (MathProof e_seed) (Trans (Sym e_nat_to_ad) e_nat_to_ad))
(let e (set-if-empty-AddView! a d e_seed (Trans (Sym e_nat_to_ad) e_nat_to_ad)))
(let e_view_prf (view-proof-AddView a d …))              ;; proves `e = Add a d`

;; connector `e_nat = e` = Trans(e_nat = Add a d, Sym(e = Add a d))
(let e_nat_to_e (Trans e_nat_to_ad (Sym e_view_prf)))
```

## Line 3 — `(let f (Neg e))`

Same shape, one child, rewritten with the `e_nat = e` connector at index 0.

```text
(let f_nat (get-fresh! "Math"))
(set (Neg e_nat f_nat) ())
(let f_prf (Rule rule_name prems (AstMath f_nat) (AstMath f_nat)))
(set (MathProof f_nat) f_prf)

(let f_nat_to_ne (Congr f_prf 0 e_nat_to_e))             ;; `f_nat = Neg e`

(let f_seed (get-fresh! "Math"))
(set (Neg e f_seed) ())
(set (MathProof f_seed) (Trans (Sym f_nat_to_ne) f_nat_to_ne))
(let f (set-if-empty-NegView! e f_seed (Trans (Sym f_nat_to_ne) f_nat_to_ne)))
(let f_view_prf (view-proof-NegView e …))                ;; proves `f = Neg e`

(let f_nat_to_f (Trans f_nat_to_ne (Sym f_view_prf)))    ;; connector `f_nat = f`
```

## The union — `(union rewrite_var f)`

The rule justifies `rewrite_var = f_nat` directly; composing with the
`f_nat = f` connector gives `rewrite_var = f`. The edge is oriented to the
union-find's `larger -> smaller` convention with `proof-of-max` / `proof-of-min`
(see the `UF_Math` `:merge` in [Proof Tracking](#proof-tracking)).

```text
(let rw_to_f_nat (Rule rule_name prems (AstMath rewrite_var) (AstMath f_nat)))
(let rw_to_f (Trans rw_to_f_nat f_nat_to_f))             ;; `rewrite_var = f`
(set (UF_Math (ordering-max rewrite_var f))
     (values (ordering-min rewrite_var f) <rw_to_f oriented via proof-of-max/min>))
```

The result is the same discipline at every level: build the term at natural ids,
`Congr` each child that moved to its canonical id, intern with `set-if-empty` to
get the canonical parent id, and record a `natural = canonical` connector for the
level above. Only canonical ids ever reach the view and union-find tables.

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
