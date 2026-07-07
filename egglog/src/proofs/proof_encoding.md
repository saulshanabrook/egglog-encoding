Rewrites an egglog program to use an encoding for equality tracking, optionally including proof tracking.

# Term Encoding

The job of the term encoding is to *remove all calls to union* in the egglog program.
This makes proof production easier, since all equality reasoning is explicit and
  can be instrumented with proof tracking.
The term encoding adds an explicit union-find structure per sort, and maintains it via
  rules that run during scheduled maintenance.
Each sort's union-find is a single self-referential function `UF_<Sort> : (S) -> S` that maps
  each term to its parent; a term with no entry is its own representative (identity-on-miss).
Its native `:merge` (built in `EGraph::build_uf_self_merge`)
  keeps the smaller endpoint on a conflict and unions the displaced parent back into `UF_<Sort>`,
  so a single `set` performs a union.
For efficiency, every constructor becomes two tables:
  a term table that stores the actual terms, and a view table storing representative terms along with their e-class (stored as the leader term).
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
(function UF_Math (Math) Math :merge (ordering-min old new) :unextractable :internal-hidden)
(rule ((= b (UF_Math a))
       (= c (UF_Math b))
       (!= b c))
      ((set (UF_Math a) c))
        :ruleset parent :name "uf_path_compress")
```

*The union-find* for each sort is the single self-referential function `UF_<Sort>`,
  mapping each term to its parent.
`UF_<Sort>` is `(S) -> S` without proof tracking, or `(S) -> (S Proof)` with proof tracking
  (the extra column carries a proof of the parent edge).
A term with no row is its own representative, so `UF_<Sort>` acts as an identity-on-miss lookup.
The source `:merge (ordering-min old new)` above is only a placeholder that lets the function
  typecheck; `declare_function` replaces it with the native self-referential merge
  (see `EGraph::build_uf_self_merge`), which on a conflicting
  parent keeps the smaller endpoint and unions the displaced one back into `UF_<Sort>`.
A single `set` on `UF_<Sort>` therefore performs a union.

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
(function AddView (i64 i64 Math) Unit :merge old :internal-term-constructor Add)
(constructor to_delete_Add (i64 i64) view :internal-hidden)
(constructor to_subsume_Add (i64 i64) view :internal-hidden)
```

Each constructor in the original program is expanded to
  a term table (`Add`), a view table (`AddView`), and helpers for deferred deletion/subsumption
  (`to_delete_Add`, `to_subsume_Add`).
The view table is a function whose output type is `Unit` (without proof tracking)
  or `Proof` (with proof tracking), with `:merge old`.
A view table stores "canonicalized" terms and their e-class representative.
A canonicalized term has representative terms for its children.
The last column of the view table is the representative term for the e-class.
The view tables are kept up to date during rebuilding.

```text
(rule ((= v (AddView c0 c1 new))
       (= v1 (AddView c0 c1 old))
       (!= old new)
       (= (ordering-max old new) new))
      ((set (UF_Math (ordering-max new old)) (ordering-min new old)))
        :ruleset rebuilding :name "congruence_rule" :internal-include-subsumed)
(rule ((= v2 (AddView c0 c1 c2))
       (= c2_leader (UF_Math c2))
       (!= c2 c2_leader))
      ((set (AddView c0 c1 c2_leader) ())
       (delete (AddView c0 c1 c2)))
        :ruleset rebuilding :name "rebuild_rule" :internal-include-subsumed)
```

For each constructor, we add a congruence rule and rebuild rules.
The congruence rule adds an equality to the union-find when two constructor applications
  have equal arguments.
The rebuild rules keep the view pointing to representative terms.
They are *fanned out*, one per eq-sort column (only `Add`'s `Math` output column here, since its
  `i64` children are not eq-sorts): each rule replaces a single column with its `UF_<Sort>` leader
  and re-sets the row.
Because `UF_<Sort>` has no row for a canonical term (identity-on-miss), a column already at its
  leader fails the `(!= c c_leader)` guard, so no self-loops or default lookups are needed.

```text
(function v3 () Math :no-merge :unextractable :internal-let)
(set (v3) (Add 1 2))
(set (AddView 1 2 (v3)) ())
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
(rule ((= v5 (AddView a b v4)))
      ((let v7 (Add a b))
       (set (AddView a b v7) ())
       (let v8 (Add b a))
       (set (AddView b a v8) ())
       (set (UF_Math (ordering-max v7 v8)) (ordering-min v7 v8)))
       :name "commutativity")
```

Here we have the instrumented commutativity rule.
The query uses the view table to find the canonical e-node.
The actions add to the term and view tables, then add an equality to the union-find.
We add the equality with a single `set` on `UF_<Sort>`, using the `ordering-max` and
  `ordering-min` egglog primitives to deterministically choose the parent.




```text
(check (= v7 (AddView 1 2 v8))
       (= v9 (AddView 2 1 v10))
       (= v8 v10))
```

All queries use the view tables, including check commands.
This query checks that the e-class representatives for `(Add 1 2)` and `(Add 2 1)` are equal,
  ensuring they share the same e-class.

```text
(rule ((to_delete_Add c0 c1)
       (AddView c0 c1 out))
      ((delete (AddView c0 c1 out))
       (delete (to_delete_Add c0 c1)))
        :ruleset delete_subsume_ruleset :name "delete_rule")
(rule ((to_subsume_Add c0 c1)
       (AddView c0 c1 out))
      ((subsume (AddView c0 c1 out)))
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

When proof tracking is enabled, the single self-referential union-find carries a
proof in a second value column:

```text
(function UF_Math (Math) (Math Proof) :merge (values old0 old1) :unextractable :internal-hidden)
```

If term `k` has parent `p`, `(UF_Math k)` returns `(values p proof)` where `proof`
proves `k = p` (the key on the LEFT). The native self-referential `:merge` (built in
`EGraph::build_uf_self_merge`) keeps the smaller parent on a conflict and stages the oriented
displaced edge back into `UF_Math`, composing proofs with `Trans`/`Sym`. Path compression flattens
cross-key chains via `Trans`.


Similarly, the constructor view is a functional-dependency tuple carrying a proof:

```text
(function AddView (i64 i64) (Math Proof) :merge (values old0 old1) :internal-term-constructor Add)
```

The view maps a term's canonicalized children to `(eclass, proof)`, where `proof`
proves `eclass = f(children)` (the eclass on the LEFT). Its native congruence `:merge`
(built in `EGraph::native_congruence_merge`) keeps the smaller eclass on a functional-dependency
conflict and stages the oriented union edge into `UF_Math`.


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

