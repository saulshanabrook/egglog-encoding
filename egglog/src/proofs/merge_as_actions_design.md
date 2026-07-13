# Design: `:merge` as an action block (retire the `MergeFn` DSL)

Status: proposal. Not implemented. Intended as a follow-up **after** the term/proof
encoding PR lands on the current `MergeFn` implementation.

## Problem

The term/proof encoding needs merges that *perform actions* during an FD conflict —
stage a union edge into the per-sort union-find and compose a `Trans`/`Sym` proof — not
merely pick `old` or `new`. The encoding PR added a bespoke merge DSL in `egglog-bridge`:

```
MergeFn::{ Old, New, OldCol, NewCol, Const, Primitive, UnionId, AssertEq,  // pick a value
           Columns,                                                        // per-column
           Seq, TableInsert, Construct, IfEq }                             // perform actions
```

The `Seq`/`TableInsert`/`Construct`/`IfEq` group is effectively a *second, weaker action
language* living in the bridge. It has its own ad-hoc lowering (`translate_expr_to_mergefn`)
and no principled type/context checking (e.g. `TupleMergeNotValues`, `TupleMergeArity` are
bespoke error paths). Meanwhile egglog already has a real action IR (`GenericAction`), a
constraint-based typechecker, a typed-capability/context system (`Context::Write`,
`PurePrim`/`ReadPrim`/`WritePrim`), and action lowering used by rules.

**Goal:** express `:merge` with the existing rule action IR — uniform language, principled
typechecking — and delete the bespoke DSL, while keeping the backend surface small and
*general*.

## Key insight

`IfEq` in the encoding does exactly two jobs. Both can be removed:

- **Role 1 — the guard:** "only stage a union when the eclass columns differ." This is the
  *only* genuinely conditional decision in the merge body, and it is precisely "did the
  identity column change?". Move it into the table's conflict detection via **identity vs
  payload columns** (below). Then the merge body stages *unconditionally*.
- **Role 2 — proof orientation:** "which input proof matches the larger eclass?" This is a
  *pure* function of `(old_ec, old_pf, new_ec, new_pf)` — no table access — so it becomes an
  ordinary **pure primitive**, not a control-flow node.

With both gone, the merge body is a straight-line action block terminated by a value, and
`If` is not needed in the IR at all.

## Design

### 1. Identity vs payload value columns (backend)

Split a function's value columns into:
- **identity** columns: participate in FD-conflict detection;
- **payload** columns: carried alongside, not identifying.

Conflict fires iff an *identity* column differs. A payload-only difference keeps the existing
row (no merge invocation, and the row is not marked dirty — strictly less churn than today's
"fire the merge, `IfEq` keeps old"). Precedent already exists: the subsume and timestamp
columns are non-identity payload.

For the encoding, `@UF : (S) -> (S, Proof)` and the FD view `(children) -> (eclass, proof)`
declare **col 0 (eclass/parent) identity, col 1 (proof) payload**.

Backend change: `FunctionConfig` gains an identity-column count/mask; `SortedWritesTable`'s
conflict path compares only identity columns. This is the one *added* backend capability, and
it is general (any "carry a witness/derivation next to the real value" use).

### 2. `:merge` as an action block ending in an expression (egglog IR)

A merge body becomes `{ action* ; result_expr }` with `old`/`new` (and `old0`/`new0`/… for
tuple output) bound. `result_expr` produces the merged value(s) (`(values e0 e1)` for tuple).
Actions are the existing set (`Set`/`Union`/constructor application/`Let`), restricted to
`Context::Write` (no queries, no `panic`) — the capability system enforces the restriction,
which is the "principled typechecking" payoff.

The one genuine IR addition is a **value-producing action block** (a `{ stmts; expr }` form;
actions today are effect-only). Existing `:merge <expr>` is the degenerate case (no actions,
just the result), so `:merge new`, `:merge (max old new)`, `:merge (values …)` keep working.

### 3. Pure orientation primitives (proof layer)

Register pure primitives that, given the two `(eclass, proof)` pairs, return the proof/eclass
of the smaller/larger endpoint (same insertion-order comparison as `ordering-min`/`-max`).
Pure ⇒ no dependency obligation ⇒ no `If`. These live in the proof-encoding layer.

### 4. Lowering & dependency tracking

`SortedWritesTable` already takes a merge **closure** (`MergeFn::to_callback` compiles to
`Box<dyn Fn(state, cur, new, out)>`). So the egglog layer compiles the typed merge action
block directly to that closure and the `MergeFn` enum is deleted. Read/write dependencies are
**derived** by walking the compiled action block (`set` targets → write deps; lookups /
constructor reads → read deps) and fed to the same strata ordering
(`DependencyGraph`/`has_read_deps`) that exists today — same obligation, better located than
`fill_deps`. Self-referential staging (`set` into the table's own id) still relies on the
core-relations self-write buffer pre-seed; that is fundamental to the single self-referential
UF and unchanged by this proposal.

## Before / after (proof-mode `@UF` self-merge)

Today (nested Rust `MergeFn` builders, `build_uf_self_merge`):

```
col0 = IfEq { a: OldCol(0), b: NewCol(0), then: OldCol(0),
              els: Seq[ TableInsert(@UF, [max_ec, min_ec,
                          Construct(Trans, [Construct(Sym, [max_pf]), min_pf])]),
                        min_ec ] }
col1 = IfEq { a: OldCol(0), b: NewCol(0), then: OldCol(1), els: min_pf }
```

After (emitted egglog action block; col0 identity so no guard; `pf-of-*` are pure primitives):

```text
:merge
  (set (@UF (ordering-max old0 new0))
       (values (ordering-min old0 new0)
               (Trans (Sym (pf-of-max old0 old1 new0 new1))
                      (pf-of-min old0 old1 new0 new1))))
  (values (ordering-min old0 new0)
          (pf-of-min old0 old1 new0 new1))
```

## Removed / kept

Removed: `MergeFn::{Seq, TableInsert, Construct, IfEq}` + the `ResolvedMergeFn` machinery;
`translate_expr_to_mergefn` and the bespoke merge typecheck errors; the hand-written
`build_uf_self_merge` / `native_congruence_merge` (become emitted action blocks).

Kept: the `Columns` idea (subsumed — per-column results are just the result `(values …)`);
the core-relations self-write pre-seed; `ordering-min`/`-max` (plus the new pure orientation
primitives).

## Risks / open questions

1. **Perf.** The merge runs in the flush inner loop, once per FD conflict — the PR's headline
   path (≈1.8× on proofs). The compiled action-block closure must be as tight as today's
   `MergeFn::run`. Bench against current on `tests/math-microbenchmark.egg` proofs; this is the
   acceptance gate.
2. **Backend subset-identity conflicts.** Confirm `SortedWritesTable`'s conflict/merge path can
   compare a column subset cleanly (keep-old on payload-only diff).
3. **Semantic equivalence.** Prove col-0-identity is exactly today's `IfEq(OldCol0 == NewCol0)`
   guard for *both* the view merge and the `@UF` self-merge before trusting it.
4. **Value-producing action block.** The IR addition and its typechecking interaction.
5. **Merge action subset.** Enforce "no query / no panic, `Context::Write`" via the capability
   system.
6. **Back-compat.** Existing `:merge <expr>` must keep parsing as a result-only block.

## Sequencing

1. Identity columns in the backend (+ test).
2. Value-producing action-block IR + typecheck.
3. Compile merge block → closure + derive deps.
4. Port the encoding's merges + add the pure orientation primitives.
5. Delete the `MergeFn` action DSL.
6. Bench proofs; gate on no regression.
