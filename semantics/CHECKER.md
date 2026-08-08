# Modelling `proof_checker.rs` in Lean — scoping note

Reconnaissance for M11 theorem (1), "every `@Proof` row the encoding writes is accepted by
the checker". Read of `egglog/src/proofs/` at `3364576`, plus empirical runs of a
constructor-only program through `--proofs`.

## The headline finding: the checker is not what reads the rows

There is a **conversion** stage between the database and the checker, and it is bigger than
the checker.

```
@Proof rows  ──extract──▶  proof term (TermDag)
                             │  RawProofStore::from_extracted        proof_format.rs:381
                             ▼  parse: shapes, @RuleLink chains, @Packed_k skeletons
                          RawProof (10 variants)                     proof_format.rs:154
                             │  ProofStore::from_raw / convert_raw_proof  :757 / :852
                             ▼  replay the rule head, compute substitutions, run merges
                          Proof = Proposition + Justification (8 variants)  :289 / :303
                             │  remove_globals                proof_simplification.rs:16
                             ▼
                          check_proof                             proof_checker.rs:600
                             │  simplify, then check_proof again  proof_extraction.rs:166
```

Consequences that bear directly on the plan:

- **The checker never sees a column, a bridge, a `@RuleLink`, or a packed skeleton.** All of
  layer 2 is consumed by conversion. `Justification::Rule` carries only `(name,
  premise_proofs, substitution)`.
- **Conversion panics where you might expect the checker to reject.** 23 `panic!` + 15
  `assert*` in `proof_format.rs`, 6 + 8 in `proof_head.rs`, against 0 `assert` and 3 `panic!`
  in `proof_checker.rs`. Trans middle terms (`proof_format.rs:1008`), congruence child
  position (`:1299`), conflicting substitutions (`:1194`), unknown head (`:612`) are all
  conversion-time. So "accepted" really means *conversion terminates without panicking, and
  then `check_proof` returns `Ok`* — and the first conjunct is where most encoder bugs die.
- **Conversion is the trusted-ish part, not the checker.** Simplification is not trusted:
  `prove_exists` checks before *and* after it (`proof_extraction.rs:154, 169`).
- Checking is separable from conversion in the other direction: `check_proof` takes a
  `ProofStore` and does not care how it was built (`proof_tests.rs` builds them by hand).

## What the checker reads (Q2)

Only two inputs, neither of them the e-graph:

1. `program: &[ResolvedNCommand]` = `EGraph::proof_check_program`, which is the **source**
   program — desugared, typechecked, put in proof normal form (`lib.rs:2611`), but *before*
   `remove_globals` and *before* the term encoding (`lib.rs:1209`). Read for: duplicate rule
   names; every top-level `CoreAction` (`gather_global_actions`); the named rule's `body` and
   `head`; and, for `MergeFn` only, a `Function` declaration's `:merge` body.
2. The proof itself (`ProofStore.id_to_proof`) and its `TermDag`.

Plus three side tables: primitive validators (`PrimitiveValidator = fn(&mut TermDag,
&[TermId]) -> Option<TermId>`, Rust closures), `container_normalizers`, and
`prim_value_constructors`.

**No e-graph tables, no backend, no union-find, no extraction, and no reference to the
encoded program.** Extraction (`proof_extractor.rs`) happens before, to get the proof term
out; it is not part of checking. Also note `termdag.rs:45`: "Terms are hashconsed, so id
equality is structural equality" — so every `TermId` comparison in the checker is structural
term equality, and a Lean model can use `Term` directly with no dag.

Gaps against the current Lean development: primitive validators and container normalizers are
opaque Rust; both are outside the fragment and can be excluded rather than modelled.

## Node kinds and what checking each needs (Q1)

Ten raw kinds collapse to eight `Justification`s. "Local" = decided from the node and its
children's propositions alone.

| raw | `Justification` | check |
| --- | --- | --- |
| `@Trans` | `Trans` | local: `left.rhs == right.lhs`, endpoints match (`:820`) |
| `@Sym` | `Sym` | local (`:853`) |
| `@Congr` | `Congr` | local: base rhs is an `App`, index in range, child lhs is that child, rebuilt term equals claim (`:873`) |
| `@Packed_<k>` | — | none; the skeleton is unpacked at parse time (`proof_format.rs:558`) |
| `@CongrAll` | — | none; expanded into a `Congr` chain at conversion time (`:1261`) |
| `@Fiat` | `Fiat` | **program**: `lhs == rhs && reflexive_value_term lhs`, or `(lhs,rhs)` in the propositions of the program's top-level actions (`:627`) |
| `@Rule_<k>`, `@RuleLink` | `Rule` | **program + recursive**: rule looked up by name; premise count == body length; each premise checked, then matched against its body fact under the substitution; finally the claim must lie in `process_actions(head, subst)` (`:646`) |
| `@MergeIdx`, `@MergeRow` | `MergeFn` | **program**: both premises reflexive; both rhs are `f(inputs…, out)` with equal heads and inputs; run `f`'s `:merge` body on the two outputs; claim must be in the result (`:709`) |
| `@ContainerNormalize` | `ContainerNormalize` | local + **oracle**: recompute the sort's normalizer and compare (`:946`) |
| `@Eval` | `Eval` | rejected standalone (`:966`); valid only as a rule-body side condition, re-evaluated in `check_side_condition` (`:988`), which may *bind* a variable into the working substitution |

Two remarks worth having:

- The `Rule` premise check is **largely a re-derivation**. Conversion computes the
  substitution by unifying each body fact against its premise's proposition
  (`compute_rule_substitution`, `proof_format.rs:1111`); `check_fact_matches_proposition`
  then evaluates the same fact under that substitution and compares. The residue that is
  genuinely checked is literals (which `unify_expr` skips) and primitive results (which it
  returns early on). *Inference from reading both sides, not from a test.*
- So the real content of the `Rule` case is `check_rule_produces_equality`
  (`proof_checker.rs:1272`): the claimed proposition must be among those the head derives.
  That is a one-line contract and is the natural Lean statement.

## Line split (Q3)

`proof_checker.rs`, 1301 lines = 1031 code / 185 comment / 71 blank.

| region | lines | what |
| --- | --- | --- |
| `ProofCheckErrorKind` (`:273–515`) | 243 | pure diagnostics — 19% of the file, zero semantic content |
| `check_proof_with_context` (`:599–981`) | 383 | the eight cases; roughly 40% of it is error construction |
| `check_fact_matches_proposition` (`:1103`) | 103 | premise matching, 3 cases |
| `eval_expr_with_subst` free fn + subterm reflexivity (`:164`) | 95 | evaluation |
| `check_side_condition` + `eval_side` (`:983`) | 67 | containers only |
| `process_actions` (`:97`) | 66 | head/global actions → propositions |
| `eval_expr_with_subst` method (`:1207`) | 63 | a *second* evaluator, different contract |
| `assert_body_proof_normal_form` (`:1051`) | 51 | primitives/containers only |
| context + formatting + `run_merge` + `reflexive_value_term` + `check_rule_produces_equality` | ~130 | |

Strip errors, formatting and `Display` and the semantic core is **roughly 450–550 lines of
Rust**. Note the duplicated evaluator: the free `eval_expr_with_subst` returns
`(TermId, propositions)`, the `ProofStore` method returns only a `TermId` and panics on custom
functions. A Lean model wants one evaluator, with the proposition set as a separate fold.

`proof_format.rs`, 1928 lines: real code `1–1492`, tests `1493–1928` (436). Of the 1492,
parsing is `379–674` (~296), conversion is `757–1335` (~579), printing `1340–1464` (~125),
declarations and docs the rest.

**Can a Lean model take proofs as already-parsed structures?** For the parse half, yes, and it
should. The row → `RawProof` reading is a structural fold with three special cases (the
`shape` table at `:450`, the `@RuleLink` chain walk at `:498`, and skeleton instantiation at
`:558`); defining `RawProof` directly and *declaring* it to be what a row denotes costs almost
nothing in fidelity, since skeletons are literal strings the encoder writes. The conversion
half cannot be skipped if the theorem is stated over rows — see below.

## Minimal subset for the constructor fragment (Q4)

Measured, not guessed. `--proofs --mode desugar` on a constructor-only program (one sort, no
`:merge`, no containers, no primitives, no delete/subsume) emits exactly these proof rows:

- `@Fiat`, `@Rule_<k>`, `@RuleLink`, `@Packed_<k>` (k = 2, 3, 4), and **one** bare `@Trans` —
  from the path-compression rule, the only site that writes an unpacked node.
- Not written: `@Sym`, `@Congr` (they occur only inside packed skeletons), `@CongrAll`,
  `@ContainerNormalize`, `@Eval`, `@MergeIdx`, `@MergeRow`.

Running the same programs through the checker (`--proofs --proof-testing`, which runs
`check_proof` twice per proof) yields proofs over exactly five `Justification`s: **`Fiat`,
`Rule`, `Trans`, `Sym`, `Congr`**. `MergeFn`, `ContainerNormalize` and `Eval` never appear —
consistent with the checked-in proof snapshots (66 in `egglog/tests/snapshots`, more in
`egglog-experimental`), where `Merge` appears in 2 files, both merge/container tests, and
`Eval`/`ContainerNormalize` only in container tests.

So the minimal checker subset is:

- `Trans`, `Sym`, `Congr` — local, and one-to-one with `Cong`'s constructors as PLAN.md
  assumes.
- `Fiat` — needs `process_actions` over the program's top-level actions.
- `Rule` — needs `process_actions` over a rule head under a substitution, plus fact matching.

Everything else — `MergeFn`, `ContainerNormalize`, `Eval`, `check_side_condition`,
`assert_body_proof_normal_form`, `run_merge`, `reflexive_value_term`, both container helpers —
is out. That is about 300 of the ~500 semantic lines gone.

The one shared piece is `process_actions` + `eval_expr_with_subst`, restricted to `Let`,
`Union`, `Expr` over constructors and variables. That is `Spec/Eval.lean`'s `evalAction`
with a different accumulator: `Union` contributes the pair both ways, every evaluated call
contributes reflexive equalities for the term *and all its subterms*
(`add_subterm_reflexive_equalities`, `:226`) — for which `Term.subterms` from M1 is already
the right function.

## Where "valid" lives (Q5)

`ProofStore::check_proof(proof_id, program) -> Result<Proposition, ProofCheckError>`
(`proof_checker.rs:600`) is the single entry point with a clear contract: it returns the
proposition the proof proves, and validity is `Ok`. Validity is *not* spread across the other
passes — `proof_normal_form.rs` is a pre-pass on the program (so the checker may assume its
shape, and `assert_body_proof_normal_form` re-asserts it), `proof_extraction.rs` is the
driver, `proof_simplification.rs` is optional and re-checked. It is spread across
`proof_format.rs`'s panics, as above.

One structural detail for a Lean model: the proof store is a DAG with a memo
(`ctx.checked_proofs`), and `check_proof_with_context` would diverge on a cycle. Conversion
never builds one (ids are pushed after their children), so in Lean this is an inductive
`Proves : Proof → Proposition → Prop`, with no termination obligation.

## Cost (Q6)

**Minimal subset, checker only: small.** 5 `Justification` constructors, one inductive
`Proves`, and one `process_actions` fold. Roughly **150–250 lines of Lean definitions**, most
of it reusing `Spec/Term.lean` and `Spec/Eval.lean`. This is not the risk.

**Whole checker: ~500–700 lines of definitions**, but `MergeFn` needs M9, and
`ContainerNormalize`/`Eval` need container and primitive models the development deliberately
does not have. Those are the cost, not the checker code.

**What actually drives M11(1)'s cost is conversion, not the checker.** If theorem (1) is
stated over rows written into the database, it must go through `convert_raw_proof` (~579
lines) and `proof_head.rs`'s `Firing`/`HeadPlan` replay (~700 of its 1116 lines). The worst
part is `Firing`'s cross-row state: one firing's rows share a memoized walk that is carried,
rewound when the bridge supply runs dry, and kept only if it "reaches" further
(`proof_format.rs:918–963`, `proof_head.rs:551–711`). That is order-dependent, stateful, and
the single least pleasant thing to formalize in this subtree.

### Recommendation

Split M11(1) at the layer boundary `proof_encoding.md` already draws:

- **(1a) The proof the encoding *means* is valid.** Define `encodeProof` in Lean as layer 1 —
  the four `ProofAlgebra` operations (`canonicalize`, `reflexive`, `connect`, `guest_view`,
  `proof_head.rs:937–1027`) applied to a head walk — and prove `Checks (encodeProof …)`. This
  is the interesting theorem, it needs only the 5-constructor checker, and none of the column,
  bridge, link or skeleton machinery appears in it.
- **(1b) Layer 2 recovers layer 1.** The column arithmetic. Defer it, or leave it to the Rust
  tests that already pin exactly this pair of properties:
  `walking_a_rule_head_states_every_proposition_it_concludes` and
  `every_column_an_encoded_head_writes_is_one_the_walk_produces` (`proof_tests.rs:79`, `:183`).

Two facts make (1a) cheaper than PLAN.md assumes. The checker reads the *source* program, not
the encoded one — so `Checks` is a predicate over the same syntax `Spec/` already models, and
theorem (2) (checker soundness → `Cong`) is close to a restatement of `Cong.le`. And the
constructor fragment needs only 5 of 8 justification kinds, all five of which have direct
counterparts in `Cong`. The thing PLAN.md under-weights is that the rows are not the proofs:
conversion stands between them, and it is where the encoder's real invariants are enforced.

# M11 status — `encode` and the theorem statements

`Spec/Encode.lean` (definitions) and `Proofs/Encode.lean` (statements, all `sorry`) are in.
Read of `egglog/src/proofs/` plus the `insta` snapshots of the emitted program for exactly this
fragment (`proof_tests.rs:1232`, `…doc_example_add_eqsort_children.snap`), which are
proofs-off and so are the encoding this models.

## What was built

`encode : Program → Program` for constructors only — no containers, no delete/subsume, no
schedules — with `Program.EncodeDomain` stating that fragment. Per source constructor `f` it
emits `@fView` (`children ↦ eclass`, the FD) and `@fTerm` (the write-only term relation), plus
one `@UF` for the sort; the `:merge` body of `@UF` and of every view is the same one egglog
uses, "keep the smaller side and `set` the larger's `@UF` edge to it", so a view collision *is*
congruence resolution and no congruence rule is emitted. Maintenance is path compression plus
per-column view canonicalization. Rendering `encode` on the running example of
`proof_encoding.md` reproduces the snapshot's shape modulo the deviations below.

The statements: `encode_sound` / `encode_complete` / `encode_simulation` (theorem 3),
`encode_rows_sound` and `encode_leader_sound` (theorem 2), `encode_proof_rows_check` and its
view sibling (theorem 1), plus `encode_not_allConstructors`, `encode_eqs_empty`,
`encode_mcong_eq` and `congOn_iff_cong`.

## What the Rust says that the markdown does not

- **`@rebuilding_cleanup` is an empty ruleset.** `proof_encoding.md`:220 declares it and the
  schedule runs it every round, with the comment "drop rows merged away". No rule is ever
  assigned to it — the only four references in the repo are the field, its `fresh`, the
  `(ruleset …)` header and the schedule. Stale view rows are removed by the `(delete …)` inside
  the `@rebuilding` rules themselves. Anyone modelling from the markdown would invent a rule
  family that does not exist.
- **One rebuild rule per eq-*sort*, not per column.** Its body joins a `@UF` delta against the
  declared index and its action re-canonicalizes every column at once through
  `@UF_<Sort>_canon`, which is identity-on-miss. Both are inexpressible here (no index, and "no
  row" is not a matchable fact), so the encoding emits one rule per column instead.
- **`get-fresh!` mints three kinds of id**, not just e-class ids: term ids, `@Proof` node ids,
  and `@Ast` ids. Its signature is `(get-fresh! "Sort") → Sort` — the sort is a *string*
  literal, so a generated `@`-name never gets mangled on re-parse.
- **Proof nodes are relations, not constructors** (`… → Unit :no-merge`, with the minted id as
  the last input column), deliberately so two structurally equal proofs are never merged.
- The markdown's lowered `rewrite` omits the guest's trailing `(let guest target)`, which
  `instrument_actions` always emits; `plan_construct_into` also silently drops `(union x x)`,
  which the markdown's "a union of two matched variables keeps the plain edge" reads against;
  `@Rule_<k>` is declared once ahead of the whole batch, not "just before the commands needing
  it" as the markdown says of both families.

Everything load-bearing checked out exactly: the `@UF_<Sort>` and `@<C>View` declarations and
their shared `:merge`, the path-compression rule, the `check` expansion, and the term-building
sequence.

## Deviations, and the one blocker

**The one-value-column blocker is fixed.** It was: `ActionStep.set` wrote `db.addRow f ts [v]`
and `MEval.lookup` read `db.Out f ts [v]`, so a multi-column row could be *created* only by a
merge and never written or read, and egglog's `@UF` / `@<C>View` — `(S) → (S, P)` and
`(children) → (out, P)`, proof at value column 1 — were inexpressible. What was done:

1. `Spec/Syntax.lean`: `| set : FnName → List Expr → List Expr → Action`, one expression per
   value column. This matches egglog's *core* action, `GenericCoreAction::Set(f, args, values)`,
   which is already per column; the surface `(values …)` is `Tests/Egg.lean`'s job.
2. `Spec/Merge.lean`: `ActionStep.set` reads the outputs with `Expr.MEvalList` and writes
   `db.addRow f ts vs`. `Spec/Eval.lean`, `Impl/Interp.lean` and `Impl/Merge.lean` follow.
3. Reading a column other than the first is **`Pattern.values`**, egglog's tuple destructure
   `(= (values v…) (f a…))`. Of the two options this document offered, that is the one egglog
   actually has: `MEval.lookup` generalized with an index is *not* — a tuple-output function
   cannot be evaluated as an expression at all (`eval_resolved_expr` panics on `values`,
   `exec_state.rs:293`) and cannot be extracted, and the error message for the latter says
   "Read its columns in a rule with `(= (values ...) ({0} ...))` instead"
   (`typechecking.rs:1639`). egglog recognizes the shape inside an ordinary `=` fact, in either
   argument order, and lowers it to the atom `f(a…, v…)` (`match_tuple_destructure`,
   `ast/mod.rs:1770`). `MEval.lookup` therefore stays single-column, which is faithful.
4. `Lit` still wants `.unit` and `.str`, as `MERGE.md` notes — that is what the proof column's
   `Unit` and `@Rule_<k>`'s rule name need, and it is now the remaining gap along with the
   encoder itself emitting the column. `encode_proof_rows_check` is still vacuous, but for an
   encoder reason rather than a language one.

Four differential cases exercise the widening end to end (`tuple-two`, `tuple-merge`,
`tuple-read`, `tuple-read-congr`), and they agree with egglog. Note what the oracle can see:
`(print-size)` counts key classes and is blind to value columns, so a row-count comparison
validates the declaration, the `set` and that the destructure *fires*, not the merged values.
`tuple-read` gets at the values anyway by guarding on literal columns, so whether the rule
fired shows up in its head constructor's count.

Three further deviations, all recorded in the file:

- **Fresh ids are structural.** PLAN.md's "add an id supply to the target configuration" is not
  implementable without touching frozen files — `Database` is fixed and no `Expr` can depend on
  a counter — so the id minted for `f` over canonical children `cs` is the term `.app f cs`.
  This is the standard skolem encoding of `get-fresh!`, and it makes source terms and target
  ids one type, which is what lets the simulation theorem compare them without a
  correspondence relation. It costs the row counts: egglog mints an id per construction *site*
  and lets the view dedup them, where a second construction of one shape here reuses the id.
  The remaining supply, over generated variable names `@v0`, `@v1`, …, is threaded at encode
  time.
- **No `!=` and no rulesets.** The guards on path compression and rebuild are dropped, which
  only adds no-op firings. `Cmd.run` carries no ruleset, so `proof_encoding.md`'s
  `run-schedule` becomes the predicate `Rebuilt` on the final state, which the completeness
  half of simulation takes as a hypothesis. A `Cmd.run` with a ruleset argument is what would
  let the schedule be encoded instead.
- **No construct-into and no `set-if-empty`.** Construct-into is an optimization whose stated
  effect is "exactly the edge the explicit union would have produced", so the plain union edge
  is emitted. `set-if-empty` has no counterpart, so the encoding `set`s and reads the view
  back; the difference is one extra union between the minted id and the existing e-class, which
  are equal, so only row counts move.

## Open design questions

1. **Should `ViewRepr` be the source-to-target correspondence?** The simulation theorem reads a
   source term out of the target by one view lookup per subterm — which is what `check`
   compiles to — and then compares `@UF` leaders. The alternative is a relation built by
   induction over the encoding's own construction. `ViewRepr` was chosen because it is
   observable in the target alone.
2. **`CongOn` versus `Cong` in the row-soundness statement.** The rebuild re-keys a view row to
   its children's leaders, so the target holds rows about applications the source never built
   (`@AddView [1,1] ↦ Add[1,2]` after `(Add 1 2)` and `(union 1 2)`). `Cong` is restricted to
   `db.terms` at `refl` and `congr` and cannot mention them, so row soundness concludes
   `CongOn db a b := Cong ((db.addTerm a).addTerm b) a b` — the form `ValidSubst` already uses.
   `congOn_iff_cong` converts on terms the source holds. If this is wrong, it is wrong in the
   direction of the *invariant* the induction will carry, so it is the statement to review
   first.
3. **Existential or universal reads.** `SameClass` says *some* pair of view readings lands on a
   common leader. Because rows are never removed, a stale reading is still a true one, so the
   universal form would be a different (and stronger) claim about the rebuild having converged.
4. **Is `Rebuilt` satisfiable often enough?** Maintenance rules fire only inside `Cmd.run`, so a
   program with no `run` after its last `union` never reaches a rebuilt state and the
   completeness half is vacuous for it. Appending `(run)`s to *both* programs fixes it; adding
   them to the target alone would break soundness, since the extra rounds also fire the encoded
   source rules.
5. **Should `encode` emit the term relation at all?** Nothing in the model reads `@fTerm`, and
   with structural ids its id column is redundant with its key. It is emitted for fidelity and
   because proof rows will refer to it.
6. **`MCong` on the target is claimed trivial** (`encode_mcong_eq`). It rests on the source
   constructor names staying undeclared — they must be `.union` to be buildable by
   `MEval.ctor` — so their rows are exactly the constructor rows their terms induce and `fd`
   only re-derives reflexivity. That is load-bearing and slightly fragile: a source `set`, or a
   declaration surviving into the target, would break it. `EncodeDomain` rules both out.
