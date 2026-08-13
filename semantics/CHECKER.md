# M11: the proof checker — a record, not a work queue

**M11 is parked** (`PLAN.md`, "Current priority"): the encoding is downstream of a model we trust
and we do not have one yet. This records what was learned from reading `egglog/src/proofs/` at
`3364576`, from `--proofs` runs on constructor-only programs, and from building `Encoding/Encode.lean`.

**Read [`ENCODING.md`](ENCODING.md) first.** The encoding's theorems have been deleted, and that
file is what survives them: two defects that made them vacuous — `Rebuilt` unsatisfiable at
reachable states, `CongOn` vacuous on the diagonal — and the repairs that do and do not work.
Nothing about them is repeated here. **This file is about the checker**, which was never written
and whose cost is what it scopes.

**Assume any statement about the encoder is wrong until checked.** Nine of the seventeen `execM`
refinement-chain statements were false as written, and *those* had proved M10 counterparts in
`Proofs/Interp.lean` to copy from. The `Spec/` rewrite added more of the same: porting the
`Proofs/` foundations turned up three lemmas false rather than merely stale, two of
`Encode.lean`'s own docstrings were making false claims about the encoding, and porting
`Proofs/Merge.lean` turned up three more — `Cong.mono_recorded` in its old shape, the
`ValidEnv`/`ValidSubst`/`ValidQuerySubst` family at a fixed substitution, and "a run under a
congruent environment records the run under the original". Getting the last two `sorry`s out found
one more, `Database.Out.mono_recorded`, false in every form that would have served its consumer.
Staleness and falsity look identical from the outside.

**Assume predictions about the *proofs* are wrong too.** `Database.Recorded.trans` was expected to
need congruence-closure completeness; what proved it was 315 lines of conservativity machinery
over a `Quot (Cong db)` model, and it gained two well-formedness premises on the way.

## The headline finding: the checker is not what reads the rows

A **conversion** stage sits between the database and the checker, and it is bigger than the
checker.

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

* **The checker never sees a column, a bridge, a `@RuleLink`, or a packed skeleton** — all of layer
  2 is consumed by conversion, and `Justification::Rule` carries only
  `(name, premise_proofs, substitution)`.
* **Conversion panics where you might expect the checker to reject.** 23 `panic!` + 15 `assert*` in
  `proof_format.rs`, 6 + 8 in `proof_head.rs`, against 0 `assert` and 3 `panic!` in
  `proof_checker.rs`; Trans middle terms (`:1008`), congruence child position (`:1299`), conflicting
  substitutions (`:1194`) and unknown head (`:612`) are all conversion-time. So "accepted" means
  *conversion terminates without panicking, then `check_proof` returns `Ok`* — and the first
  conjunct is where most encoder bugs die.
* **Conversion is the trusted-ish part, not the checker.** Simplification is not trusted:
  `prove_exists` checks before *and* after it (`proof_extraction.rs:154, 169`). Checking is
  separable in the other direction — `check_proof` takes a `ProofStore` and does not care how it was
  built (`proof_tests.rs` builds them by hand).

## What the checker reads

Two inputs, neither of them the e-graph. (1) `program: &[ResolvedNCommand]` =
`EGraph::proof_check_program`, the **source** program — desugared, typechecked, in proof normal
form (`lib.rs:2611`), but *before* `remove_globals` and *before* the term encoding (`lib.rs:1209`)
— read for duplicate rule names, every top-level `CoreAction` (`gather_global_actions`), the named
rule's `body`/`head`, and, for `MergeFn` only, a declaration's `:merge` body. (2) The proof
(`ProofStore.id_to_proof`) and its `TermDag`. Plus three side tables: primitive validators
(`PrimitiveValidator = fn(&mut TermDag, &[TermId]) -> Option<TermId>`, Rust closures),
`container_normalizers`, `prim_value_constructors` — the first two opaque Rust, outside the
fragment, excludable rather than modellable. **No e-graph tables, no backend, no union-find, no
extraction, no reference to the encoded program.** `termdag.rs:45` — "Terms are hashconsed, so id
equality is structural equality" — so every `TermId` comparison is structural term equality and a
Lean model can use `Term` with no dag.

`ProofStore::check_proof(proof_id, program) -> Result<Proposition, ProofCheckError>`
(`proof_checker.rs:600`) is the single entry point: it returns the proposition proved, and validity
is `Ok`. Validity is *not* spread across the other passes — `proof_normal_form.rs` is a pre-pass,
`proof_extraction.rs` the driver, `proof_simplification.rs` optional and re-checked — only across
`proof_format.rs`'s panics. The store is a DAG with a memo (`ctx.checked_proofs`) and
`check_proof_with_context` would diverge on a cycle, but conversion never builds one (ids are
pushed after their children), so in Lean this is an inductive `Proves : Proof → Proposition → Prop`
with no termination obligation.

## Node kinds and what checking each needs

Ten raw kinds collapse to eight `Justification`s. "Local" = decided from the node and its
children's propositions alone.

| raw | `Justification` | check |
| --- | --- | --- |
| `@Trans` | `Trans` | local: `left.rhs == right.lhs`, endpoints match (`:820`) |
| `@Sym` | `Sym` | local (`:853`) |
| `@Congr` | `Congr` | local: base rhs is an `App`, index in range, child lhs is that child, rebuilt term equals claim (`:873`) |
| `@Packed_<k>` | — | none; skeleton unpacked at parse time (`proof_format.rs:558`) |
| `@CongrAll` | — | none; expanded into a `Congr` chain at conversion time (`:1261`) |
| `@Fiat` | `Fiat` | **program**: `lhs == rhs && reflexive_value_term lhs`, or `(lhs,rhs)` in the propositions of top-level actions (`:627`) |
| `@Rule_<k>`, `@RuleLink` | `Rule` | **program + recursive**: rule by name; premise count == body length; each premise checked then matched against its body fact under the substitution; claim must lie in `process_actions(head, subst)` (`:646`) |
| `@MergeIdx`, `@MergeRow` | `MergeFn` | **program**: both premises reflexive; both rhs are `f(inputs…, out)` with equal heads and inputs; run `f`'s `:merge` body on the two outputs; claim must be in the result (`:709`) |
| `@ContainerNormalize` | `ContainerNormalize` | local + **oracle**: recompute the sort's normalizer and compare (`:946`) |
| `@Eval` | `Eval` | rejected standalone (`:966`); valid only as a rule-body side condition, re-evaluated in `check_side_condition` (`:988`), which may *bind* a variable into the working substitution |

The `Rule` premise check is **largely a re-derivation**: conversion computes the substitution by
unifying each body fact against its premise's proposition (`compute_rule_substitution`,
`proof_format.rs:1111`), and `check_fact_matches_proposition` then evaluates the same fact under
that substitution and compares. What is genuinely checked is literals (which `unify_expr` skips)
and primitive results (which it returns early on) — *inference from reading both sides, not from a
test*. So the real content of the `Rule` case is `check_rule_produces_equality`
(`proof_checker.rs:1272`): the claimed proposition must be among those the head derives. One line,
and the natural Lean statement.

## Size, and where the cost actually is

`proof_checker.rs`, 1301 lines = 1031 code / 185 comment / 71 blank.

| region | lines | what |
| --- | --- | --- |
| `ProofCheckErrorKind` (`:273–515`) | 243 | pure diagnostics — 19% of the file, zero semantic content |
| `check_proof_with_context` (`:599–981`) | 383 | the eight cases; ~40% error construction |
| `check_fact_matches_proposition` (`:1103`) | 103 | premise matching, 3 cases |
| `eval_expr_with_subst` free fn + subterm reflexivity (`:164`) | 95 | evaluation |
| `check_side_condition` + `eval_side` (`:983`) | 67 | containers only |
| `process_actions` (`:97`) | 66 | head/global actions → propositions |
| `eval_expr_with_subst` method (`:1207`) | 63 | a *second* evaluator, different contract |
| `assert_body_proof_normal_form` (`:1051`) | 51 | primitives/containers only |
| context, formatting, `run_merge`, `reflexive_value_term`, `check_rule_produces_equality` | ~130 | |

Strip errors, formatting and `Display` and the semantic core is **roughly 450–550 lines of Rust**.
Note the duplicated evaluator: the free `eval_expr_with_subst` returns `(TermId, propositions)`,
the `ProofStore` method returns only a `TermId` and panics on custom functions. A Lean model wants
one evaluator with the proposition set as a separate fold.

`proof_format.rs`, 1928 lines: real code `1–1492`, tests to `1928`; parsing `379–674` (~296),
conversion `757–1335` (~579), printing `1340–1464` (~125). A Lean model **can** take proofs as
already-parsed structures for the parse half and should: row → `RawProof` is a structural fold with
three special cases (`shape` table at `:450`, `@RuleLink` chain walk at `:498`, skeleton
instantiation at `:558`), and declaring `RawProof` to be what a row denotes costs almost nothing in
fidelity, since skeletons are literal strings the encoder writes.

**Cost.** Minimal subset, checker only: **small** — 5 `Justification` constructors, one inductive
`Proves`, one `process_actions` fold, roughly **150–250 lines of Lean definitions**, mostly reusing
`Spec/Term.lean` and `Spec/Eval.lean`. Whole checker: **~500–700 lines**, but `MergeFn` needs M9
and `ContainerNormalize`/`Eval` need container and primitive models the development deliberately
does not have. **Neither drives M11(1)'s cost — conversion does.** Stated over rows written into
the database, theorem (1) must go through `convert_raw_proof` (~579 lines) and `proof_head.rs`'s
`Firing`/`HeadPlan` replay (~700 of its 1116 lines), the worst part being `Firing`'s cross-row
state: one firing's rows share a memoized walk that is carried, rewound when the bridge supply runs
dry, and kept only if it "reaches" further (`proof_format.rs:918–963`, `proof_head.rs:551–711`) —
order-dependent, stateful, and the single least pleasant thing to formalize in this subtree.

**So split M11(1) at the layer boundary `proof_encoding.md` already draws.** (1a) *The proof the
encoding means is valid* — define `encodeProof` as layer 1, the four `ProofAlgebra` operations
(`canonicalize`, `reflexive`, `connect`, `guest_view`, `proof_head.rs:937–1027`) applied to a head
walk, and prove `Checks (encodeProof …)`; that is the interesting theorem, it needs only the
5-constructor checker, and no column, bridge, link or skeleton machinery appears in it. (1b) *Layer
2 recovers layer 1* — the column arithmetic; defer it, or leave it to the Rust tests that already
pin exactly this pair, `walking_a_rule_head_states_every_proposition_it_concludes` and
`every_column_an_encoded_head_writes_is_one_the_walk_produces` (`proof_tests.rs:79`, `:183`).

## The minimal subset, measured

`--proofs --mode desugar` on a constructor-only program (one sort, no `:merge`, no containers, no
primitives, no delete/subsume) emits exactly `@Fiat`, `@Rule_<k>`, `@RuleLink`, `@Packed_<k>`
(k = 2, 3, 4), and **one** bare `@Trans` — from the path-compression rule, the only site that
writes an unpacked node. Not written: `@Sym`, `@Congr` (they occur only inside packed skeletons),
`@CongrAll`, `@ContainerNormalize`, `@Eval`, `@MergeIdx`, `@MergeRow`. Through the checker
(`--proofs --proof-testing`, which runs `check_proof` twice per proof) the proofs use exactly five
`Justification`s: **`Fiat`, `Rule`, `Trans`, `Sym`, `Congr`**. `MergeFn`, `ContainerNormalize` and
`Eval` never appear — consistent with the checked-in snapshots (66 in `egglog/tests/snapshots`,
more in `egglog-experimental`), where `Merge` appears in 2 files, both merge/container tests, and
`Eval`/`ContainerNormalize` only in container tests.

`Trans`/`Sym`/`Congr` are local and one-to-one with `Cong`'s constructors as `PLAN.md` assumes;
`Fiat` needs `process_actions` over top-level actions, `Rule` needs it over a rule head under a
substitution plus fact matching. Everything else — `MergeFn`, `ContainerNormalize`, `Eval`,
`check_side_condition`, `assert_body_proof_normal_form`, `run_merge`, `reflexive_value_term`, both
container helpers — is out, about 300 of the ~500 semantic lines. The one shared piece,
`process_actions` + `eval_expr_with_subst` restricted to `Let`, `Union`, `Expr` over constructors
and variables, is `Spec/Eval.lean`'s `evalAction` with a different accumulator: `Union` contributes
the pair both ways, and every evaluated call contributes reflexive equalities for the term *and all
its subterms* (`add_subterm_reflexive_equalities`, `:226`), for which M1's `Term.subterms` is
already right. Two facts make (1a) cheaper than `PLAN.md` assumes: the checker reads the *source*
program, so a Lean `Checks` would be a predicate over the syntax `Spec/` already models and theorem (2) (checker
soundness → `Cong`) is close to a restatement of `Cong.le`; and the fragment needs only 5 of 8
justification kinds, all with direct counterparts in `Cong`. What `PLAN.md` under-weights is that
the rows are not the proofs.

## `Encoding/Encode.lean`

`encode : Program → Program` for constructors only, `Program.EncodeDomain` stating that fragment.
Per source constructor `f` it emits `@fView` (`children ↦ eclass`, the FD) and `@fTerm`
(write-only), plus one `@UF` per sort; the `:merge` body of `@UF` and of every view is egglog's
own, "keep the smaller side and `set` the larger's `@UF` edge to it", so a view collision *is*
congruence resolution and no congruence rule is emitted. Rendering it on `proof_encoding.md`'s
running example reproduces the snapshot's shape modulo the deviations below.

### What the Rust says that `proof_encoding.md` does not

* **`@rebuilding_cleanup` is a declared, commented, scheduled ruleset with no rule ever assigned to
  it.** `proof_encoding.md`:220 declares it and the schedule runs it every round, commented "drop
  rows merged away", but the only four references in the repo are the field, its `fresh`, the
  `(ruleset …)` header and the schedule. Stale view rows are removed by the `(delete …)` inside the
  `@rebuilding` rules themselves. Anyone modelling from the markdown would invent a rule family
  that does not exist.
* **One rebuild rule per eq-*sort*, not per column.** Its body joins a `@UF` delta against the
  declared index and its action re-canonicalizes every column at once through `@UF_<Sort>_canon`,
  identity-on-miss. Both are inexpressible here (no index, and "no row" is not a matchable fact),
  so the encoding emits one rule per column instead.
* **`get-fresh!` mints three kinds of id** — term ids, `@Proof` node ids, `@Ast` ids — not just
  e-class ids. Its signature is `(get-fresh! "Sort") → Sort`, the sort a *string* literal, so a
  generated `@`-name never gets mangled on re-parse.
* **Proof nodes are relations, not constructors** (`… → Unit :no-merge`, minted id as the last
  input column), deliberately so two structurally equal proofs are never merged.
* The markdown's lowered `rewrite` omits the guest's trailing `(let guest target)`, which
  `instrument_actions` always emits; `plan_construct_into` silently drops `(union x x)`, which the
  markdown's "a union of two matched variables keeps the plain edge" reads against; and
  `@Rule_<k>` is declared once ahead of the whole batch, not "just before the commands needing it".

Everything load-bearing checked out exactly: the `@UF_<Sort>` and `@<C>View` declarations and their
shared `:merge`, the path-compression rule, the `check` expansion, and the term-building sequence.

### Deviations

Each is recorded at its definition in `Encoding/Encode.lean`; the reasons in one line each.

* **Fresh ids are structural.** `PLAN.md`'s "add an id supply to the target configuration" needs
  frozen files, so the id minted for `f` over canonical children `cs` is the term `.app f cs` — the
  skolem encoding of `get-fresh!`, which makes source terms and target ids one type and lets the
  simulation theorem compare them with no correspondence relation. It costs row counts: egglog
  mints an id per construction *site* and lets the view dedup them, where a second construction of
  one shape here reuses the id.
* **No `!=`, no rulesets, no construct-into, no `set-if-empty`.** The first two only add no-op
  firings, but a ruleset-less `Cmd.run` is why `run-schedule` becomes the predicate `Rebuilt` and
  hence why `ENCODING.md`'s first finding bites. The last two only move row counts.
* **The one-value-column blocker is fixed**: `Action.set` takes one expression per value column
  (egglog's core `GenericCoreAction::Set(f, args, values)`) and `Pattern.values` reads a non-first
  column (`MERGE.md`, "Multi-column outputs"). `tuple-two`, `tuple-merge`, `tuple-read`,
  `tuple-read-congr` exercise it and agree — but `(print-size)` counts key classes and is blind to
  value columns, so a row-count comparison validates the declaration, the `set` and that the
  destructure *fires*, not the merged values; `tuple-read` reaches the values by guarding on
  literal columns so the firing shows in its head constructor's count. So when a proof-column
  theorem is restated, the language will not be what stops it — the encoder not emitting the column
  will.

### Open design questions

Parked with the milestone; each is argued at its statement in `Encoding/Encode.lean`, which is the
only Lean the encoding still has. Whether `ViewRepr` should be the source-to-target correspondence
(chosen because it is observable in the target alone); whether `SameClass` should be universal
rather than existential (a stronger claim, about the rebuild having converged, and only meaningful
because nothing is ever removed); and whether `encode` should emit `@fTerm` at all (nothing reads
it, and with structural ids its id column is redundant with its key).

Read `ENCODING.md`, "What survives", before restating any of them: congruence on the target is
trivial, which is what makes the `Recorded` transports usable there and is stated exactly only in
that file.
