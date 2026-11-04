# Find a nontrivial EggCC payoff from injectivity or disequality

## Outcome and current evidence

This goal succeeds only after demonstrating at least one of the following:

1. a genuine EggCC compiler bug that already exists in a freshly pinned pre-integration baseline; or
2. a correctness-preserving, reproducible speedup in end-to-end compilation or generated-program execution.

The result must also use injectivity or disequality in a way that cannot be replaced by one constructor-specific comparison of primitive fields. A new analysis, a useful intermediate fact, an unmeasured optimization, or an unsuccessful search is progress but does not satisfy the goal. The [accepted facts](facts.md) are the controlling specification.

Setup performed read-only source analysis over the retained EggCC and encoding worktrees and asked Claude Fable for an independent read-only hypothesis pass. It did not fetch current remotes, build code, run EggCC, or establish a payoff. The most recent locally inspected EggCC main was `a0bbec127f83249074a46af3fd6f6126c90fe0fb`; that identity is historical setup evidence and must be refreshed when execution starts.

The completed `ObservedBool` findings for Mul, Add, and Sub are excluded. Each can be detected by a direct rule that rejects `ObservedBool(true) = ObservedBool(false)`, so they do not establish a need for the generic encoding. The prior structural type, LocalCell, CSR/NoAlias, and branch-integration studies are also excluded by the accepted facts.

## Approach

Use a two-gate search. Every lead must first pass a **mechanism gate** showing a causally consumed equality or disequality over equality-sort terms, a chain through semantic constructors, or essential use of both encodings. It must then pass a **payoff gate** showing a pre-existing compiler bug or a measured endpoint speedup. Keep every lead and falsifier in an append-only ledger.

First screen fixed-translation cancellation and same-mask reverse disequality as separate scoped false-`Eq` families. Then test the stronger bounded alias candidate: a private branch-local reasoning graph derives that two dynamic indices are unequal, propagates that fact through fixed translation and live-cell constructors, and exports an exact `NoAlias` fact. EggCC's existing `mem-simple` rules can then commute a load past an unrelated store and forward the earlier stored value. The decisive relation is between dynamic equality-sort terms; fixed primitive metadata such as mask values, bounds, allocation size, and translation constants cannot determine it. Screen each native endpoint before implementing its integration, because LLVM may already remove the branch or load.

After each candidate family is resolved, perform a fresh Codex source pass and a new read-only Claude Fable pass using the accumulated evidence. Source-check every proposed law, producer, consumer, and endpoint before admission. Continue after a first success to look for a stronger or additional example. Stop only at the finite exhaustion boundary in Step 8.

## 1. Admit fresh, isolated sources and evidence

Preserve the dirty primary checkouts and all prior study worktrees. Do not edit or use their generated outputs as fresh evidence. At goal launch:

1. Fetch the current remote main revisions for both EggCC and `egglog-encoding`.
2. Create new isolated worktrees for an untouched EggCC baseline, an integration baseline, candidate implementations, and the selected encoding source.
3. Record commit IDs, dirty patches, submodule or path dependencies, lockfiles, Rust and LLVM versions, build flags, binary hashes, machine identity, and exact commands in a source manifest.
4. Establish that the untouched baseline builds and passes its ordinary small canaries before interpreting any candidate result.
5. Put durable experiment artifacts under an ignored `benchmarks/local/eggcc-nontrivial-encoding-payoff/` directory. Use temporary files only for disposable iteration.

Do not commit, push, open a pull request, add proof support, edit the paper, or destructively clean prior artifacts as part of this goal. Those actions require separate authorization.

The roles are:

| Role | Purpose |
| --- | --- |
| `U0` | Untouched, freshly pinned EggCC baseline. Establishes whether a bug pre-exists integration and supplies the performance baseline. |
| `B1` | Same EggCC source retargeted to the selected encoding engine, with candidate reasoning and bridges disabled. Separates dependency/integration overhead from the feature. |
| `SeedOnly` | Performs the same traversal, term materialization, and source-fact collection but does not infer or export a result. Measures preparation overhead. |
| `Manual` | Faithful hand-written closure over the same finite terms and assumptions. It may use several rules; it may not skip directly to a primitive endpoint. |
| `Encoding` | Private e-graph using the generic injectivity and disequality machinery. |

Create `hypotheses.jsonl` before probing. Each append-only row records: cycle and proposer; source revision; law and domain; valid trigger; producer; intermediate facts; consumer; predicted payoff; primitive-only null treatment; cheapest falsifier; attempt count; evidence paths; and disposition. Do not silently revive a closed lead without new source evidence.

**Verification:** compare clean source manifests before and after work; verify every old study directory remains unchanged; run `cargo metadata --locked` in each admitted Rust root; record the actual CLI help and supported modes rather than assuming historical command syntax.

## 2. Run the recurring Codex/Fable hypothesis loop

Cycle zero consists of the setup analyses and [Claude Fable's initial proposals](claude-fable-ideation.md). Its proposals are hypotheses, not verified facts. In particular, its suggestion to store branch disequality in EggCC's main graph is rejected: a branch-local assertion can survive later equality collapse or contaminate sibling contexts. Use a fresh private graph for each exact branch and query.

At the end of every candidate family:

1. Write a short evidence synopsis containing the exact falsifier or successful causal chain.
2. Have Codex rescan the current pinned EggCC source and any emitted graphs for new valid producers and blocked consumers.
3. Run Claude Fable read-only with the synopsis, current ledger, source manifests, and relevant roots. Limit its tools to reading/searching, disable session persistence, and forbid edits.
4. Independently verify all cited files and line ranges against the pinned source. Reject proposals with no valid source trigger, sound law, actual producer, actual consumer, novel endpoint, or non-primitive mechanism.
5. Rank admitted leads by cheapest decisive experiment and append them to the ledger.

For a given lead, run the cheapest falsifier, then at most one smallest actual-host/native probe and one revision justified by a concrete falsifier. Two cycles with no new evidence close that lead. A family is resolved only when every admitted lead in it has a disposition; then run the required fresh Codex and Fable passes. The recurring loop is part of execution, including after a qualifying result; it is not a one-time setup exercise.

**Verification:** retain every Codex synopsis, Fable prompt/output, source-validation note, and resulting ledger rows. A model suggestion cannot appear in the final fact set unless its source and behavior were independently checked.

## 3. Stabilize the generic engine prerequisite

Freshly inspect the selected `egglog-experimental` main before assuming the retained feature worktree still describes it. The candidate needs these generic operations:

- equal applications of a marked constructor cancel to equal equality-sort children;
- a known child disequality propagates forward through a marked constructor;
- a known disequality between committed applications of the same constructor can imply disequality of one selected equality-sort child when every other equality-sort sibling is canonically equal and every primitive sibling is equal;
- `known-disequal?` reads the result without growing the graph; and
- contradiction checking distinguishes an inconsistent local assumption set from an unknown query.

The reverse query requires unionable output and selected-child sorts, committed applications at the same selected position, exactly one unresolved child pair, and supported sibling fields. Containers and unsupported native/custom fields do not participate; two differing children remain unknown. The constructor need not be marked, and `Bitand`/`Mask` must remain unmarked.

If n-ary reverse congruence is not on current main, port only the retained generic delta and its focused tests into the isolated encoding worktree. Do not add EggCC-specific constructors or scope semantics to the engine. Private NEE is the compiler contract. Run EE as a differential diagnostic on the finite consistent test corpus; an EE-only storage/lifting difference is recorded but does not reject a sound NEE candidate unless it exposes a violation of a shared mathematical law.

Required engine boundaries include unary and n-ary positive cases; equal scalar siblings; two differing children remaining unknown; late equalities; subsumed rows; distinct constructor names; marked and unmarked constructors; recursive queries that do not create terms; primitive and container rejection; self-disequality; and contradiction behavior. Check scheduling explicitly: ordinary consumers may need another ruleset iteration after new equalities, while a query sees the committed canonical state.

**Verification:** run focused registered tests while iterating, then the encoding repository's required suite:

```bash
cargo test --locked -p egglog-experimental --test injectivity_disequality
make check
```

Use names discovered from the fresh source for individual filters. Assert that every intended filtered invocation selects at least one test.

## 4. Apply front-door falsifiers before integration

### 4.1 Required scoped cancellation and reverse-disequality families

Give these two families separate ledger entries, source fixtures, causal receipts, and dispositions before combining them with alias reasoning.

The fixed-shift cancellation family is:

```text
Translate1(x) = Translate1(y)
x != z
  => x = y                         marked-constructor cancellation
  => y != z                        canonical transport
  => Translate2(y) != Translate2(z) marked forward disequality
  => Eq(Translate2(y), Translate2(z)) = false in the exact context
```

The same-mask reverse family is:

```text
Bitand(x, m) != Bitand(y, m)
  => x != y                         reverse congruence; canonical common mask
  => TranslateK(x) != TranslateK(y) marked forward disequality
  => Eq(TranslateK(x), TranslateK(y)) = false in the exact context
```

Use a distinct marked constructor for each fixed wrapping translation. Keep `Bitand` unmarked. Required negatives include unequal translation constants, different or unresolved masks, two differing children, absent parent equality/disequality, wrong context, and an infeasible branch. Each family gets its own false-`Eq` bridge/native screen. If LLVM or current EggCC already removes the branch, retain the mechanism evidence but close that payoff lead. The strengthened combined chain may use cancellation, same-mask reverse reasoning, canonical transport, and marked forward propagation in one feasible context, but it does not replace the two individual dispositions.

Independently establish at least one feasible positive witness for each admitted family before promotion: `x=y=0, z=1` for cancellation; `x=0, y=1, m=1` for same-mask reverse; and `x=y=0, z=1, m=1` for their combined form. Add wrapping-boundary witnesses for fixed translations. A contradictory path alone cannot qualify.

### 4.2 Combined scoped masked-index `NoAlias` candidate

Construct the smallest valid Bril workload with dynamic `i` and `j` and a false branch of:

```text
Mask(i, 1) = Mask(j, 1)
```

Here `Mask` is the sidecar representation of the source `Bitand` application; it is a data constructor in the local reasoning domain, not a new EggCC operator.

Inside the false branch, use pointers at fixed translated indices from the same live allocation and a repeated `store pi; store pj; load pi` pattern. The intended optimization is:

```text
Mask(i, 1) != Mask(j, 1)
  => i != j                         congruence contrapositive; common mask
  => Translate1(i) != Translate1(j) marked bijective constructor
  => LiveCell(r, Translate1(i))
       != LiveCell(r, Translate1(j)) marked exact-cell constructor
  => NoAlias(pi, pj)                checked live-region bridge
  => commute load past store pj     existing mem-simple rule
  => forward store pi into load pi  existing mem-simple rule
```

`Mask`, the symbolic indices, the region, and both wrappers are equality-sort terms. `Mask` itself is not marked injective; the reverse implication is the contrapositive of ordinary congruence and requires the common sibling. `Translate1` is wrapping addition by a fixed constant and is a bijection on 64-bit words. `LiveCell` denotes an exact cell only after checking a common live region, in-bounds indices, unchanged pointer expressions, no free, escape, call, or relevant mutation, and the exact branch scope. Mask literals, translation constants, bounds, and allocation sizes are available as primitive guard metadata, but no comparison among them determines whether the two dynamic indices or cells are unequal.

Interpret the false integer-`Eq` branch pointwise: for every feasible input to that contextual region, the two total pure integer expressions evaluate to different words. Import this as a local assumption only after verifying the predicate, types, context, input transport, and totality. It is not a global statement about either source expression.

The alias workload also needs an independently checked concrete witness with a live allocation and all accesses in bounds, such as `i=0, j=1`, translated offsets `1,2`, and allocation size `3`. Check the allocation lifetime and every access independently of the sidecar.

Before writing engine or EggCC integration code:

1. Confirm the saturated baseline retains the relevant store/store/load demand and does not already derive `NoAlias`.
2. Create a manually optimized Bril variant that removes only the load enabled by the proposed fact.
3. Lower baseline and manual variants through the same native backend and compare optimized Bril, LLVM, assembly, output, and a short runtime screen.
4. Close the generated-runtime lead if the backend produces equivalent final code. Keep a compile-time lead only if the complete candidate, including analysis overhead, could plausibly reduce end-to-end time.
5. If the source shape is absent for one reasonable workload, revise it once from the actual graph; close that lead after a second no-demand result.

Also screen a strengthened `NoAlias` form that prefixes the chain with cancellation, when a natural contextual program shape exists:

```text
Translate1(x) = Translate1(y) => x = y
Mask(x, m) != Mask(z, m)      => x != z
x = y and x != z              => y != z
Translate2(y) != Translate2(z)
```

This version exercises cancellation, reverse disequality, canonical transport, and forward propagation. Prefer it if it reaches the same real consumer without manufacturing an unnatural input; otherwise retain the smaller chain and state exactly which mechanisms are essential.

### 4.3 Scoped false-`Eq` endpoint

Use this endpoint for the two required families and their combined form: a nested branch in which the derived translated-index disequality makes an inner `Eq` false. Existing Boolean/`If` folding is the consumer. This is a smaller integration canary, but it qualifies only if the shifted or multi-constructor intermediate is essential and the final native or compile-time endpoint survives LLVM. A direct repeated guard or direct `i != j` lookup is too small.

### 4.4 Fixed-split tuple census

Do one fresh current-main graph census before implementing tuple cancellation. Examine current fixtures that exercise IVT, loop/If passthrough, loop hoisting, and multi-output regions. Group equal-output `Concat` rows by equal known left length, then record whether child classes already match, demanded `Get` projections already match, semantic guards hold, and a whole-child equality reaches a consumer.

Close the tuple family if there is no surviving pair, if projection closure already supplies the demanded equalities, or if only opaque whole-child equality remains with no consumer. Do not mark `Concat` globally injective: associativity and empty-tuple rewrites make that unsound. Only if a survivor exists may execution introduce a guarded `FixedSplitParts(left, right) :injective` analysis record with identical type, context, finite-tuple, purity, and totality premises, plus a matched manual rule.

### 4.5 Fresh-region and new-family screens

Screen a fresh live-region lead only when an existing hot consumer is actually blocked. Allocation-site identity or distinct primitive IDs alone fail the mechanism gate. A new general points-to, effect, lifetime, or loop-memory optimizer crosses the bounded-implementation limit. Keep the signed-MIN low-bit hypothesis as a possible ordinary EggCC bug report, but do not count it when its only detector is the excluded primitive observation check.

**Verification:** every screen appends its inputs, graph or emitted-code evidence, comparator, endpoint, and disposition to `hypotheses.jsonl`. A screen can close a lead; a family closes only after all of its admitted leads have dispositions. A screen cannot establish a speedup without Step 7.

## 5. Build a private scoped reasoning oracle

Proceed only for a candidate that survives its front-door screen. Add a narrow finite sidecar rather than storing path assumptions in EggCC's main e-graph.

The only initial branch-fact producers are exact contextual integer equality predicates. A true `Eq(lhs, rhs)` ancestor contributes a local union of the translated operands; a false `Eq(lhs, rhs)` ancestor contributes local `(disequal lhs rhs)`. For a nested target, retranslate every ancestor assumption through the checked parent-input to child-`Get` map. Different source symbol IDs never seed disequality, and unsupported predicates remain unsupported rather than being negated or approximated.

For each exact branch and target demand:

1. Reconstruct source expressions through a checked mapping of parent inputs to the contextual child expressions produced by `add_context`.
2. Reject unsupported operators, ambiguous bindings, calls, loops or memory effects in translated terms and path predicates outside the candidate's proved profile. This purity/totality restriction applies to the proof expressions; branch bodies may contain the effects or hot work being optimized. Verify EggCC's lazy `If` semantics, and require a proved false expression to be the exact predicate of the eliminated `If`.
3. At a declared main-egraph fixed-point boundary, map every relevant host value to its current canonical class. Give already-equal host values the same sidecar symbol, and explicitly import relevant equalities that cannot be represented by that quotient. Recheck that the false-branch endpoints have not already become equal before adding their local disequality.
4. Create a fresh experimental NEE e-graph. Materialize a finite grammar of opaque symbolic values, the unmarked mask application, a distinct marked constructor for each fixed wrapping translation, and the marked exact live-cell descriptor if the alias candidate needs it. Represent fixed constants as named equality-sort terms in the reasoning chain; retain their primitive values separately as checked host metadata.
5. Commit all terms, imported equalities, and source-derived assumptions.
6. Saturate the `injectivity` ruleset, then run `(check-contradiction)`. Success means the private assumptions establish local Bottom, so discard every consequence. Only the expected `CheckError` means Bottom was not proved; every other error is analysis failure. Contradiction closure covers the private disequality theory only and is not a satisfiability decision. The first slice never uses local Bottom to eliminate an outer EggCC branch.
7. For a non-Bottom graph, run one `:naive` query rule that calls `known-disequal?` on an already-materialized target and writes success to a host-owned status relation. Inspect that relation after the run. Queries cannot create terms, run cancellation, or establish equality. Unless a checked Rust API separately captures internal query errors, an absent status is recorded as `unknown-or-error`, never as a proved negative or a separately classified unknown.
8. Recheck canonical host classes, context, types, region identity, bounds, liveness, expression identity, and scope immediately before export.
9. Emit one exact contextual result such as `ScopedFalseEq(expr, context)` or a scoped alias witness. Never export local value equality as an unconditional global `Expr` equality.

Build an independent finite-term oracle that enumerates the intended mathematical implications without calling `known-disequal?`. Require private NEE to agree with the oracle. Run EE over the finite consistent corpus as a differential diagnostic and investigate shared-law disagreement without making unrelated EE storage behavior part of the compiler acceptance contract. Required negatives include equal paths, infeasible false branches, different masks, two varying mask children, mismatched translation constants, non-bijective even multiplication, wrong context, sibling scope, same or out-of-bounds cells, differing bases, free/call/escape, unsupported mutation, late equalities, and self-disequality.

Retain a machine-readable receipt for every attempted query: source expression IDs, exact context, translated terms, source assumptions, engine identity/mode, Bottom status, each intermediate equality/disequality, final query, exported fact, and consumer result.

**Verification:** add registered unit tests for the finite translator and oracle, both engine modes, every export guard, contradiction handling, and the positive/negative cases. A test-only bridge that injects the final exact fact must independently demonstrate that the existing EggCC consumer performs the predicted rewrite before full integration begins.

## 6. Integrate only the surviving bounded consumer path

The source traversal begins after contextualization in `dag_in_context/src/add_context.rs`, but the sidecar query and export must occur at a declared main-egraph fixed-point boundary in `dag_in_context/src/schedule.rs`, after relevant address equalities are stable. Reverify that seam on the freshly pinned source. Keep the implementation in one narrow module such as `dag_in_context/src/scoped_reasoning.rs`, with explicit `Off`, `SeedOnly`, `Manual`, and `Encoding` modes.

Current EggCC's `NoAlias(Expr, Expr)` relation has no context field, so the private graph's scope does not automatically constrain an exported row. First record an exact `ScopedNoAlias(pi, pj, ctx)` witness, or an equivalent host-owned record. Require both addresses and the target load/store demand to share the exact target `Assumption`, and verify that its ancestry reaches the intended false `InIf`. A loop body normally has an `InLoop` context, so transport into it needs a checked invariant/passthrough map rather than pretending its direct context is `InIf`. Insert the current row immediately ahead of `mem-simple`, oriented as `NoAlias(pj, pi)` for write address `pj` and load address `pi`, or explicitly run the existing symmetry rule first. Include sibling- and parent-context escape tests.

For the alias candidate, run only the existing targeted closure in `dag_in_context/src/optimizations/mem_simple.egg`: write-before-load commute followed by store forwarding or duplicate-load elimination. A monotone `NoAlias` row must not outlive the canonical-class snapshot that justified it. Either prove that no later phase can merge the address classes, then consume and extract in that frozen phase, or use a guarded one-shot consumer that revalidates the classes and all live-region premises immediately before executing the actual existing `mem-simple` rewrite in an isolated/frozen phase and does not leave the row available to later saturation. A host reimplementation is a new bounded consumer and must be labeled and compared as such. Close the candidate if neither lifetime discipline fits EggCC's schedule. Do not enable a broad optional memory analysis merely to make the case work.

For the false-`Eq` endpoint, use a bridge equivalent to:

```lisp
(relation ScopedFalseEq (Expr Assumption))

(rule ((ScopedFalseEq expr ctx)
       (ContextOf expr ctx)
       (HasArgType expr ty))
      ((union expr (Const (Bool false) ty ctx)))
      :ruleset scoped-false-eq-bridge)
```

Export only a verified Boolean `Eq` in that exact context. A context conflict, missing type, or wrong target shape blocks promotion. Run the bridge, then `interval-analysis` so the false constant obtains its bound, followed by `interval-rewrite` so the existing false-`If` consumer fires. The bridge rescue injects precisely the `Eq = false` equality. The consumer knockout retains that equality and disables only `interval-rewrite`, leaving the `If` intact.

Capture these causal treatments on the same input, graph, seeds, schedule boundary, and backend:

| Treatment | Expected diagnostic purpose |
| --- | --- |
| `U0` | Untouched baseline with its original dependency and existing behavior. |
| `B1` / `Off` | Retargeted dependency with the feature entirely disabled. |
| `SeedOnly` | Same contextual traversal and term materialization, without inference or export. |
| `Manual` | Fair explicit symbolic closure over the same finite domain. |
| `Encoding` | Generic engine result. |
| Cancellation mark removed | Remove only `Translate1`'s mark: parent equality remains; `x=y` and its downstream facts disappear. |
| Cancellation rescued | With cancellation disabled, inject exactly `x=y`; all later stages return. |
| Reverse step removed | Parent disequality remains; index disequality disappears. |
| Final translation mark removed | Remove only `Translate2`/`TranslateK`'s mark: child equality/disequality remains; final translated disequality disappears. |
| Live-cell mark removed | Translated disequality remains; cell disequality disappears. |
| Bridge removed | Internal target fact remains; `NoAlias` or false predicate disappears. |
| Consumer removed | Exported fact remains; emitted program does not change. |
| Intermediate rescue | Injecting precisely the missing intermediate restores all downstream steps. |

Compare `B1` against `U0` for dependency overhead, `SeedOnly` against `B1` for preparation overhead, `Encoding` against `B1` for the complete feature effect, and `Encoding` against `Manual` for the generic-versus-explicit implementation comparison.

Also run the primitive-only null treatment on the identical graph and seeds. Give it every primitive guard value used by the candidate, including masks, offsets, bounds, allocation sizes, and tags. It may compare primitive children of a single constructor and emit the final panic, guard, or fact, but it may not inspect or propagate the equality-sort relation. It must fail to reproduce the candidate. A larger faithful manual implementation may match the generic result; report equivalence honestly rather than claiming unique logical power.

If integration exposes a main-graph equality between endpoints that the sound private oracle proves unequal, freeze that exact case as a possible compiler bug and follow the bug route in Step 7. An error introduced only by the new bridge or dependency retargeting is an integration defect and cannot qualify.

**Verification:** registered focused tests must show every intermediate receipt, each knockout and rescue, consumer action, primitive null, manual parity, and nearby negative. Compare source and optimized interpreter outputs, emitted Bril, LLVM, native output, and the exact pass at which the endpoint changes.

## 7. Establish a qualifying bug or speedup

### Bug route

A candidate bug qualifies only when all of these hold:

1. the minimized valid input fails in `U0`, before the encoding integration;
2. an independent source/interpreter or mathematical oracle establishes the correct behavior;
3. the violated invariant and first invalid compiler step are localized;
4. actual compiler and native execution reproduce the consequence when applicable;
5. nearby valid positive and negative controls pass;
6. the encoding's intermediate fact materially enabled discovery or localization; and
7. source chronology shows it was not a planted fault, malformed input, known excluded result, or integration regression.

Preserve the first detection artifact before repairing anything. Then apply the smallest sound fix, rerun the minimized case and controls, and verify the full suites. An engine panic alone is not a compiler bug unless the independent evidence shows a real invalid EggCC equivalence or output.

### Speed route

Do not time a candidate until correct outputs and an actual final-program or complete-compiler-path difference are established. Compare matched `U0`, `B1`, `SeedOnly`, `Manual`, and `Encoding` arms with the same source input, backend, optimization settings, CPU conditions, and timing boundary. Include private-graph construction and translation in compiler time.

Use at least ten independent observations per arm and workload, interleaved in a balanced order after a declared warmup. Retain raw samples, timeouts, errors, neutral results, regressions, output checks, and machine load metadata. Report compiler and generated-program time separately and report every workload rather than an aggregate headline. Freeze the comparison method and improvement threshold before a fresh confirmation batch. Require the confirmation to exceed observed variability; an inconclusive result is not success.

The native backend comparison is mandatory even for a compile-time claim because it establishes that all arms compile the same correct program or documents the intentional output difference. Rule time, e-graph node count, fewer rewrites, and failed-versus-successful runs are diagnostics, not endpoint speedups.

Memory pressure does not block the search. Use bounded smaller workloads and finite timeouts when full workloads are impractical, retain genuine resource failures, and do not reinterpret them as semantic or performance results.

**Verification:** write a machine-readable acceptance record binding source, dependency, patch, binary, input, command, configuration, output hash, emitted-code hash, raw observations, and causal receipts. Independently rerun the winning case from that record before admission.

## 8. Continue, exhaust, or stop at the redesign boundary

After every disposition, return to Step 2. Continue after the first qualifying result to search for a stronger or additional case, especially one that combines cancellation, reverse disequality, forward marked propagation, and a substantial existing consumer.

Stop the search only when a retained Codex pass and a fresh Fable pass both produce no new source-backed eligible lead, or when every remaining lead requires a wholesale IR, alias, effect, path-sensitive, or loop-memory redesign. Before stopping, ensure each admitted lead has a recorded eligibility screen, cheapest falsifier, actual-host probe when eligible, at most one evidence-driven revision, and final disposition.

If no candidate passes both gates, write the bounded conclusion: no qualifying payoff was found in the searched source revision and recorded lead set. Preserve useful ordinary bug reports and mechanism results separately, mark the goal unmet, and do not claim global impossibility or goal completion.

## 9. Full validation and collaborator-facing deliverables

Run focused tests throughout. Once a candidate source change is stable, run the repositories' complete required checks from their fresh isolated roots:

```bash
# egglog-encoding
make check

# EggCC
make test
make nits
```

Recheck the exact current project commands at execution admission. Do not accept zero selected tests, inherited snapshots, or unexplained baseline differences as validation. Run the actual EggCC CLI through source interpretation, optimized interpretation, emitted form, and native execution for every claimed endpoint.

Deliver:

- `report.md`: a Diátaxis-style explanation of the successful case, or a clearly labeled bounded negative result. Connect the source program, mathematical laws, intermediate facts, existing consumer, before/after compiler behavior, manual comparison, endpoint evidence, and limitations.
- `reference.md`: compact definitions of the injectivity and disequality operations used, their schedule, the scoped sidecar API, exact supported domain, contradiction behavior, receipts, and treatment modes.
- `reproduce.md`: fresh setup, identities, commands, inputs, expected outputs, emitted-code checks, measurements, and known resource requirements.
- `acceptance.json`: one machine-readable row per accepted fact with evidence paths and pass/fail status.
- `hypotheses.jsonl`: the complete append-only lead and falsifier ledger, including both Codex and Fable cycles.

Have separate semantic, implementation, measurement, and documentation reviews. Confirm that the explanation makes the contribution understandable to an Egglog reader without requiring the experiment history, while the reproduction guide remains operational and exact.

## Accepted-fact verification map

| Fact | Required check |
| --- | --- |
| `strict-payoff` | Automated acceptance rejects every outcome lacking either the complete pre-existing-bug bundle or confirmed endpoint-speedup bundle. |
| `nontrivial-mechanism` | Receipt shows a consumed equality-sort equality/disequality or multi-constructor chain; reviewer identifies the exact essential mechanism. |
| `primitive-null-exclusion` | Fixed-input primitive-only null cannot reproduce the final fact, guard, or panic. |
| `manual-comparison` | Faithful manual closure runs on identical terms, assumptions, schedule boundary, and endpoint. |
| `causal-mediation` | Intermediate receipt, each knockout, precise rescue, bridge/consumer knockout, and negative controls all have expected outcomes. |
| `maximize-results` | Ledger shows continued search after a first success until the stated exhaustion/redesign boundary. |
| `iterative-ideation` | Every resolved family is followed by retained Codex and Fable artifacts and source-validation notes. |
| `lead-lifecycle` | Ledger enforces admission questions, cheapest falsifier, bounded probe/revision, and closure after two no-progress cycles. |
| `search-stop` | Final ledger demonstrates the finite exhaustion condition; no-success outcome remains unmet. |
| `initial-portfolio` | Fixed-translation cancellation, same-mask `Bitand` reverse disequality, fixed-split tuple, and live-region screens each have a separate evidence-backed disposition. |
| `prior-results` | Novelty audit excludes all named prior findings and disallowed fault classes. |
| `bug-evidence` | `U0` replay, valid minimized input, independent oracle, localization, native/compiler consequence, controls, and chronology. |
| `speedup-evidence` | Matched correct arms, explicit endpoint, raw repeated samples, variability analysis, and independent confirmation. |
| `semantic-scope` | Review covers types, contexts, effects, feasibility, Bottom, lifetimes, mutation, and unsupported outcomes. |
| `implementation-scope` | Diff and architecture review confirm bounded bridge/analysis work and identify any redesign boundary. |
| `validation` | Nonzero registered tests, full checks, exact identities, emitted/native checks, and explicit failures. |
| `preservation` | Before/after manifests show dirty author work and frozen studies unchanged; no unauthorized commit, push, PR, proof, paper edit, or cleanup. |
| `deliverables` | Explanation, reference, reproduction guide, acceptance map, and complete ledger exist and cross-reference the same evidence. |

## Principal risks and open gates

- Current remote main may differ materially from the locally inspected `a0bbec12` source. Refresh source paths and assumptions before implementation.
- The retained n-ary reverse-disequality change may not be merged. Treat it as a separately tested engine prerequisite, not an assumed API.
- Branch facts become unsound if stored in the main e-graph. Private graph isolation, contradiction handling, and exact contextual export are mandatory.
- A private graph built from distinct placeholder symbols can miss equalities already known in EggCC. Quotient its symbols by current canonical classes, import remaining relevant equalities, and recheck them at export.
- A persisted `NoAlias` fact can become invalid if later saturation merges its endpoints. Consume it only in a proved frozen phase or through a guarded one-shot rewrite.
- `known-disequal?` is incomplete; an unknown result is not equality, satisfiability, or permission to optimize.
- `LiveCell` needs a narrowly proved live-region meaning. If that proof requires general points-to/effect/lifetime analysis, close the candidate at the redesign boundary.
- LLVM may already erase the proposed branch or load. The early manual/native screen exists to avoid building a mechanism with no endpoint payoff.
- Current projection closure probably makes fixed-split tuple cancellation redundant. One fresh census is enough unless it finds a real survivor.
- A source-derived microbenchmark can establish a real endpoint speedup, but it must be labeled as such and cannot be presented as a suite-wide result.
- Fable and Codex hypotheses can be wrong. Only pinned source, executable behavior, independent semantics, and retained evidence can promote them to facts.
- A qualifying result is not guaranteed. The goal remains unmet if the search yields only useful reasoning machinery, ordinary primitive bugs, or negative evidence.
