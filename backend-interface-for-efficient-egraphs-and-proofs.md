# Backend Interface for Efficient E-Graphs and Proof Production

**Status:** Ready for team review as a research report; not yet a validated
production interface or a self-contained reproducibility bundle.<br>
**Revision date:** 2026-07-13<br>
**Accepted performance-study checkout:** `d7f2532f0e726738d040af668d09165a55f9f0bc`
for M1-M5.<br>
**Current integrated implementation:** `32d5507` combines current main
(`22f4840e`), PR #6 (`aa03f914`), the DD tuple/action-merge implementation
introduced by `a1342d64`, rule-name hoisting, the full default math fixture,
composed proof snapshots, and transactional DD error rollback. M6 and M7 remain
measurements of the earlier equivalent dirty prototype based on `fc86c37`;
they are not presented as measurements of the integrated commit. M8 is a fresh
bounded comparison from clean integrated commit `412fb58`.<br>
**Audience:** egglog contributors and backend implementers<br>
**Authorship:** Drafted by an AI assistant, then reviewed against the source code,
tests, benchmark artifacts, profiler evidence, and team meeting notes listed in
the evidence appendix.

## Decision Requested

Should egglog distinguish two integration boundaries?

1. A full `EGraphBackend` owns authoritative e-graph state and implements the
   complete table, merge, equality, rebuild, execution-session, and snapshot
   contract.
2. A narrower `JoinEngine` may accelerate rule-body matching while one shared
   runtime continues to own those semantics; it is not presented as a complete
   backend.

For the full proof-capable interface, should every backend implement native
e-class maintenance plus an optional-at-runtime evidence mode that carries
opaque causal tokens, while one shared runtime owns proof selection, formatting,
and checking?

This document recommends **yes as the next architecture to test**. It does not
claim that the interface or the `<2x` target is validated, and it does not
recommend retaining the current term/proof encoding as a production fallback.

## Executive Summary

The research question is not simply whether egglog can swap one join engine for
another. It is:

> What semantic API must a backend implement to execute e-graphs efficiently,
> and can proof production be shared without making every backend understand
> egglog's proof representation?

This restates the team-notes questions about how much performance requires
native/generalized equality and custom rebuilding, and what minimal backend
interface remains after those mechanisms move below the frontend.[N1]

The current evidence supports the following answer:

- A proof-format-unaware backend can execute the existing proof encoding
  **semantically**. The integrated DD backend now supports full output tuples,
  action-valued merges, dependency-ordered merge reads, generated writes to a
  fixed point, and proof-mode constructor conflicts without changing the proof
  format or checker.[S11]
- Tuple and merge support did **not** require a proof-format change. It required
  a stronger generic backend contract: explicit key/output arity, atomic access
  to complete old/new output tuples, effectful merge expressions, dependency
  ordering, and transactional table updates.[S1][S11]
- That semantic result is not a performance result. On the fresh integrated
  mini-math comparison, DD remained `3.511x` main in proofs and `4.171x` main
  in term mode, with much higher RSS. The short main runs made the wall-time
  intervals noisy, but not the direction of the memory result. Full math timed
  out at 120 seconds in the earlier boundary probe, and eggcc reached a
  registry-backed container-rebuild boundary after 73 seconds and about 4.0
  GiB RSS.[M7][M8]
- A full backend is therefore more than a generic join engine. In the current DD
  split, Differential Dataflow performs body-table joins; a Rust mirror and
  host interpreter remain authoritative for body primitives, ordered actions,
  merge behavior, subsumption, row generations, and lookup-or-insert.[S8][S11]
- Backends should not know `Proof`, `ProofStore`, proof syntax, witness
  rendering, or the proof checker. Those can remain shared.[S9]
- If the expensive generated proof relations are removed, a full backend likely
  cannot remain completely unaware of causality: equality paths, merge winners,
  constructor creation, no-op operations, rebuild collisions, and mutations
  initiated through execution-state APIs occur inside backend-owned state
  transitions.[S1][S3][M3][M4]
- The proposed middle layer is **generic evidence support**: every full backend
  carries fixed-width opaque tokens and reports typed semantic events, while a
  shared evidence runtime builds the causal DAG and materializes the proof
  format only when requested. This remains the leading design hypothesis, not a
  proven necessity for every possible architecture.
- `ExecutionState`-style operations and custom primitives are part of the
  architectural boundary, not an unrelated feature. The initial implementation
  may reject arbitrary stateful Rust callbacks in proof mode, but it must not
  permit any mutation path that silently bypasses evidence collection.[S4][S6]

The concise research hypothesis is:

> Efficient portable e-graphs require native e-graph maintenance and generic
> evidence plumbing, but not backend-native knowledge of egglog proofs.

Two direct prototypes narrow, but do not close, this hypothesis:

- A native-maintenance ablation removed the five targeted generated
  UF/rebuild families and reproduced a checked congruence proof, but a broader
  proof regression spent more than 80 seconds in recursive extraction over
  eager proof values. This is evidence that native equality/rebuild can expose
  the required causes, and evidence against retaining concrete proof rows in
  the semantic fixed point; it is not performance evidence for the proposed
  interface.[M4]
- A proof-format-free RelationalV1 recorder deterministically transported
  fixed-width cause IDs through one relation premise and committed insertion
  without callbacks or disabling parallel insertion. It missed its strict
  single-thread wall gate (`1.32x` observed versus `<1.25x`) and did not close
  every public mutation path. This is qualified semantic evidence, not a passed
  performance or portability result.[M5]

The measured implementation of the present generated encoding still does not
meet the `<2x` eggcc target. The DD experiment strengthens the semantic
portability result while weakening any claim that generic joins plus a host-side
merge interpreter are sufficient for performance. The combined evidence
supports the proposed separation as the most credible next design, while
leaving the central performance claim unproven.[M1][M2][M4][M5][M7][M8]

## What Changed in This Revision

The integrated DD compatibility work added one missing semantic layer rather
than a proof-specific feature:

- relation metadata and all reads now retain every declared output column;
- one recursive merge IR handles scalar and tuple outputs without a scalar fast
  path;
- every output expression sees one immutable old tuple and one immutable new
  tuple;
- function and constructor reads are dependency ordered;
- merge-generated writes execute in later waves until no writes remain;
- subsumed rows remain current for keyed lookup/merge and retain their location;
- row generations refresh when a logical row is replaced; and
- pure container primitives use backend-owned base/container registries without
  requiring the bridge `ActionRegistry`.[S1][S11]

This was enough for the existing term/proof encoding to run through the DD
backend on the enabled corpus and for focused DD witnesses to pass the checker.
It was not enough for native UF or registry-backed read/write/full primitives,
and it did not make DD competitive with main. Push/pop now works through a deep
authoritative-state clone that reconstructs transient DD state; it is not a
native dataflow snapshot.[S8][M7][M8]

The implementation therefore clarifies three boundaries:

1. **Proof-format boundary:** tuple/action merges are generic execution
   semantics; they do not require a new proof representation.
2. **Backend boundary:** a component that owns only joins should implement a
   join interface. A full backend must also own the authoritative transaction,
   equality, rebuild, primitive, and snapshot semantics.
3. **Performance boundary:** proof-format independence is demonstrated, but an
   efficient no-fallback design still needs native maintenance and probably
   compact backend-integrated evidence rather than generated proof relations.

## Terminology

This report uses three deliberately different terms:

- **Proof-format aware:** understands egglog proof terms, `ProofStore`, witness
  selection, printing, or checking.
- **Evidence aware:** preserves opaque causal identities through semantic
  operations and can return a witness token for an established equality.
- **Evidence unaware:** executes values and state transitions without retaining
  why they happened.

The proposal requires backends to be evidence aware but proof-format unaware.
Whether that is called "native proof support" is a terminology choice. The
operational distinction is that backend code implements generic causal
propagation, but no backend implements egglog proof syntax or proof checking.

## Current Answer

The integrated DD implementation answers the semantic half of the research question more
strongly than before: a backend does not need to understand the proof format to
run proof-producing egglog programs. Proof tuples and action-valued merges can
remain ordinary typed values and generic merge operations. The unchanged proof
checker accepted the resulting witnesses on the tested cases.[S11]

It does not answer the efficiency half. The current evidence does not support
"incrementally move UF and rebuild, then keep the rest of the proof encoding"
as the likely route below `2x`. Native maintenance is still part of the answer,
but the H1 ablation failed while eager concrete proof/View rows remained. The
required redesign is therefore narrower than replacing the entire egglog
runtime, but broader than swapping two maintenance algorithms: remove proof
objects and generated proof relations from the semantic fixed point, retain
compact causal sidecars on native state, and materialize proofs lazily above the
backend.[M2][M4]

The minimal **semantic backend** contract established by current code requires:

1. Full-row schemas with an explicit key/output split and keyed reads that return
   every output.
2. Stable iteration read views, staged ordered actions, seminaive row identity,
   deletion, and subsumption.
3. Atomic multi-output conflict resolution over complete old/new tuples.
4. An effectful merge language covering primitive calls, table insertion,
   lookup-or-insert, construction, sequencing, and conditionals.
5. Declared merge-read dependencies and fixed-point processing of generated
   writes.
6. Primitive and container operations against the backend's authoritative
   execution state.
7. Defined snapshot/restore behavior where push/pop is part of the supported
   language.[S1][S8][S11]

For the proposed efficient, no-fallback **proof-capable backend**, the leading
hypothesis adds:

1. Native equality, congruence, canonicalization, and rebuild semantics.
2. Reason-producing canonicalization and equality, without requiring any one UF
   representation or annotations on every physical edge.
3. Typed post-commit receipts for actual rule/action/merge/rebuild outcomes and
   propagation of opaque fixed-width cause IDs.
4. A backend-neutral execution session through which every public read and
   mutation path, including custom primitives and container operations, is
   routed.
5. Mutation-closure semantics that preserve evidence in recording mode and add
   no evidence-proportional state in off mode.

The shared runtime, not the backend, should own proof DAG policy, witness
selection, proof syntax, formatting, and checking. Thus a backend does **not**
need native support for egglog proofs; the no-fallback hypothesis requires
native support for causal e-graph operations. A joins-only API does not expose
enough semantic outcomes to be the full backend API, as shown by the current DD
split and the failed after-the-fact observer probe.[S8][M3]

This remains a research conclusion, not a performance result. H2 shows that one
narrow cause-transport family can be implemented without proof types or serial
insertion, but it failed its local wall gate and did not close all public
mutation paths.[M5] The next decisive implementation is a main-backend vertical
slice that combines native equality/rebuild, commit-fused causal receipts, and
lazy proof materialization on real frozen fixtures. Only after that passes can
a second full backend establish genuine swappability.

## Current Evidence

### The generated proof path is not near the target

The final five-fixture benchmark at the accepted checkout used one optimized,
single-threaded binary and six fresh samples per cell. Four fixtures were near or
below the desired point ratio, but two failed the requirement that the upper end
of the 95% confidence interval for `main/proofs / main/off` be below `2.0x`.[M1]

| Fixture | Mean off | Mean proofs | Point ratio | 95% CI | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| `math-microbenchmark-mini` | `0.060216s` | `0.120831s` | `2.0066x` | `[1.863x, 2.173x]` | fail |
| `rw-analysis` | `0.058075s` | `0.060563s` | `1.0428x` | `[0.946x, 1.154x]` | pass |
| `integer_math` | `0.061755s` | `0.059183s` | `0.9584x` | `[0.883x, 1.034x]` | pass |
| `resolution` | `0.058327s` | `0.059148s` | `1.0141x` | `[0.916x, 1.121x]` | pass |
| `eggcc-2mm-pass1-merge-old` | `1.123064s` | `15.343593s` | `13.6623x` | `[13.403x, 13.929x]` | fail |

The 95% CIs for mean eggcc peak RSS were `4.001-4.124 GiB` with proofs and
`115.254-120.043 MiB` with proofs off.[M1]

The same audit reports that all focused proof-output tests, the full workspace
test suite, Clippy, and the Python benchmark-runner checks passed. The timing
results come from one Apple M4 host and one source commit; their confidence
intervals estimate repeated-run uncertainty on that host, not variation across
machines.[M1]

A separate controlled diagnostic compared `off`, term encoding without proof
payloads, and full proofs on eggcc:[M2]

| Comparison | Point ratio | 95% CI | Mean increment |
| --- | ---: | ---: | ---: |
| `term / off` | `7.7457x` | `[7.4898x, 8.0137x]` | `8.059s` |
| `proofs / term` | `1.7537x` | `[1.7199x, 1.7888x]` | `6.975s` |

Under the current architecture, approximately 54% of the measured off-to-proof
increment came from structural term/view/UF machinery and 46% from enabling
proof payloads. These increments are diagnostic partitions, not independent
lower bounds: replacing the structural machinery may also reduce the cost of
propagating proof data.[M2]

The profiles place substantial CPU in generated joins, canonicalization, hash
indexes, table merging, containers, and rebuilding. No resolved final proof
extraction, checker, or simplifier frame appeared. This supports the narrower
claim that the observed cost is predominantly in maintaining and propagating
the encoded state, rather than printing or checking the final proof. Application
symbol coverage was high but incomplete, and the proofs profile contained one
long recorded iteration, so the profile supports mechanism localization rather
than a variance estimate or a categorical claim about every frame.[M2]

**Supported inference:** native equality and rebuilding are plausible necessary
optimizations, but changing only those two mechanisms is not a credible complete
plan for eggcc. The duplicated term/view state and eager proof payload path must
also be substantially reduced or eliminated. This is an inference from the
measured cost split. The native-maintenance ablation below strengthens the
second half of that inference without establishing a timing improvement.

### DD now supports proof tuples and action-valued merges

Commit `a1342d64` removes the earlier tuple/merge compatibility blocker on top
of current main and PR #6. Commit `32d5507` adds failure-atomic fresh-ID rollback
and records the composed proof-policy and witness snapshots. The implementation
and focused regression tests are now part of the branch rather than an
uncommitted experiment.[S11]

The implementation remains hybrid:

| Responsibility | Current owner |
| --- | --- |
| Rule-body relation joins | one fused Differential Dataflow per ruleset |
| Body primitive evaluation | host interpreter over DD-produced bindings |
| Ordered head actions | host interpreter |
| Authoritative visible rows | Rust `mirror` and `subsumed` sets |
| Function conflict resolution | host-side `MergeTransaction` |
| Base values and ordinary primitive dispatch | embedded core-relations `Database` |
| Equality and rebuild | frontend term encoding over ordinary tables |
| Proof construction | frontend term/proof encoding and shared checker |

The merge transaction uses full rows and explicit `n_vals`, evaluates every
output against the same old/new tuples, orders table waves by declared
`Function`/`Lookup` read dependencies, and queues merge-generated writes for
later waves until a fixed point. It preserves a row's live/subsumed location and
refreshes the row generation when the logical row changes. Scalar and tuple
merges use the same recursive `MergeExpr`; there is no separate scalar fast
path.[S1][S11]

`MergeExpr::UnionId` is not native UF support: DD retains the smaller ID only as
term-encoding compatibility, while the encoded UF merge emits the actual table
writes. The frontend rejects DD without term encoding, so this behavior is not
evidence of native equality parity.[S8][S11]

This is direct evidence that tuple-valued proof data and action-valued merge
semantics do not require a proof-format change. The proof format and checker
were unchanged. Replacing separate per-output generated UFs with one tuple UF
did change 14 selected proof witnesses, so those snapshots were regenerated;
all 170 proof cases still passed the existing checker. The required backend
change was to make generic function semantics complete enough to carry the
existing encoding.[S11]

The integrated branch passed the following validation. These results are not
retroactively attributed to the earlier M6/M7 performance artifacts:

| Gate | Result |
| --- | --- |
| `cargo test -p egglog-experimental-dd` | 31 unit tests, 8 file trials, 2 rewrite tests, and 8 smoke tests passed |
| `cargo test --release -p egglog-experimental-dd --test files` | 131 corpus trials passed |
| `cargo test --workspace --test files 'proofs/'` | 170 proof cases passed (162 main, 8 experimental) |
| `cargo test --workspace` | passed |
| `cargo clippy --workspace --all-targets -- -D warnings` | passed |
| locked Ruff, mypy, and pytest checks | passed; 96 Python tests |
| `cargo doc --workspace --no-deps`, formatting, and `git diff --check` | passed; rustdoc completed with non-fatal link warnings |

The focused tests cover cross-column tuple reads, identity guards, block
`Let`/`Set` effects, recursive self-writes, tuple rule actions, subsumed tuple
replacement, generation-sensitive incremental joins, clone reconstruction, and
rollback of staged rows and fresh IDs after a failing tuple merge. Smoke tests
exercise proof-mode tuple containers and a constructor-view conflict through
the existing checker.[S11]

A review search found no rule-name, ruleset-name, environment-variable, or
backend-name semantic switches in the DD patch, and no scalar merge fast path.
The remaining ordering assumption is structural: merge reads must name an
already registered dependency, from which the prototype derives an acyclic
level. A final IR should state that dependency graph and its cycle policy
explicitly rather than leave registration order as an accidental API.[S11]

The review classifies the implementation choices as follows:

| Current choice | Classification | Portable requirement |
| --- | --- | --- |
| full old/new output tuples | semantic | atomic multi-output merge inputs |
| dependency-ordered waves | semantic | declared read dependencies and an explicit cycle policy |
| later waves for merge-generated writes | semantic | transaction reaches its specified fixed point |
| `HashSet<Row>` mirror | prototype artifact | storage order must not affect semantics |
| numeric `merge_level` from registration order | prototype artifact | dependency graph belongs in normalized IR |
| embedded `Database` plus authoritative mirror | prototype artifact | one authoritative execution-state abstraction |
| term encoding and minimum-ID `UnionId` | experimental limitation | native equality contract for a full backend |
| deep clone plus transient DD reconstruction | implemented compatibility path | specify snapshot/restore semantics and cost |
| bridge `ActionRegistry` | current-backend mechanism | backend-neutral read/write execution session |

The bounded performance result is negative. Three fresh samples per cell at the
clean integrated commit `412fb58` on `math-microbenchmark-mini` produced:[M8]

| Mode | main mean | DD mean | DD/main point | DD/main 95% CI |
| --- | ---: | ---: | ---: | ---: |
| term | `0.0838s` | `0.3494s` | `4.171x` | point only |
| proofs | `0.0983s` | `0.3451s` | `3.511x` | `[1.955x, 16.362x]` |

DD peak RSS was `242.4 MiB` in term mode and `232.3 MiB` in proofs mode,
versus `21.5 MiB` and `43.0 MiB` for main: DD/main was `11.293x` and `5.405x`,
respectively. Within DD, `proofs/term` was `0.988x` with a
`[0.887x, 1.102x]` interval. The main runs are close enough to the startup floor
that the wall ratio is imprecise; the defensible conclusion is not that proofs
make DD faster, but that fixed DD/runtime cost dominates incremental proof
payload cost in this short workload. The earlier dirty-prototype M6 result had
the same direction (`3.105x` DD/main in proofs) with a narrower interval.[M6][M8]

Two one-sample boundary probes reinforce the distinction between semantic and
full-system parity:[M7]

- main completed full `math-microbenchmark` proofs in `7.98s`; DD timed out at
  120 seconds;
- after pure container merge primitives were made registry-free, DD ran the
  eggcc proof fixture for `73.28s`, reached about `4.0 GiB` peak RSS, and then
  failed because `@container_rebuild` in read context requires the bridge
  `ActionRegistry`; main completed the same fixture in `5.96s` in the preceding
  probe.

These are mechanism probes, not confidence-interval comparisons. The release
corpus has no enabled known mismatches, but it still skips explicit hang and
unsupported sets. Therefore it establishes parity only for the enabled corpus;
it does not establish full DD parity.[S8][M7]

The architectural consequence is precise: the stronger table/merge contract is
semantically sufficient for the tested proof encoding, but generic DD joins plus
host-side state maintenance are not performance sufficient. Container parity
also needs a backend-owned execution-session capability over the authoritative
mirror, not merely access to an embedded primitive database.

### Native maintenance did not rescue eager proof rows

An isolated ablation replaced the generated UF/rebuild path with native
maintenance for `math-microbenchmark-mini` and a direct congruence canary. It
removed the five targeted generated families from the desugared programs. The
canary's proof snapshot exactly matched its baseline witness and passed the
existing checker; focused non-proof regressions also passed.[M4]

The first broader proof regression, `proofs/eqsolve_proof_testing`, did not
finish after more than 80 seconds. Process sampling found live work in recursive
`prove_exists` extraction over hundreds of distinct proof values, with
approximately 425.6 MiB peak memory. Structural UF/rebuild non-quiescence was
not observed in that sample. Because the prototype still stored and transformed
concrete proof objects in eager View/proof rows, no benchmark result from the
ablation was valid.[M4]

The ablation therefore supports a narrower architectural conclusion: native
equality and rebuilding need reason-producing operations, but concrete proof
syntax must move out of the backend fixed point. It also exposed requirements
for equality domains, preferred versus actual leaders, evidence-opaque columns,
row rekeys, constructor-prefix collisions, same-ID container dirtiness, and a
stable post-commit receipt boundary.[M4]

### Fixed-width evidence transport is feasible but not yet accepted

A second isolated prototype tested only source relation facts, one positive
relation premise, committed relation insertion, and deterministic duplicate
arbitration. It used 8-byte opaque causes, 32-byte committed events, and
backend-owned event pages. No proof-format types, observer callbacks, or
table-to-database reentry appeared in the recording path, and normal parallel
insertion remained enabled.[M5]

On the synthetic E0 case, 4,000,000 attempts produced 3,500,000 committed
events. Two 112 MB reports were byte-identical; off and record state digests
matched; and a standalone verifier checked sequential causes, premise
references, and the recorded digests. The verifier is hash-authoritative rather
than row-authoritative: records contain 64-bit hashes of run-local values, so
the result does not prove collision-free row reconstruction.[M5]

The focused `-j1` checkpoint observed `1.32x` wall, `1.35x` user time, and
approximately `1.13x` peak RSS for record versus off. These are point ratios,
not confidence intervals, and the wall result failed the experiment's `<1.25x`
gate. Maximal-thread measurements are useful only as mechanism diagnostics and
do not replace the required single-thread result.[M5]

Independent review also found that command-level rejection was tested but
public mutation-path closure was incomplete: a Rust API such as
`clear_function` could clear a recorded table without a deletion event. Higher
arities can spill the prototype's inline buffers, compaction uses an unmeasured
serial rehash, and repeated report draining is unproven.[M5]

This result supports the feasibility of proof-format-free causal transport for
one producer family. It does not validate the complete event vocabulary, the
selected overhead budget, equality/rebuild integration, execution sessions,
proof materialization, frozen-fixture performance, or a second backend. The
failed local wall gate suggests that evidence arbitration should be fused into
native table commit/index maintenance instead of implemented as a second
full-row pipeline.

### The current encoding turns e-graph maintenance into ordinary data

The current term encoding removes source-level `union` operations and creates,
per equality sort, explicit UF relations, a function-backed UF index, term
tables, view tables, self-loop rows, and generated maintenance rules. Rebuild and
congruence are also generated as rules, and proof values are stored directly in
UF and view-table outputs.[S2]

That transformation gives a backend-agnostic implementation over ordinary
relations, but the benchmark above shows that this particular portability
mechanism does not satisfy the eggcc performance target.[M1][M2]

### The current backend API exposes values but not causes

The current `Backend` trait deliberately exposes a small operational surface:
table registration and scans, representative lookup, rule construction and
execution, execution-state access, primitive registration, flushing, and
snapshots.[S1]

Its proof-relevant methods return only value/state summaries:

- `get_canon_repr` returns a representative value, not a witness for the path;
- `run_rules` returns an `IterationReport`, not executed-match or mutation
  evidence;
- `flush_updates` returns only whether state changed; and
- rule-builder `set`, `remove`, `subsume`, and `union` operations return no
  producer token or mutation outcome.[S1]

Consequently, a proof implementation outside the backend cannot observe enough
information to reconstruct all causes after execution. The current encoding
works around that limitation by representing proof state as ordinary rows.[S2]

### Execution state is currently concrete and only partially portable

`core-relations::ExecutionState` is a concrete view over the in-memory database.
It exposes visible tables, external functions, base/container registries,
predicted lookup-or-insert values, and staged insertion/removal buffers. Its
mutations are applied later during table merge.[S3]

Egglog's user-facing primitive API wraps that state in four capability types:

| Context | Reads | Writes | Current wrapper |
| --- | --- | --- | --- |
| pure | no | no | `PureState` |
| read | yes | no | `ReadState` |
| write | no | yes | `WriteState` |
| full | yes | yes | `FullState` |

The read/write/full wrappers dispatch table operations through a bridge-owned
`ActionRegistry`; pure wrappers need only base/container registries.[S4] The
reference backend delegates its execution-state hook directly to the bridge's
concrete state.[S5] The backend trait currently makes the action registry
optional. DD can now execute pure container merge primitives through its own
base/container registries, and ordinary expression primitives through an
embedded core-relations database. It still rejects registry-backed
read/write/full primitives because the embedded database is not the
authoritative `mirror`/`subsumed` relation state.[S1][S8][S11]

This is an observed blocker rather than a hypothetical one: the eggcc DD probe
advanced through its pure container merge, then failed when
`@container_rebuild` requested read access through the unavailable action
registry.[M7]

Proof mode currently rejects `EGraph::update`, `rust_rule`, and
`rust_rule_full` because their writes or callbacks bypass the proof-encoding
pipeline. Tests enforce those errors.[S6] Pure expression primitives can
participate in checked proofs only when they provide validators that the proof
checker can re-run.[S7]

These are current implementation facts, not desired restrictions. They show
that a clean backend contract must account for execution-state operations and
custom primitives explicitly.

## Proposed Portability Boundary

### Distinguish a full backend from a join engine

The current `Backend` trait asks an implementation to own table registration,
rule execution, table reads, merge semantics, primitive dispatch, and snapshots.
DD only delegates body-table matching to Differential Dataflow, so satisfying
that trait required a second implementation of the reference runtime's merge,
generation, subsumption, and action semantics around the join engine.[S1][S8]

There are two coherent architectures:

| Interface | Owns | Does not own |
| --- | --- | --- |
| `EGraphBackend` | authoritative tables, actions, merges, equality, rebuild, primitives, snapshots, and optional evidence | shared source lowering, proof DAG policy, formatting, checking |
| `JoinEngine` | compiling normalized body plans and returning bindings/deltas over a supplied stable relation view | table mutation, merges, UF/rebuild, primitive state, snapshots, proofs |

If DD remains a join accelerator, the second shape is smaller and avoids
duplicating core-relations semantics. The shared runtime would own one table and
merge implementation, feed relation changes into DD arrangements, and consume
bindings back. Such a component should not be advertised as a swappable e-graph
backend.

If the research goal is truly swappable full backends, use the first shape and
require the complete semantic conformance suite. A full backend must not rely on
the reference database for some state while maintaining different authoritative
rows elsewhere. This report recommends that clean boundary for the portability
research, while recognizing `JoinEngine` as a legitimate implementation option
for DD.

### One semantic e-graph IR

The frontend should compile into a backend-neutral `EGraphIr` that identifies:

- typed relations, functions, constructors, and equality sorts;
- table keys, defaults, merge behavior, and subsumption support;
- normalized rule bodies and ordered action streams;
- stable source IDs for rules, body atoms, action sites, top-level commands, and
  primitive call sites;
- schedules, iteration boundaries, and snapshot boundaries; and
- primitive/container descriptors and their declared capabilities.

This IR should preserve source correspondence, but it should not contain the
generated UF, view, self-loop, or proof tables used by the current encoding.

The backend should receive a whole normalized program and schedule, rather than
being constrained to reproduce the current bridge's internal lowering one call
at a time. That permits different backends to choose different query plans,
batch boundaries, indexes, and equality representations while sharing one
observable semantic contract.

### Illustrative backend API

The following is an API sketch, not a final Rust signature:

```rust
trait EGraphBackend {
    fn compile(&mut self, program: &EGraphIr) -> Result<ProgramHandle>;

    fn run(
        &mut self,
        program: ProgramHandle,
        schedule: &ScheduleIr,
        evidence: EvidenceMode,
    ) -> Result<RunOutcome>;

    fn execution_session(
        &mut self,
        context: ExecutionContext,
        origin: OriginId,
        evidence: EvidenceMode,
    ) -> Result<Box<dyn BackendExecutionSession + '_>>;

    fn query(&self, query: Query) -> Result<QueryResult>;
    fn canonicalize(
        &self,
        domain: EqualityDomain,
        value: Value,
    ) -> Canonicalized;
    fn equality_witness(
        &self,
        domain: EqualityDomain,
        left: Value,
        right: Value,
    ) -> Option<EvidenceToken>;

    fn snapshot(&self) -> Result<Snapshot>;
    fn restore(&mut self, snapshot: Snapshot) -> Result<()>;
}
```

The direct `query` method above is for observational queries against a stable
post-barrier state. A read performed during rule execution, a custom callback,
or any operation whose result can influence a later mutation must use an
execution session so its dependencies are captured.

Every conforming backend implements both `EvidenceMode::Off` and
`EvidenceMode::Record`. `Record` is therefore not an optional backend
capability, and there is no generated-encoding fallback. A backend that cannot
satisfy the evidence contract is not a proof-capable implementation of this
interface. A project may still expose a separate value-only backend profile,
but it must reject proof mode explicitly rather than silently switching to the
current encoding.

### Required e-graph semantics

The interface should specify observable behavior, not mandate a physical data
structure. A backend must implement:

1. Full-row schemas with explicit key and output arities; scans and keyed reads
   return the complete visible row.
2. Stable iteration read views and staged, emission-ordered action effects.
3. Deterministic keyed conflict resolution in which every output expression
   observes the same complete old/new output tuples.
4. Effectful merge operations, declared read dependencies, transaction-local
   lookup-or-insert, and fixed-point processing of merge-generated writes.
5. Row generations or equivalent seminaive event identity.
6. Subsumption, deletion, and lookup-or-insert behavior.
7. Declared equivalence domains with reason-producing canonicalization and
   union.
8. Deterministic preferred/actual leader behavior and evidence-opaque columns.
9. Incremental rebuilding and congruence after equality changes, including
   reasoned row rekeys, constructor collisions, and same-ID dirty outcomes.
10. A stable post-commit receipt boundary for actual winners and maintenance
   effects.
11. Backend-neutral execution sessions for standard reads, writes, primitive
   dispatch, and container operations.
12. Explicit capability negotiation only for language extensions outside the
   accepted core conformance profile.
13. Snapshot/restore behavior for both ordinary state and recorded evidence.

Items 1-6 now appear in the documented backend execution contract and are
exercised by the DD tuple/merge implementation.[S1][S11] Items 7-10 are
motivated by current native behavior plus the native-maintenance ablation; the
current public backend interface does not expose them as a portable,
reason-producing contract.[S1][M4] The DD backend requires the term encoding
because it has no native UF/rebuild implementation.[S8]

Under this proposal, a backend that cannot connect an execution session to its
authoritative live state is not fully conforming. The current DD implementation
would therefore remain an experimental partial implementation until its
execution-state operations target its mirror/dataflow state rather than only
its embedded primitive database and native equality is supplied or explicitly
excluded from a narrower profile. Its clone-based push/pop path satisfies the
current frontend capability but does not settle the cost or representation of a
general backend snapshot contract.[S8][M7]

## Generic Evidence Runtime

### Backend-visible representation

Backends should carry fixed-width opaque identities, not proof objects:

```rust
struct EvidenceToken(u64);
struct EqualityToken(EvidenceToken);

enum EvidenceMode {
    Off,
    Record(RecorderSession),
}
```

In recording mode, every semantic producer returns a token. Rows, predicted
rows, retained merge candidates, equality components, tombstones, and container
candidates retain the token needed by later operations. Events are accumulated
in backend-local batches and published at stable barriers. Proof terms are not
constructed in the execution hot path. The shared `RecorderSession` owns the
token namespace and event schema; backend code allocates or reserves tokens at
semantic commit points and transfers completed pages without callback reentry.

An earlier uncommitted event-transport experiment found that an after-the-fact
observer repeatedly missed producer classes and causal frontiers. Its review
identified predicted rows, merge candidates, UF components, tombstones,
container collisions, post-filter matches, and raw mutation paths as distinct
sources of required evidence. That experiment was never performance-tested and
is not evidence that the proposed representation is fast; it is evidence that
the producer census must be typed and complete before measurement.[M3]

RelationalV1 then implemented one such producer family. It demonstrated
deterministic post-commit token assignment for source facts and one-premise
relation insertion without proof objects, callbacks, or serial insertion. Its
single-thread wall checkpoint failed the selected `<1.25x` gate, and its public
mutation closure was incomplete. The result supports the representation's
narrow semantic feasibility while arguing for fusion with native table commit
rather than a separate full-row arbitration pipeline.[M5]

### Shared typed event vocabulary

The shared runtime should provide operations such as:

```text
source(action_site)
rule_application(rule_id, premise_tokens)
primitive_result(call_site, input_tokens, result_descriptor)
lookup_hit(row_token)
lookup_create(key, value, origin)
merge(old_token, incoming_token, retained_value)
equate(left, right, reason_token)
congruence(constructor, child_equalities)
canonicalize(old_value, representative, equality_token)
delete(row_token)
subsume(row_token)
container_normalize(input_token, output_descriptor)
```

The exact event set is a design task. The requirement is that it describe
semantic commit outcomes, not low-level implementation steps or pre-filter join
candidates.

### Shared proof ownership

The shared evidence runtime should own:

- the token namespace, event schema, and publication protocol;
- the immutable causal DAG;
- source and descriptor catalogs;
- deterministic witness selection;
- lazy conversion into the existing `ProofStore` representation;
- proof printing; and
- proof checking.

The backend owns the hot-path storage and actual-commit integration needed to
implement that protocol efficiently. This distinction lets every backend choose
its physical layout while keeping token meaning and proof algorithms shared.

A backend should not import or construct `Proof`, `RawProof`, `ProofStore`, or
checker AST nodes. The current proof format already separates proof
justifications from the runtime tables that produced them, which makes it a
reasonable shared output target.[S9]

## Equality Interface

The semantic contract should be an annotated equivalence relation, not a
requirement to store arbitrary objects on physical union-find edges:

```rust
canonicalize(domain, value) -> Canonicalized {
    representative,
    equality_token,
}

equate(domain, left, right, cause, preferred_leader) -> UnionOutcome {
    changed,
    preferred_leader,
    actual_leader,
    equality_token,
}

rebuild(epoch) -> MaintenanceBatch {
    row_rekeys,
    constructor_collisions,
    container_dirty_outcomes,
}
```

An implementation may use:

- a parent-pointer UF whose edges carry compact tokens;
- an ordinary UF plus an immutable explanation forest;
- a generalized/annotated UF; or
- a relational/dataflow representation satisfying the same contract.

Therefore, the interface does **not** require generalized data on every physical
UF edge. It requires an annotated-equivalence service capable of returning a
stable witness for canonicalization and equality, plus reasoned maintenance
receipts. A backend may realize that with annotated edges, a separate
explanation forest, persistent union history, or another representation.

For a parent-edge implementation, equality evidence needs identity, inversion,
and composition so path compression can replace a path with one composed token.
The team notes describe generalized UF in similar terms: annotations on
follower-to-leader edges and composition during path compression.[N1]

The native-maintenance ablation reproduced one checked congruence witness only
after canonicalization returned both a value and a cause. It also exposed
preferred/actual leader behavior, row rekeys, prefix collisions, same-ID dirty
containers, and a post-commit boundary as semantic requirements. That is direct
prototype evidence for the API shape, but not for its performance or
completeness.[M4]

The mutable canonicalization structure still cannot be the complete proof store
if proof selection depends on historical or no-change operations. A separate
immutable event graph can preserve those causes while edge tokens act as compact
references or caches. This remains a design inference from first-witness
requirements and the ablation, not a measured performance result.[M1][M3][M4]

## Execution Sessions and Custom Primitives

### Why this belongs in the architecture

Rule actions are not the only way egglog state changes. Top-level APIs,
constructor lookup-or-insert, container interning/rebuilding, merge functions,
and custom primitives all use execution-state operations.[S3][S4]

If these paths bypass evidence collection, a backend can reach a state whose
later derivations cannot be justified. Therefore, the target interface must
either record, explicitly trust, or reject every state-changing entry point.
This closure property belongs in the initial architecture even if every
operation is not enabled in the first release. RelationalV1's command guards
did not satisfy this requirement because a public Rust mutation could still
clear a recorded table without a deletion event.[M5]

### Backend-neutral execution session

The concrete core-relations `ExecutionState` should not be the cross-backend
contract: it directly exposes core-relations tables, buffers, counters, and
predicted-value machinery.[S3] Instead, preserve the existing user-facing
capability split while changing what the wrappers delegate to:

```rust
trait BackendExecutionSession {
    fn context(&self) -> ExecutionContext;
    fn origin(&self) -> OriginId;

    fn lookup(&self, table: TableHandle, key: &[Value]) -> LookupOutcome;
    fn lookup_or_insert(
        &mut self,
        table: TableHandle,
        key: &[Value],
    ) -> Produced<Value>;

    fn set(&mut self, table: TableHandle, row: &[Value]) -> MutationOutcome;
    fn remove(&mut self, table: TableHandle, key: &[Value]) -> MutationOutcome;
    fn subsume(&mut self, table: TableHandle, key: &[Value]) -> MutationOutcome;
    fn equate(&mut self, left: Value, right: Value) -> UnionOutcome;

    fn call_primitive(
        &mut self,
        primitive: PrimitiveHandle,
        args: &[Value],
    ) -> PrimitiveOutcome;
}
```

The sketch omits row iteration, table-size inspection, counters, base-value
conversion, container interning, and early-stop control for brevity. The current
typed states expose those operations, so the eventual portable session must
either include them with defined semantics or classify them explicitly as
backend-local.[S3][S4]

`PureState`, `ReadState`, `WriteState`, and `FullState` can remain the public
Rust API. They would wrap this backend-neutral session rather than a concrete
core-relations database view. Table and union handles should come from the
compiled schema, replacing the bridge-specific `ActionRegistry` as the
portability mechanism.

Every frontend mutation and every execution-time primitive or callback read
must route through this session, including public Rust methods such as table
clearing, external updates, custom rules, and container operations. Ordinary
backend-neutral queries may use `EGraphBackend::query` under the same
stable-view semantics. A direct backend/table escape hatch may exist for
backend internals, but it cannot be reachable from the portable proof-capable
surface. The conformance test is global mutation-path closure, not merely
command-parser validation.[M5]

All backends should therefore support the same **execution-session semantics**;
they should not be required to expose the same concrete core-relations
`ExecutionState`. The current low-level `ExternalFunction` interface takes a
concrete `&mut ExecutionState`, so it would either become an internal
main-backend API or be adapted to the backend-neutral session.[S3]

During a custom primitive invocation, the session can accumulate the evidence
tokens of rows actually read and make the invocation token a dependency of any
result or mutation. The Rust callback need not manipulate tokens itself. This
provides causal completeness, but it still does not prove that arbitrary Rust
control flow computed a valid result; that is the separate authority question
below.

In recording mode, callback dispatch should be transactional at the backend
boundary: validate authority and capabilities before invoking the callback,
execute reads against one stable session view, stage writes, and publish both
state and evidence only if the invocation succeeds. This can make backend state
atomic; it cannot roll back arbitrary process-external side effects performed
inside user Rust code, which is another reason unsupported callbacks must be
rejected before invocation.

Raw operations such as `stage_insert`, `stage_remove`, or direct table access
should not be part of the portable proof-capable API because they lack enough
semantic information to classify the resulting mutation. A concrete backend
may retain them as an explicitly nonportable internal escape hatch.

### Proof authority for custom operations

Recording that a Rust callback performed an operation is not the same as
independently proving that the operation was valid. The initial interface should
distinguish three authority models:

| Authority | Meaning | Checker treatment |
| --- | --- | --- |
| validated | shared validator recomputes the primitive result | check validator |
| certified | primitive supplies a certificate and shared verifier | check certificate |
| trusted | host application explicitly declares the operation an assumption | check against declared trust boundary |

The existing checker already uses validators for primitive expressions and
rejects primitives without them in proof-compatible programs.[S7] It does not
currently provide a general certificate or trusted-stateful-primitive mechanism.

Recommended first-version (`1.x`) scope:

- **In scope:** backend-neutral execution sessions; evidence-aware reads and
  writes; pure primitives with validators; explicit rejection before side
  effects when no proof authority is available; and conformance tests proving
  that no mutation path is invisible.
- **Potentially in scope after one design decision:** `EGraph::update` as a
  sequence of explicit external assumptions. The current `Fiat` checker accepts
  global-action equalities and reflexive literal equalities, so arbitrary API
  updates would require a synthetic source catalog or a checker-input
  extension.[S6][S9]
- **Deferred unless required for the first performance fixtures:** independent
  verification of arbitrary Rust `ReadPrim`, `WritePrim`, `FullPrim`,
  `rust_rule`, and `rust_rule_full` callbacks. Supporting these requires a
  certificate/trust design, not merely event recording.
- **Out of the portable interface:** unrestricted raw access to backend-specific
  tables and mutation buffers.

This scope does not make stateful primitives a permanent non-goal. It prevents
the initial performance experiment from silently weakening proof validity while
leaving a clear extension point.

All typed primitive contexts should work across conforming backends when
evidence is off. In recording mode, the session and causal capture are still
mandatory; only the authority to materialize an independently checkable proof
may be unavailable for a particular stateful primitive.

Put differently, backend-neutral execution-state support is **in 1.x scope**;
independent proof authority for arbitrary stateful callbacks may be deferred.
A deferred callback must fail before invocation in recording mode. It must not
run and then produce an under-specified or silently trusted proof.

## Responsibility Split

| Concern | Backend | Shared frontend/runtime |
| --- | --- | --- |
| Physical storage and indexes | owns | specifies semantics |
| Join planning and execution | owns | supplies normalized rule IR |
| Equality representation | owns | specifies annotated-equivalence contract |
| Incremental rebuild | owns | specifies observable congruence semantics |
| Carrying row/equality tokens | owns | defines token and event contracts |
| Executed-match identification | owns | supplies source/action IDs |
| Execution session implementation | owns | supplies typed user wrappers |
| Event DAG and descriptor catalog | publishes batches | owns |
| Witness selection | no | owns |
| Proof materialization and checking | no | owns |
| Proof syntax and output snapshots | no | owns |

This is the intended meaning of "proofs are abstracted away": proof language and
proof algorithms are shared, while evidence capture is integrated at backend
semantic commit points.

## Why a Single Generic Row Annotation Is Not Enough

The current execution contract includes ordered destructive updates, old/new
merge arbitration, lookup-or-insert predictions, row generations, deletion,
subsumption, and stable iteration views.[S1] A monotone provenance annotation on
the final set of rows does not by itself specify the history or selected cause
for these operations.

This does not rule out an algebraic formulation. It means the algebra must cover
typed state transitions and annotated equality, rather than only semiring-style
combination of monotone relation tuples. This is a design inference, not an
experimental result.

## Alternatives Considered

### Keep the current encoding as a fallback

**Not proposed.** It would maintain two proof implementations, preserve the
complexity the research is trying to characterize, and retain a path already
measured far above the eggcc target.[M1][M2]

The current encoding may be used temporarily as a differential oracle while the
new implementation is incomplete. It should not execute in the final runtime or
remain as a claimed compatibility path. Once the conformance suite and golden
proof corpus cover the required semantics, the encoding should be removed.

### Implement a complete proof system independently in every backend

**Not proposed.** It would preserve backend swappability only at the frontend
API level while duplicating witness selection, proof construction, and checker
integration. It would not answer whether proof production can be abstracted.

### Keep backends completely evidence unaware and observe them externally

**Not proposed as the main hypothesis.** An external observer cannot determine
all backend-internal outcomes from final rows alone, including which merge
candidate was retained, whether a constructor was created or found, which
equality path canonicalization used, and why rebuild merged two rows.[S1][S3]
An observer inserted into every internal operation becomes the evidence-aware
interface proposed here.

### Require a particular generalized UF implementation

**Not proposed.** The API should require canonicalization and equality witnesses,
not parent pointers or a particular annotation storage layout. Generalized UF is
one important implementation and research comparison.[N1]

## Research and Implementation Sequence

The sequence below is intended to test the abstraction, not to preserve two
production proof paths.

### Phase 0: Freeze semantics and evidence

1. Define `EGraphIr`, source IDs, execution epochs, and the observable update
   contract.
2. Promote the DD implementation's full-row, cross-column merge, dependency-order,
   fixed-point write, subsumption, and generation tests into a backend-neutral
   conformance suite; add predicted rows, equality, rebuilding, snapshots, and
   execution sessions.[S11]
3. Keep the proof format and checker as the semantic oracle. Treat snapshot
   changes as reviewable witness changes that must remain checker-valid rather
   than requiring byte-for-byte identity.

### Phase 1: Equality vertical slice

1. Implement the shared token arena and source catalog.
2. Implement native, domain-aware `canonicalize`/`equate` evidence in the main
   backend, including preferred/actual leader behavior.
3. Implement reason-producing native congruence/rebuild with post-commit rekey,
   collision, and dirty-container receipts.
4. Prove a small end-to-end case such as `a = b` implying `f(a) = f(b)` and
   require the existing checker to accept the materialized proof.
5. Remove the generated UF/index/self-loop/rebuild rules **and all eager
   concrete proof/View rows** from this path. The H1 ablation showed that doing
   only the first removal leaves proof extraction non-viable.[M4]

### Phase 2: Rule and table provenance

1. Fuse premise-token arbitration into native commit/index maintenance rather
   than retaining RelationalV1's separate full-row pipeline.[M5]
2. Carry premise tokens only for post-filter matches that reach actions.
3. Add token-bearing lookup, constructor creation, set, merge, delete, and
   subsume outcomes.
4. Close every public mutation path, not only parsed commands.
5. Replace duplicate term/view proof rows with compact sidecars on native rows.
6. Materialize proofs lazily from tokens.

### Phase 3: Containers and execution sessions

1. Add deterministic descriptors and evidence for container normalization and
   collision handling.
2. Route typed execution-session operations through the same mutation API.
3. Support validated primitives and reject unsupported stateful callbacks before
   side effects.
4. Decide whether external updates are assumptions, certified operations, or
   out of the first release.

### Phase 4: Second backend

Implement the same IR and evidence contract in a backend with a meaningfully
different execution model. The same shared runtime must materialize and check
the proofs. This phase is necessary before claiming that proof construction has
been abstracted rather than merely moved out of the main backend.

## Acceptance Criteria

### Semantic and proof criteria

- All existing proof-output tests pass.
- Materialized proofs pass the existing checker.
- Merge ordering, first-witness behavior, no-change operations, rebuild epochs,
  snapshots, containers, and seminaive generations have focused conformance
  tests.[M1][M3][M4][M5]
- Every public mutation path in recording mode either returns a producer token
  or rejects before side effects.
- Backends contain no proof-format or checker types.

### Portability criteria

- At least two backends execute the same `EGraphIr` and schedule semantics.
- Both implement the same execution-session contract.
- Both publish the same typed event vocabulary to the shared runtime.
- Backend-specific code is limited to storage, execution, equality/rebuild, and
  propagation of opaque evidence tokens.

### Performance criteria

The mission criterion remains an upper 95% confidence bound below `2.0x` for
`main/proofs / main/off` on every frozen fixture using the repository benchmark
methodology.[M1][S10]

A useful working budget, not yet an accepted project requirement, is:

- native maintenance plus evidence recording, before materialization, should
  have an upper wall-time bound near `1.5x` on every frozen fixture, leaving
  headroom for lazy witness selection and conversion;
- evidence-off mode should allocate no event pages or evidence-proportional
  per-row state; and
- profiling should show that generated term/view/UF joins are absent rather
  than merely hidden under a different name.

RelationalV1 does not satisfy this criterion: its `1.32x` synthetic point ratio
has no confidence interval, covers only one relation producer family, and omits
the more expensive equality, merge, container, and materialization work.[M5]
The DD compatibility result also does not satisfy it: integrated DD was
`3.511x` main in proof mode on the short mini-math probe, while the earlier
boundary run timed out on full math and did not complete eggcc.[M7][M8] The
only completion gate is still the full `<2x` frozen-fixture result.

## Accepted Constraints

- The current generated encoding may remain a temporary differential oracle,
  but it is not a production fallback in the proposed architecture.
- The proof format and checker contract remain shared. Proof snapshots need not
  remain byte-for-byte identical when a change is caused by a specific bug fix,
  merge-order clarification, or demonstrated nondeterminism, provided the new
  witness is semantically equivalent, checker-valid, tested, and documented.
- DD compatibility is useful evidence, but it is not a constraint on the first
  main-backend performance prototype.
- Proof-format types must not enter backend implementations in the target
  design; generic evidence tokens and semantic event types may.

## Open Decisions

1. **Trust model for external writes:** Should `EGraph::update` mutations become
   explicit assumptions, require certificates, or remain unavailable in proof
   mode?
2. **Stateful primitive authority:** Is a declared trusted primitive acceptable,
   or must every proof-affecting primitive supply a shared verifier?
3. **Evidence policy dispatch:** Should `Off` and `Record` be monomorphized
   backend variants or one runtime branch? This is a performance experiment.
4. **Snapshot identity:** How are tokens and source catalogs named across
   push/pop and cloned e-graphs?
5. **Concurrency:** Which ordering is semantic, and which ordering may vary
   across worker counts while preserving a deterministic selected witness?
6. **Second backend:** Which backend provides the strongest test that the
   interface is genuinely portable rather than shaped around core-relations?
7. **DD integration level:** Should DD remain a full experimental backend, or
   become a `JoinEngine` behind one shared state/merge implementation?
8. **Merge dependency cycles:** Should frontend lowering guarantee an acyclic
   merge-read graph, or should the backend contract define rejection or
   fixed-point semantics for cycles?

The first two decisions affect the initial supported surface. They do not block
writing the core backend/evidence interface, provided unsupported operations are
rejected atomically in recording mode.

## Evidence Review

This section records the review pass applied to the report.

### Established by current source or tests

- The current backend API and its stable-iteration, merge, generation, and
  subsumption semantics.[S1]
- The structure of the generated term/proof encoding.[S2]
- The concrete `ExecutionState`, predicted-value, and staged-mutation model.[S3]
- The typed primitive capability wrappers and bridge-owned action registry.[S4]
- Current proof-mode rejection of update/Rust-rule APIs.[S6]
- Validator-based checking of primitive expressions.[S7]
- The DD backend's join/host split, lack of native UF, and lack of action-registry
  support.[S8]
- Full tuple rows, atomic old/new tuple merge evaluation, effectful merge
  expressions, dependency-ordered reads, fixed-point generated writes, and
  proof-checker parity on the tested DD cases.[S11]
- Pure container primitives can be backend-neutral over base/container
  registries; registry-backed read/write/full primitives still require an
  authoritative execution-session integration.[S8][S11]
- The native-maintenance ablation's checked congruence canary, value-plus-cause
  requirement, and failure of eager proof-row extraction on the broader proof
  regression.[M4]
- RelationalV1's deterministic commit-only cause transport, byte-identical
  reports, matching state digests, focused tests, and independent code-review
  qualifications within its declared parsed-command subset.[M5]

### Established by measurement

- The five-fixture final wall-time and RSS results.[M1]
- The eggcc off/term/proofs split and profile attribution.[M2]
- The earlier dirty-prototype DD/main mini-math comparison.[M6]
- The full-math timeout and eggcc registry-boundary probe outcomes.[M7]
- The clean integrated DD/main mini-math wall-time and RSS comparison.[M8]

RelationalV1's timing is deliberately excluded from this category. Its values
are focused point observations without retained sample vectors or confidence
intervals, and its `<1.25x` wall gate failed.[M5] M7 is included only as a
measured boundary outcome; its one sample per cell cannot support a performance
ratio or variance claim.

### Supported design inferences, not proven results

- Native equality/rebuild without removing eager concrete proof rows is not a
  viable completion path.[M2][M4]
- Under the no-generated-proof-relations hypothesis, a full backend likely must
  preserve causal tokens internally to avoid incomplete after-the-fact
  observation.[M3][M5]
- A typed event vocabulary is more appropriate than a final-row-only annotation
  for egglog's destructive and ordered operations.
- A backend-neutral execution session is required for a clean cross-backend
  custom-primitive and container-rebuild story.[S3][S4][M5][M7]
- Evidence arbitration should be fused into native commit and maintenance
  paths rather than layered as a second full-row pipeline.[M5]
- A DD integration that owns only joins should use a narrower join interface;
  presenting it as a full backend necessarily assigns it the remaining table
  and transaction semantics.[S1][S8][S11]

### Explicitly unproven

- That the proposed interface will achieve `<2x`.
- That fixed-width tokens and lazy materialization will fit the proposed `1.5x`
  recording budget.
- Complete producer and public mutation-path closure.
- Collision-proof row authority, arbitrary-arity allocation behavior,
  compaction performance, and repeated recorder drains.
- That generalized UF is the best physical equality representation for every
  backend.
- That DD has full corpus parity, acceptable performance, native equality, or
  a native dataflow snapshot with measured restore cost. Its current deep-clone
  compatibility path reconstructs transient DD workers.[S8][S11]
- That arbitrary stateful Rust primitives can be independently verified without
  extending the current proof/checker contract.
- That a second backend can implement the proposed contract with acceptably
  little backend-specific evidence code.

## Evidence Appendix

### Current source and tests

- **[S1] Backend contract:**
  [`egglog/egglog-backend-trait/src/lib.rs`](egglog/egglog-backend-trait/src/lib.rs),
  especially the crate-level rule execution contract plus `Backend` and the
  complete `RuleSpec`; `FunctionConfig`, `MergeFn`, and `MergeAction` in
  [`egglog/egglog-bridge/src/lib.rs`](egglog/egglog-bridge/src/lib.rs).
- **[S2] Generated proof encoding:**
  [`egglog/src/proofs/proof_encoding.md`](egglog/src/proofs/proof_encoding.md),
  especially its term encoding, UF, view-table, rebuild, and proof-encoding
  sections.
- **[S3] Concrete execution state:**
  [`egglog/core-relations/src/action/mod.rs`](egglog/core-relations/src/action/mod.rs),
  especially `ExecutionState`, its predicted rows, and staged updates;
  external-function dispatch in
  [`egglog/core-relations/src/free_join/mod.rs`](egglog/core-relations/src/free_join/mod.rs).
- **[S4] Typed execution wrappers and action registry:**
  [`egglog/src/exec_state.rs`](egglog/src/exec_state.rs), especially
  `PureState`, `ReadState`, `WriteState`, and `FullState`;
  `ActionRegistry` in
  [`egglog/egglog-bridge/src/lib.rs`](egglog/egglog-bridge/src/lib.rs).
- **[S5] Current backend execution-state delegation:**
  `with_execution_state_tracked_dyn` in
  [`egglog/egglog-backend-trait/src/backend_impl.rs`](egglog/egglog-backend-trait/src/backend_impl.rs).
- **[S6] Proof-incompatible API behavior:**
  the proof-compatibility guard in [`egglog/src/lib.rs`](egglog/src/lib.rs),
  [`egglog/tests/api_proofs.rs`](egglog/tests/api_proofs.rs), and the
  `rust_rule`/`rust_rule_full` entrypoints in
  [`egglog/src/prelude.rs`](egglog/src/prelude.rs).
- **[S7] Primitive proof validation:**
  [`egglog/src/proofs/proof_checker.rs`](egglog/src/proofs/proof_checker.rs),
  especially primitive validation; unsupported-reason checks in
  [`egglog/src/proofs/proof_encoding_helpers.rs`](egglog/src/proofs/proof_encoding_helpers.rs),
  especially primitive lowering and validation requirements.
- **[S8] DD backend boundaries:**
  [`egglog-experimental/dd/src/interpret.rs`](egglog-experimental/dd/src/interpret.rs),
  especially `run_iteration` and `fused_bindings`;
  [`egglog-experimental/dd/src/lib.rs`](egglog-experimental/dd/src/lib.rs),
  especially `EGraph`, `requires_term_encoding`, capability flags, and
  `clone_boxed`; the hang/unsupported/mismatch taxonomy in
  [`egglog-experimental/dd/tests/files.rs`](egglog-experimental/dd/tests/files.rs).
- **[S9] Shared proof format and checker boundary:**
  [`egglog/src/proofs/proof_format.rs`](egglog/src/proofs/proof_format.rs),
  especially proof nodes and `ProofStore`; `Fiat` validation in
  [`egglog/src/proofs/proof_checker.rs`](egglog/src/proofs/proof_checker.rs),
  especially global-action and literal handling.
- **[S10] Benchmark methodology:** [`bench.py`](bench.py), especially
  `workload_command` and `fieller_interval`. Workloads run with `-j 1`; ratios
  use Fieller 95% intervals over equal-sized sample sets.
- **[S11] DD tuple/action merge implementation and tests:**
  [`egglog-experimental/dd/src/compile.rs`](egglog-experimental/dd/src/compile.rs),
  especially `MergeExpr` and `visit_read_dependencies`;
  [`egglog-experimental/dd/src/lib.rs`](egglog-experimental/dd/src/lib.rs),
  especially `MergeTransaction`, `translate_merge_program`, `add_table`, and the
  adjacent unit tests; [`egglog-experimental/dd/src/interpret.rs`](egglog-experimental/dd/src/interpret.rs),
  especially tuple-aware head execution and lookup; proof/container smoke tests in
  [`egglog-experimental/dd/tests/smoke.rs`](egglog-experimental/dd/tests/smoke.rs);
  pure container registration in
  [`egglog-experimental/src/lib.rs`](egglog-experimental/src/lib.rs) and
  [`egglog-experimental/src/container_primitives.rs`](egglog-experimental/src/container_primitives.rs).

### Measurement artifacts

The artifacts below are intentionally excluded from git. When this report is
shared outside the current worktree, attach those files separately or use the
recorded command and hashes to reproduce them.

- **[M1] Final benchmark and correctness audit:** the `Final Audit` section of
  local excluded artifact `.codex/proof-overhead-under-2x.md`. The raw 60-row
  final report is
  `.codex/proof-overhead-under-2x-data/final-d7f2532.jsonl`, SHA-256
  `001679eebf76ed8de8f3ab17e71eb6db23523f1b59dbc63595cd60f1e3ee27c1`.
- **[M2] Off/term/proofs diagnostic and profiles:** local excluded artifact
  `.codex/proof-overhead-under-2x-data/diagnostic-d1-d7f2532-evidence.md`,
  SHA-256
  `c88eb939dde3bd7271ebaa435bad04a76208794450cd109371480befaef51d65`.
  It records exact commands, samples, ratios, profile hashes, symbolization
  coverage, and limitations.
- **[M3] Retired event-transport design probe:**
  the retired event-transport section of
  `.codex/proof-overhead-under-2x.md`. The probe remained uncommitted and
  unmeasured; it is cited only for the producer/completeness audit, never as
  performance evidence.
- **[M4] Native-maintenance ablation and independent review:** the `H1
  Native-Maintenance Ablation Result` and `H1 Independent Review` sections of
  `.codex/proof-overhead-under-2x.md`. The retained desugared mini and
  congruence outputs have SHA-256
  `982eec23005133b10c887d79d55ad92d20aaab5c4946e13ede419261fa9f3928`
  and
  `70a86780e86769aba122c0d58388e5d1e9d4b29bdd218806c016b12d9b3e7e7e`.
  The sampled stalled `eqsolve` process is
  `/tmp/native-eqsolve.sample.txt`, SHA-256
  `24b5745b9ae7adda8b516f04ae1f9f3837615fd99f52b30a89df66a445958847`.
  The patch remains isolated and uncommitted in
  `/Users/saul/p/wt/egglog-encoding-native-maintenance-ablation`. A frozen
  changed-file bundle is
  `.codex/proof-overhead-under-2x-data/native-maintenance-d7f2532-files.tar.gz`,
  SHA-256
  `0ce33be8ef2ca2636aef1e2ae1c4fa43d42aedaa5645883636df2f07a2d8b6d2`.
  Its three output artifacts are bundled as
  `.codex/proof-overhead-under-2x-data/native-maintenance-d7f2532-output-evidence.tar.gz`,
  SHA-256
  `c3074bac74cd1cab26f46fe343d20d3d20242bb74719f00cc2c723f3cf4e1c97`.
- **[M5] RelationalV1 implementation and independent review:**
  `/Users/saul/p/wt/egglog-encoding-evidence-recorder-v1/relational_v1_evidence.md`,
  SHA-256
  `0b0166c2856cf4fdea30f88a29101e7221a42e6c61bbee0915aa8caa35a09018`,
  plus the `H2 Independent Review` section of
  `.codex/proof-overhead-under-2x.md`. The two retained record files are
  byte-identical and have SHA-256
  `a0c706419f07e945097f5d6446624a819aca12680c5232ffc6cd92cf2e3698e8`.
  The patch remains isolated and uncommitted in
  `/Users/saul/p/wt/egglog-encoding-evidence-recorder-v1`. A frozen
  changed-file bundle, including the handoff, generator, and verifier, is
  `.codex/proof-overhead-under-2x-data/relational-v1-d7f2532-files.tar.gz`,
  SHA-256
  `62d4ee7deb4a75a3d7a8a554567cda5a7f050038a49c49fb82a363b76baf44aa`.
- **[M6] Final DD/main mini-math comparison:** 12-row local report
  `/tmp/egglog-dd-tuple-final-20260713.jsonl`, SHA-256
  `7510896ca2ac5b2e4e4c78f1d72e1c32fc163d6d887c958939db7ba91be2844a`.
  It contains three fresh samples for each of main/DD crossed with term/proofs,
  records dirty base commit `fc86c37`, benchmark binary SHA-256
  `94a17d7f3b86e8eea9ed5963691f8d190ebe1130400003e8d765bc33a91fa46a`,
  and workload SHA-256
  `85b616bd104884035db922b24970d72023bc00255360651525beab9821e18223`.
  Command:

  ```shell
  ./bench.py --rounds 3 --force-run \
    --report /tmp/egglog-dd-tuple-final-20260713.jsonl \
    --backend main,dd --treatments term,proofs --timeout-sec 120 \
    --format markdown egglog/tests/math-microbenchmark-mini.egg
  ```

- **[M7] DD full-workload boundary probes:** four-row local report
  `/tmp/egglog-dd-tuple-full-probes-20260713.jsonl`, SHA-256
  `c7916898bd189068d3050599f65bb0675f3e3ff017c2861a74f7e0b608b91d67`,
  plus the post-container-registration DD eggcc rerun
  `/tmp/egglog-dd-eggcc-rerun-20260713.jsonl`, SHA-256
  `8e28833068055e7aa4235041db296f82cf1372a3f9fc79f2519aa36ab465b545`.
  Each cell has one sample, so these artifacts support only timeout/failure and
  mechanism claims, not ratio confidence intervals. Commands:

  ```shell
  ./bench.py --rounds 1 --force-run \
    --report /tmp/egglog-dd-tuple-full-probes-20260713.jsonl \
    --backend main,dd --treatments proofs --timeout-sec 120 --format markdown \
    egglog/tests/math-microbenchmark.egg \
    egglog-experimental/tests/fixtures/eggcc-2mm-pass1-merge-old.egg

  ./bench.py --rounds 1 --force-run \
    --report /tmp/egglog-dd-eggcc-rerun-20260713.jsonl \
    --backend dd --treatments proofs --timeout-sec 120 --format markdown \
    egglog-experimental/tests/fixtures/eggcc-2mm-pass1-merge-old.egg
  ```

- **[M8] Integrated DD/main mini-math comparison:** 12-row local report
  `/tmp/pr13-dd-integrated-mini-20260713.jsonl`, SHA-256
  `bd28740635b587953ae5f7067b720200f874cf4c919094a3402b1fa6e1052828`.
  It contains three fresh samples for each of main/DD crossed with term/proofs
  at clean commit `412fb580d293b38fe72bfb2057afba596829c9f3`, benchmark
  binary SHA-256
  `621025ec4f9bc8654106d307bf55761f41757d15b370ba2c9fd3f475873ea3c6`,
  and workload SHA-256
  `85b616bd104884035db922b24970d72023bc00255360651525beab9821e18223`.
  Command:

  ```shell
  ./bench.py --rounds 3 --force-run \
    --report /tmp/pr13-dd-integrated-mini-20260713.jsonl \
    --backend main,dd --treatments term,proofs --timeout-sec 120 \
    --format markdown egglog/tests/math-microbenchmark-mini.egg
  ```

The final benchmark command was:

```shell
./bench.py --target final=. --backend main --treatments off,proofs \
  --rounds 6 --timeout-sec 120 --force-run \
  --report .codex/proof-overhead-under-2x-data/final-d7f2532.jsonl \
  --format markdown \
  egglog/tests/math-microbenchmark-mini.egg \
  egglog/tests/web-demo/rw-analysis.egg \
  egglog/tests/integer_math.egg \
  egglog/tests/web-demo/resolution.egg \
  egglog-experimental/tests/fixtures/eggcc-2mm-pass1-merge-old.egg
```

### Team notes

- **[N1] Team meeting notes:** excluded attachment
  `/Users/saul/Downloads/egglog encoding project.md`, SHA-256
  `d0fa44527f4f2f442d824c0dd66dd6949b9c6885e5b9e25dfeabce04fedbc850`.
  Lines 40-52 ask whether
  native/generalized UF and custom rebuilding are necessary; lines 180-204
  discuss edge annotations and path-compression composition; lines 698-714 and
  778-787 connect the backend interface question to the `<2x` target; lines
  968-1011 discuss generalized UF as data/annotations on equality edges. These
  notes motivate the research question but do not substitute for benchmark or
  implementation evidence.

### Sharing package

The Markdown report is ready for team review on its own, but M1-M8 and N1 are
local or excluded evidence. For an independently auditable distribution,
attach:

- this report with both source identities shown at the top;
- `.codex/proof-overhead-under-2x.md` and the M1/M2 files named above;
- the two content-addressed changed-file bundles and the H1 output-evidence
  bundle;
- the M6/M7 historical JSONL reports, the clean M8 JSONL report, and integrated
  implementation commit `32d5507`;
- the N1 meeting-notes attachment; and
- the retained RelationalV1 record file if the recipient needs to rerun the
  standalone verifier rather than rely on its recorded hash and review.

Without those attachments, cite this document as a locally audited architecture
recommendation, not as a self-contained reproducibility package.
