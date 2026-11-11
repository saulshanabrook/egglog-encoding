# Frontend overhead: measurements and redesign options

## Status and decision

This is a read-only architecture and performance investigation on
`codex/frontend-overhead-minimization` at
`ffb8ae435bd6421077b1c15826f32a6aeecf5b1b`. No production code was changed.

The recommended first implementation is **typed proof/term lowering**, not a
general rewrite of the public type checker and not mandatory manual annotations
in user programs.

Today the proof encoder consumes already-resolved source commands, emits a new
surface program—often by formatting strings—and then sends that generated
program through parsing, desugaring, inference, global removal, and installation
again. The encoder already knows the introduced declarations and their sorts.
Preserving that information in a structural typed IR attacks all of the measured
frontend costs together and follows the architecture used by the surveyed
compilers.

The practical target should be stated in two ways:

- A 20% reduction in the **proof-over-off excess** requires saving 765.1 ms in
  this suite. The measured typecheck excess alone is 782.4 ms, so removing nearly
  all generated inference could just meet it.
- A 20% reduction in **total proof wall time** requires saving 1,382.8 ms. All
  measured typecheck and frontend excess is 1,472.9 ms, so this is barely inside
  the optimistic frontend ceiling and requires typed lowering plus a faster
  declaration/install path. A typechecker-only change cannot meet it.

This recommendation is deliberately narrower than “remove desugaring.” One
source parse, source validation, and several semantic lowerings must remain.
The avoidable part is treating generated internal code as source again.

## Measured baseline

The main experiment was:

```bash
./bench.py --detail rulesets \
  --report /tmp/egglog-frontend-overhead-ffb8ae4.jsonl \
  --force-run
```

It collected six fresh rounds for both endpoints on each of the default ten
files: 120/120 successful runs, one release binary, `proofs` versus `off`, and a
120-second per-process timeout. The target was clean when the rows were
collected.

The suite mean was 3,088.209 ms for `off` and 6,913.800 ms for `proofs`, a
3,825.591 ms delta. The suite ratio was 2.22–2.26x at 95% confidence; the point
estimate was 2.23877x, or 123.877% overhead.

| Exclusive mechanism | `off` mean | `proofs` mean | Delta | Share of added wall | Share of proof wall |
| --- | ---: | ---: | ---: | ---: | ---: |
| Typecheck | 83.241 ms | 865.636 ms | +782.395 ms | 20.452% | 12.521% |
| Parse | 17.068 ms | 198.409 ms | +181.341 ms | 4.740% | 2.870% |
| Other frontend lowering | 30.958 ms | 366.863 ms | +335.905 ms | 8.780% | 5.306% |
| Declaration/install | 61.877 ms | 235.158 ms | +173.282 ms | 4.530% | 3.401% |
| Program rules | 2,259.366 ms | 3,498.116 ms | +1,238.749 ms | 32.378% | 50.599% |
| Equality rules/native rebuild | 421.851 ms | 1,174.793 ms | +752.943 ms | 19.682% | 16.992% |
| Actions/checks/other commands | 150.732 ms | 409.966 ms | +259.234 ms | 6.776% | 5.930% |
| Residual | 63.117 ms | 164.860 ms | +101.743 ms | 2.660% | 2.385% |

`Frontend` in the benchmark report is parse + other frontend lowering +
declaration/install: +690.527 ms, or 18.050% of added wall. Typecheck + frontend
is +1,472.922 ms, or 38.502% of added wall and 24.091% of the proof endpoint's
absolute time.

### What “20%” means numerically

All projections below subtract observed endpoint-mean deltas. They are
optimistic ceilings, not forecast confidence intervals.

| Goal or counterfactual | Required saving | Resulting proof time | Resulting overhead |
| --- | ---: | ---: | ---: |
| Current measurement | — | 6,913.800 ms | 123.877% |
| 20% relative reduction in excess overhead | 765.118 ms | 6,148.682 ms | 99.102% |
| 20 percentage-point overhead reduction | 617.642 ms | 6,296.158 ms | 103.877% |
| 20% reduction in total proof wall | 1,382.760 ms | 5,531.040 ms | 79.101% |
| Eliminate proof-specific typecheck excess | 782.395 ms | 6,131.405 ms | 98.542% |
| Eliminate proof-specific typecheck + frontend excess | 1,472.922 ms | 5,440.878 ms | 76.182% |
| Physically impossible: erase all proof typecheck + frontend time | 1,666.066 ms | 5,247.734 ms | 69.928% |

The first target is realistic enough to use as an implementation gate. The
strict total-wall target is a stretch target: it requires removing about 94% of
the entire proof-specific typecheck/frontend excess. This is why a broad
typechecker cleanup has insufficient ceiling, while a typed lowering plus
direct installation is at least numerically capable of succeeding.

### Workload concentration

The suite aggregate is not a fixed startup tax. Luminal and eggcc together
account for about 74% of the +1,472.9 ms typecheck/frontend excess.

| Workload | Proof wall delta | Typecheck delta | Frontend delta | Typecheck + frontend share of that workload's delta |
| --- | ---: | ---: | ---: | ---: |
| Luminal | +1,576.212 ms | +444.382 ms | +358.377 ms | 50.9% |
| eggcc | +707.836 ms | +150.833 ms | +136.640 ms | 40.6% |
| Hardboiled | +195.741 ms | +54.396 ms | +49.822 ms | 53.2% |
| MISAAL | +110.933 ms | +53.090 ms | +49.385 ms | 92.4% |

MISAAL is the clean frontend-sensitive canary; Luminal is the bulk-cost canary;
eggcc is a representative mixed workload. Math remains important as a negative
control because frontend work is only a small fraction of its proof overhead.

### Clean CPU profile: MISAAL

A clean Samply profile ran the proof endpoint for 40 fixed MISAAL iterations
after all other profiling processes had exited. Inclusive sampled CPU was:

```bash
./bench.py profile \
  egglog/tests/papers/misaal-hvx-dot-product.egg \
  --treatment proofs \
  --iterations 40 \
  --profiles-dir /tmp/egglog-frontend-profiles-ffb8ae4 \
  --top 60 \
  --format markdown \
  --force-run \
  --timeout-sec 30
```

The artifact contains 6.007 seconds of observed CPU.

| Inclusive stack | Sampled CPU share |
| --- | ---: |
| `resolve_command` | 71.15% |
| `typecheck_program` | 44.65% |
| `typecheck_rule` | 37.38% |
| `Problem::solve` | 15.66% |
| `PrimitiveWithId::accept` | 7.80% |
| Generated + source parsing | 8.86% |
| `ProofInstrumentor::add_term_encoding` | 14.26% |
| `remove_globals` | 5.41% |
| Desugaring | 2.45% |
| `run_command` | 22.21% |

These are inclusive and overlap; they must not be added. Of the parse samples,
8.19 percentage points—92.3%—occur beneath the proof encoder. The profile
therefore localizes the parse tax to generated source, not the one user parse.
It also shows why annotations alone have a smaller practical ceiling than the
aggregate typecheck number: `Problem::solve` accounts for roughly one third of
the inclusive `typecheck_program` samples, while rule traversal, constraint
construction, primitive specialization, and resolved-tree annotation remain.
Rule checking accounts for 83.7% of inclusive typechecker CPU. Ordinary solver
work outside primitive re-specialization accounts for only 10.54% of total
sampled CPU. Under typechecking, 33.0% of leaf CPU was in `libsystem_malloc` and
11.4% in `libsystem_platform`, pointing to allocation, cloning, hashing, and
assignment-map traffic in addition to inference logic.

The independent six-round exclusive timing for the same fixture agrees:
145.719 ms proof wall, of which typecheck was 64.488 ms, parse 12.348 ms, other
frontend lowering 26.734 ms, and install 23.015 ms. The profile artifact is:

`/tmp/egglog-frontend-profiles-ffb8ae4/v4/61e24f12c4bb93029dea07e097aef50deb5f5e3d558f6b348b9debe8cb243a53/fff7843c2ae50c811bb6e57e6a6a317ee0dfa575d0cd61cd47cbbff484ead1c6/no-facts/proofs-i40.json.gz`

A 20% MISAAL endpoint improvement is 29.144 ms/run. Recovering about 54.9% of
its 53.090 ms proof-specific typecheck delta would cross that canary gate, so it
is demanding but does not require a perfect frontend elimination.

### Fixed-cost controls

An empty file was measured for 30 rounds:

```bash
./bench.py --detail phases --rounds 30 \
  --report /tmp/egglog-frontend-empty-ffb8ae4.jsonl \
  --force-run /tmp/egglog-frontend-empty.egg
```

The mean wall delta was +0.049 ms and the ratio CI was 0.969–1.06x. This
falsifies cloning/startup as a meaningful wall-time target, although the empty
proof process used 1.08x peak RSS.

A tiny nonempty file (`egglog/tests/i64.egg`) measured +0.435 ms mean wall time
and a 1.06–1.15x ratio across 30 rounds. Its typecheck + frontend delta was only
+0.223 ms. The suite-scale costs therefore grow with the encoded program.

## Where the frontend time comes from

### Current execution path

The proof path is structurally:

```text
source text
  -> Command AST
  -> sequential command macros
  -> NCommand (source desugaring)
  -> ResolvedNCommand (source typecheck in retained EGraph)
  -> typed proof-normal form
  -> remove_globals
  -> proof/term encoder
  -> generated text / unresolved Command
  -> parser
  -> NCommand (generated desugaring)
  -> ResolvedNCommand (generated inference)
  -> remove_globals again
  -> install / core lowering / bridge
```

The repeated generated loop is visible in
`egglog/src/lib.rs:2620–2737`. `resolve_command_before_proofs` first desugars and
typechecks the source command in `original_typechecking`; after encoding,
`resolve_command_inner` calls `desugar_command`, `typecheck_program`, and
`remove_globals` for every generated command.

The repository already has the right typed boundary:

- `NCommand = GenericNCommand<String, String>` is the desugared untyped form.
- `ResolvedNCommand = GenericNCommand<ResolvedCall, ResolvedVar>` adds resolved
  heads, leaves, and sorts.

Those aliases are documented in `egglog/src/ast/mod.rs:77–94`. The proof encoder
starts with the latter but returns `Vec<Command>` from
`ProofInstrumentor::add_term_encoding` at
`egglog/src/proofs/proof_encoding.rs:407–412`.

### Generated source is a material expansion

Fresh structural measurements used the existing release binary with
`--mode desugar`. These are size/count measurements, not timing claims.

| Fixture | Mode | Bytes | Emitted command-line proxy | Rules |
| --- | --- | ---: | ---: | ---: |
| MISAAL | off | 281,892 | 468 | — |
| MISAAL | proofs | 1,105,606 | 1,031 | — |
| eggcc | off | 570,604 | 1,149 | 660 |
| eggcc | term | 1,733,236 | 2,546 | 1,203 |
| eggcc | proofs | 3,398,528 | 2,599 | 1,203 |
| Luminal | off | 515,895 | 3,934 | 491 |
| Luminal | term | 4,274,991 | 9,601 | 2,429 |
| Luminal | proofs | 10,325,257 | 9,654 | 2,429 |

Proof mode emits 3.92x as many bytes as off for MISAAL, 5.96x for eggcc, and
20.0x for Luminal. Term and proofs differ by only 53 command lines in both
eggcc and Luminal, but proof payloads roughly double the term-mode bytes.
Equality infrastructure drives the command/rule expansion; proof columns and
terms make the bodies much larger. The command metric is a formatting proxy:
it counts emitted lines beginning with `(` at column zero, not parser-confirmed
AST nodes.

The four `proof_encoding*.rs` implementation files contain 17 static edges into
generated-text parsing helpers: 12 program/local-action parses, two fact parses,
two expression parses, and one schedule parse. The wrappers are in
`egglog/src/proofs/proof_encoding_helpers.rs:473–631`. Examples include UF and
view declarations, query facts, rebuild rules, instrumented source rules,
schedules, extract setup, and the proof header.

### Current type inference is local, not whole-program inference

The proposed manual-annotation strategy assumes a global inference problem, but
that is not the current shape:

- `typecheck_program` walks commands sequentially
  (`egglog/src/typechecking.rs:463–471`).
- Each rule creates and solves a fresh `Problem`
  (`egglog/src/typechecking.rs:1246–1306`). Standalone actions use the same
  pattern.
- `Problem::solve` repeatedly scans all constraints until no assignment changes
  (`egglog/src/constraint.rs:741–759`).
- Function atoms get direct assignments from declared schemas. Polymorphic
  primitives are the main overload/XOR case.

After solving, annotation walks the tree again and resolves each call.
`ResolvedCall::from_resolution` scans primitive candidates, and
`PrimitiveWithId::accept` constructs and solves another constraint problem for
each candidate. A later checker optimization should carry the selected
primitive alternative out of solving instead of re-specializing it during
annotation.

There is also a small tactical duplication: `typecheck_rule` obtains query
constraints into an unused vector before `Problem::add_rule` builds them again.
Profiling bounds the entire affected `Query::get_constraints` work at roughly
1–2% of typechecking, so deleting it is worthwhile cleanup but not a route to
the performance goal.

There is real room for a worklist solver and expected-type checking, but the
source/off typecheck is only 83.2 ms across the suite. The much larger problem
is running even a local checker over a generated program that is many times
larger than the source representation.

### Install is not merely inserting declarations

Each generated resolved command still passes through `run_command`
(`egglog/src/lib.rs:2010–2052`). Function installation re-resolves schema names
even though `ResolvedFunctionDecl` already holds a resolved schema
(`egglog/src/lib.rs:1046–1105`). Rules are canonicalized, translated, and built
through the bridge. Directly producing a bridge rule does not automatically
remove plan assembly: `RuleBuilder::build` stores `cached_plan: None`, and the
plan is constructed later.

This makes a staged approach safer: remove the repeated source frontend first,
then optimize typed registration and fixed generated templates based on fresh
timings.

## Answers to the proposed directions

### 1. Manual annotations and a fully downward-directed checker

**Useful experiment, wrong first architecture.**

Manual annotations can help when they choose an overload, instantiate a
polymorphic primitive, or let an expected sort flow down through a subtree. But
there are two materially different proposals:

- **User-source annotations** mostly optimize the source check already present
  in `off`. Even erasing the entire 83.2 ms source/off typecheck is only 1.2% of
  proof wall and largely cancels in a proof-versus-off comparison.
- **Generated textual annotations** can reduce part of the proof-specific
  solver work, but still pay formatting, parsing, AST allocation, desugaring,
  constraint creation, resolved-tree annotation, `remove_globals`, and
  installation. Textual ascriptions also enlarge an already large generated
  program.

A better eventual public checker would expose both operations:

```text
synth(expr) -> sort
check(expr, expected_sort) -> typed_expr
```

Declared function applications and generated nodes normally have an expected
result sort, so `check` can be deterministic and local. Synthesis remains for
leaves and genuinely ambiguous source expressions. Require user annotations
only at boundaries where no expected sort exists; do not require every user to
fully annotate every term.

If a fully directed public fast path is later added, rule-variable binders must
be collected before checking facts so fact order remains semantically
irrelevant. Polymorphic primitives still need all argument sorts, an expected
output sort, and the execution context. Partial annotations merely seed the
current solver; complete annotations justify a different single-pass checker.

This direction matches local/bidirectional inference research, but it should be
introduced after generated inference is bypassed. Otherwise a risky public
checker rewrite is being used to compensate for an avoidable IR round trip.

Recommended annotation experiments before any syntax change:

1. Add counters for constraint count, solver sweeps, XOR candidates, and
   unresolved variables, split between source and generated commands.
2. Seed expected sorts for generated primitive applications without changing
   public syntax.
3. Replace full rescans with a dependency worklist on one branch and measure
   typecheck time, not just solver iterations.

Stop if these do not save at least 0.6 seconds suite-wide: they then cannot
provide even a 20-percentage-point overhead reduction alone.

### 2. Emit typed code in the encoding

**This is the recommended first implementation.**

The encoder already knows the schema of every synthetic term, view, equality,
path-compression, and proof relation. It should construct typed objects rather
than print assertions and ask the public frontend to rediscover their meaning.

The lowest-risk intermediate is for the encoder to produce
execution-bound `ResolvedNCommand`. This removes generated parsing, generated
desugaring, and generic inference while retaining the existing
installation/core-lowering path. It may still carry string names and duplicate
some resolution work.

There is an important feasibility constraint: proof mode has two type/runtime
universes. Source commands are resolved in the cloned `original_typechecking`
EGraph; generated commands are registered and executed in the outer EGraph.
`ArcSort`, resolved primitive IDs, and similar handles from the source checker
cannot simply be copied into the execution checker. The typed encoder needs an
explicit declaration registrar/rebinder keyed by stable sort and function
identities. It registers each generated schema in the outer `TypeInfo`, creates
outer-runtime primitive/function handles, and returns commands bound to that
environment.

This registrar is also semantically necessary. `typecheck_command` currently
does more than inference: generated declarations register sorts, primitive
entrypoints, union-find metadata, mint/set-if-empty primitives, and container
rebuild behavior. Those state effects must be factored out before the second
typecheck can safely disappear.

The higher-ceiling form is a narrower `EncodedCommand`/typed core layer with:

- stable `SortId` and function/relation handles;
- typed expressions, facts, actions, rules, declarations, and schedules;
- explicit origin metadata: source span, lowering pass, and generated role;
- builders that enforce arity and child/result sorts locally;
- a linear verifier for scope, declaration order, IDs, arities, sorts, and
  ruleset invariants;
- a pretty-printer used only for `--mode desugar`, snapshots, and debugging.

This does **not** mean trusting arbitrary asserted types. It means checking
transform-local invariants instead of reconstructing a general inference
problem from generated source.

Measured ceiling by boundary:

| Proposed boundary | Directly targeted measured excess | Best-case share of proof wall | Assessment |
| --- | ---: | ---: | --- |
| Text annotations through current frontend | At most 782.4 ms typecheck | 11.3% | Cheap ablation; likely far below ceiling |
| Direct `Command` AST, still desugar/typecheck | 181.3 ms parse, plus some `frontend_other` allocation | 2.6% directly measured | Useful migration step, not goal |
| Typed `ResolvedNCommand` lowering | 1,299.6 ms typecheck + parse + other-lowering excess | 18.8% | High-value first architecture |
| Typed lowering + resolved declaration install | 1,472.9 ms including install excess | 21.3% | Only frontend design capable of strict 20% total-wall target |
| Direct bridge templates | Also targets part of 526.0 ms added rule assembly | Separate campaign | Higher risk; use only for measured fixed templates |

The typed-lowering rows are optimistic upper bounds. A verifier, builder work,
and unavoidable source checking remain, so the implementation must be accepted
or rejected by end-to-end measurements.

### 3. Remove or reimplement desugaring

**Do not delete desugaring as a concept. Split it by semantic dependency and
remove source-to-source boundaries from internal lowering.**

Classify transformations into three groups:

1. **Type-transparent surface normalization.** Convenient grouping or syntax
   whose expansion does not depend on inferred sorts can lower structurally
   before checking.
2. **Type-directed elaboration.** Overloads, implicit behavior, polymorphic
   instantiation, and any expansion selected by a resolved sort lower after
   typechecking into typed core nodes.
3. **Proof/term encoding.** This is a typed-to-typed compiler pass, not a second
   source program.

The existing `desugar.rs` is only about 480 lines and contains real semantics
for datatype, relation, rewrite, prove, and related forms. Deleting the file
would simply move those semantics elsewhere. Generated commands, however, are
already normalized sorts/functions/indexes/rules/actions/checks/schedules and
do not need to visit the public desugarer at all.

Globals need an explicit design rather than pass deletion. Today
`remove_globals` represents a global as a nullary function plus a set and
injects reads into rule bodies. A direct typed path can encode that once, or
teach core lowering the semantics. It cannot currently pass globals through:
the rule translator rejects them and `run_command` rejects surviving `let`
commands.

## What other compilers do

The surveyed implementations disagree about the exact placement of sugar, but
agree on the important boundary: internal passes exchange structural IR with
resolved identities, types, and provenance. None uses pretty-print/reparse as a
normal internal phase boundary.

| System | Primary-source design | Lesson for egglog |
| --- | --- | --- |
| Rust | Rust structurally lowers AST to HIR, removing some sugar; after typechecking, [THIR](https://rustc-dev-guide.rust-lang.org/thir.html) records every expression's type and makes type-directed behavior explicit. Its [HIR lowering guide](https://rustc-dev-guide.rust-lang.org/hir/lowering.html) distinguishes structural lowering, and the checker supports [expected types](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_hir_typeck/fn_ctxt/struct.FnCtxt.html). | Lower type-transparent syntax early and type-directed constructs after checking; consume typed nodes in the encoder. |
| Swift | Swift documents constraint generation, solving, and solution application into a fully checked expression. It deliberately limits inference to an expression or statement and uses connected components/worklists for performance in its [type checker design](https://github.com/swiftlang/swift/blob/main/docs/TypeChecker.md). | Annotations help overload search; scope inference locally and materialize the resolved result instead of inferring generated code again. |
| OCaml | OCaml's [compiler frontend](https://ocaml.org/docs/compiler-frontend) produces a `Typedtree`; expressions retain types, locations, environments, and resolved paths in the [Typedtree API](https://ocaml.org/p/ocaml-compiler/latest/doc/compiler-libs.common/Typedtree/index.html). `Translcore` maps it directly to Lambda. | Use a typed command tree as the handoff to encoding and installation; text remains an I/O/debug format. |
| GHC | GHC typechecks rich Haskell syntax and directly desugars it to a much smaller, explicitly typed [Core language](https://ghc.gitlab.haskell.org/ghc/doc/libraries/ghc-9.15-inplace/src/GHC.Core.html). [Core Lint](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/debugging.html) checks internal invariants. | Produce a small typed proof core and use a cheap verifier rather than rerunning public inference. |
| MLIR | [Dialect conversion](https://mlir.llvm.org/docs/DialectConversion/) performs progressive typed structural rewrites with explicit legality and type conversion. Operation definitions generate [operand/result verification](https://mlir.llvm.org/docs/DefiningDialects/Operations/); transformed nodes retain [location attributes](https://mlir.llvm.org/docs/Dialects/Builtin/#location-attributes). | Typed builders, verifier rules, and origin chains allow incremental migration without losing diagnostics. |
| Soufflé | The closest Datalog analogue parses and checks Datalog, then translates it to RAM. The current checker operates [clause by clause](https://github.com/souffle-lang/souffle/blob/master/src/ast/transform/TypeChecker.cpp), and its [AST-to-RAM translator context](https://github.com/souffle-lang/souffle/blob/master/src/ast2ram/utility/TranslatorContext.cpp) consumes cached type analyses directly. The overall architecture is described in the [Soufflé paper](https://www.souffle-lang.com/pdf/cav16.pdf). | Keep checking local and translate typed structural rules directly to execution/install structures. |
| Local type inference | Pierce and Turner's [Local Type Inference](https://www.cis.upenn.edu/~bcpierce/papers/lti-toplas.pdf) uses adjacent syntax and expected types to reconstruct omitted annotations into a fully typed internal language. | Add synth/check modes and annotations at ambiguity boundaries, not mandatory annotations everywhere. |

The common pattern supports typed structural lowering, but not unchecked typed
input. Rust, Swift, GHC, MLIR, and Soufflé all retain validation at the
appropriate IR boundary.

## Recommended target architecture

```text
text -> Surface Command -> source normalization -> source typecheck/elaboration
                                                        |
                                          source-bound typed IR
                                                        |
                                               proof/term encoder
                                                        |
                                   generated typed schemas + commands
                                                        |
                          execution registrar/rebinder -> verify
                                                        |
                                      execution-bound TypedCommand
                                                        |
                                                install/core
```

More concretely:

1. Parse and validate user syntax once.
2. Preserve resolved names, schemas, and sort identities across proof-normal
   form and proof/term lowering, without copying EGraph-local runtime handles.
3. Rebind generated schemas once into the execution EGraph through an explicit
   declaration-state API.
4. Make both the source frontend and proof encoder converge on one
   execution-bound typed command interface.
5. Validate generated commands with local builders plus a linear IR verifier.
6. Register resolved declarations without general name-to-sort inference a
   second time.
7. Keep core canonicalization and the bridge shared initially.
8. Move fixed UF/view/rebuild templates directly to bridge builders only after
   their assembly time is separately measured.

This architecture also gives diagnostics a principled home. Generated nodes
should carry `GeneratedFrom { source_span, pass, role }`-style origins rather
than fabricated text spans. Multiple origins can be fused when one generated
rule derives from multiple source constructs.

## Staged implementation and falsifiable gates

### Stage 0: make the profile causal

Split the current timers into:

- source macro/desugar;
- source typecheck;
- proof-normal form/support checks;
- encoder construction;
- generated parsing;
- generated desugaring;
- generated typecheck;
- generated global removal;
- typed declaration install;
- source-derived versus fixed-template rule assembly.

Also count generated bytes/nodes, constraints, solver sweeps, overload choices,
and declarations/rules by encoding family. This stage changes no semantics and
prevents optimizing a misleading aggregate.

### Stage 1: typed pilot

First factor the generated-declaration state effects out of
`typecheck_command`. Then convert one high-volume family—term/view declarations
plus rebuild rules—to a typed builder which registers/rebinds schemas into the
execution environment and returns execution-bound `ResolvedNCommand`. Keep the
text emitter behind a test-only comparison path.

Acceptance gates:

- identical normalized declarations/rules after generated-name and span
  sanitization;
- strict proof tests match;
- no regression in off mode;
- at least a 10% end-to-end MISAAL improvement or a clear reduction in the
  newly split generated frontend phase before broadening.

### Stage 2: remove generated source from execution

Convert generated facts, expressions, actions, checks, schedules, and remaining
declarations. Delete the 17 parser edges from the production path. Preserve a
pretty-printer for `--mode desugar` and snapshots.

Primary gate: at least 20% reduction in proof-over-off excess on the full ten
file suite, with Luminal and eggcc individually non-regressing outside measured
uncertainty. The completed MISAAL path should also save at least 29.144 ms/run,
which is a 20% proof-endpoint improvement on the measured mean.

### Stage 3: complete typed registration and globals

Generalize the pilot registrar into the single declaration path for every
generated sort/function/index. Make it update type state and runtime state from
resolved schemas exactly once. Lower generated globals directly. Remove the
second `remove_globals` and duplicate schema lookup.

Stretch gate: 20% reduction in total proof wall time on the suite. If Stage 2
does not leave enough install/frontend time to cross this gate, stop treating
the remaining gap as a frontend problem.

### Stage 4: source checker improvements, if still material

Only after generated inference is gone:

- replace constraint rescans with a dependency worklist;
- add `check(expr, expected_sort)` alongside synthesis;
- cache immutable declaration/signature resolution;
- consider annotations only at ambiguous public boundaries;
- replace the retained full typechecking `EGraph` with a frontend environment
  if RSS or clone/setup profiles justify it.

The empty control says the last item is not currently a wall-time priority.

### Stage 5: separate assembly campaign

If rule assembly remains material, measure and hoist or cache plans for fixed
generated templates. Do not route all source-derived rules directly to the
bridge merely to chase this number; `add_rule` currently centralizes important
canonicalization, context, and groundedness behavior.

## Validation matrix

Every performance claim should include:

- balanced or reversed endpoint order;
- at least six full-suite rounds and a reported ratio confidence interval;
- exclusive phase deltas and generated-node counts;
- MISAAL, Luminal, eggcc, and Math canaries;
- `make check` for repository correctness;
- `make benchmark-smoke` for benchmark-facing changes;
- strict proof snapshots/tests, not only generation or `--mode desugar` output.

The implementation should be stopped or reframed if the optimistic measured
lower bound cannot meet the selected 20% gate. In particular, parsing-only work
has a measured ceiling of 181.3 ms and should not be sold as a suite-level 20%
project.

## Evidence, caveats, and artifacts

- Main raw report:
  `/tmp/egglog-frontend-overhead-ffb8ae4.jsonl`
- Empty control:
  `/tmp/egglog-frontend-empty-ffb8ae4.jsonl`
- Tiny-input control:
  `/tmp/egglog-frontend-i64-ffb8ae4.jsonl`
- Structural output:
  `/tmp/frontend-{eggcc,luminal}-{off,term,proofs}.egg`

One exploratory term-versus-off timing run overlapped another machine profiler
and produced very wide confidence intervals. It is rejected and is not used in
any number or conclusion above.

The reported phase floors use endpoint means and do not propagate uncertainty
through counterfactual subtraction. They are useful for rejecting
insufficient-ceiling ideas, not predicting the exact speedup of an
implementation. The full-suite before/after benchmark remains the decision
criterion.
