# SpEQ frontend PHI repair — measured diagnostic and opt-in capture

The first isolated repair is concrete and deliberately limited to PHI polarity.
The original application C, reference FIR/rules, source pipeline, and schedules
are unchanged. This working-artifact correction is separate from the historical
seven capture/replay successes and makes no universal C-equivalence claim.

## Actual guarded result

The real LLVM17 diagnostics have now run. Evidence is retained below
`/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/`:

- `speq-phi-diagnostic-0001` stopped after the LLVM version query because the
  diagnostic receipt writer could not JSON-encode a Path. No compiler ran.
- `speq-phi-diagnostic-0002` compiled and ran both exact-function harnesses.
  Original direct-true bypass checks fail; the patched function passes all
  **21 checks**. Full plugin compilation then revealed the omitted custom
  `MemorySSA.h` prerequisite; original failed evidence remains unchanged.
- `speq-phi-diagnostic-0003` includes that unchanged pinned header (SHA-256
  `99eebae9253222fd998975546537fe47740c2979d5afdcf608a7a6efc353289e`), verifies the
  retained successful harness evidence, and successfully compiles the full
  plugin in 2.768 seconds. All four reference FIR hashes are exactly unchanged.
  The peak observed process-group RSS was 347,389,952 bytes. Every native child
  used the guard with a 5-GiB cap, 10-GiB disk reserve and 60-second timeout.
- The retained actual Parboil LLVM emits corrected conditionals:
  `%cmp17.not` selects `%call4` on true and `%call4.4` on false;
  `%cmp111.not` selects `%call4.3` on true and `%call4.5` on false.
  Patched FIR SHA-256 is
  `e39047bb895e5da07522ef008ca76ca0d9cea2d97a7b187e3eae6279e4876b27`.
- The unchanged original reference rules and 5/1/3 schedule still detect
  **Histogram**, with native extraction cost **108** (historical inverted-PHI
  lane: 80). This is one matched diagnostic region, not a fresh original-C
  capture, ordinary replay admission, optimality claim or universal source-C
  equivalence proof. The native selected term and logs are retained in
  `speq-phi-diagnostic-0003/eqsat-result.json`; `run.json` binds every input,
  command, output and predecessor diagnostic hash.

The normal capture opt-in is integrated and **the complete original-C Parboil
run passed on 2026-09-25**, followed by ordinary standalone replay. The native
run took 3.80 seconds with about 364 MiB peak RSS; these are acquisition
diagnostics, not performance samples. Its immutable evidence is
`benchmarks/local/reproduction/stages/speq-parboil_hist/complete/43e3d2760620007472e9a4eb722799e51cbe2190ab1afa29ce26b1e295074d02/attempt-0001/capture-result.json`.
This confirms this source case under the repaired frontend; other cases must
pass their own full captures. The opt-in is wired as follows:
settings `phi_polarity_repair: true` maps to Namespace
`speq_phi_polarity_repair`, public `--speq-phi-polarity-repair`, and recorder
`--repair-phi-polarity`. The recorder requires complete mode, rejects supplied
prebuilt plugins, and builds from freshly materialized patched sources only
after original source/header hash checks. The adapter records why it omits a
configured historical plugin. Source/patch/original/patched hashes appear in
`phi_repair_evidence`, alongside the actual compiled plugin hash. Defaults retain
the historical frontend. No Polybench repair or reference change is included.

`SPEQ-PHI-OPT-IN.patch` covers nine owned code/test files against current live
baselines, including the missing-header preparation closure. **101 focused
lightweight tests**, Ruff and Mypy pass. Two unchanged test dependencies
(`reproduction_validation.py`, `hardboiled_replay.py`) were refreshed from live
root in the mirror so DialEgg tie-contract tests can run; they are not in the
handoff patch. Root owns dispatch/identity threading and actual recapture.

## Files and current evidence

- `scripts/speq_phi_diagnostic.py` validates the pinned REV and custom MemorySSA source hashes, writes
  immutable originals, an isolated patched source tree, a unified patch, and
  original/patched LLVM harnesses. It never compiles, runs a tool, or changes
  recorder/capture/admission code.
- `scripts/paper_benchmarks/speq_phi_harness.cpp` is a native **analysis** harness;
  its `getPhiBr` implementation is inserted verbatim from each source variant.
  It builds a real LLVM dominator tree and MemorySSA for the fixture, then checks
  scalar PHIs and MemoryPhis, including reversed MemoryPhi incoming order. Input
  LLVM is parsed/verified but never executed.
- `scripts/paper_benchmarks/speq_phi_fixtures.ll` has direct-true bypass,
  direct-false bypass, two-sided diamond, reversed scalar incoming order for each,
  and an unsupported switch merge. Stores and scalar values independently encode
  true/false semantics. Expected patched outcome is 21 checks, zero failures;
  the original should fail the direct-true bypass in at least one incoming order.
- `tests/test_speq_phi_diagnostic.py`: six lightweight tests pass, including exact
  patch scope, source hash rejection, immutable materialization and an independent
  fixture branch/value oracle. Ruff and Mypy pass. The actual pinned source passes
  the patch hash/anchor gate; `SPEQ-PHI-REPAIR.patch` is its exact three-hunk diff.
  Native results are now recorded in the preceding section; the remaining
  full Parboil capture and ordinary replay now also pass, as recorded above.

The root's retained evidence remains authoritative:
`benchmarks/reproduction/speq-recovery.md`,
`benchmarks/local/reproduction/speq-polarity-diagnostic/memoryssa.stderr.log`, and
`benchmarks/local/reproduction/speq-scalar-no-gvn/{analysis.ll,probe.stderr.log}`.

## Exact failed invariant and repair

At pinned `REVPass.cpp:1818–1830`, the source assumes that failure of the true
successor to dominate incoming predecessor 0 implies predecessor 1 is true.
This is false for a direct true edge into the merge: the merge dominates neither
predecessor. The Parboil inner `%cmp17.not` and outer `%cmp111.not` have precisely
that shape. Incoming ordering changes the emitted result.

The replacement examines both incoming edges. A predecessor equal to the
conditional branch block is classified by which successor is the PHI merge.
Other predecessors must be dominated by exactly one non-merge successor. The
method requires a conditional branch and one distinct true/false predecessor;
unrecognized control flow returns null. `translatePhi` checks that result and
reports a precise unsupported-shape error before reading incoming values. Both
`PHINode` and const `MemoryPhi` callers are covered. No rule reversals, source-C
rewrites or assumed e-graph equalities are involved.

## Reproducible native gate recipe

Materialize in a fresh durable directory after integration (this command itself
only reads/writes source/evidence):

```sh
uv run --locked python -m scripts.speq_phi_diagnostic \
  --source benchmarks/local/sources/speq/lleq \
  --output benchmarks/local/reproduction/speq-phi-diagnostic-0001
```

After a heavy-slot grant, use the existing `run_bounded_command` for each native
step, with `require_guard=True`, a 5-GiB process cap, 10-GiB disk reserve, authorized
warning pressure, and 60 seconds per compile/run. Record the exact command,
executable hashes, stdout, stderr and status in that diagnostic directory.

1. Query `/opt/homebrew/Cellar/llvm@17/17.0.6/bin/llvm-config` for `--version` and
   `--cxxflags --ldflags --libs core analysis irreader support --system-libs`;
   require 17.0.6 and retain flags. Use `shlex.split` on its returned flags.
2. Compile each `original-phi-harness.cpp` / `patched-phi-harness.cpp` with the
   sibling `clang++`, returned flags and `-o` a fresh diagnostic binary.
3. Run each binary against `phi-cases.ll`. The original nonzero result is an
   expected regression observation, not a reusable successful artifact. Require
   the patched binary to pass all 21 checks. No fixture code is executed.
4. Only then compile the full plugin from the isolated patched REV source plus
   the unchanged `scripts/paper_benchmarks/speq_rev_plugin.cpp`, using the same
   plugin flags/include layout as existing `record_speq.build_rev_plugin`.
   Do not bypass that recorder's original source hash check; this is a separate
   explicitly patched diagnostic build.
5. Run all four retained reference analyses through unchanged `print<revpass>`.
   Record hashes and actual deltas. The reference source/rules remain unchanged;
   a difference must be reviewed, not silently accepted as a new reference.
6. Run the real retained flag-lane Parboil `analysis.ll` through the repaired
   plugin. Inspect actual MemorySSA incoming values: inner `%cmp17.not=true`
   must select unchanged memory 6, false updated memory 4; outer
   `%cmp111.not=true` must select memset memory 3, false loop-result memory 5.
   Hash all inputs and generated FIR. This is source-translation evidence, not
   yet a complete recapture.
7. A separately recorded complete Parboil lane can then acquire the original C
   with its accepted fortification flag, use the corrected compiler, retain all
   regions, and compare native extraction with ordinary standalone replay. If
   the corrected frontend stops deriving Histogram, retain that failure; never
   edit the reference or manufacture a target to restore apparent success.

## Polybench: viable boundaries, no implementation in this slice

The no-GVN SCALAR_LB evidence establishes two distinct broken assumptions.

**Nested child memory outputs.** `translateLoopBody` at 1939 skips all child-loop
blocks, but it also only collects memory liveouts while scanning those direct
blocks. The k/i bodies therefore output `()` even though their child folds write
C. Simply collecting all descendant stores is wrong: it can return intermediate
states, duplicate child outputs, or lose conditional joins.

A narrow supported-case repair should require a single exiting latch and the
existing single-memory-state model. Obtain the memory state on that iteration's
backedge/exit from the header MemoryPhi's latch incoming value, resolving the
actual child fold output or join (the same state before the latch's branch exits
or continues). Emit exactly that final state as the parent fold output, and keep
all preceding child folds and direct writes in order. A conditional child path
must use its real join MemoryPhi; do not choose an arbitrary child store. Reject
unsupported multi-exit/multi-state cases. Regression cases must cover child-only
stores, direct store before/after child, two sequential children, skipped child,
child with internal conditional store, and separate parent iterations. Both
memory state identity and bound loop variables must be checked before expecting
a GEMM result.

**Iteration bounds.** `translateLoop` at 2082 prints `getFinalIVValue()` as an
exclusive Python-style Range bound. The retained latch instead tests current IV
`j < 1099` *after* performing that iteration, so it runs 1100 iterations. The
symbolic next-IV form already uses an exclusive bound; unconditional `+1` is
incorrect. `makeLevelBounds` at 679–740 also copies the same final value, and
its `UpperBound` participates in dimension/dense address construction later.
Fixing only the printed Range would leave inconsistent address/bounds evidence.

A minimal first repair can support constant, unit-positive-step, single-latch
loops by asking ScalarEvolution for an exact backedge-taken count, deriving the
number of executed body iterations and their exclusive bound at sufficient bit
width, and rejecting unknown/overflow cases. Keep the original guard so zero
iterations are not invented for an entered do-while-shaped loop. Share the
normalized bound between LevelBounds and FIR output. Before symbolic support,
test current-IV vs next-IV comparisons with 0/1/2 body executions, zero/nonzero
starts, reversed branch successors, strict/non-strict predicates, and overflow
edges. ScalarEvolution or predicate normalization alone must not discard
signedness/wraparound or guard conditions.

The standard GVN lane has a separate supported-format rejection:
`findLiveOut:2432–2465` permits exactly one scalar or one store output, whereas
LCSSA can expose both a reused index and C. The parser's Fold requires exactly
one return and one initial state (`parseIR.py:493–522`). Merely weakening the REV
`Legal` test cannot represent that tuple. Either prove/eliminate the redundant
liveout in a recorded frontend normalization, or add coherent multi-state support
across REV/FIR/parser. The diagnostic no-GVN lane avoids this rejection but is not
an unchanged-pipeline reproduction.

C99_PROTO's unbound dominating stride values, loss of pointer element typing,
and chained GEP address composition are still separate failures. None is fixed
by PHI polarity, child outputs or a bound adjustment. No GEMM or Reduction
reference was invented, and TPAL/TSVC exact input recovery remains separate.
