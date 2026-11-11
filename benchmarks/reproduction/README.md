# Paper-derived Egglog workloads

The current [limited corpus goal](limited-corpus-status.md) reuses complete,
retained Egglog workloads and the authors' 42 published HardBoiled files. It does
not require byte-for-byte paper reproduction, all paper configurations, or new
compiler generation. Complete independent optimization calls can contribute
workloads even when the enclosing compiler later fails; that failure remains
part of their provenance. Setup-only and unfinished calls do not qualify.

After publishing the frozen corpus into the family catalog, qualify its normal
runtime through the existing benchmark cache:

```sh
./bench.py --suite eggcc --suite hardboiled --suite misaal \
  --suite churchroad --suite dialegg --suite speq \
  --baseline-window --baseline-only --target figures=. \
  --rounds 30 --timeout-sec 300
```

This collects only missing proofs-off observations in `.reports.jsonl`. Selection
requires 30 successful observations with `0.1 < mean wall_sec < 30`. Memory is
reported but does not select workloads; the memory guard still protects the host.
The per-family report retains fast, slow, failed, blocked, and pending cases.
Proof collection, charts, Math, and Luminal are outside this command.

The frozen 28 September corpus contains 827 workloads. Completed baseline
qualification selects 433; 392 are too fast and two retain host-pressure
failures. SpEQ has no qualifying workloads. See the
[per-family results and evidence](limited-corpus-status.md).

## Historical source-regeneration pipeline

This pipeline acquires standalone Egglog workloads for Eggcc, HardBoiled,
MISAAL, Churchroad, DialEgg, and SpEQ and validates their ordinary execution.
HardBoiled uses the authors' 42 published files with their original extractions;
other families record complete source optimizations and actual outputs. MISAAL
is being changed to stop after its Egglog work, before native LLVM lowering.
The pipeline does not collect performance observations or read or write `.reports.jsonl`.

The source-backed expected population is in [population.json](population.json).
The current execution report is generated at
`benchmarks/local/reproduction/REPORT.md`; it includes missing preparation,
failed parents, resource stops, and stale evidence. Its strict source-completion
accounting is separate from the limited corpus: an individually completed call
does not establish successful completion of the enclosing source program.

```sh
# Resume the six-family population using prepared source/tool settings.
make reproduce-benchmarks

# Select families or a specific source configuration.
uv run --locked python scripts/suite_acquisition.py reproduce --family eggcc --family dialegg
uv run --locked python scripts/suite_acquisition.py reproduce --family misaal --case misaal-x86-blur3x3

# Inspect current evidence without starting a compiler or replay.
uv run --locked python scripts/suite_acquisition.py reproduce --stage report

# Validate retained captures with the current ordinary engine.
uv run --locked python scripts/suite_acquisition.py reproduce --stage validate

# Acquire and build pinned prerequisites without running source optimizations.
uv run --locked python scripts/suite_acquisition.py reproduce --family eggcc --stage prepare
```

Preparation is integrated for all six families, including sequential MISAAL
x86, ARM and HVX preparation with per-case blockers. All 102 MISAAL host
generators now have successful native preparation; complete source runs and
ordinary replay are accounted for separately. These recipes have focused tests; successful preparation is
reported only after their native dependency gates actually pass. `all` prepares a supported family when its
settings are absent, or replaces legacy native HardBoiled settings with the selected
published-input settings. Explicit `prepare` checks the recorded preparation identity
and retained outputs, and rebuilds missing or changed results. Prepared paths and
environment identities are saved to `benchmarks/local/reproduction/settings.json`
(override with `--settings`). A family without a recipe or prepared settings
remains pending. Capture and validation attempts
are immutable and reused only when their inputs and retained outputs match.
The current index links to shared preparation/history receipts instead of copying
their artifact inventories into every case; index updates are atomic.
`--retry` deliberately creates a new attempt, including for a previous failure;
it is not needed for changed inputs.

Eggcc settings may specify `case_timeout_sec` as a map from exact inventory case IDs to
positive finite seconds. For example, adding
`"case_timeout_sec": {"eggcc-raytrace--statewalk": 900}` inside the existing
`eggcc` settings gives only raytrace a 900-second source-capture budget and a
separate 900-second budget for each ordinary replay. Unlisted cases keep their
family `timeout_sec` (300 seconds when absent). Unknown IDs, IDs from another
family, patterns, booleans, and invalid numeric budgets are rejected before work
starts. Overrides for other families are rejected; MISAAL native budgets remain
in their per-case requests. The JSON and Markdown reports show the resolved
ordinary replay timeout and note that Eggcc source parents use the same budget.
Explicit preparation preserves this coordinator-owned override map.

The coordinator resolves the timeout map and the optional raytrace materialization
policy for each case before computing its identity.
An affected case gets a fresh identity containing its resolved `timeout_sec`;
unaffected case identities and reusable receipts remain unchanged. Earlier
300-second timeout receipts remain immutable evidence. An override changes no
source schedule, completion/output checks, memory or disk guards, or performance
cache. This is an explicit time policy, not permission to accept a partial source
run. Keep overrides in a separate `--settings` copy when evaluating a longer
budget; no override is enabled by this documentation.

Eggcc's Gurobi configurations require the genuine CLI and usable license access.
The current settings record that unavailable prerequisite against those exact
configurations; they do not launch a substitute solver. Statewalk remains
independent. Update the explicit configuration blocker after provisioning access.

The generated `benchmarks/local/reproduction/corpus/manifest.json` retains every
source configuration and its outcome. Successful ordinary validations contribute
one `.egg` file per byte identity, named by its SHA-256, with all source/session
aliases in the manifest. The immutable acquisition receipts retain original
commands, outputs, adaptations and hashes. Corpus publication currently supports
self-contained replays; undeclared external facts are rejected.
Only files listed in this manifest belong to the current corpus. Unlisted files
with older content hashes may remain in the directory as historical evidence;
do not select workloads by globbing all `.egg` files. Paper-cell mapping outcomes
are listed separately in the report. Historical HardBoiled AMX cells remain
visible but do not gate its selected author-published suite. Required unresolved
inputs still make full-family collection return a nonzero exit.

One heavy job runs at a time. Native jobs and OrbStack containers have memory,
time and disk guards; container limits apply to the container itself. A safety
stop preserves evidence and stops the invocation. Rerunning the command skips
intact cached failures and continues remaining cases; a new safety stop halts
that invocation too. Changed identities or explicit `--retry` create a new
attempt under the same guards. Historical failures are never converted into
successful observations or hidden by a later source alias.

For repository validation on a constrained host, use
`CARGO_BUILD_JOBS=1 make check RUST_TEST_ARGS=--test-threads=1` under the memory
monitor. The custom Rust file-test harness needs the explicit test argument;
`RUST_TEST_THREADS` alone does not serialize it.

Family investigation and environment notes:

- [Churchroad prerequisites](churchroad-environment.md)
- [Eggcc preparation](eggcc-preparation.md) and [Gurobi access](eggcc-gurobi.md)
- [HardBoiled preparation](hardboiled-preparation.md) and [native canary audit](hardboiled-native-audit.md)
- [Author-published HardBoiled Egglog inputs](hardboiled-published-suite.md)
- [MISAAL and HardBoiled capture contracts](misaal-hardboiled.md)
- [MISAAL wrapper-inliner repair](misaal-wrapper-inliner.md)
- [MISAAL positive-width literal repair](misaal-literal-width-repair.md)
- [MISAAL x86 selector literal repair](misaal-x86-selector-literals.md) and [exact pattern deduplication](misaal-pattern-deduplication.md)
- [MISAAL family preparation](misaal-family-preparation.md) and [isolated solver prerequisites](misaal-racket-preparation.md)
- [MISAAL x86 generator preparation](misaal-cases-preparation.md) and [complete blur3x3 audit](misaal-blur3x3-audit.md)
- [MISAAL ARM/HVX recovery and native lowering](misaal-arm-hvx-recovery.md)
- [MISAAL HVX selector preparation](misaal-hvx-preparation.md)
- [HardBoiled AMX paper-cell mapping](hardboiled-amx-mapping.md)
- [DialEgg extraction output comparison](dialegg-output-contract.md)
- [DialEgg preparation](dialegg-preparation.md) and [fresh native/replay audit](dialegg-fresh-native-audit.md)
- [SpEQ source recovery](speq-recovery.md) and [PolyBench frontend gaps](speq-polybench-frontend.md)
- [SpEQ PHI frontend diagnostic](speq-phi-repair.md)
- [SpEQ preparation and archive acquisition](speq-preparation.md)
