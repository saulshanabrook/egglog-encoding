# Complete source reproductions

This pipeline captures complete source optimizations for Eggcc, HardBoiled,
MISAAL, Churchroad, DialEgg, and SpEQ. It preserves the native compiler's actual
outputs and validates ordinary standalone Egglog replays. It does not collect
performance observations or read or write `.reports.jsonl`.

The source-backed expected population is in [population.json](population.json).
The current execution report is generated at
`benchmarks/local/reproduction/REPORT.md`; it includes missing preparation,
failed parents, resource stops, and stale evidence. Files emitted before a parent
failed are diagnostic evidence, not reproduced workloads.

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
settings are absent. Explicit `prepare` checks the recorded preparation identity
and retained outputs, and rebuilds missing or changed results. Prepared paths and
environment identities are saved to `benchmarks/local/reproduction/settings.json`
(override with `--settings`). A family without a recipe or prepared settings
remains pending. Capture and validation attempts
are immutable and reused only when their inputs and retained outputs match.
`--retry` deliberately creates a new attempt, including for a previous failure;
it is not needed for changed inputs.

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
are listed separately in the report, including all ten HardBoiled AMX cells.
Full-family `all` collection retains a nonzero exit while required paper-cell
mappings remain unresolved, even if every available artifact program succeeds.

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
- [MISAAL and HardBoiled capture contracts](misaal-hardboiled.md)
- [MISAAL wrapper-inliner repair](misaal-wrapper-inliner.md)
- [MISAAL family preparation](misaal-family-preparation.md)
- [MISAAL x86 generator preparation](misaal-cases-preparation.md) and [complete blur3x3 audit](misaal-blur3x3-audit.md)
- [MISAAL ARM/HVX recovery and native lowering](misaal-arm-hvx-recovery.md)
- [MISAAL HVX selector preparation](misaal-hvx-preparation.md)
- [HardBoiled AMX paper-cell mapping](hardboiled-amx-mapping.md)
- [DialEgg extraction output comparison](dialegg-output-contract.md)
- [DialEgg preparation](dialegg-preparation.md) and [fresh native/replay audit](dialegg-fresh-native-audit.md)
- [SpEQ source recovery](speq-recovery.md) and [PolyBench frontend gaps](speq-polybench-frontend.md)
- [SpEQ PHI frontend diagnostic](speq-phi-repair.md)
- [SpEQ preparation and archive acquisition](speq-preparation.md)
