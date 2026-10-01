# Representative corpus qualification

This report records the original limited-corpus snapshot. See
[the DialEgg/Churchroad additions](dialegg-churchroad-additions.md) for the
current 434-workload selected cohort and the separately retained source blockers.

The 28 September 2026 scope amendment replaces exhaustive source regeneration
with a frozen population of retained, complete Egglog workloads. Math, Luminal,
proof collection, and charts are outside this run. A complete independent
optimization call qualifies even when its enclosing compiler later fails.
Preserve that parent failure; do not promote it to successful compilation.

Use the 42 selected published HardBoiled files and recoverable complete retained
captures for Eggcc, MISAAL, Churchroad, DialEgg, and SpEQ. Keep dependencies within
a shared egraph intact; exclude helpers and incomplete calls. Deduplicate input
identities while retaining aliases. No compiler generation, licensing campaign,
invented inputs, or artificial runtime padding is required.

Qualification uses 30 proofs-off observations in `.reports.jsonl`, with
`0.1 < mean wall_sec < 30`, a 300-second timeout, and the existing sequential
10-GiB process-group / 2-GiB host-reserve memory guard. Memory does not select the
cohort. Failures remain recorded; safety interruptions leave pending cases.

## Ownership and current state

| Owner | Domain | Output / stop condition |
|---|---|---|
| Coordinator | Scope, preservation, final review, guarded execution, reporting | Candidate accounting and baseline qualification, or explicit safety blocker |
| Corpus implementation | Retained-evidence publication and catalog projection | Small tested implementation; no source generation or timed collection |
| MISAAL evidence review | Existing complete-call evidence only | Bounded candidate/evidence map; no edits or processes |
| Independent code review | Retained-evidence and catalog trust boundaries | One correctness/minimality review, then recheck material fixes |

Pre-change files and hashes are saved under
`benchmarks/local/reproduction/limited-20260928/before/` and `before.json`.
Existing unrelated workspace changes remain untouched. The old full reproduction
index and receipts remain historical evidence, not a prerequisite for publication.

The limited goal is complete: 827 standalone workloads are frozen and published,
825 have 30 successful normal-mode observations each, and two have terminal
host-pressure interruptions. No observations remain pending. Qualification
selects 433 workloads for subsequent proof preparation; it does not establish
that their proof treatments succeed.

| Family | Workload files | Selected | Too fast | Too slow | Host stop |
|---|---:|---:|---:|---:|---:|
| Eggcc | 575 | 219 | 356 | 0 | 0 |
| HardBoiled | 42 | 39 | 3 | 0 | 0 |
| MISAAL | 174 | 172 | 0 | 0 | 2 |
| Churchroad | 2 | 1 | 1 | 0 | 0 |
| DialEgg | 26 | 2 | 24 | 0 | 0 |
| SpEQ | 8 | 0 | 8 | 0 | 0 |
| Total | 827 | 433 | 392 | 0 | 2 |

“Too fast” means a 30-observation mean at or below 0.1 seconds; “too slow” means
at or above 30 seconds. All eight SpEQ workloads are too fast, so this family
does not enter the selected cohort. The files and provenance remain available.
Memory was not an eligibility filter.

The exact executable identity has 24,785 successful observations and two saved
host-pressure failures. This includes 35 successful observations from the two
interrupted samples; neither partial sample qualifies. The final snapshot is
`benchmarks/local/reproduction/limited-20260928/baseline-selection-final.json`,
also archived at `benchmarks/local/baseline-selections/562dc547f2e7839b90742f2bfe369006ba14d5a06ed1fcbf459224bb5f53bb39.json`.
`collection-audit.json` verifies every selected row's identity, sample hash,
classification, input hash, and the preserved historical cache prefix.

Rerunning the public command after completion reported “nothing to collect.”
The complete cache remained byte-for-byte unchanged, as did the selection
snapshot and its modification time. See `cached-cli-check/result.json`.

### Safety history

The first collection invocation stopped after 8,132 observations when macOS
briefly reported warning memory pressure. It retained 8,131 successes and one
host-pressure failure for `misaal-hexagon-tensor_add` (replay
`4fecfde70eafc4b0ad2665c57a384ebc5da5010234589e57da5231bd3464241c`).
This was an ambient host stop, not an execution error or evidence that the
workload exceeded its memory cap. Normal pressure returned, and the second
invocation resumed the remaining observations without retrying that failure.
The second invocation added 1,331 successes before pressure prevented a new
launch; it recorded no additional failed observation. Pressure then rose again
during a 50-second idle observation with no benchmark running. Collection waited
for normal pressure. The user freed memory, restoring approximately 10 GiB
of host headroom, and the third invocation started the remaining 15,327
observations for 826 workloads. Neither safety stop is a time-window exclusion.
That invocation added 13,064 successes before another host-pressure interruption
stopped `misaal-arm-add` (replay
`886e1c5ab4636d14a50e8c67a2b7ee974548adbcd68b1450691fdcc567816207`)
on its 27th observation. The two unsuccessful samples remain terminal and are
not retried automatically. Neither indicates a workload memory-cap violation.

### Build metadata recovery

The fourth invocation unexpectedly rebuilt after a generated
`egglog/tests/web-demo/eqsat-basic-split.json` changed. Egglog's build script
watches its package by default and embeds the UTC build date in `FULL_VERSION`.
Crossing midnight changed the executable SHA-256 to
`07cb2e45ba94526e8392f800f2c709df236e69d992f737b6894195f36035e579`.
Its 430 successful observations remain in the cache under that separate
identity and do not contribute to this cohort. The collector was stopped when
the unexpected identity was confirmed.

Restoring only the cached build-script output's prior `2026-09-28` date and
rebuilding reproduced the original `009d3d…` executable **exactly**, verified by
its full SHA-256. No repository source was edited for this recovery. Both
executables are archived under this campaign's `engine/<sha256>/` directory;
`build-metadata-recovery/inputs.json` and `result.json` record the operation.
The fifth invocation completed all 2,259 missing observations successfully under
the original identity. No measurements from the other executable were pooled.

The corpus is `benchmarks/local/reproduction/limited-20260928/corpus/`.
Its manifest preserves 1,803 successful and 167 blocked provenance rows;
these are source/configuration/call records, not distinct workload counts.
The family catalog resolves exactly 827 unique file/fact identities. Acquisition
inventory, Math/Luminal entries, and the default suite remain unchanged.
All 117 independent MISAAL validation jobs passed. The final candidate snapshot,
`candidates-final.json`, has SHA-256
`d8d593c718134eb2847c46147bfda7fb8c1cc962aa3b12766b4cfec67864b790`.

The guarded release rebuild succeeded in 70.7 seconds with a sampled process-group
peak of 0.72 GiB. Its SHA-256 is
`009d3db72644c8c2993859ee8c07c43cb8c35d8e68540e3ff77540f9ef6816c4`;
this differs from the historical cache identities. Existing measurements are
preserved, and fresh baseline observations were collected for this executable.
The before-snapshot contains 21,882 historical observations.

## Source coverage

| Family | Represented sources | Retained omissions |
|---|---|---|
| Eggcc | All 96 programs | 94 Gurobi configurations lack the licensed solver; other configurations supply the represented programs. |
| HardBoiled | All 42 selected author-published inputs | The selected suite omits `conv_layer-16`, `conv_layer-32`, `attention`, and AMX inputs. |
| MISAAL | 64 of 102 target/program pairs | 38 HVX pairs lack qualifying retained workloads; five failed or interrupted individual calls are also excluded. |
| Churchroad | Both selected circuits | 27 artifact extras lack retained validation: 18 multiply, five multiply-add, four MAC. |
| DialEgg | 9 of 10 source identities | NMM-160 lacks retained validation. |
| SpEQ | 8 of 10 sources | Exact TPAL and TSVC2 source inputs and setup remain unresolved. |

The 167 blocked provenance rows comprise 94 Eggcc configurations, 38 MISAAL
sources and five individual calls, 27 Churchroad extras, one DialEgg source,
and two SpEQ sources. The suite reports only 41 unavailable catalog sources:
38 MISAAL, one DialEgg, and two SpEQ. Gurobi configurations and failed MISAAL
calls share source IDs that have other retained workloads; Churchroad's extras
are outside the main catalog. Neither count is a number of timed failures.

Preserved MISAAL missing-pattern errors are historical. Later preparation
[recovered those dependencies](misaal-arm-hvx-recovery.md); missing qualifying
capture/validation evidence is the current limitation of this frozen corpus.
See also [Gurobi accounting](eggcc-gurobi.md),
[HardBoiled source coverage](hardboiled-published-suite.md), and
[SpEQ recovery](speq-recovery.md).

## Reuse

The corpus manifest lists the selected self-contained files and preserves all
source aliases and original receipt links. Select files through that manifest
or the family catalog, not by globbing historical capture directories.

```sh
./bench.py --suite eggcc --suite hardboiled --suite misaal \
  --suite churchroad --suite dialegg --suite speq \
  --baseline-window --baseline-only --target figures=. \
  --rounds 30 --timeout-sec 300
```

This command collects only missing proofs-off observations. Existing exact-
identity failures are terminal; changing the executable or input requires new
measurements. Source omissions remain visible alongside runtime qualification.

To republish the frozen inputs without source generation or benchmark runs:

```sh
uv run --locked python -m scripts.retained_corpus \
  --candidates benchmarks/local/reproduction/limited-20260928/candidates-final.json \
  --validation-directory benchmarks/local/reproduction/limited-20260928/validations \
  --output benchmarks/local/reproduction/limited-20260928/corpus \
  --catalog-output benchmarks/local/reproduction/limited-20260928/catalog.json
```

Publication verifies retained receipts and file hashes. Repeated publication
preserves manifest bytes and modification time and produces the same projected
catalog, including normal-only proof-query exclusions.

## Validation

- `make check`: passed, including 1,823 Python and 1,487 Rust tests; six Rust
  tests remain ignored by their existing configuration. Builds and tests ran
  sequentially under the guard, with debug symbols disabled to conserve disk.
- `make benchmark-smoke`: passed all 20 observations in a temporary cache.
- Final `make python-check`: passed formatting, Ruff, mypy, and 1,825 tests
  after the archive integrity fix. Selection archives are written atomically;
  existing content-addressed archives with changed bytes are rejected. Reusing
  an unchanged archive leaves its modification time intact.
- Focused retained-corpus checks cover receipt tampering, failed-parent
  independent calls, timeout identity, deduplication, preserved proof blockers,
  and repeated publication. The final projection fix passed 22 focused tests,
  Ruff, formatting, and mypy.
- The final cache audit verified all 827 samples against their original rows,
  recomputed qualification, and verified all frozen input hashes. The cache
  contains 47,099 observations: 21,882 historical, 24,787 for the qualified
  executable, and 430 for the separate date-changed executable.
- The production cache's original 56,467,132-byte prefix remains unchanged after
  collection. Its SHA-256 is
  `51f2d8e29819429dfc86887c6ce8a2045cab82a8eb91796733d6128346dc33fd`.

Execution receipts and logs are under
`benchmarks/local/reproduction/limited-20260928/`, including
`make-check-0002/result.json`, `benchmark-smoke/result.json`,
`publication-idempotence.json`, and `baseline-run.json` through
`baseline-run-0005.json`. The three interrupted original-identity snapshots and
the alternate-build snapshot remain alongside the final selection. The final
cache and selection audit is `collection-audit.json`; the final Python and
cache-reuse checks are `final-python-check/result.json` and
`cached-cli-check/result.json`.
