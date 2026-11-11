# Expanded benchmark campaign status

## Current work — 2026-09-23

The user's overnight invocation finished screening and collected all requested
observations for ready cases. Of 166 captured replays: 59 ready and measured,
66 resource-limited, 38 proof errors, three historical safety deferrals, and
zero pending. All 59 ready cases have 30 successful off and 30 successful
proof-extraction observations for the current identities.

The overnight error investigation is complete. The existing benchmark runner,
engine sources, canonical workloads, cache schema and measured rows are not
being changed. No commit, push, or unrelated cleanup has been performed.

| Agent | Domain | Aim | Status | Stop |
| --- | --- | --- | --- | --- |
| root | Error diagnosis and campaign state | Recover HardBoiled diagnostic, run bounded MISAAL control | Complete; no benchmark process running | Explanation and controlled results recorded |
| coverage_review | Overnight cache audit | Confirm completion and distinguish saved/new failures | Complete | 59 complete comparisons; zero pending |
| current_measurements | MISAAL proof diagnosis | Check variable-collision hypothesis using diagnostic copy | Complete; root executed controls | Renamed copy passes normal and strict modes |

## Preserved evidence and results

The cache has 6,373 rows, up from 4,291 before the overnight run. The 2,082 new
rows comprise 2,056 successes, 25 proof-extraction timeouts and one
proof-extraction panic (Eggcc Nussinov). All 26 failures occurred during the
remaining screening pass. The subsequent 2,030 top-up observations all
succeeded: 290 for five Luminal workloads and 1,740 for thirty Eggcc workloads.
The 24 earlier complete comparisons remain, giving 59 complete comparisons
and 3,540 successful observations for those comparisons.

The original 4,137-row prefix from the prior continuation and both executable
hashes were verified unchanged. This investigation does not append diagnostic
runs to `.reports.jsonl`. Preservation evidence and full diagnostic logs live
under `local/diagnostics-20260923/`; generated coverage has been refreshed.

A guarded HardBoiled matmul_flat_1x1 reproduction recovered the omitted error:
`primitive operation lacks a validator function`. Its rule uses `unstable-app`,
registered without a validator. The ordinary mode works, but proof encoding
rejects it before extraction/strict validation. The previous cached errors
retained only the final 1,000 characters and omitted this headline. All 35
HardBoiled failures are retained; the diagnostic has not changed their inputs.

The MISAAL strict failure is older exact-identity evidence, not an overnight
rerun. It rejects an equality substitution before simplification. Fresh controlled execution confirms a global/rule-local name collision: the
original input reproduces the panic, while renaming only three globals and
three uses makes normal execution and strict proof validation pass. Rules,
schedule and final query are unchanged. The original input and failure remain
in the campaign; the engine is not patched.

All original preservation archives and validation logs remain under
`local/cache-campaign-checkpoint/` and `local/cache-campaign-source/`.
Source accounting retains 101 MISAAL and six SpEQ blockers; Math 12–100 remains
deferred, and Herbie/pointer analysis remains excluded.

## Source preparation

All original 131 replay paths/raw hashes were checked. Thirty-five additional
HardBoiled replays preserve the complete original 20-iteration schedule and
query the first derived equality in original extraction order. All 35 positive
and 35 initialization-only negative controls passed. The earlier all-root
conjunction's conservative 2-GiB preparation stop remains diagnostic evidence.
There are 36 raw HardBoiled invocation aliases, with 30 complete and five partial
generator captures. The reusable adapter and tests are checked in as source.
MISAAL's 101 missing-generation prerequisites are grounded in retained pinned
Git-tree/Makefile evidence, not a fabricated fresh linker failure.

## Validation

- Guarded `make check` passed: 357 Python tests and 1,463 Rust test/doc-test
  passes; peak process-group RSS was 3.49 GiB.
- After final figure and stop-export fixes, guarded `make python-check` passed
  all 360 Python tests, Ruff, formatting, and mypy for 70 files.
- Final guarded `make benchmark-smoke` passed all 20 temporary-cache runs.
- All ten Vega numerical/rendering tests passed after the compact-marker fix.
- Report UI checks passed 60 cached-only combinations across one/ten files,
  ordinary/suite modes, three detail levels, and five widths. Interactive
  runtime and cached-only `--open` checks passed; manual browser inspection was
  unavailable (preview queued/no accessible browser).
- Independent reviews fixed explicit retries of normal-mode failures,
  interactive validation scope, preservation of failed projected observations,
  Math label overlap, and coverage refresh on retained/preflight safety stops.

Logs and reviews live under `local/cache-campaign-source/`. Full source coverage
is in `local/coverage.json` and `local/coverage.md`.

## Safety and remaining work

Every diagnostic engine invocation is guarded: one heavy process, 6-GiB
process-group threshold, 2-GiB host reserve, normal host pressure, and an
explicit timeout. Diagnostic executions do not count as benchmark samples.

The MISAAL control and updated REPORT.md explain the saved errors. The original admitted collection is complete;
addressing proof bugs or deliberately retrying resource failures is separate
work. The subsequent visualization refresh is complete: the Math comparison and
two-page Egglog proof-overhead atlas use the latest measurements. Independent
CSE 512-based review passed at 180 mm; numerical checks match the benchmark
implementation. The frozen gallery and review evidence are under
`figures/review/refreshed-20260923/`. No measurements were added during that work.
