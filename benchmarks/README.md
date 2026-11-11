# Paper proof benchmarks

These suites measure complete, independent Egglog computations: initialize an
e-graph, run the source rules and schedule, then extract or check a result.
Stages that reuse graph state stay together. A source program can contribute
several independent calls; identical workload/fact identities share measurements
while retaining their source aliases and invocation order.

The [source recipes](sources.json) pin the repositories, artifacts,
configurations, and adaptations. They describe representative paper workloads,
not a byte-for-byte reproduction of every paper experiment. A completed Egglog
call can qualify when a later compiler phase fails. Setup-only and unfinished
calls do not qualify, and downstream LLVM/code-generation work is outside the
measurement boundary.

## Prepared inputs

The standalone `.egg` files and `manifest.json` in `benchmarks/corpus/` belong in
Git. Collection reads these files directly; it does not need author compilers
or a local generation history. Run preparation when the corpus is absent or
when refreshing inputs from the pinned recipes:

```sh
make reproduce-benchmarks
# Or select a family or source configuration:
make reproduce-benchmarks REPRODUCE_ARGS='--family hardboiled'
```

Preparation acquires the pinned author sources and prerequisites, captures
complete calls, and validates their ordinary replay. It writes portable inputs
to `benchmarks/corpus/`; toolchains, source captures, and build logs stay under
ignored `benchmarks/local/`. Resume state and validation evidence stay under
ignored `benchmarks/corpus/.local/`. Source modifications are checked-in
[patches](reproduction/patches), applied to pinned revisions with
`git apply --check`. A changed engine revalidates retained workloads or captures
without rerunning the authors' compilers; generation identity tracks each
family's recipe, adapters and patches. No preparation timing becomes a benchmark
observation.

Interrupted preparation retains completed diagnostics and retries interrupted or
unattempted calls. Eggcc's prepared compiler is reused while its source and
artifact hashes match; unavailable Gurobi configurations do not trigger a build.

The resulting `benchmarks/corpus/manifest.json` is the sole input inventory
used by collection. It records actual source revisions, content hashes,
adaptations, aliases, and unavailable cases. Generated paths are relative to the
manifest; old machine-specific settings and capture receipts are not inputs.
A changed generated file gets a new identity, rather than being forced to match
a historical hash. Source failures and unsupported prerequisites are reported
explicitly; they do not become successful or empty workloads.

After preparation, review and commit `benchmarks/corpus/`. Its manifest records
the available population and blockers, even when some sources could not be
prepared. Measurements and images remain ignored; use the figure evidence
archive to preserve them separately.

| Family | Included source boundary |
| --- | --- |
| Math | The original combined seven-seed, 24-rule workload at iteration 11 |
| Luminal | Seven author-exported model programs, retaining schedules and derived-result queries |
| Eggcc | Complete optimization calls from the declared passing programs, followed by ordinary extraction from original Function roots; unavailable Gurobi configurations remain blockers |
| HardBoiled | The authors' 42 published Egglog files, with original extraction roots and declared compatibility adaptations |
| MISAAL | Completed Egglog rewriting/legalization calls; generation stops before later LLVM compilation |
| Churchroad | Declared integration/evaluation circuits through the complete Egglog mapping phase, preserving shared state and extracting original output ports; no later synthesis |
| DialEgg | Complete optimization and substantive shape-inference computations; setup-only invocations are excluded |

SpEQ is excluded from this expanded campaign; its source and exclusion reason
remain in the recipes. Herbie and pointer analysis are also outside this
campaign. The ordinary default uses seven existing regression fixtures, one per
included family; it does not require this source-generation pipeline.

Eggcc's replay uses the original input roots, rules and schedule. Ordinary
Egglog extraction does not enforce Tiger's effect/linearity constraints, so the
result is not a claim of compilable native output. Native Tiger still supplies
inputs to later passes during generation; reconstruction-only helper graphs are
not benchmark workloads.

Churchroad's circuit extraction establishes an Egglog result; it does not claim
that the author's subsequent hardware-mapping extractor or synthesis succeeded.
Necessary source repairs and proof-compatible adaptations belong to the pinned
recipe and generated provenance and apply equally to both timed conditions.

## Collect measurements

```sh
make expanded-bench-recording  # Proofs off and recording only.
make expanded-bench            # Also recording + extraction and native Egg Math.
make figures-all               # Collect missing observations, then render.
```

Or select families through the normal runner:

```sh
./bench.py --suite eggcc --suite luminal --target figures=. \
  --treatment proofs --compare-treatment off --rounds 10 --timeout-sec 300
```

Each comparison collects every prepared workload using one sequential plan.
Ten observations per condition is the Make default. Compatible observations are
reused, including proofs-off runs shared between the two proof comparisons;
repeated Make invocations do not remeasure completed samples. The checked-in
[known-failure list](../benchmarking/known_failures.py) skips only affected
workload/mode combinations and retains their reasons in coverage. Neither
explicit paths nor `--force-run` bypasses that list; remove an entry to retry.

The time window is a Vega-Lite parameter, not a collection gate. Figure
eligibility uses **all** exact-identity proofs-off observations: a nonempty,
wholly successful, finite sample with `0.1 < mean wall seconds < 30`. Memory and
proof outcomes never select the cohort. Figures show selected, too-fast,
too-slow, unresolved, and unavailable counts by family. Changing the window
requires only rerendering. A partial render describes available samples,
not a completed collection campaign.

All timed observations, including failures, go into append-only `.reports.jsonl`.
Reuse requires matching executable, workload, facts, treatment, disequality
encoding, and timeout. Labels and requested counts do not partition the cache.
Expanded analysis uses all matching observations; an earlier failure remains
visible and invalidates the ratio. Explicit retries append evidence and cannot
turn this into a success-only sample. Ordinary positional comparisons retain
their requested newest-N selection.

Measurements are whole-executable wall time and peak process RSS. Compilation,
source generation, and strict proof verification are outside timing. The
`proofs` treatment records proofs while performing ordinary checks/extracts;
`proof-extraction` also materializes and simplifies proofs of those results.
Both compare against the same proofs-off observations.

Expanded Make targets use a 300-second timeout. With
`EGGLOG_BENCH_MEMORY_GUARD=1`, the controlled `egglog-experimental` and
`egg-math-benchmark` executables install a native 6 GiB address-space allowance
before loading a workload. Ordinary corpus replay validation and explicit strict
validation always request it. On macOS the allowance is additional VM above the
startup mappings (which include very large fixed reservations); on Linux it is
total VM. Existing mappings can become resident without growing VM, so this is
not a 6 GiB RSS guarantee or a process-group hard cap. RSS is not polled or
limited. Benchmark peak process RSS is still measured by `wait4` and retained in
the reports. Builds and third-party author generators/drivers have no memory cap;
timeouts, output limits, process identity checks, and descendant cleanup remain.
Host memory pressure, host headroom, and free-disk reserve checks do not stop
runs. Source diagnostics retain a 256 MiB combined stdout/stderr limit. An
output-limit outcome is retained as an unavailable call and is not repeatedly
retried during preparation; this limit does not change timed measurements.
A workload failure stops the failed treatment's remaining repetitions; other
treatments still collect their samples. A safety stop preserves the observation
and stops the invocation. Historical RSS-polling, host-pressure, and disk-reserve
diagnostics remain recorded but no longer defer future runs. Timed failures stay in the append-only cache.
Timeout limits are never substituted for measured runtimes.

Both controlled Rust executables use mimalloc. Their benchmark and validation
launchers set `MIMALLOC_ARENA_RESERVE=0`, `MIMALLOC_DISALLOW_ARENA_ALLOC=1`,
`MIMALLOC_RESERVE_OS_MEMORY=0`, and `MIMALLOC_RESERVE_HUGE_OS_PAGES=0` before exec,
including unguarded benchmark runs. This keeps allocator behavior consistent for
the same binary identity. Memory-guard policy is not a cache identity dimension;
collection uses the fixed allowance rather than exposing a per-run override.

For a small standalone probe, set the same environment and pass
`--memory-limit-bytes=N` (positive integer, at most 10 GiB). Missing environment,
unsupported platforms, and limit setup errors fail before workload execution.
The limit is installed inside the executable after loader startup, never in a
Python preexec hook. A null Rust allocation under an active limit exits with
status 86; it reports an allocation failure under the limit without claiming
that the cap was necessarily its cause. Setup failures also use status 86.
Timed collection retains the known allocation failure as a failed observation,
skips that workload/treatment's remaining repetitions, and continues other work,
as it does for ordinary errors and timeouts. Cached failures are not retried
unless `--force-run` is supplied. Setup failures, unsupported old-binary option errors,
and stacker's specific stack-mapping failure remain resource stops. Unexpected SIGKILL
also stops collection with its cause left unknown. Other native libraries may
have different failure paths.

Preparation treats the known native allocation diagnostic with exit 86 as an
unavailable call and continues independent calls and cases, publishing only
successful workloads. Its retained receipt binds the engine, input and output
contract, timeout, native allowance, allocator settings, and intact diagnostic
logs. Identical retries reuse that failure; changes to those inputs allow another
attempt. A change only to the validator source does not retry allocation failures,
while successful validation still requires the complete validator identity.
Already published files remain intact; exclusions apply only to the affected
file and execution identity. Handled memory-limit outcomes let preparation exit
successfully so figure generation can continue. Strict validation also continues
with later files, but returns nonzero when any check remains unavailable. Setup
errors, unknown kills, interrupts, and process cleanup failures still halt.

## Correctness and Math configuration

```sh
make check                # Engine and checked-in fixture tests.
make validate-benchmarks  # Explicit strict checks for prepared corpus files.
```

The explicit validator, `scripts/validate_benchmarks.py`, writes identity-bound
diagnostic outcomes and logs under `benchmarks/corpus/.local/`, without changing
the tracked corpus. It is not a dependency of collection.
Matching strict failures suppress proof performance conclusions; absent or stale
validation is not a correctness claim.

Source generation and validation use `scripts/reproduction_process.py` for
bounded diagnostic processes and logs. Benchmarking keeps its whole-process
timing runner in `benchmarking/processes.py`; both use the neutral
`process_guard.py` for host protection and process cleanup.

Math uses simple/seminaive schedules without backoff or internal match/node
caps. Both engines check the same terminal equality. Native Egg looks up the
terms before explaining them, and tests verify that checking/extraction does
not change logical constructor or class counts. The fixed equality is absent
after iteration 10 and established after iteration 11 under these schedules;
this is not a claim about its mathematical truth or minimum proof depth.

Egg uses the fork revision locked in `Cargo.lock`, with builtin timing and
explanation-length optimization disabled. That revision includes other upstream
changes; this is a current matched-workload comparison, not an isolated timer
ablation or a reproduction of the original Egg rebuilding or Small Proofs
experiments. Logical graph-size parity is a consistency check, not graph
isomorphism. Timed results continue to use external process timing.

See [figure commands and interpretation](../figures/README.md) for rendering and
archiving the exact paper evidence.
