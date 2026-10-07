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

Expanded Make targets use a 300-second timeout and a 10 GiB process-group RSS
guard. Host memory pressure, host headroom, and free-disk reserve checks do not
stop runs. Source diagnostics retain a 256 MiB combined stdout/stderr limit. An
output-limit outcome is retained as an unavailable call and is not repeatedly
retried during preparation; this limit does not change timed measurements.
A workload failure stops the failed treatment's remaining repetitions; other
treatments still collect their samples. A safety stop preserves the observation
and stops the invocation. Historical host-pressure and disk-reserve diagnostics remain recorded
but no longer defer future runs. Timed failures stay in the append-only cache.
Timeout limits are never substituted for measured runtimes.

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
