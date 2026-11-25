# GPU backend for term-encoded egglog

`egglog-gpu` replaces relational storage, query planning, and rule action
execution. The CLI uses this replacement in all three modes: Rust simulation,
software Vulkan, and hardware Vulkan. There is **no native relational fallback**.
The earlier join-only `Matcher` remains a separate library experiment and test
oracle; the CLI uses `Backend`.

```sh
# No GPU or Vulkan driver needed.
cargo run --locked -p egglog-gpu -- --backend simulate \
  egglog-gpu/examples/scheduled-terms.egg

# Run the actual WGSL kernels on software Vulkan.
cargo run --locked -p egglog-gpu -- --backend software \
  egglog-gpu/examples/scheduled-terms.egg

# Require hardware; a CPU adapter is an error.
cargo run --locked -p egglog-gpu -- --backend gpu program.egg

cargo test --locked -p egglog-gpu
cargo test --locked -p egglog-gpu -- --ignored --nocapture
```

Files run in order in one term-encoded e-graph. Adapter identity and backend
statistics go to stderr. The library entrypoint is
`Arc::new(Backend::simulated(limit)).egraph()` or
`Arc::new(Backend::vulkan(mode, limit)?).egraph()`.

The development host has no exposed hardware GPU. Mesa's software Vulkan
adapter, `llvmpipe (LLVM 20.1.2, 256 bits)`, executes the kernels and differential
tests. Software mode explicitly requests that adapter; it does not silently
switch to Rust simulation. These results establish correctness on the tested
software driver, not hardware performance. `./bench.py` remains the benchmark
entrypoint. The `gpu-simulate` and `gpu-software` treatments compare the
replacement with `off` (ordinary egglog) or `term` (native term encoding):

```sh
./bench.py --treatment gpu-software --compare-treatment off --rounds 3 \
  --no-memory-limit --report /tmp/egglog-gpu-report.jsonl \
  egglog-experimental/tests/math-microbenchmark-rational.egg
```

These modes measure whole-process wall time and peak RSS, including adapter and
pipeline initialization. The GPU CLI does not implement the allocator cap, so
its report endpoint is explicitly uncapped; the command also disables the
baseline cap. Device allocation and indexing limits remain active. Use a separate report per machine
and adapter, since the executable hash alone does not identify hardware or
driver configuration. A hardware GPU treatment is not registered yet.
Registering these treatments advances the report-cache schema to version 12;
older measurement caches require recomputation rather than migration.

On 2026-11-19, the unchanged eleven-round `math-microbenchmark-rational.egg`
completed with the default CLI settings. Three serial release runs through
`./bench.py`, without allocator caps, gave these medians on the development host:

| Backend | Whole-process time | Peak RSS |
| --- | ---: | ---: |
| Ordinary egglog | 0.783 s | 132 MiB |
| Native term encoding | 1.757 s | 245 MiB |
| Replacement Rust simulator | 28.609 s | 418 MiB |
| Replacement software Vulkan | 39.102 s | 574 MiB |

This establishes a working Math workload; the replacement remains slower on
this CPU. Software Vulkan timings do not predict hardware GPU performance.

## Execution contract

The existing frontend retains parsing, type checking, term lowering, the
schedule interpreter, and per-rule seminaive timestamps. The new backend takes
logical atoms and action instructions **before native physical planning**.
It installs its own tables for every function, including encoding internals.
Native Free Join plans, the native action interpreter, `SortedWritesTable`, and
`FlatTable` do not execute replacement rules. Runtime checks reject mixed
storage and native plans.

| Operation | Replacement implementation |
| --- | --- |
| Tables | Generation-stamped host mirrors and immutable resident device buffers; new pending-write queues, FD indexes, merges, deletion and compaction |
| Queries | Logical atom filtering and projection, occurrence disjunctions, connected binary joins, duplicate elimination |
| Vulkan relational operators | WGSL filtering, tiled bitonic sorting, hierarchical workgroup scans, range joins, payload emission, compaction and keyed lookup |
| Actions | Separate interpreter for every action opcode; Vulkan batches keep bindings on device across projections, assertions, writes, deletes, counters and lookups |
| Keyed term creation | Unique request batches, lookup, checked allocation for misses, publication to the shared prediction ABI, and scatter back to requesters |
| Opaque primitives | Explicit host calls; lookup fallbacks transfer only misses to their callback |
| Merge callbacks | Replacement storage invokes the bridge's compiled host callback, including additional staged effects |
| Schedules and commits | Existing frontend schedule interpreter and dependency ordering; the replacement table implementation performs commits |

This is a relational backend replacement with host extension boundaries, not
an entirely device-only engine. The core `Database` still supplies the ABI for
base values, containers, counters, predictions, and dependency scheduling.
Primitive callbacks can inspect and modify **replacement-owned** tables.
Host mirrors also serve extraction, printing and introspection.

Device tables persist across queries. Intermediate query payloads stay on the
device; cardinality readbacks allocate subsequent buffers. At commit, staged
rows are downloaded for host merge callbacks, and changed tables are uploaded
again. Keyed creation transfers compact unique requests to reconcile the shared
prediction cache used by arbitrary Rust primitives. These transfers are explicit
implementation costs. Removing them requires device implementations of the
corresponding callbacks and interning ABI.

Compute passes and copies share command buffers until a host readback, a backend
boundary, or 256 recorded operations. Each compute pass retains its global
ordering barrier. Pipelines compile on first use; unused bindings and scalar
readback buffers are reused. Prefix scans recurse over workgroup totals without
host reads at each level. Bitonic sorting performs tile-local steps in shared
memory, then merges tiles with fewer dispatches.

Immutable matrices cache sorted row permutations by key columns. Snapshots
share those indexes; changed tables receive new matrices, while no-op commits
retain their existing buffers and indexes. Up to eight lookup keys use a direct
workgroup scan instead of sorting the table. Already-compacted committed tables
also avoid a redundant filter and deduplication pass. Query planning omits
deduplication when the projected columns and equality filters determine an FD
key, and natural joins preserve the distinctness of their complete variable
bindings. Unused local variables and occurrence expansions still receive the
required duplicate elimination.

For each join step, the planner counts connected candidate joins and chooses
the smallest result before allocating its payload. Vulkan computes those counts
on the device and reuses the selected prefix scan for emission; simulation uses
sorted ranges. Unselected candidates can exceed an optional row guard without
failing the query. This avoids the large multiplication-pair intermediate in
Math's factoring rule when the outer addition relation is more selective.

Term creation deduplicates bindings by constructor keys before widening request
rows, then reads unique requests and lookup results together. A single resolved
key scatters through a constant assignment kernel. Wide action batches split
into contiguous pieces sized for the adapter's binding limit. Each instruction
finishes across all pieces before the next begins, preserving counter reads,
shared predictions, staged writes and later filtering. Simulation stores compact
binding rows and reuses one scratch variable map per instruction.
These optimizations
preserve source command, schedule, primitive callback and commit boundaries;
they do not defer source facts across commands. CLI statistics expose compute
dispatches, explicit queue submissions, readbacks, sorts and sort-cache hits.

## Schedules, equality, and IDs

`run`, `seq`, finite `repeat`, `saturate`, and `:until` retain their source
boundaries. Each run reads committed tables and stages its actions before
committing. Seminaive restrictions are copied into logical atoms, including
both lower and upper timestamp bounds. Watermarks remain **per rule**, so a
ruleset resumed after another ruleset ran still sees its intervening changes.
Merges and rebuilding preserve timestamps, and no-op writes do not keep
saturation alive. Local unused body variables are existential; shared join
variables are retained even when the RHS does not mention them.

There is no native union-find in the replacement. A read-only empty bootstrap
table satisfies the bridge's identity-table handle; attempting to write native
unions fails. The current term encoding represents equality through ordinary
`@UF_<sort>` tables and explicit rebuilding rules. Those tables run through the
same replacement machinery. See the
[encoding specification](../egglog/src/proofs/proof_encoding.md).

Fresh IDs are keyed, not allocated once per match. Duplicate requests within a
batch, across rules in one run, and from host primitive callbacks share the
prediction cache. Dependent constructor actions consume their children's
returned IDs. Device batches reserve checked contiguous ranges only for
unresolved keys; `CurrentVal` copies a previously written field of that row.
Device batch counter exhaustion fails instead of wrapping into the reserved stale marker.
Construct-into-existing-class writes and encoded merge effects preserve their
existing semantics. Values are interned `u32` handles, not truncated source
integers.

Push/pop clones committed storage and isolates pending queues. Immutable device
buffers can be shared between snapshots; later commits replace buffers rather
than mutate a restored snapshot. Compaction invalidates row indexes by advancing
the table generation, while preserving source term IDs and timestamps.

## Limits and validation

Source support follows the current term encoder. For example, user-authored
merge action blocks and tuple-output functions remain rejected by that frontend. Generated encoding merges,
supported merge expressions, and container rebuilding use the host extension
ABI. The default frontend/backend elsewhere in the workspace is unchanged.

`--max-join-rows N` optionally bounds materialized relations and device table
buffers, including pre-compaction query candidates. The CLI has no fixed
million-row default: without that option, the representation bound is
`u32::MAX - 1` rows. The device requests the adapter's advertised buffer limits;
this host's software adapter still advertises a 128 MiB storage-binding limit.
Action working buffers are partitioned, but each query result and resident
table must still fit one binding. Buffer sizes, dispatch dimensions, and row
indexing are checked. Exceeding a limit returns an error; it
never selects the native backend. This is not a process memory cap. Binary
intermediates can be much larger than the final result. Execution errors are
not transactional: discard the failed graph or restore an earlier push/pop
snapshot before continuing.

The replacement tests compare full encoded programs with the native term
backend, covering delayed rulesets, nonlinear recursion, `:until`, congruence,
merges, deletion, subsumption, containers, and push/pop. Random
queries are compared with an independent nested-loop oracle, including empty
and nullary relations, flat and FD storage, repeated values, range constraints and occurrence
queries. Direct ABI tests exercise nested ID creation, cross-rule and host
primitive reuse, exhaustion, action failures, partial effects, and conditional
fallbacks. The default tests require no driver and validate WGSL with Naga;
explicit ignored tests execute the same contracts on software Vulkan.
Additional device tests cover partial tiles, multiple scan levels, saturated
counts, stable sort ties, snapshot index isolation, both lookup paths, batched
command ordering, paired readbacks, concurrent scalar readback reuse, and
cross-chunk predictions and instruction ordering. Selective-join regressions
check that an oversized unselected candidate does not fail an otherwise
bounded query.
The Rust paper runner also dispatches these treatments, comparing source-visible
tables and outputs with ordinary egglog and checking extraction alternatives in
ordinary graph clones. Its simulator dispatch smoke test runs by default; the
software Vulkan dispatch test requires `--include-ignored`.
The full eleven-round Rational Math benchmark also runs through the paper
correctness harness against ordinary and native term-encoded egglog, retaining
its terminal equality check and exact source-visible table-size comparisons. Its
software Vulkan counterpart requires `--include-ignored`. The public benchmark
CLI smoke test includes this Math workload with the default simulator settings.
The unchanged twelve-round Math witness does not yet complete here: software
Vulkan reaches a 446,324,112-byte resident table beyond its binding limit, and
the simulator did not finish within a 500-second diagnostic timeout. These are
unresolved scaling limits, not passing correctness cases or benchmark exclusions.

Run the workspace validation through `make check` as documented in the root
`AGENTS.md`. Hardware differential testing and performance measurement remain
necessary before making hardware speedup claims.

## Research and next optimizations

The primary sources motivating this design are:

| Work | Relevant result | Implication here |
| --- | --- | --- |
| [GPUJoin, USENIX ATC 2023](https://www.usenix.org/conference/atc23/presentation/shovon) | GPU hash joins, fused operators, and deduplication for iterative relational algebra. | Joins alone are insufficient: repeated deduplication and allocation belong in the design. |
| [GDlog, Modern Datalog on the GPU](https://arxiv.org/html/2311.02206v3) | Hash-indexed sorted arrays, range queries, and full/delta/new relation management; CUDA and HIP implementations. | Use indexed ranges and explicit delta ownership, rather than a pointer-heavy CPU table translated into kernels. |
| [FVlog, Column-Oriented Datalog on the GPU](https://arxiv.org/html/2501.13051v1) | Flat columns and surrogate row IDs; count/scan/write joins; multiple rules contribute before a shared delta merge. | Columnar storage and delayed payload materialization fit term tables. Its evaluated TGD workload explicitly excludes existential rules, so it does not establish keyed fresh-ID semantics. |
| [SRDatalog, Scaling Worst-Case Optimal Datalog to GPUs, 2026 preprint](https://arxiv.org/html/2604.20073v2) | GPU worst-case-optimal joins, flat storage, two-phase allocation, and skew-aware scheduling. | Keep multiway join structure available. Large binary intermediates can exhaust VRAM even when the answer is small. |
| [WGLog, Terascale Query Processing in the Browser, 2026 preprint](https://arxiv.org/html/2607.17571v1) | WebGPU sorted-array joins and batched indirect dispatch for recursive queries. | Particularly relevant to the WGSL route here: eliminate per-stage readbacks once device actions and valid schedule boundaries are available. |
| [Slog, Datalog with First-Class Facts](https://arxiv.org/html/2411.14330v1) | Unique fact identities and parallel deduplication/interning in an MPI implementation. | A useful semantic reference for keyed fresh IDs; this is not a GPU implementation or a drop-in egglog equality engine. |


Seminaive evaluation is already central to GPU Datalog. Egglog additionally
needs resumable schedules, keyed term creation, mutable functional tables, and
effectful merges. The implementation above extends the relational approach to
those semantics; it does not claim the cited systems implement them.

The main remaining performance work is incremental device commits and index
maintenance, device implementations of common primitives, fewer
cardinality synchronizations, and chunked or multiway joins for large
intermediates. Radix sorting and device-side indirect dispatch remain candidates
for reducing work further. Benchmark comparisons should use
`./bench.py`, identify the actual adapter and executable, and account for
transfers, launches, interning, merges and memory as well as join time.
