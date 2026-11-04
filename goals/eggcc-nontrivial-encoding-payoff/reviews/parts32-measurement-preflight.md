# Parts32 generated-runtime measurement preflight audit

**Verdict: PASS to create the preflight and collect the two frozen sessions.** This is a protocol-readiness verdict, not evidence of a speedup. At audit time, `timing-preflight.json` and all timing-session outputs were absent.

The first attempted preflight subsequently rejected the host under policy v1.
The prospective [process-policy amendment](parts32-process-policy-amendment.md)
supersedes the 10% rule and producer/verifier hashes recorded in this audit.

## Frozen cohort

- Design: `prospective-timing-design-frozen.json`, SHA-256 `c646d77e41334fd252a4e951245068f771afbbb41e44cd828e30edd58b0f6367`.
- Producer: `timing.py`, SHA-256 `339a77000275f0927e5d188e16a38e4e43431dd1a070fafb2fc0efe6af793843`.
- Verifier: `verify-timing.py`, SHA-256 `7bbd66245ead33f1d9cb97f2777a8b76a724f33e105d93dc9a26f4d1fbf910c9`.
- Preparer: `prepare-timing.py`, SHA-256 `57c3d7a9195e7d28e9563936effe26585dd1a9953cc59af31922ab7063861577`.

All declared runtime binaries, optimized Bril files, entry assemblies, source input, candidate compiler, source archive, and source-identity manifest currently match their recorded hashes. `U0`, `B1`, and `SeedOnly` have identical optimized Bril and entry assembly; `Manual` and `Encoding` likewise match one another. Their full binaries remain separately hashed. The three identical-code placebo comparisons therefore test binary/path/startup bias rather than assuming it away.

## Design and estimator

The design covers all five required arms and all seven declared comparisons on three workloads. Each session has 90 cycles, with 32 sequential process invocations in each arm/workload observation and three exact-output warmups per arm/workload. Every 15-cycle block places each arm three times in each position, contains every directed adjacent arm pair three times, and places each workload five times in each position. Session 2 reverses each corresponding arm and workload row.

For each session, workload, and comparison, cycle `c` contributes

`z_c = log(duration_numerator,c / duration_denominator,c)`.

The point estimate is `exp(median(z_c))`. The 95% interval uses 10,000 percentile-bootstrap draws with seed `20261019`, resampling the six complete 15-cycle blocks and retaining all 90 cycle log ratios in each draw. Thus the resampling unit is a complete joint block, with six units per session; individual invocations or rows are never treated as independent bootstrap units. Producer and verifier implementations return byte-for-byte equal synthetic interval results.

Acceptance is prospective and per workload: in each of both sessions, the upper 95% bound must be below `0.99` for `Encoding/U0`, `Manual/U0`, and `Encoding/B1`. The final verifier also rejects the result when any of `B1/U0`, `SeedOnly/B1`, or `Encoding/Manual` has a point estimate below `0.99` in both sessions or above `1.01` in both sessions for the same workload. Workloads and sessions are not pooled.

## Endpoint and evidence integrity

The measured endpoint is generated-program process execution; compilation is excluded. The timer encloses exactly the 32 `subprocess.run` calls. Exit status, empty stderr, exact stdout, output hashing, JSON serialization, process inventories, and fsyncs occur outside that boundary. A synthetic call-order audit confirmed the second timer read precedes every output/status inspection.

Every completed observation is fsynced before the next. Timeouts, nonzero exits, stderr, wrong output, and checkpoint admission failures retain an event and abort the session. The verifier reconstructs warmups, exact session order and positions, row uniqueness/counts, output hashes, row means, every diagnostic and comparison, block bootstrap intervals, all acceptance gates, completion/end-state identity, and current/preflight source and artifact hashes.

The preparer records a privacy-preserving complete process list (`pid`, `ppid`, `%cpu`, `%mem`, and executable `comm`) plus its own cwd/argv. Each session repeats that inventory at start, every 15-cycle boundary, and end. A known compiler/benchmark executable at any utilization, or another process at or above 10% CPU, rejects the checkpoint; snapshot hashes bind the process file, events, summary, and verifier result. The common lock excludes the other Parts32 collectors. `prepare-timing.py` and `verify-timing.py` explicitly reject optimized Python so their assertions cannot be disabled.

Preflight, session directories, summaries, and independent verification use exclusive creation or equivalent fresh-directory refusal, and durable outputs are flushed and fsynced. Partial or rejected artifacts cannot be silently replaced.

## Execution conditions and limits

Run the preparer and producer with host process visibility: a restricted sandbox that denies `ps` correctly produces a rejected process check and is not an admissible measurement environment. The measurement owner must also keep builds, tests, other collectors, and material external work out of the collection window; any checkpoint rejection invalidates the session rather than authorizing a selective rerun.

The host is not CPU-isolated, and boundary inventories cannot prove that no short-lived process ran between checkpoints. Balanced/reversed ordering, two separately required sessions, load metadata, and the three code-identical placebos are the declared controls for that residual risk. A passing result supports only these three workloads and the generated-runtime endpoint. Six block-bootstrap units per session are adequate for the frozen decision rule but do not justify broader workload or machine generalization.

Independent audit checks passed for syntax, frozen hashes, source/artifact identities, all six blocks in both schedules, exact session reversal, estimator parity, timer placement, process-policy reconstruction, and the absence of campaign outputs. No timing samples or preflight were run by this audit.
