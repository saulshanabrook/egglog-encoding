# PR 69 performance evidence disposition

This note supersedes the interpretation, not the contents, of the sealed
August 19 archive for baseline `fdd4eac12c1` and candidate `1c974cf99a8`.
The raw JSONL, original `provenance.md` and `results.md`, and checksum
manifests remain byte-for-byte unchanged. All archived checksums verify;
the SHA-256 of `archive-files.sha256` is
`ce79dbfe6e36cabd30d58f3b1dc57bc35546e0e13a2f1b1f1ede9e13ee1b3b38`.

The archived `term` ratio `0.887905` and `proofs` ratio `0.859259` are
reproducible calculations from the recorded rows, but they are withdrawn as
overall speedup and follow-up-sizing claims. Both collections contain visible
unmonitored timing transients. No post-hoc subset is substituted for them;
decision-bearing timing requires a continuously monitored run that also passes
the clean-machine and observer-budget gates. The August 20 observer-control
campaign described below was continuously monitored, but it was intentionally
collected under an environment override and fails those gates.

The comparatively stable `off` collection measured `1.003608`, 95% Fieller CI
`[0.993136, 1.014144]`, consistent with no measured off-mode change in that run.
The durable causal claim is structural: generated proof commands no longer
re-enter source parsing, desugaring, typechecking, or `remove_globals`. A
permanent call-counting regression covers the complete `add_term_encoding` plus
`resolve_generated_batch` window; archived phase timings have the expected
direction, but their exact magnitude is not clean sizing evidence.

Churchroad remains a performance risk. Its proofs-mode point estimate was
`1.011920`, CI `[1.000121, 1.023817]`, initially and `1.023252`,
CI `[0.999861, 1.046852]`, on retest. The slowdown direction reproduced and
the point estimate grew; the retest made statistical boundedness inconclusive
rather than showing that the slowdown disappeared.

Four proof workloads retained `CI high < 1` in both collections. Treat these as
workload-level witnesses, not an overall PR speedup percentage.

## August 20 observer-control campaign

This diagnostic campaign compares two binaries with the same final PR source:

- observer-free control `d208575d62b9cecda4494a3f80c9d7ebdb2e0450`;
- timer-instrumented `b33984b527ab0dd9b19c7b6f566f5f101f855f24`.

It does **not** compare PR #69 with main. Its purpose is to bound the overhead
of four mutually exclusive generated-frontend counters—construct, signatures,
resolve/cache, and lower/materialize—before using those counters to size a
compact-template experiment.

At the user's explicit direction, collection proceeded despite a red machine
gate. The public runner produced 156 excluded warmup rows and 936 measured
rows: a three-file canary and the default ten-file suite, each in `off`, `term`,
and `proofs` with six rounds in both endpoint orders. Every row succeeded. An
independent raw audit verified exact block/file order, schema v5, clean pinned
SHAs, stable distinct binaries, workload hashes, nonnegative timing fields,
and unchanged JSONL digests.

The permanent counter contract also passed end to end:

- all observer-free control counters are zero;
- all timer-instrumented `off` counters are zero;
- every timer-instrumented `term` and `proofs` row has all four counters
  strictly positive.

Ratios below are timer-instrumented/control and use every measured row:

| Scope | Mode | Ratio | 95% Fieller CI | Frozen gate |
| --- | --- | ---: | --- | --- |
| Canary | off | `1.004867` | `[0.997324, 1.012450]` | pass |
| Canary | term | `0.996699` | `[0.989997, 1.003487]` | fail: observer bound `10.0609% > 10%` |
| Canary | proofs | `1.004536` | `[1.000740, 1.008355]` | pass |
| Full | off | `1.006160` | `[1.002694, 1.009635]` | pass: radius `0.9635% <= 1%` |
| Full | term | `1.005119` | `[1.002317, 1.007928]` | fail: observer bound `12.5461% > 5%` |
| Full | proofs | `0.992187` | `[0.982788, 1.001599]` | fail: observer bound `16.7541% > 5%` |

All suite point-difference and per-file guards passed, but full proofs had a
material endpoint-order split: `1.000300` control-first versus `0.983969`
instrumented-first.

The full-suite generated pools were `303.287 ms` in term mode and `652.119 ms`
in proofs mode per suite observation. Construction was the largest descriptive
leaf (`111.619 ms` term; `286.287 ms` proofs), followed by lower/materialize,
signatures, and resolve/cache. These are not accepted optimization budgets:
the observer-bound gates failed and the measurements were environmentally
contaminated.

The 0.1-second process monitor covered every row, but iTerm2 exceeded 5% CPU in
all 4,612 measured-window samples (mean `73.68%`, maximum `107.0%`).
WindowServer, XProtect, `duetexpertd`, Codex, indexing, media, and other system
work also overlapped observations. Therefore the campaign is valid only as
schema, provenance, and counter-shape evidence. Its timing must not be pooled
into PR performance claims, and it does not authorize compact-template work.

Upstream winner-recording and duplicate-solving remain tracked solely in
issue #76.
