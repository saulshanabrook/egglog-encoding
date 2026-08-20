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

## August 20 direct PR-versus-main snapshot

The simplest current public-CLI comparison uses PR base/main
`fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0` and PR head
`cd84530d37571c853cc480642fca8647a5776e35`, the default ten workloads, the
same treatment on both endpoints, and six fresh rounds per endpoint/file. All
360 rows succeeded.

| Mode | Main suite | PR suite | PR/main | 95% Fieller CI | Reading |
| --- | ---: | ---: | ---: | --- | --- |
| off | `3.147 s` | `3.118 s` | `0.9905` | `[0.9771, 1.0041]` | no clear change |
| term | `5.091 s` | `4.935 s` | `0.9692` | `[0.9485, 0.9904]` | 3.1% faster |
| proofs | `7.361 s` | `6.381 s` | `0.8669` | `[0.8481, 0.8865]` | 13.3% faster |

### Per-file wall time

These are the public runner's Markdown confidence intervals from the same six
fresh rounds per endpoint/file. Ratios are PR/main; intervals below `1.0` are
faster, while intervals crossing `1.0` are inconclusive.

#### Term

| File | Main (95% CI) | PR (95% CI) | PR/main (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| math-microbenchmark-rational.egg | 859–901 ms | 907–953 ms | 1.02–1.09x | slower |
| eggcc-2mm-pass1.egg | 1.15–1.27 s | 1.12–1.25 s | 0.903–1.05x | CI includes 1 |
| pointer-analysis-initdb.egg | 137–144 ms | 124–173 ms | 0.886–1.24x | CI includes 1 |
| hardboiled_conv1d_32.egg | 213–221 ms | 195–204 ms | 0.896–0.946x | faster |
| luminal-llama.egg | 1.25–1.28 s | 1.11–1.18 s | 0.876–0.934x | faster |
| herbie.egg | 104–109 ms | 97.4–104 ms | 0.905–0.979x | faster |
| misaal-hvx-dot-product.egg | 103–105 ms | 75.0–80.3 ms | 0.717–0.770x | faster |
| churchroad-wide-multiply.egg | 709–734 ms | 714–726 ms | 0.979–1.02x | CI includes 1 |
| dialegg-nmm40.egg | 266–274 ms | 264–276 ms | 0.973–1.03x | CI includes 1 |
| speq-preserved-reference-suite.egg | 165–181 ms | 158–163 ms | 0.886–0.976x | faster |

#### Proofs

| File | Main (95% CI) | PR (95% CI) | PR/main (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| math-microbenchmark-rational.egg | 1.52–1.74 s | 1.50–1.54 s | 0.869–1.00x | CI includes 1 |
| eggcc-2mm-pass1.egg | 1.56–1.71 s | 1.41–1.45 s | 0.833–0.918x | faster |
| pointer-analysis-initdb.egg | 207–226 ms | 197–204 ms | 0.884–0.973x | faster |
| hardboiled_conv1d_32.egg | 309–321 ms | 264–267 ms | 0.826–0.860x | faster |
| luminal-llama.egg | 1.98–2.12 s | 1.59–1.61 s | 0.754–0.811x | faster |
| herbie.egg | 155–166 ms | 141–148 ms | 0.867–0.939x | faster |
| misaal-hvx-dot-product.egg | 146–161 ms | 100–105 ms | 0.636–0.706x | faster |
| churchroad-wide-multiply.egg | 482–517 ms | 473–478 ms | 0.920–0.987x | faster |
| dialegg-nmm40.egg | 474–525 ms | 467–473 ms | 0.895–0.993x | faster |
| speq-preserved-reference-suite.egg | 194–215 ms | 176–179 ms | 0.824–0.914x | faster |

The public phase decomposition attributes the proofs suite's `979 ms` mean
reduction primarily to `828 ms` less typechecking. The typed path adds `117 ms`
of other frontend work, while program rules, equality/rebuild, commands, and
the residual are also lower in this snapshot. Term saves `358 ms` of
typechecking but adds `75 ms` of frontend work and smaller runtime increases,
for a net `157 ms` reduction. Off's `30 ms` point improvement is statistically
inconclusive.

This is deliberately the straightforward baseline-first `./bench.py` run, not
the preregistered balanced final gate. Main ran first in every mode, and its
first off block immediately followed a `22.27 s` release build. Treat these as
the clearest current snapshot rather than replacing the archived balanced
evidence or its caveats.

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
