# Typed host AST follow-up

Run date: 2026-09-01 (America/Los_Angeles)

These files compare the final typed-AST host adapter with its immediate clean
parent. The parent renders and reparses mutation batches and retains operation
history in every graph. The candidate constructs `egglog::ast` commands,
submits them through `EGraph::run_program`, and records interactions only when
source export is requested.

## Revisions and hashes

| Item | Revision or SHA-256 |
| --- | --- |
| source-reparse baseline | `6b3f7b8981be086fab768e79cc0cd23cca943748` |
| typed-AST candidate | `d5a463bf17f099f26965a72503f756185855711e` |
| baseline Propel executable | `b2ed9fadf11a9c9bb99e02de712f2acc3cbcc686ba642b404fbae92104f20ac9` |
| candidate Propel executable | `c3a6df9bb9431b4d19dd3b95a41d3903824d402e8c6cc012ce00b4e941ac2005` |
| baseline EUF executable | `8946fe21dc5303f88ce663c85669055f253a212976fe69279e4691f512f8ce6b` |
| candidate EUF executable | `728d315e28c94aa9dfc51f8653eab90d6f00cacbd5ceaf5c8b1262b7c1d5b2ec` |
| `gset_comm.propel` | `e032fdc6c85c82c48993e06336deab5cd0cd2f2fa94aa2cbaf68373c64d8045e` |
| `tip_bin_plus_assoc.propel` | `680ef39351e0de07432b8d195178ed9af92ad5ab7dd2261e304c2501c837df3a` |
| `tests/sat.smt2` | `f0cdba8a3ae11f943ff878897e7513013adc52d7b30623be9c0b5a5fd2990f61` |

Both source trees were clean when their release executables were built. The
complete machine-readable provenance is in `provenance.json`.

## Method

Propel and EUF use the paper-faithful Vec term language. DE and NEE were
measured because they exercise the two materially different retained
representations. Each workload was run in forward and reverse endpoint order;
no accepted sample was removed. `gset_comm` and the recording ablation use
eight runs per order, `tip_bin_plus_assoc` uses four, and the tiny EUF fixture
uses 30. Hyperfine warned that the EUF commands complete below 5 ms, so those
results are retained only as a regression smoke.

Combined medians and full ranges:

| Workload | Encoding | baseline | candidate | Candidate delta |
| --- | --- | ---: | ---: | ---: |
| Propel `gset_comm` | DE | 207.7 ms (195.6-237.6) | 200.8 ms (185.5-236.0) | -3.3% |
| Propel `gset_comm` | NEE | 195.7 ms (189.2-207.3) | 192.3 ms (183.8-322.5) | -1.7% |
| Propel `tip_bin_plus_assoc` | DE | 7.400 s (7.062-8.236) | 7.163 s (6.988-7.793) | -3.2% |
| Propel `tip_bin_plus_assoc` | NEE | 5.657 s (5.415-5.986) | 5.430 s (5.178-6.288) | -4.0% |
| EUF `sat.smt2` | DE | 3.022 ms (2.566-5.043) | 2.961 ms (2.397-4.043) | below reliable resolution |
| EUF `sat.smt2` | NEE | 2.986 ms (2.394-4.402) | 2.867 ms (2.303-4.181) | below reliable resolution |

On NEE `gset_comm`, recording disabled had a 177.6 ms median
(174.1-207.3 ms). Recording plus source and desugared export had a 202.1 ms
median (195.5-223.1 ms), or 1.138x. This includes tracing, rendering,
desugaring, and overwriting 104 files, not only trace retention.

## Commands

The variables below identify the four hash-checked executables used in the
accepted run. `BASE_*` came from a clean checkout of the baseline revision;
`CAND_*` came from the candidate checkout.

```sh
BASE_PROPEL=/path/to/6b3f7b89/propel
CAND_PROPEL=benchmarks/disequality/inductive-prover/propel/.native/target/scala-3.4.2/propel
BASE_EUF=/path/to/6b3f7b89/euf-solver
CAND_EUF=benchmarks/disequality/euf-solver/target/release/euf-solver
GSET=benchmarks/disequality/inductive-prover/benchmarks/propel/gset_comm.propel
MEDIUM=benchmarks/disequality/inductive-prover/benchmarks/propel/tip_bin_plus_assoc.propel
EUF_SMALL=benchmarks/disequality/euf-solver/tests/sat.smt2
OUT=benchmarks/disequality/reports/typed-host-ast
```

The Propel commands used the following four command bodies in the listed
forward order, then in exact reverse order:

```sh
hyperfine --warmup 2 --runs 8 --export-json "$OUT/propel-gset-forward.json" \
  -n baseline-de "$BASE_PROPEL -f $GSET --variant egglog-de --term-language vec" \
  -n candidate-de "$CAND_PROPEL -f $GSET --variant egglog-de --term-language vec" \
  -n baseline-nee "$BASE_PROPEL -f $GSET --variant egglog-nee --term-language vec" \
  -n candidate-nee "$CAND_PROPEL -f $GSET --variant egglog-nee --term-language vec"

hyperfine --warmup 2 --runs 8 --export-json "$OUT/propel-gset-reverse.json" \
  -n candidate-nee "$CAND_PROPEL -f $GSET --variant egglog-nee --term-language vec" \
  -n baseline-nee "$BASE_PROPEL -f $GSET --variant egglog-nee --term-language vec" \
  -n candidate-de "$CAND_PROPEL -f $GSET --variant egglog-de --term-language vec" \
  -n baseline-de "$BASE_PROPEL -f $GSET --variant egglog-de --term-language vec"

hyperfine --warmup 1 --runs 4 --export-json "$OUT/propel-medium-forward.json" \
  -n baseline-de "$BASE_PROPEL -f $MEDIUM --variant egglog-de --term-language vec" \
  -n candidate-de "$CAND_PROPEL -f $MEDIUM --variant egglog-de --term-language vec" \
  -n baseline-nee "$BASE_PROPEL -f $MEDIUM --variant egglog-nee --term-language vec" \
  -n candidate-nee "$CAND_PROPEL -f $MEDIUM --variant egglog-nee --term-language vec"

hyperfine --warmup 1 --runs 4 --export-json "$OUT/propel-medium-reverse.json" \
  -n candidate-nee "$CAND_PROPEL -f $MEDIUM --variant egglog-nee --term-language vec" \
  -n baseline-nee "$BASE_PROPEL -f $MEDIUM --variant egglog-nee --term-language vec" \
  -n candidate-de "$CAND_PROPEL -f $MEDIUM --variant egglog-de --term-language vec" \
  -n baseline-de "$BASE_PROPEL -f $MEDIUM --variant egglog-de --term-language vec"
```

The EUF commands used the same forward and reverse order with five warmups and
30 runs:

```sh
hyperfine --warmup 5 --runs 30 --export-json "$OUT/euf-small-forward.json" \
  -n baseline-de "$BASE_EUF $EUF_SMALL --backend egglog-de --term-language vec" \
  -n candidate-de "$CAND_EUF $EUF_SMALL --backend egglog-de --term-language vec" \
  -n baseline-nee "$BASE_EUF $EUF_SMALL --backend egglog-nee --term-language vec" \
  -n candidate-nee "$CAND_EUF $EUF_SMALL --backend egglog-nee --term-language vec"

hyperfine --warmup 5 --runs 30 --export-json "$OUT/euf-small-reverse.json" \
  -n candidate-nee "$CAND_EUF $EUF_SMALL --backend egglog-nee --term-language vec" \
  -n baseline-nee "$BASE_EUF $EUF_SMALL --backend egglog-nee --term-language vec" \
  -n candidate-de "$CAND_EUF $EUF_SMALL --backend egglog-de --term-language vec" \
  -n baseline-de "$BASE_EUF $EUF_SMALL --backend egglog-de --term-language vec"
```

The recording ablation used the candidate NEE `gset_comm` command, first in
the order shown and then reversed:

```sh
CAPTURE=/tmp/typed-host-ast-recording-final
hyperfine --warmup 2 --runs 8 --export-json "$OUT/recording-overhead-forward.json" \
  -n recording-off "$CAND_PROPEL -f $GSET --variant egglog-nee --term-language vec" \
  -n recording-and-export "$CAND_PROPEL -f $GSET --variant egglog-nee --term-language vec --emit-source-dir $CAPTURE"

hyperfine --warmup 2 --runs 8 --export-json "$OUT/recording-overhead-reverse.json" \
  -n recording-and-export "$CAND_PROPEL -f $GSET --variant egglog-nee --term-language vec --emit-source-dir $CAPTURE" \
  -n recording-off "$CAND_PROPEL -f $GSET --variant egglog-nee --term-language vec"
```

`SHA256SUMS` covers the eight raw Hyperfine JSON files and `provenance.json`.
It intentionally excludes this explanatory README.
