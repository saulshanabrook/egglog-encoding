# AST-first host integration follow-up

Run date: 2026-09-10 (America/Los_Angeles)

This report measures the final AST-first EUF and Propel host integrations
against the clean merged branch immediately before the refactor. Raw Hyperfine
JSON stays under `/tmp`; this file preserves the revisions, hashes, commands,
accepted summaries, and limitations needed to audit the result.

## Revisions and hashes

| Item | Revision or SHA-256 |
| --- | --- |
| merged baseline | `4737838d853f988ae550a64af8f0c9621e7584ef` |
| `origin/main` merged into the baseline | `82aab2a5ea4e37a46310a5ee97e02fec156fcc77` |
| measured AST-first implementation | `069d9ac45d9da281ba4eb1803a39b0ad27d6357a` |
| baseline Propel executable | `e884328b02af4455f54746b2a28b3645892f37fd71fe9c25d117c255bce1cf76` |
| candidate Propel executable | `3dc2bd94929827c2601b6f808a14c98d600c554ba97242576bef4b89b6c8a6da` |
| baseline EUF executable | `3095a62c13ca21df6d956f4787b84dd3be92fec99eb49b3fe77abb970eb2e04a` |
| candidate EUF executable | `2cf470583d4e6fb73de44955cfea52eb1e309bcc8c6fa83541c67a70a8f3800a` |
| `gset_comm.propel` | `e032fdc6c85c82c48993e06336deab5cd0cd2f2fa94aa2cbaf68373c64d8045e` |
| `tip_bin_plus_assoc.propel` | `680ef39351e0de07432b8d195178ed9af92ad5ab7dd2261e304c2501c837df3a` |
| `uf.815405.smt2` | `957697674165b33dc541f2a905e60e7524c314e58b3d74991127d6f598a0a800` |
| `uf.614981.smt2` | `3f6de121f080be7d0b8220993fe72610a2bb50dbb80e9e8a21ef9e056335a5da` |

Both worktrees were clean when their release executables were built. The
candidate includes the same merged base as the baseline. Measurements used an
Apple M4 with 16 GiB RAM, arm64 macOS 26.6 (Darwin 25.6.0), Hyperfine 1.20.0,
Rust/Cargo 1.91.0, and uv 0.12.12.

## Result

All ordinary candidate-versus-baseline comparisons had less than a 10%
slowdown in each endpoint order. The largest directional mean slowdown was
5.42% (`tip_bin_plus_assoc`, DE). The landing gate was a slowdown above 10% in
both orders, so the refactor passes that gate.

Times below are arithmetic mean +/- sample standard deviation. Forward order
is baseline DE, candidate DE, baseline NEE, candidate NEE. Reverse order is the
exact reverse.

| Workload | Encoding | Forward baseline -> candidate | Reverse baseline -> candidate |
| --- | --- | ---: | ---: |
| Propel `gset_comm` | DE | 194.9 +/- 1.1 -> 202.8 +/- 0.9 ms (+4.05%) | 194.5 +/- 0.8 -> 203.9 +/- 2.0 ms (+4.79%) |
| Propel `gset_comm` | NEE | 184.3 +/- 1.9 -> 189.1 +/- 0.6 ms (+2.61%) | 190.1 +/- 17.4 -> 192.5 +/- 6.5 ms (+1.27%) |
| Propel `tip_bin_plus_assoc` | DE | 4.480 +/- 0.140 -> 4.645 +/- 0.004 s (+3.68%) | 4.392 +/- 0.026 -> 4.630 +/- 0.014 s (+5.42%) |
| Propel `tip_bin_plus_assoc` | NEE | 3.607 +/- 0.066 -> 3.793 +/- 0.003 s (+5.18%) | 3.610 +/- 0.049 -> 3.796 +/- 0.007 s (+5.16%) |
| EUF `uf.815405` | DE | 893.6 +/- 4.4 -> 911.2 +/- 6.6 ms (+1.97%) | 903.4 +/- 8.1 -> 916.9 +/- 12.7 ms (+1.50%) |
| EUF `uf.815405` | NEE | 509.1 +/- 1.0 -> 524.6 +/- 7.9 ms (+3.04%) | 528.1 +/- 25.1 -> 524.6 +/- 9.2 ms (-0.66%) |
| EUF `uf.614981` | DE | 8.621 +/- 0.106 -> 8.533 +/- 0.144 s (-1.03%) | 9.059 +/- 0.293 -> 8.534 +/- 0.006 s (-5.80%) |
| EUF `uf.614981` | NEE | 4.860 +/- 0.004 -> 4.997 +/- 0.010 s (+2.82%) | 4.881 +/- 0.004 -> 5.024 +/- 0.046 s (+2.94%) |

The reverse `gset_comm` baseline NEE samples and reverse `uf.815405` baseline
NEE samples contain visible high outliers. Reverse `uf.614981` baseline DE is
also noisier than the candidate. The paired orders prevent those observations
from being presented as speedups or precise regression estimates.

## Source-export ablation

Normal candidate runs above do not record a replay. With NEE `gset_comm`,
enabling `--emit-source-dir` changes the mean from 182.2 +/- 2.8 to
211.4 +/- 0.8 ms (+16.06%) in forward order and from 179.9 +/- 0.7 to
212.7 +/- 2.6 ms (+18.25%) in reverse order. This is
not the cost of AST execution. It combines persistent trace construction,
rendering source from AST `Display`, desugaring, and overwriting 104 files.

## Method and commands

All commands use the paper-faithful Vec term language. EUF omits `--stats`,
while Propel retains its normal per-reduction statistics collection. Propel
small uses two warmups and eight runs per order; Propel medium uses one warmup
and four runs; `uf.815405` uses two warmups and five runs; `uf.614981` uses two
warmups and three runs. No sample inside a completed invocation was removed.

```sh
BASE_PROPEL=/path/to/4737838d/propel
CAND_PROPEL=/path/to/069d9ac4/propel
BASE_EUF=/path/to/4737838d/euf-solver
CAND_EUF=/path/to/069d9ac4/euf-solver
GSET=benchmarks/disequality/inductive-prover/benchmarks/propel/gset_comm.propel
TIP=benchmarks/disequality/inductive-prover/benchmarks/propel/tip_bin_plus_assoc.propel
EUF_815405=/tmp/egglog-ast-first-euf-inputs/uf.815405.smt2
EUF_614981=/tmp/egglog-ast-first-euf-inputs/uf.614981.smt2
OUT=/tmp/egglog-ast-first-perf-20260910
```

Each Propel input used this command shape, once in the displayed order and
once with all four endpoints reversed:

```sh
hyperfine --warmup WARMUPS --runs RUNS --export-json "$OUT/OUTPUT.json" \
  -n baseline-de "$BASE_PROPEL -f INPUT --variant egglog-de --term-language vec >/dev/null" \
  -n candidate-de "$CAND_PROPEL -f INPUT --variant egglog-de --term-language vec >/dev/null" \
  -n baseline-nee "$BASE_PROPEL -f INPUT --variant egglog-nee --term-language vec >/dev/null" \
  -n candidate-nee "$CAND_PROPEL -f INPUT --variant egglog-nee --term-language vec >/dev/null"
```

The EUF inputs used the same order and this command shape:

```sh
hyperfine --warmup 2 --runs RUNS --export-json "$OUT/OUTPUT.json" \
  -n baseline-de "$BASE_EUF INPUT --backend egglog-de --term-language vec >/dev/null" \
  -n candidate-de "$CAND_EUF INPUT --backend egglog-de --term-language vec >/dev/null" \
  -n baseline-nee "$BASE_EUF INPUT --backend egglog-nee --term-language vec >/dev/null" \
  -n candidate-nee "$CAND_EUF INPUT --backend egglog-nee --term-language vec >/dev/null"
```

The export ablation used eight runs per order after two warmups:

```sh
CAPTURE="$OUT/captures"
hyperfine --warmup 2 --runs 8 --export-json "$OUT/recording-overhead-forward.json" \
  -n recording-off "$CAND_PROPEL -f $GSET --variant egglog-nee --term-language vec >/dev/null" \
  -n recording-and-export "$CAND_PROPEL -f $GSET --variant egglog-nee --term-language vec --emit-source-dir $CAPTURE >/dev/null"
```

The reverse invocation swaps the two export-ablation endpoints.

## Raw-output hashes

These files remain machine-local under `/tmp/egglog-ast-first-perf-20260910`.

| Hyperfine output | SHA-256 |
| --- | --- |
| `propel-gset-forward.json` | `1a6bbba9a1d67e78e43a2946441df9b2af5fc40b5f6e897bc457c442b433c3fd` |
| `propel-gset-reverse.json` | `32c4842297d79deb35b9d8f436d96051f6ca08ef95f0ed8a2fc45a436fe461b0` |
| `propel-tip-forward.json` | `ffd533ce68c477a5025d825f491a8d7069d5c13549b7ce25e7caec652f4d1229` |
| `propel-tip-reverse.json` | `3e42e54847215328416c1411a7ba88f6b0228ee58593f8d43708e7b283bad748` |
| `euf-815405-forward.json` | `94677e000ccc0170092ecbd4afd6336b357d33ae106cc8c353691a794a7f58b1` |
| `euf-815405-reverse.json` | `4c5ffb8c57739ef6411febed1540ae8756bdd8568c84c3cb87cac4911b6c8c41` |
| `euf-614981-forward.json` | `405be8de1417d3da16406c2484a47cf74b84124503ce5001ec4a3dc6665b7c98` |
| `euf-614981-reverse.json` | `c82c33c88b2391268d718b0cbf14d0ba51f338ee374ea906b793f0bcff81a198` |
| `recording-overhead-forward.json` | `fbefebdfca61cb0e9c77edee431c270d8992f5d989612d02fb54c320194e68ef` |
| `recording-overhead-reverse.json` | `47a48d6e5eb6d15f3944d674fe46f7d8a4874e0184aa176c2f18096d80d1f7a8` |

## Limitations

- This is an end-to-end regression gate, not a publication-quality confidence
  interval and not a claim of parity with the paper's native engines.
- Only DE and NEE were timed because they exercise the materially different
  retained representations. EE and OEE remain covered by semantic tests and
  the source-replay matrix.
- The two EUF inputs are published stress cases, not the complete corpus.
- The source-export ablation includes trace creation, rendering, desugaring,
  and filesystem writes; it does not isolate any one component.
- The persistent AST trace shares clone prefixes, but ordinary benchmark runs
  do not create it unless source export is requested.

## Semantic parity reports

The final bounded Propel audits retain all timeout rows as unknown. Vec matches
332/332 comparable outcomes, with 81 programs fully complete and 196 timeout
rows. Direct constructors match 251/251 comparable outcomes, with 59 programs
fully complete and 280 timeout rows. Both reports contain zero execution
errors and zero mismatches. Completion at this short boundary is load-sensitive
and is not a term-language performance comparison.

| Report | Source state | SHA-256 |
| --- | --- | --- |
| `../propel-parity.json` | clean `069d9ac4` | `8f3cc6e1e0b1a3e0c44c280a0f1cf2be9a277baf3441808c3342a615f49bb1e1` |
| `../propel-direct-parity.json` | clean `eaabcbaa` | `e6ab537dca47208164e199684b281d2e980d53d51d007991e80cf98952d8d693` |
