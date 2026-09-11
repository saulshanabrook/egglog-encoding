# Disequality performance analysis

Run date: 2026-09-11

This report measures the three case studies from *Dis/Equality Graphs* after
reducing the second stacked PR. It distinguishes the cost of the compiled
disequality rules from the cost of loading terms, running egglog, and crossing
the host boundary. These measurements are diagnostic; this PR does not claim
native performance parity.

## Result summary

- The reduced branch passes its performance regression gate. Across eight NEE/DE workloads,
  every reduced-versus-old-PR delta is between -12.01% and +1.07%. The large
  negative value is not claimed as a speedup, and no workload regressed by
  more than 10% in either endpoint order.
- Parameter analysis takes about 5.0 seconds under every egglog encoding. The
  private disequality schedule takes 0.2-11.6 milliseconds; term
  reconstruction, pair traversal, and time outside measured rulesets dominate.
- Propel's egglog NEE path is 3.57-3.65x the native DE time on `gset_comm` and
  6.13-6.26x on `tip_bin_plus_assoc`. Set-backed DE is slower at 3.80-3.89x
  and 7.42-7.70x, respectively.
- In the bounded 128-program Propel audit, all 329 completed egglog-to-native
  comparisons matched. Timeouts leave 199 individual runs unknown; 79
  benchmarks completed under all five tested variants.
- On the two published EUF inputs, egglog NEE is 10.37-10.82x the native
  `disegg` DE time; set-backed egglog DE is 17.86-18.43x. The paper's native
  egg EE backend is substantially slower than both egglog paths on these
  inputs, but that compares different disequality representations.

## Environment and method

- Apple M4, 16 GiB RAM, arm64 macOS 26.6 (Darwin 25.6.0)
- Rust/Cargo 1.91.0, uv 0.12.13, Hyperfine 1.20.0
- release builds, recording disabled, and the paper-faithful Vec term language
- three accepted runs after one warmup for Propel and EUF
- both forward and exact reverse endpoint order for every Hyperfine comparison
- three interleaved trials for parameter analysis

The preserved endpoint is PR #63 head `87fab7d813f79bbc116adb88fa2cc0471ff2f197`.
The reduced endpoint is the finalized functional tree at
`43f4dd48e859f113a5ed9858221f528f9ed33b1a`. Only this report and PR metadata
changed after the measurement. Executable hashes identify the measured
programs exactly; the final one-commit PR head is recorded in the canonical
GitHub PR body.

| Endpoint | Program | SHA-256 |
| --- | --- | --- |
| preserved PR | Propel | `cfe15b07e905ec0c38524fe57f89cc24df54153c294bb7a77c5dd01418e3653d` |
| reduced PR | Propel | `73502361ef88794c9de3b1d72aa4c45baad4b5b658d3e05e47402e97b1b10014` |
| preserved PR | EUF solver | `38f44062cc0e47c773832c438289e60928206a73b5c45fbbd25017018f8f72a1` |
| reduced PR | EUF solver | `3b6a2c308b7a5adc5fd194e28700a78a5ca290167608af1b4a290a84ac7872b5` |

## Reduction regression gate

The table reports `(reduced / preserved - 1)` from separate forward and
reverse-order Hyperfine invocations. Negative values are not claimed as
speedups at this sample size.

| Workload | Encoding | Forward | Reverse |
| --- | --- | ---: | ---: |
| EUF `uf.815405` | DE | +0.62% | +0.08% |
| EUF `uf.815405` | NEE | -0.66% | +0.41% |
| EUF `uf.614981` | DE | -2.22% | -0.06% |
| EUF `uf.614981` | NEE | -0.45% | -0.06% |
| Propel `gset_comm` | DE | -0.14% | -3.21% |
| Propel `gset_comm` | NEE | +1.07% | -1.08% |
| Propel `tip_bin_plus_assoc` | DE | -0.40% | -12.01% |
| Propel `tip_bin_plus_assoc` | NEE | -1.68% | -0.29% |

The predeclared blocker was a slowdown above 10% in both orders. The gate
passes: no arm crosses that threshold in either order. The -12.01% reverse
result is not repeated by its forward arm and is treated as noise, not as an
improvement claim. The reduction removes report generation and unused
integration surface without materially changing the ordinary execution path.

## Parameter analysis

The egglog program loads generated TSV relations, reconstructs 60,000 source
expressions, traverses 30,000 equality/disequality pairs, and invokes the
selected private disequality schedule. The native artifact programs parse the
same SHA-verified `exprs.in` and call egg or disegg directly.

Values below are medians across three interleaved trials. Ranges are the minimum
and maximum observed wall times.

| Implementation | Wall median (range) | Private schedule | Matching native wall | Wall ratio |
| --- | ---: | ---: | ---: | ---: |
| egglog EE | 5.030 s (5.016-5.513) | 11.603 ms | egg EE 1.031 s | 4.88x |
| egglog OEE | 4.991 s (4.961-5.114) | 1.335 ms | egg EE 1.031 s | 4.84x |
| egglog NEE | 4.988 s (4.976-4.998) | 0.197 ms | disegg DE 0.744 s | 6.71x |
| egglog DE | 5.009 s (4.958-5.014) | 3.683 ms | disegg DE 0.744 s | 6.73x |

The timing summary localizes most egglog time:

| Encoding | Term rules | Pair rules | Private schedule | Outside measured rulesets |
| --- | ---: | ---: | ---: | ---: |
| EE | 2.622 s | 0.567 s | 11.603 ms | 1.829 s |
| OEE | 2.597 s | 0.584 s | 1.335 ms | 1.808 s |
| NEE | 2.609 s | 0.568 s | 0.197 ms | 1.808 s |
| DE | 2.602 s | 0.574 s | 3.683 ms | 1.826 s |

This case study does not show a meaningful end-to-end difference among the
four egglog encodings. It mainly measures relational input reconstruction and
general engine work. The schedule values exclude set construction, set merges,
and rebuild work that DE can trigger outside its private ruleset, so the DE
schedule alone is not its complete representation cost.

## Propel

Propel retains its parser, evaluator, induction strategy, and graph lifecycle.
The egglog variants replace its equality-graph operations with AST commands sent
through the Rust C ABI. The table reports arithmetic means from both endpoint
orders; each cell includes the egglog/native ratio for that order.

| Workload | Native DE | Egglog NEE | Egglog DE |
| --- | ---: | ---: | ---: |
| `gset_comm`, forward | 45.2 ms | 164.8 ms (3.65x) | 175.8 ms (3.89x) |
| `gset_comm`, reverse | 46.4 ms | 165.6 ms (3.57x) | 176.6 ms (3.80x) |
| `tip_bin_plus_assoc`, forward | 0.567 s | 3.549 s (6.26x) | 4.368 s (7.70x) |
| `tip_bin_plus_assoc`, reverse | 0.591 s | 3.620 s (6.13x) | 4.383 s (7.42x) |

The larger input amplifies graph cloning, command dispatch, queries, and
database/rebuild work. The increasing gap between NEE and set-backed DE also
points to set canonicalization and merge work as a useful profiling target.
Input parsing is shared by the native and egglog variants inside the same
Propel binary, so it does not explain most of these ratios.

The separate corpus audit used a 10-second timeout for native DE and all four
egglog encodings. Every one of the 329 completed egglog-to-native comparisons
matched; 199 of 640 individual runs timed out, and 79 of 128 benchmarks were
fully complete. No timeout is treated as agreement or disagreement. The raw
JSON remained in `/tmp` with SHA-256
`ff7546616c691ace7bec89873914fac7ca2e1ef087fc93e5912896a449bd7b24`.

## EUF solver

The six backends share the artifact's SMT parser, CNF conversion, and MiniSat
candidate-assignment enumeration. For each candidate assignment, the egglog
path clones a compiled template, applies unions and disequalities, and checks
consistency. The table reports arithmetic means from both endpoint orders.

| Input | Native disegg DE | Egglog NEE | Egglog DE |
| --- | ---: | ---: | ---: |
| `uf.815405`, forward | 47.1 ms | 0.495 s (10.51x) | 0.853 s (18.11x) |
| `uf.815405`, reverse | 47.8 ms | 0.496 s (10.37x) | 0.854 s (17.86x) |
| `uf.614981`, forward | 0.440 s | 4.759 s (10.82x) | 8.103 s (18.43x) |
| `uf.614981`, reverse | 0.442 s | 4.759 s (10.76x) | 8.106 s (18.33x) |

For context, native egg EE took 1.24-1.43 seconds on `uf.815405` and
40.09-40.18 seconds on `uf.614981`. Egglog NEE and DE beat that backend here,
but this is not an engine-to-engine parity result: EE saturates an equality
embedding while NEE and DE use different representations. One forward
`uf.815405` egg EE run was a visible high outlier, so the range is reported and
no precise comparison is claimed.

The common parser and SAT solver make the NEE/DE versus disegg ratios primarily
an equality-graph backend difference. Likely costs to measure next are
per-model template cloning, many small AST command batches, generic database
query setup, and set-valued DE rebuilds.

## Optimization priorities

1. Give parameter analysis a bulk typed input path so it does not reconstruct
   millions of occurrence rows through seminaive rules before doing the actual
   equality work.
2. Profile host integrations by phase: template clone, command construction,
   typechecking, execution, rebuild, pair query, global query, and statistics.
3. Batch more host mutations and avoid statistics scans unless the caller asks
   for them.
4. Profile DE's `Set` canonicalization and merge path separately from its
   private schedule. A specialized set representation may be warranted only
   after that evidence exists.
5. Keep source capture opt-in. Rendering and desugaring are review tools and
   should remain outside ordinary benchmark timings.

## Reproduction and provenance

The artifact archive is Zenodo record 13938878, SHA-256
`3e9080ca461457af0a10cfc433a5150952f82f752b4c316df1e03236d93599c4`.
`make` verifies this before extracting any generated input.

```sh
make -C benchmarks/disequality parameter-analysis PARAMETER_TRIALS=3 \
  PARAMETER_RESULTS=/tmp/pr63-parameter-analysis.csv
make -C benchmarks/disequality prepare-euf-input
make -C benchmarks/disequality propel-native
```

The exact reduction-gate endpoint commands were generated by this matrix and
passed to Hyperfine once in the shown order and once in reverse:

```sh
PRESERVED=/tmp/egglog-pr63-preserved
REDUCED="$(git rev-parse --show-toplevel)"
OLD_EUF="$PRESERVED/benchmarks/disequality/euf-solver/target/release/euf-solver"
NEW_EUF="$REDUCED/benchmarks/disequality/euf-solver/target/release/euf-solver"
OLD_PROPEL="$PRESERVED/benchmarks/disequality/inductive-prover/propel/.native/target/scala-3.4.2/propel"
NEW_PROPEL="$REDUCED/benchmarks/disequality/inductive-prover/propel/.native/target/scala-3.4.2/propel"
UF815=/tmp/uf.815405.smt2
UF614="$REDUCED/target/disequality/euf/uf.614981.smt2"
GSET="$REDUCED/benchmarks/disequality/inductive-prover/benchmarks/propel/gset_comm.propel"
TIP="$REDUCED/benchmarks/disequality/inductive-prover/benchmarks/propel/tip_bin_plus_assoc.propel"

for input in "$UF815" "$UF614"; do
  for encoding in egglog-nee egglog-de; do
    old="'$OLD_EUF' '$input' --backend $encoding"
    new="'$NEW_EUF' '$input' --backend $encoding"
    hyperfine --warmup 1 --runs 3 "$old" "$new"
    hyperfine --warmup 1 --runs 3 "$new" "$old"
  done
done
for input in "$GSET" "$TIP"; do
  for encoding in egglog-nee egglog-de; do
    old="'$OLD_PROPEL' -f '$input' --variant $encoding"
    new="'$NEW_PROPEL' -f '$input' --variant $encoding"
    hyperfine --warmup 1 --runs 3 "$old" "$new"
    hyperfine --warmup 1 --runs 3 "$new" "$old"
  done
done
```

The paper-engine comparisons used the same inputs and current binaries with
these concrete backend sets, again in forward and exact reverse order:

```sh
for input in "$UF815" "$UF614"; do
  hyperfine --warmup 1 --runs 3 \
    "'$NEW_EUF' '$input' --backend egg-ee" \
    "'$NEW_EUF' '$input' --backend disegg-de" \
    "'$NEW_EUF' '$input' --backend egglog-nee" \
    "'$NEW_EUF' '$input' --backend egglog-de"
  hyperfine --warmup 1 --runs 3 \
    "'$NEW_EUF' '$input' --backend egglog-de" \
    "'$NEW_EUF' '$input' --backend egglog-nee" \
    "'$NEW_EUF' '$input' --backend disegg-de" \
    "'$NEW_EUF' '$input' --backend egg-ee"
done
for input in "$GSET" "$TIP"; do
  hyperfine --warmup 1 --runs 3 \
    "'$NEW_PROPEL' -f '$input' --variant de" \
    "'$NEW_PROPEL' -f '$input' --variant egglog-nee" \
    "'$NEW_PROPEL' -f '$input' --variant egglog-de"
  hyperfine --warmup 1 --runs 3 \
    "'$NEW_PROPEL' -f '$input' --variant egglog-de" \
    "'$NEW_PROPEL' -f '$input' --variant egglog-nee" \
    "'$NEW_PROPEL' -f '$input' --variant de"
done
```

Input SHA-256 values:

| Input | SHA-256 |
| --- | --- |
| `uf.815405.smt2` | `957697674165b33dc541f2a905e60e7524c314e58b3d74991127d6f598a0a800` |
| `uf.614981.smt2` | `3f6de121f080be7d0b8220993fe72610a2bb50dbb80e9e8a21ef9e056335a5da` |
| `gset_comm.propel` | `e032fdc6c85c82c48993e06336deab5cd0cd2f2fa94aa2cbaf68373c64d8045e` |
| `tip_bin_plus_assoc.propel` | `680ef39351e0de07432b8d195178ed9af92ad5ab7dd2261e304c2501c837df3a` |
| parameter `exprs.in` | `829b712812d7e1c8563e2f9c9dbd5a8b520c967086d05bc407d8f7b733f70638` |

Raw CSV/JSON files remain under `/tmp`. A sorted manifest containing each raw
filename and SHA-256 has SHA-256
`4f530caf30aea95615c2d3e3926749a6431a9138baeed2e4163ae3b195b7570e`.
The parameter CSV itself has SHA-256
`100f9a613b44d488cbf36ddd02eb2cda29d71564cd273378b76c96cc6f461c96`.
The 16 final regression-gate JSON files have a separate sorted SHA-256 manifest
at `/tmp/pr63-final-regression-manifest.sha256`, whose SHA-256 is
`6302db2879d7fc9c3bd55256c84353ea375a864b354e68138a929c468212f02b`.

## Limitations

- Three samples per order expose large effects but are not a publication-grade
  statistical study. Small deltas are treated as noise.
- Timings are from one Apple M4 machine. They do not reproduce the paper's
  hardware or toolchain.
- The EUF and Propel results time NEE and DE, not every cross-product of
  encoding and workload. Parameter analysis supplies the four-encoding
  comparison.
- Vec is the timed term language. Direct constructors are an inspectability
  ablation and are covered by correctness tests, not these timings.
- Disequality encodings are ordinary-mode only in this reduced PR. Proof and
  term-encoding composition is explicitly deferred.
- The native parameter projects are generated under `target/` from verified
  archive members. Their absolute `/disegg` dependency is rewritten to the
  imported Stage 1 checkout and isolated with a generated `[workspace]` table;
  source hashes before and after adaptation are recorded in their manifest.
