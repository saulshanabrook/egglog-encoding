# Set-backed DE follow-up

Run date: 2026-08-19 (America/New_York)

These files retain the balanced measurements used in
[`PERFORMANCE_ANALYSIS.md`](../../PERFORMANCE_ANALYSIS.md). The candidate was an
uncommitted working tree based on
`46a73776ba5b09d5e9fa7d24d8cfa330ab5170b9`; the exact measured executable
hashes are recorded below. The dirty source diff that produced those
executables was not retained and there is no final measured source commit, so
these are hash-identified pre-final measurements rather than
revision-reproducible benchmarks. At final review the local egglog executable
still matched its recorded hash; the local Propel path had since been rebuilt
and no longer matched its recorded hash. Neither measured executable is
committed.

## Environment

- Apple M4, 16 GiB RAM, arm64 macOS, Darwin 25.6.0
- `rustc 1.91.0`
- `uv 0.12.5`
- `hyperfine 1.20.0`
- one egglog worker thread for parameter analysis

## Inputs and executables

| File | SHA-256 |
| --- | --- |
| `target/release/egglog-experimental` | `a6cab75ce3cfc9e63f229983cc549edc235fc53db836734e967dc536b5f2d810` |
| Propel Scala Native executable | `385d74dbc0ac59a892eb57908d86478bba0b5b48b36b83aa4b4e95d875223d14` |
| `parameter-analysis.egg` | `5c8d14e62c7a5f59cd5cb6a43db54161469af798369ed258a29ddd9f4415a152` |
| generated parameter-fact manifest | `d5917bbcbed207f76cbd08b08e6768868620d80cc169f5ca3e0d643a44c5cad1` |
| `gset_comm.propel` | `e032fdc6c85c82c48993e06336deab5cd0cd2f2fa94aa2cbaf68373c64d8045e` |
| `tip_bin_plus_assoc.propel` | `680ef39351e0de07432b8d195178ed9af92ad5ab7dd2261e304c2501c837df3a` |

## Method

Each workload was run in forward and reverse endpoint order after one warmup.
Parameter analysis and `tip_bin_plus_assoc` use three samples per endpoint in
each order. `gset_comm` uses five. No sample was removed. Each Hyperfine JSON
contains command labels and individual timings; the exact invocations are
recorded below.

The four `parameter-*-timing.json` files are separate single runs with
`--timing-summary`; they support only the private-ruleset diagnostic and are
not mixed into the wall-time medians.

The published large EUF inputs were unavailable locally, so this follow-up has
no large-corpus EUF timing. The focused EUF semantic fixtures remain part of
the test gate.

## Commands

These are the exact flags, command bodies, endpoint order, and temporary output
names used for the accepted data. The variables expand to the literal
repository-relative paths used in the original invocations:

```sh
EGGLOG=target/release/egglog-experimental
FACTS=egglog-experimental/benchmarks/disequality/parameter-analysis-facts
PARAMETER=egglog-experimental/tests/disequality/parameter-analysis.egg
PROPEL=benchmarks/disequality/inductive-prover/propel/.native/target/scala-3.4.2/propel
GSET=benchmarks/disequality/inductive-prover/benchmarks/propel/gset_comm.propel
MEDIUM=benchmarks/disequality/inductive-prover/benchmarks/propel/tip_bin_plus_assoc.propel

hyperfine --warmup 1 --runs 3 \
  --export-json /tmp/disequality-set-de-hyperfine.json \
  -n EE "$EGGLOG --disequality-encoding ee --threads 1 --fact-directory $FACTS $PARAMETER" \
  -n OEE "$EGGLOG --disequality-encoding oee --threads 1 --fact-directory $FACTS $PARAMETER" \
  -n NEE "$EGGLOG --disequality-encoding nee --threads 1 --fact-directory $FACTS $PARAMETER" \
  -n DE-set "$EGGLOG --disequality-encoding de --threads 1 --fact-directory $FACTS $PARAMETER"

hyperfine --warmup 1 --runs 3 \
  --export-json /tmp/disequality-set-de-hyperfine-reverse.json \
  -n DE-set "$EGGLOG --disequality-encoding de --threads 1 --fact-directory $FACTS $PARAMETER" \
  -n NEE "$EGGLOG --disequality-encoding nee --threads 1 --fact-directory $FACTS $PARAMETER" \
  -n OEE "$EGGLOG --disequality-encoding oee --threads 1 --fact-directory $FACTS $PARAMETER" \
  -n EE "$EGGLOG --disequality-encoding ee --threads 1 --fact-directory $FACTS $PARAMETER"

hyperfine --warmup 1 --runs 5 \
  --export-json /tmp/disequality-propel-gset-set-de.json \
  -n native-DE "$PROPEL -f $GSET --variant de >/dev/null" \
  -n egglog-EE "$PROPEL -f $GSET --variant egglog-ee --term-language vec >/dev/null" \
  -n egglog-OEE "$PROPEL -f $GSET --variant egglog-oee --term-language vec >/dev/null" \
  -n egglog-NEE "$PROPEL -f $GSET --variant egglog-nee --term-language vec >/dev/null" \
  -n egglog-DE-set "$PROPEL -f $GSET --variant egglog-de --term-language vec >/dev/null"

hyperfine --warmup 1 --runs 5 \
  --export-json /tmp/disequality-propel-gset-set-de-reverse.json \
  -n egglog-DE-set "$PROPEL -f $GSET --variant egglog-de --term-language vec >/dev/null" \
  -n egglog-NEE "$PROPEL -f $GSET --variant egglog-nee --term-language vec >/dev/null" \
  -n egglog-OEE "$PROPEL -f $GSET --variant egglog-oee --term-language vec >/dev/null" \
  -n egglog-EE "$PROPEL -f $GSET --variant egglog-ee --term-language vec >/dev/null" \
  -n native-DE "$PROPEL -f $GSET --variant de >/dev/null"

hyperfine --warmup 1 --runs 3 \
  --export-json /tmp/disequality-propel-medium-set-de.json \
  -n native-DE "$PROPEL -f $MEDIUM --variant de >/dev/null" \
  -n egglog-EE "$PROPEL -f $MEDIUM --variant egglog-ee --term-language vec >/dev/null" \
  -n egglog-OEE "$PROPEL -f $MEDIUM --variant egglog-oee --term-language vec >/dev/null" \
  -n egglog-NEE "$PROPEL -f $MEDIUM --variant egglog-nee --term-language vec >/dev/null" \
  -n egglog-DE-set "$PROPEL -f $MEDIUM --variant egglog-de --term-language vec >/dev/null"

hyperfine --warmup 1 --runs 3 \
  --export-json /tmp/disequality-propel-medium-set-de-reverse.json \
  -n egglog-DE-set "$PROPEL -f $MEDIUM --variant egglog-de --term-language vec >/dev/null" \
  -n egglog-NEE "$PROPEL -f $MEDIUM --variant egglog-nee --term-language vec >/dev/null" \
  -n egglog-OEE "$PROPEL -f $MEDIUM --variant egglog-oee --term-language vec >/dev/null" \
  -n egglog-EE "$PROPEL -f $MEDIUM --variant egglog-ee --term-language vec >/dev/null" \
  -n native-DE "$PROPEL -f $MEDIUM --variant de >/dev/null"

for enc in ee oee nee de; do
  "$EGGLOG" --disequality-encoding "$enc" --threads 1 \
    --fact-directory "$FACTS" \
    --timing-summary "/tmp/disequality-$enc-timing.json" \
    "$PARAMETER" >/dev/null
done
```

The six Hyperfine outputs were copied respectively to `parameter-forward.json`,
`parameter-reverse.json`, `propel-gset-forward.json`,
`propel-gset-reverse.json`, `propel-medium-forward.json`, and
`propel-medium-reverse.json`. The four timing summaries were copied to the
corresponding `parameter-*-timing.json` files. `SHA256SUMS` covers those ten raw
JSON files; it intentionally does not cover this explanatory README.
