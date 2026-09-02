# Relational NEE follow-up

Run date: 2026-09-02

This follow-up compares the previous result-producing NEE constructor with the
binary-relation realization that replaced it. Both executables use Propel's
default Vec term language and differ only in the NEE support declaration.

- constructor source: clean commit
  `e11f3f578919b8be938d5847beac63d328d1bc3c`
- constructor executable SHA-256:
  `e8ae31aeb3c46799db8846f02204ea5b3456e47835fc8cbc86b9115d45070570`
- relation source: the NEE relation change applied to `e11f3f57`; that source
  diff is retained by the commit containing this report
- measured relation executable SHA-256:
  `80bcca6fc1b5942076240028c788998470c9019c7afcc891901261b7266fec79`
- `gset_comm.propel` SHA-256:
  `e032fdc6c85c82c48993e06336deab5cd0cd2f2fa94aa2cbaf68373c64d8045e`
- `tip_bin_plus_assoc.propel` SHA-256:
  `680ef39351e0de07432b8d195178ed9af92ad5ab7dd2261e304c2501c837df3a`
- Apple M4, 16 GiB RAM, arm64 macOS 26.6 (`Darwin 25.6.0`)
- Rust/Cargo 1.91.0, uv 0.12.6, Hyperfine 1.20.0

Each invocation used one warmup. Small Propel used seven samples per endpoint
order; medium Propel used three. Every sample is retained in the four JSON
files, and `SHA256SUMS` hashes those files.

```sh
BASE=/tmp/propel-nee-constructor-e11f3f57
CAND=benchmarks/disequality/inductive-prover/propel/.native/target/scala-3.4.2/propel
GSET=benchmarks/disequality/inductive-prover/benchmarks/propel/gset_comm.propel
MEDIUM=benchmarks/disequality/inductive-prover/benchmarks/propel/tip_bin_plus_assoc.propel

hyperfine --warmup 1 --runs 7 \
  -n constructor "$BASE -f $GSET --variant egglog-nee --term-language vec >/dev/null" \
  -n relation "$CAND -f $GSET --variant egglog-nee --term-language vec >/dev/null"

hyperfine --warmup 1 --runs 7 \
  -n relation "$CAND -f $GSET --variant egglog-nee --term-language vec >/dev/null" \
  -n constructor "$BASE -f $GSET --variant egglog-nee --term-language vec >/dev/null"

hyperfine --warmup 1 --runs 3 \
  -n constructor "$BASE -f $MEDIUM --variant egglog-nee --term-language vec >/dev/null" \
  -n relation "$CAND -f $MEDIUM --variant egglog-nee --term-language vec >/dev/null"

hyperfine --warmup 1 --runs 3 \
  -n relation "$CAND -f $MEDIUM --variant egglog-nee --term-language vec >/dev/null" \
  -n constructor "$BASE -f $MEDIUM --variant egglog-nee --term-language vec >/dev/null"
```

Pooled medians are 176.8 ms for the constructor and 177.2 ms for the relation
on `gset_comm` (relation/constructor 1.002x), and 4.883 s versus 4.940 s on
`tip_bin_plus_assoc` (1.012x). Directional mean ratios range from 1.003x to
1.008x on the small input and 1.006x to 1.019x on the medium input. These
descriptive samples show parity, not a relation speedup.
