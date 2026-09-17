# Disequality encodings and a proof benchmark

This is an egglog encoding/proof-overhead experiment inspired by the parameter
analysis in [Dis-Equality Graphs](https://doi.org/10.1145/3704913), not a
reproduction of the paper's native performance results. Neither native artifact
engine is built or measured here. The earlier artifact/integration PRs remain
independent.

## Encodings

`--disequality-encoding nee` (the default) lowers `(disequal a b)` to a private
relation for the operands' equality sort. A self-edge after congruence derives
a contradiction. The paper uses a private `ne` term; the relation preserves
contradiction detection without making its result a unionable equality class.
No symmetry rule is needed for self-edge detection.

`--disequality-encoding ee` uses the paper's five-rule equality embedding:
inequality becomes `eq(a,b) = false`, with lifting, symmetry, double-negation,
and left/right reflexivity rules. A separate equality embedding handles the
private truth sort; equating its `true` and `false` derives contradiction.

`(disequal ...)` also works in rule heads. `(check-contradiction)` saturates the
private encoding ruleset, then positively checks the contradiction relation.
Ordinary `(run ...)` does not run that private ruleset. Both encodings lower to
ordinary egglog before term/proof encoding, without changing union-find.
Existing core restrictions still apply: `begin` blocks are normal-mode only;
the benchmark uses individual top-level actions and needs no batching support.

`--proofs` records proofs; it does not verify them. `--proof-extraction` extracts
and simplifies the proof of the final check. `--proof-testing` additionally
checks that derivation against the lowered program, including the encoding
rules. This is not a separate machine-checked proof that the compiler pass
implements the paper's semantics.

## Workload and regeneration

The regeneration script downloads [the pinned artifact](https://zenodo.org/records/13938878),
verifies the complete archive and generator hashes, and extracts only
`parameter-analysis/rand_exprs.py` into a local cache. It executes that file
unchanged, retains its first 60,000 expressions, and calls its own `gen(5)` for
the remainder using the same seeded random stream. No artifact source is
vendored, no native engine is executed, and only the reviewed generator member
is run.

Adjacent expressions form pairs: the first 10,000 pairs are disequalities and
the next 100,000 are equalities. The benchmark also asserts the ten distinct
numeral pairs described by the paper; the archive driver's off-by-one loop
asserts only six. Numerals become `N1` through `N5`, with `f`, `g`, and `h`
retaining their original arities. Every assertion is a top-level action.

Selection tries successive seeds, accepting the first contradiction confirmed
by both encodings and checked in both encodings under `--proof-testing`. It neither filters pairs
nor appends an artificial contradiction. An ordinary consistent result permits
a retry; disagreement, timeout, crash, or proof failure stops selection.
This conditioning makes the fixture suitable for measuring contradiction proofs,
not for estimating the frequency of contradictions or unbiased random-input
performance. Generation and selection are outside the timed benchmark.

```sh
cargo build --release -p egglog-experimental
uv run --locked python benchmarks/disequality/generate.py
```

The accepted seed and Python version are recorded in the `.egg` header. To
reproduce that exact fixture, use that Python version and the recorded seed
with `--max-attempts 1`. The archive and original generator stay in the ignored
user cache; the full `.egg` file is the reviewable, runnable benchmark artifact.

The committed fixture uses seed **2026** and CPython **3.13.11**. Seed 2025 was
consistent in both encodings; 2026 was the first contradictory candidate. Both
encodings passed strict proof checking before the fixture was accepted.
The 62,910,081-byte file has SHA-256
`88ea961380031ea7cd46f805888bdba638d3a86cb8da67191938044abdae83f3`.

```sh
uv run --python 3.13.11 --locked python benchmarks/disequality/generate.py --seed 2026 --max-attempts 1
```

## Comparisons

The runner records both endpoint encodings in its cache and report. Old report
caches require recomputation after the schema change. These comparisons include
parsing, compilation, ingestion, propagation, and the selected proof work:

The full-size proof runs take minutes and substantial memory. The benchmark
and regeneration timeout defaults are 30 minutes per process, not an expected
runtime. Use `--rounds 1` for an initial diagnostic; the runner normally collects
six observations per endpoint. Missing or timed-out results are not speedups.
The full workload is included by default in `./bench.py`, but not in the CI
`make benchmark-smoke` target, which uses small fixtures.

```sh
# NE: proof recording versus ordinary execution.
./bench.py benchmarks/disequality/parameter-analysis.egg --report /tmp/ne-proof-overhead.jsonl

# EE versus NE, both without proof recording.
./bench.py benchmarks/disequality/parameter-analysis.egg --treatment off --compare-treatment off \
  --disequality-encoding ee --compare-disequality-encoding nee --report /tmp/ee-vs-ne.jsonl

# Optional EE strict-proof run; not part of the recorded timing comparison.
./bench.py benchmarks/disequality/parameter-analysis.egg --treatment proof-testing \
  --disequality-encoding ee --compare-disequality-encoding ee --report /tmp/ee-proof-checking.jsonl
```

Existing native egg treatments remain limited to the Math workload. This PR
does not implement native disequality comparisons, OEE, DE, EUF, or Propel.

## Small examples and snapshots

`egglog-experimental/tests/disequality/` contains a congruence example and a
rule-head/multiple-sort example. Each has runnable NE and EE desugared snapshots.
Their integration test checks all five execution modes and verifies that the
snapshots match the compiler output. Regenerate only these small snapshots with:

```sh
UPDATE_DISEQUALITY_SNAPSHOTS=1 cargo test -p egglog-experimental --test disequality
```

Negative tests separately ensure that consistent inputs do not prove a
contradiction. Full-size timing and validation results belong in the performance
[report](PERFORMANCE.md); raw output is kept outside git.
