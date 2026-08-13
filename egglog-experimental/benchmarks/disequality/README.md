# Disequality encoding validation and benchmark

Run dates: 2026-08-12 through 2026-08-13 (America/New_York)

Implementation base: `46f69b70d0819b03da110e6e785f91c080d58556`
(`origin/main` before this change). The compiler revision used to produce the
checked-in expansions is recorded in
[`desugared/manifest.json`](desugared/manifest.json).

Machine: Apple M4, arm64 macOS 26.6; `rustc 1.91.0`; one egglog worker thread.

## Result

`egglog-experimental` compiles one typed `(disequal lhs rhs)` action to any of
the four representations in Section 2.2 of *Dis/Equality Graphs*: EE, OEE, NEE,
or DE. None changes egglog's union-find, e-class, or congruence-closure code.
The selected extension is ordinary generated egglog declarations, actions,
and rules.

The generated rules are isolated in the private `@disequality` ruleset. They
run only when the source program invokes:

```lisp
(check-disequalities)
```

That command saturates the private ruleset and reports `disequality constraint
contradicted` if a stored constraint has become reflexive. It is a no-op before
the first disequality is compiled. An ordinary `(run)` does not accidentally
run extension rules. Generated names use egglog's reserved `@` prefix, which
ordinary source programs cannot forge.

| CLI value | Paper name | Compiled representation |
| --- | --- | --- |
| `ee` | Equality embedding | `eq(lhs, rhs) = false` plus the paper's propagation rules |
| `oee` | Optimized equality embedding | The reduced equality embedding with a reflexive contradiction rule |
| `nee` | Negated equality embedding | A private `ne(lhs, rhs)` constructor and a reflexive contradiction rule |
| `de` | Disequality edges | A private symmetric relation and a self-loop contradiction rule |

DE is a relational encoding of the paper's interface, not its patched native
data structure. Both edge orientations are materialized by an egglog rule.
Congruence closure canonicalizes relation columns after union, so an invalid
edge becomes a self-loop without modifying union-find.

## Composition

The same generated commands pass ordinary execution, term encoding, proof
generation, proof testing, and proof extraction for all four encodings. This
establishes composition with those existing compiler modes. Proof testing
checks generated equality proofs; this change does not yet expose a standalone
certificate whose conclusion is disequality inconsistency.

The fixtures in [`tests/disequality/`](../../tests/disequality/) cover direct
and congruence-created contradictions, rule and action local variables,
multiple e-sorts, push/pop, symmetric DE materialization, and examples ported
from the paper and artifact.

## Relational workload

[`parameter-analysis.egg`](parameter-analysis.egg) is the complete benchmark
driver. It uses only public egglog source constructs:

1. Six TSV inputs describe numeral, `f`, `g`, and `h` AST occurrences, roots
   paired by the artifact, and the disequality cutoff.
2. `parameter-analysis-terms` reconstructs typed `Expr` terms bottom-up into
   `TermAt`.
3. `parameter-analysis-pairs` traverses the roots and invokes either
   `(disequal left right)` or `(union left right)`.
4. `(check-disequalities)` runs whichever compiled encoding was selected.

The converter deliberately assigns a distinct postorder ID to every AST
occurrence instead of interning repeated terms. This preserves the source
artifact's repeated parsing and insertion work while moving the bulk data
through relations rather than 30,000 top-level actions. At ratio 0.5, the
committed input contains:

| Item | Count |
| --- | ---: |
| Source expressions | 60,000 |
| Expression pairs | 30,000 |
| Disequality/equality pairs | 15,000 / 15,000 |
| AST occurrence nodes | 3,728,927 |
| Generated TSV size | 59 MB |

The full generated facts and their per-file hashes are in
[`parameter-analysis-facts/manifest.json`](parameter-analysis-facts/manifest.json).
The 795 MB source archive is verified and cached locally but is not committed.

## Sources and discrepancies

- Paper: [DOI 10.1145/3704913](https://doi.org/10.1145/3704913).
- Artifact: [Zenodo 13938878](https://doi.org/10.5281/zenodo.13938878), published
  2024-10-16 under Apache-2.0.
- `die-graph.zip`: 795,031,027 bytes; MD5
  `fc6661447dcbc1c01a8330db664df094`; SHA-256
  `3e9080ca461457af0a10cfc433a5150952f82f752b4c316df1e03236d93599c4`.
- `parameter-analysis/exprs.in`: SHA-256
  `829b712812d7e1c8563e2f9c9dbd5a8b520c967086d05bc407d8f7b733f70638`.
- Native DE uses the artifact's `disegg.patch` over egg v0.9.5 commit
  `c590048817a35236ce9910e7c1e0b1fac670822c`.

The paper describes 110,000 pairs (100,000 equalities and 10,000 candidate
disequalities), but the published artifact supplies 30,000 pairs as 60,000
newline-terminated expressions. This benchmark uses the published file.

The native source comment says all numbers 1 through 5 are pairwise unequal,
but both programs use the exclusive range `x + 1..5`. The egglog driver matches
the resulting six constraints over 1 through 4. It also reproduces the native
program's binary32 ratio arithmetic and its trailing empty `split("\n")` slot.

The artifact has native parameter-analysis executables only for EE and DE. Its
EE program uses two egg multi-rewrites rather than a literal five-rule
transcription, so native versus egglog is a workload comparison, not an
isolated backend comparison.

## Reproduction

Build the experimental CLI:

```sh
cargo build --release -p egglog-experimental
```

Regenerate the pinned ratio-0.5 tables, or compare fresh bytes with the
committed directory by adding `--check`:

```sh
uv run python -m scripts.paper_benchmarks.prepare_parameter_analysis \
  --download \
  --ratio 0.5 \
  --output egglog-experimental/benchmarks/disequality/parameter-analysis-facts \
  --check
```

Run one encoding over the full input:

```sh
target/release/egglog-experimental \
  --disequality-encoding nee \
  --threads 1 \
  --fact-directory egglog-experimental/benchmarks/disequality/parameter-analysis-facts \
  egglog-experimental/benchmarks/disequality/parameter-analysis.egg
```

Run five interleaved rounds against the artifact's native EE and DE binaries:

```sh
uv run python egglog-experimental/benchmarks/disequality/run_parameter_analysis.py \
  --egglog target/release/egglog-experimental \
  --program egglog-experimental/benchmarks/disequality/parameter-analysis.egg \
  --facts egglog-experimental/benchmarks/disequality/parameter-analysis-facts \
  --native-ee /path/to/parameter_analysis_ee \
  --native-de /path/to/parameter_analysis_de \
  --native-input /path/to/parameter-analysis/exprs.in \
  --output egglog-experimental/benchmarks/disequality/relational-ratio-0.5.csv
```

The runner rotates endpoint order, requires successful native results with no
contradiction, and emits timing-summary-v2 rule costs separately from process
wall time.

Regenerate the four actual compiler expansions after building the recorded
compiler revision:

```sh
uv run python -m scripts.paper_benchmarks.snapshot_disequality_parameter_analysis \
  --binary target/release/egglog-experimental \
  --program egglog-experimental/benchmarks/disequality/parameter-analysis.egg \
  --output egglog-experimental/benchmarks/disequality/desugared \
  --compiler-revision "$(git rev-parse HEAD)" \
  --force
```

Use `--check` without `--compiler-revision` to regenerate all four expansions
and compare them byte-for-byte with the committed files.

## Timing boundaries

The deterministic artifact-to-TSV preprocessing is outside all timed runs.
Egglog `wall_ms` includes process startup, TSV reading, relation loading,
program compilation, term reconstruction, pair traversal, and the private
disequality check. The timing summary partitions only database rule execution:

- `term_rules_ms`: occurrence-preserving term reconstruction;
- `pair_rules_ms`: root traversal and union/disequality actions;
- `disequality_rules_ms`: the private encoding-specific saturation;
- `non_ruleset_wall_ms`: the remaining process, input, compilation, and
  non-rule time.

Native `wall_ms` is the similarly broad process boundary. Its printed
`full_time` starts after file reading and the six base constraints, but includes
expression parsing, insertion, rebuild/saturation, and consistency checking.
The two internal timers therefore do not have identical boundaries; only broad
wall time is presented as an end-to-end comparison.

## Relational results

Median of five final-code, interleaved ratio-0.5 trials. Ranges are wall-time
ranges, not confidence intervals.

| Engine | Encoding | Wall | Term rules | Pair rules | Disequality rules | Non-ruleset wall | Wall range |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| egglog | EE | 5,047.6 ms | 2,875.1 ms | 194.6 ms | 18.347 ms | 1,952.0 ms | 4,752.6-5,095.7 ms |
| egglog | OEE | 5,059.0 ms | 2,883.3 ms | 192.2 ms | 0.063 ms | 1,977.5 ms | 4,742.1-5,308.9 ms |
| egglog | NEE | 5,059.4 ms | 3,008.8 ms | 191.1 ms | 0.034 ms | 1,847.2 ms | 4,756.7-5,717.3 ms |
| egglog | relational DE | 5,053.1 ms | 2,995.8 ms | 194.6 ms | 2.223 ms | 1,856.3 ms | 4,767.5-5,138.9 ms |
| native egg 0.9.5 | EE | 974.3 ms | n/a | n/a | n/a | n/a | 907.3-1,004.7 ms |
| native patched egg | DE | 657.8 ms | n/a | n/a | n/a | n/a | 618.6-696.5 ms |

Raw observations are in
[`relational-ratio-0.5.csv`](relational-ratio-0.5.csv). The five rounds are too
few for a statistical significance claim, and one NEE observation reached
5.72 seconds. No observations were discarded.

The end-to-end relational replay is about 5.2x the native EE wall median and
7.7x the native DE median. That result should not be attributed to the
disequality representation: all four egglog wall medians are within 12 ms,
while term reconstruction alone costs about 2.9-3.0 seconds and non-ruleset
work costs another 1.85-1.98 seconds. The private extension phase costs 18.3 ms
for EE, 2.2 ms for DE, and less than 0.1 ms for OEE and NEE on this input.

EE's larger extension cost follows from its additional equality terms and
propagation rules. DE materializes symmetric edges. OEE and NEE need only a
reflexive contradiction check once congruence has canonicalized their stored
terms. These are observed implementation facts, not a claim that the encodings
have equal behavior on every workload.

## Historical measurements

Earlier revisions explored 30,000 generated top-level actions and a low-level
Rust database writer. Those observations remain available for diagnosis but do
not describe the current public implementation:

- [`ratio-0.5.csv`](ratio-0.5.csv): source-command measurements;
- [`ratio-sweep.csv`](ratio-sweep.csv): one-trial structural ratio sweep;
- [`host-contention-sequential.csv`](host-contention-sequential.csv): excluded
  host-contention run, retained rather than dropped as an outlier;
- [`optimized-ratio-0.5.csv`](optimized-ratio-0.5.csv): the removed
  `CompiledDisequalityWriter` path at revision `83dd4e2`.

The writer showed that direct compiled database insertion could beat the two
native artifact programs on this machine, but it bypassed source typechecking
and proof instrumentation and exposed encoding-specific Rust loading logic.
It was removed in favor of the self-contained relational `.egg` program. The
current result therefore supports a narrower claim: all four extensions can be
compiled and exercised compositionally without Rust-side access to their
representations, with low encoding-specific saturation overhead. It also
identifies bulk relational ingestion and term reconstruction as the remaining
performance boundary for this replay.

## Validation

```sh
cargo test -p egglog-experimental --all-targets
uv run pytest tests/test_disequality_parameter_analysis.py
uv run ruff check .
uv run mypy .
```

The Python test hashes every committed full-corpus table and verifies its row
and byte counts. The Rust tests execute the same relational source with the
small fixture under every encoding and proof treatment. The desugared snapshot
test resolves the source with the compiler and compares all four generated
programs byte-for-byte.
