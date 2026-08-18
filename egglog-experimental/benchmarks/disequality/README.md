# Disequality encoding validation and benchmark

Run dates: 2026-08-12 through 2026-08-14 (America/New_York)

Initial implementation base: `46f69b70d0819b03da110e6e785f91c080d58556`.
The branch was subsequently merged with `origin/main` at
`ffb8ae435bd6421077b1c15826f32a6aeecf5b1b`. The compiler revision used to
produce the checked-in expansions is recorded in
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

[`parameter-analysis.egg`](../../tests/disequality/parameter-analysis.egg) is
the complete benchmark driver and a checked-in test fixture. It uses only
public egglog source constructs:

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
generated input contains:

| Item | Count |
| --- | ---: |
| Source expressions | 60,000 |
| Expression pairs | 30,000 |
| Disequality/equality pairs | 15,000 / 15,000 |
| AST occurrence nodes | 3,728,927 |
| Generated TSV size | 59 MB |

The generated fact directory is ignored by Git. Its `manifest.json` records
the source and per-file hashes after generation. The 795 MB source archive is
verified and cached locally but is not committed.

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

Generate the pinned ratio-0.5 tables:

```sh
uv run python -m scripts.paper_benchmarks.prepare_parameter_analysis \
  --download \
  --ratio 0.5 \
  --output egglog-experimental/benchmarks/disequality/parameter-analysis-facts \
  --force
```

Subsequent runs may use `--check` instead of `--force` to compare freshly
generated bytes with the existing local directory.

Run one encoding over the full input:

```sh
target/release/egglog-experimental \
  --disequality-encoding nee \
  --threads 1 \
  --fact-directory egglog-experimental/benchmarks/disequality/parameter-analysis-facts \
  egglog-experimental/tests/disequality/parameter-analysis.egg
```

Run three interleaved rounds against the artifact's native EE and DE binaries:

```sh
uv run python egglog-experimental/benchmarks/disequality/run_parameter_analysis.py \
  --egglog target/release/egglog-experimental \
  --program egglog-experimental/tests/disequality/parameter-analysis.egg \
  --facts egglog-experimental/benchmarks/disequality/parameter-analysis-facts \
  --native-ee /path/to/parameter_analysis_ee \
  --native-de /path/to/parameter_analysis_de \
  --native-input /path/to/parameter-analysis/exprs.in \
  --output egglog-experimental/benchmarks/disequality/relational-ratio-0.5.csv \
  --trials 3
```

The runner rotates endpoint order, requires successful native results with no
contradiction, and emits supported timing-summary rule costs separately from
process wall time. With the current timing-summary-v4 schema, each ruleset cost
includes assembly, search, apply, execution, and merge. Global native rebuild
and command/frontend phases remain in `non_ruleset_wall_ms`.

Regenerate the readable EUF and Propel captures plus all four compiler
expansions for every disequality test fixture:

```sh
make -C benchmarks/disequality update-snapshots
```

Use `make -C benchmarks/disequality snapshots` to regenerate all outputs and
compare them byte-for-byte with the committed files.

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

Median of three accepted, interleaved ratio-0.5 trials at `88c40cf` on
2026-08-14 after merging `origin/main`. The later `e7b7969` change only affects
live `fail`; this consistent workload invokes the private schedule directly.
Ranges are wall-time ranges, not confidence intervals. Rejected final-revision
reruns and their host-contention evidence are documented in
[`../../../benchmarks/disequality/PERFORMANCE_ANALYSIS.md`](../../../benchmarks/disequality/PERFORMANCE_ANALYSIS.md).

| Engine | Encoding | Wall | Term rules | Pair rules | Disequality rules | Non-ruleset wall | Wall range |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| egglog | EE | 4,936.6 ms | 2,525.4 ms | 608.2 ms | 11.815 ms | 1,739.8 ms | 4,851.7-5,331.3 ms |
| egglog | OEE | 4,822.2 ms | 2,510.9 ms | 607.5 ms | 1.238 ms | 1,712.8 ms | 4,793.5-4,905.3 ms |
| egglog | NEE | 4,789.4 ms | 2,499.9 ms | 556.4 ms | 0.192 ms | 1,734.6 ms | 4,754.1-4,828.5 ms |
| egglog | relational DE | 4,770.7 ms | 2,485.7 ms | 566.6 ms | 2.492 ms | 1,722.7 ms | 4,767.2-4,850.2 ms |
| native egg 0.9.5 | EE | 932.8 ms | n/a | n/a | n/a | n/a | 924.1-940.6 ms |
| native patched egg | DE | 639.0 ms | n/a | n/a | n/a | n/a | 630.4-722.8 ms |

Raw observations are in
[`relational-ratio-0.5.csv`](relational-ratio-0.5.csv). Three rounds are too few
for a statistical significance claim, and the first EE observation reached
5.33 seconds. No observations were discarded.

The end-to-end relational replay is about 5.3x the native EE wall median and
7.5x the native DE median. That result should not be attributed to the
disequality representation: all four egglog wall medians are within 166 ms,
while term reconstruction costs about 2.5 seconds, pair traversal about 0.6
seconds, and non-ruleset work about 1.7 seconds. The private extension phase
costs 11.8 ms for EE, 2.5 ms for DE, 1.2 ms for OEE, and 0.2 ms for NEE.

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

The Python test verifies deterministic fixture conversion, row counts, timing
summary parsing, and command construction. The full-corpus TSV directory is
ignored and regenerated on demand. The Rust tests execute the same relational
source with the small fixture under every encoding and proof treatment. The
desugared snapshot test resolves the source with the compiler and compares all
four generated programs byte-for-byte.
