# Disequality encoding validation and benchmark

Run dates: 2026-08-12 through 2026-08-13 (America/New_York)

Implementation base: `46f69b70d0819b03da110e6e785f91c080d58556`
(`origin/main` before this change)

Machine: Apple M4, arm64 macOS 26.6; `rustc 1.91.0`; one egglog worker thread.

## Scope

The `(disequal lhs rhs)` command macro implements the four representations in
Section 2.2 of *Dis/Equality Graphs*: EE, OEE, NEE, and DE. The generated
symbols use egglog's reserved `@` prefix, so the default parser prevents user
programs from forging the private NEE constructor or DE relation. Generated
definitions are per e-sort.

DE here is a **compiled relational encoding**, not the artifact's native data
structure extension. It stores both orientations in an ordinary egglog relation;
when congruence closure canonicalizes both columns to the same e-class, a rule
reports a contradiction. No egglog union-find or e-class code is changed.
All contradiction rules live in the default ruleset, so a schedule that runs
only named rulesets must include `(run)` to check stored constraints.

The tests cover direct and congruence-created contradictions, rule and action
local variables, multiple e-sorts, push/pop, the symmetric DE invariant, and all
fixtures under ordinary, term-encoding, and proof-testing modes. Proof testing
checks generated equality proofs. The implementation does not yet expose a
standalone proof certificate whose conclusion is disequality inconsistency.

## Sources and provenance

- Paper: [DOI 10.1145/3704913](https://doi.org/10.1145/3704913).
- Artifact: [Zenodo 13938878](https://doi.org/10.5281/zenodo.13938878), published
  2024-10-16, Apache-2.0.
- Artifact archive `die-graph.zip`: 795,031,027 bytes; MD5
  `fc6661447dcbc1c01a8330db664df094` (matches Zenodo); SHA-256
  `3e9080ca461457af0a10cfc433a5150952f82f752b4c316df1e03236d93599c4`.
- Supplied `parameter-analysis/exprs.in`: SHA-256
  `829b712812d7e1c8563e2f9c9dbd5a8b520c967086d05bc407d8f7b733f70638`.
- Native DE was built by applying the artifact's `disegg.patch` to egg v0.9.5
  commit `c590048817a35236ce9910e7c1e0b1fac670822c`.

The artifact lockfiles no longer resolve with current Cargo under `--locked`.
The native EE and DE programs were therefore rebuilt with Cargo 1.91 after
redirecting DE's path dependency to that patched egg checkout. No source logic
was changed.

## Ports

The following executable fixtures are in `tests/disequality/` and run under all
four encodings:

- `paper-figure-2.egg`: the shared EE/OEE/NEE/DE example behind paper Figures
  2-4, where `a = b` makes `f(a) != f(b)` contradictory.
- `artifact-euf-example.egg`: the artifact EUF solver's documented example.
- `artifact-propel-example.egg`: Propel's `testEGraph` equality/disequality case.
- `artifact-parameter-shape.egg`: a small form of the parameter-analysis input.

The full driver, `examples/disequality_parameter_analysis.rs`, parses the exact
artifact input language, maps its numeral symbols to nullary constructors, and
reproduces the supplied native programs' split of expression pairs into
disequalities and equalities.

The driver has two loading modes. `source` emits ordinary egglog commands and
therefore measures the language frontend as well as the generated database
implementation. `batched-api` builds the same terms and writes the exact
representation emitted by the disequality compiler through
`CompiledDisequalityWriter` inside one `EGraph::update`. The latter is the
matched bulk-loading path for the native Rust API benchmarks. The source setup
first installs the generated tables and rules, so the writer does not duplicate
or replace the compiler implementation.

The full EUF solver and Propel application are not egglog ports. They contain
SAT/theorem-prover front ends and integration behavior outside the disequality
extension. The fixtures port their documented e-graph states and contradiction
cases; they do not establish end-to-end parity for those applications. The
paper's native DE implementation listings are likewise comparison code, not
code paths used by the compiled relational DE encoding.

## Artifact discrepancies

The paper describes 110,000 **pairs** (100,000 equalities and 10,000 candidate
disequalities). The published artifact README and input instead provide 30,000
pairs, represented by 60,000 newline-terminated expressions. These measurements
use the supplied 30,000-pair input, not the paper-scale corpus.

The native source comment says it makes all numbers 1 through 5 pairwise
unequal, but both Rust loops use the exclusive range `x + 1..5`; they add six
constraints among 1 through 4. The egglog driver deliberately reproduces those
six constraints. It also preserves the artifact's threshold calculation over
`content.split("\\n")`, including the trailing empty slot.

The standalone parameter-analysis artifact contains native executables only for
EE and DE. It does not provide like-for-like OEE or NEE programs. Its EE uses
two egg multi-rewrites rather than a literal transcription of the paper's five
rules, so absolute native-versus-egglog timing is a workload comparison, not an
isolated backend comparison.

## Method

Build the egglog driver with:

```sh
cargo build --release -p egglog-experimental \
  --example disequality_parameter_analysis
```

Run the source-command path with:

```sh
target/release/examples/disequality_parameter_analysis \
  /path/to/parameter-analysis/exprs.in 0.5 nee source
```

Run the matched bulk-loading path with:

```sh
target/release/examples/disequality_parameter_analysis \
  /path/to/parameter-analysis/exprs.in 0.5 nee batched-api
```

The six numeral disequalities and declarations run before timing, matching the
native programs. `artifact_parse_ms` measures conversion of the artifact's
expression syntax into the driver's typed tree. `source_render_ms` and
`source_parse_ms` apply only to source mode. `load_ms` covers either normal
command compilation/execution or one batched database update, and `schedule_ms`
covers the generated consistency rules. The bulk total includes artifact
parsing, loading, and saturation.

The native artifact's `full_time` also starts after file loading and includes
expression parsing, insertion, rebuild/saturation, and consistency checking.
Thus the optimized totals have matched timer boundaries. Process startup and
the six base constraints are excluded from both internal totals; `wall_ms` in
the raw CSV records the wider process boundary separately.

The checked-in runner executes all four egglog encodings plus native EE and DE
in five interleaved rounds, rotating the endpoint order on every round:

```sh
python egglog-experimental/benchmarks/disequality/run_parameter_analysis.py \
  --egglog-driver target/release/examples/disequality_parameter_analysis \
  --native-ee /path/to/parameter_analysis_ee \
  --native-de /path/to/parameter_analysis_de \
  --input /path/to/parameter-analysis/exprs.in \
  --output egglog-experimental/benchmarks/disequality/optimized-ratio-0.5.csv
```

An earlier encoding-blocked egglog run overlapped with another worktree's
`math_benchmark_proofs` process at 100% CPU; host load reached 15.36 and timings
doubled midway through NEE. Those observations are retained in
[`host-contention-sequential.csv`](host-contention-sequential.csv), labeled as
excluded from the summary for a directly observed environmental confound rather
than removed as statistical outliers.

The native binaries print Rust debug durations with adaptive precision. The CSV
normalizes displayed values such as `2.00s` to milliseconds but cannot recover
precision that the executable did not print.

Source-level `(begin ...)` batches of 2, 5, and 10 actions improved the
ratio-zero path by only about 10%; a batch of 100 regressed, and an earlier
batch of 1,000 was slower than the matching unbatched run. The existing proof
transformation already handles action blocks, so no new proof-only batch syntax
was needed. The faster Rust bulk writer intentionally uses `EGraph::update`,
which rejects proof-enabled e-graphs rather than bypassing proof recording.

## Results

### Source-command baseline

Median of the original five ratio-0.5 source trials:

| Engine | Encoding | Parse | Execute/full | Total | Relative total to same-engine EE | Representation rows/nodes |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| egglog | EE | 551 ms | 7,568 ms | 8,112 ms | 1.000x | 59,663 rows |
| egglog | OEE | 547 ms | 7,586 ms | 8,129 ms | 1.002x | 15,006 rows |
| egglog | NEE | 557 ms | 7,105 ms | 7,663 ms | 0.945x | 15,006 rows |
| egglog | relational DE | 557 ms | 7,195 ms | 7,752 ms | 0.956x | 30,012 rows |
| native egg 0.9.5 | EE | n/a | 920 ms | 920 ms | 1.000x | 499,904 total nodes |
| native patched egg | DE | n/a | 554 ms | 554 ms | 0.603x | 484,869 total nodes |

The raw observations are in [`ratio-0.5.csv`](ratio-0.5.csv). Egglog and native
row/node counts are not directly comparable: egglog reports rows in generated
disequality tables plus total database tuples, while egg reports e-nodes and
e-classes.

At ratio 0.5, the observed NEE and relational DE medians are 5-6% below EE in
egglog, while OEE and EE are nearly identical. Five trials are not enough for a
confidence interval or a statistical significance claim. The representation-size
effect is clearer: EE has about four generated
rows per asserted disequality, OEE and NEE one, and relational DE two symmetric
rows. In the one-trial ratio sweep, NEE and DE were lower than EE at the two high
disequality fractions, but this sweep has no uncertainty estimate and is retained
only as structural corroboration in [`ratio-sweep.csv`](ratio-sweep.csv).

These source totals use the original timer schema, which excludes the driver's
artifact parser and source renderer. They remain useful as measurements of the
large per-command frontend cost but should not be compared directly with the
matched bulk totals below.

### Compiled bulk loading

Median of five final-code, interleaved ratio-0.5 trials:

| Engine | Encoding | Artifact parse | Load/full | Schedule | Total | Observed range |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| egglog | EE | 38.8 ms | 435.5 ms | 18.1 ms | **492.2 ms** | 490.2-515.8 ms |
| egglog | OEE | 38.9 ms | 440.5 ms | 1.4 ms | **480.1 ms** | 477.5-492.5 ms |
| egglog | NEE | 39.0 ms | 436.2 ms | 0.2 ms | **475.6 ms** | 469.6-486.5 ms |
| egglog | relational DE | 38.9 ms | 429.1 ms | 2.8 ms | **470.5 ms** | 467.7-497.3 ms |
| native egg 0.9.5 | EE | included in full | 800.7 ms | included in full | **800.7 ms** | 796.3-805.8 ms |
| native patched egg | DE | included in full | 512.7 ms | included in full | **512.7 ms** | 507.6-540.2 ms |

The observations are in
[`optimized-ratio-0.5.csv`](optimized-ratio-0.5.csv). Egglog EE is 38.5% below
the contemporaneous native EE median. Compiled relational DE is 8.2% below the
native DE median. Every egglog EE sample is below every native EE sample, and
every egglog DE sample is below every native DE sample in these five rounds.
Five rounds are still too few for a broad statistical claim, but the result is
not driven by one outlier.

The optimized source and bulk modes produce identical representation-row and
total-tuple counts for each encoding. At ratio 0.5 those pairs are EE
59,663/544,534, OEE 15,006/499,876, NEE 15,006/499,875, and DE
30,012/514,881. This is a structural check that the fast path did not omit the
compiled representation or its saturation rules.

### Why the original path was slow

The ratio-zero control isolates shared loading overhead: it contains 30,000
ordinary equalities and only the six setup disequalities. On the final binary,
the source path took 7,541 ms, the compiled bulk path took 457 ms including
artifact parsing, and native EE took 502 ms. All three produced the matching
484,887 egglog tuples or 484,877 native nodes (the ten-row difference is the
fixed egglog extension support). Therefore the multi-second gap exists even
when the selected disequality encoding has no workload assertions.

A 1 kHz `samply` profile of the full ratio-zero source path collected 8,490
main-thread samples. The important inclusive frames were:

| Frame | Inclusive samples | Share of all samples | Relationship |
| --- | ---: | ---: | --- |
| `EGraph::resolve_command` | 3,761 | 44.3% | command-resolution branch |
| `typecheck_standalone_action(s)` | 3,380 | 39.8% | nested under resolution |
| `EGraph::run_command` | 3,420 | 40.3% | command-execution branch |
| `EGraph::eval_actions` | 2,999 | 35.3% | nested under execution |
| backend `run_rules` | 1,041 | 12.3% | nested under `eval_actions` |
| `EGraph::parse_program` | 598 | 7.0% | source parser |

Nested rows are not additive. Resolution and execution are the two disjoint
large branches. About 90% of resolution samples are under standalone action
typechecking, while `eval_actions` accounts for about 88% of execution samples.
Each top-level action is macro-expanded and typechecked, lowered to core
actions, compiled into a temporary backend rule, run, and freed. Expression
lowering and type constraints also allocate and clone heavily. The generated
database rule execution itself accounts for a much smaller share.

This establishes the causal boundary:

* The disequality encodings are not responsible for the original 8-14x gap.
  Source timings differ by only about 6% across EE/OEE/NEE/DE, and ratio zero is
  still slow.
* Egglog's database implementation is not intrinsically slower on this
  workload. Once the compiler output is bulk-loaded, both like-for-like EE and
  relational DE beat the corresponding native artifact programs.
* The bottleneck is compiling and dispatching 30,000 independent source
  commands through a general typed language interface. Small `(begin ...)`
  blocks reduce temporary-rule overhead but do not remove repeated expression
  lowering and typechecking; large blocks make the joint constraint problem
  more expensive.
* EE's remaining 18 ms saturation cost is larger than OEE/NEE/DE because EE
  materializes 59,663 representation rows. Even so, bulk term/database loading
  at roughly 430-441 ms dominates every optimized encoding.

The bulk result is the appropriate evidence for the paper's claim about the
performance of extensions compiled to egglog's database. The source result is
separate evidence that egglog still needs a typed, proof-aware bulk input path
if large generated datasets must be expressed as top-level commands. The
current `CompiledDisequalityWriter` is useful to Rust data loaders but is not
that proof-aware language feature.

## Reproduction checks

```sh
cargo test -p egglog-experimental disequality --lib
cargo test -p egglog-experimental --example disequality_parameter_analysis
cargo test -p egglog-experimental --test files
cargo test -p egglog-experimental --test files -- --proof-testing
```

The last two commands exercise the checked-in fixtures and snapshots. Full
workspace validation is described in the change's final test report.
