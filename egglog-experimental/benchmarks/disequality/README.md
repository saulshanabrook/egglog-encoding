# Disequality encoding validation and benchmark

Run date: 2026-08-12 (America/New_York)

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

Run one encoding with:

```sh
target/release/examples/disequality_parameter_analysis \
  /path/to/parameter-analysis/exprs.in 0.5 nee
```

The six numeral disequalities and declarations run before timing, matching the
native programs. `parse_ms` measures egglog source parsing. `execute_ms` includes
macro expansion, typechecking, database loading, and saturation. `total_ms` is
their sum. The native artifact's `full_time` starts after input-file loading and
includes expression parsing, insertion, rebuild/saturation, and consistency
checking. The four egglog encodings were run in five interleaved rounds at ratio
0.5, rotating their order to limit temporal bias. Native EE and DE were each run
five times. No sample from either summarized block was discarded.

An earlier encoding-blocked egglog run overlapped with another worktree's
`math_benchmark_proofs` process at 100% CPU; host load reached 15.36 and timings
doubled midway through NEE. Those observations are retained in
[`host-contention-sequential.csv`](host-contention-sequential.csv), labeled as
excluded from the summary for a directly observed environmental confound rather
than removed as statistical outliers.

The native binaries print Rust debug durations with adaptive precision. The CSV
normalizes displayed values such as `2.00s` to milliseconds but cannot recover
precision that the executable did not print.

An exploratory pre-optimization batch of 1,000 top-level actions made EE slower
(`13.07s` execution versus `10.89s` for the matching unbatched implementation).
Top-level batch support in the proof encoding is therefore not required by this
workload and was not added.

## Results

Median of five ratio-0.5 trials:

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

The native artifact reproduces the paper's stronger result for native DE: its
median is 40% below native EE. Absolute egglog times are 8.8x (EE) to 14x (DE)
the native programs here. Most egglog time is shared command loading and
typechecking rather than disequality saturation; the ratio-zero sweep still
takes about 7.7 seconds. This benchmark therefore supports expressibility and
low *incremental representation* overhead, but it does not support an absolute
performance-parity claim with the specialized Rust API.

## Reproduction checks

```sh
cargo test -p egglog-experimental disequality --lib
cargo test -p egglog-experimental --example disequality_parameter_analysis
cargo test -p egglog-experimental --test files
cargo test -p egglog-experimental --test files -- --proof-testing
```

The last two commands exercise the checked-in fixtures and snapshots. Full
workspace validation is described in the change's final test report.
