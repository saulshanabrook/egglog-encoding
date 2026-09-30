# What the disequality benchmark measures

The parameter-analysis benchmark compares the cost of two disequality encodings
in egglog and the additional cost of proof recording. It uses
the expression generator from [Dis-Equality Graphs](https://doi.org/10.1145/3704913),
but runs an egglog program, not the paper's native engines. Its timings therefore
cannot establish performance parity with the paper.

The benchmark guide contains commands for [running comparisons](README.md#comparisons)
and [regenerating the input](README.md#workload-and-regeneration). This document
explains what those comparisons tell us.

## Why select a contradictory input?

The [committed program](parameter-analysis.egg) asserts 100,000 equalities,
10,000 randomly generated disequalities, and ten pairwise numeral disequalities.
It finishes with `(check-contradiction)`. A consistent input could measure the
cost of recording proof information, but would provide no contradiction proof
to extract or check.

The [generator](generate.py) therefore tries whole workloads from successive
seeds until both encodings detect a contradiction and validate its proof. It
does not filter individual pairs or add a constraint to force a contradiction.
The resulting input is fixed across comparisons, but selected for this outcome:
it does not measure how often random workloads are contradictory or their
average execution cost.

## Why encoding overhead differs from proof overhead

Both [compiler passes](../../egglog-experimental/src/disequality.rs) lower
disequality to ordinary egglog before term or proof encoding, without changing
union-find. NE stores a relation between terms and detects a self-edge after
congruence. EE creates equality terms in a private truth sort; its propagation
rules make `true` and `false` equal when a contradiction is found.

The same source program exercises these different representations. An NE-versus-EE
comparison holds the input, executable, and proof treatment fixed. A proof-overhead
comparison instead holds the encoding fixed and changes the proof treatment.
Changing both at once cannot attribute a difference to either one alone.

The [runner](../../benchmarking/processes.py) measures the whole engine process.
That includes reading and parsing the source, typechecking, compiler passes,
inserting and unioning terms, and the final propagation and check. Builds,
input generation, and seed selection are outside that boundary. The result is
not an isolated measurement of a disequality lookup or propagation rule.

This matters because the input contains over 100,000 top-level actions. Proof
mode transforms those actions and records their derivations, not just the final
contradiction. A cheap final check can coexist with expensive proof recording.

## What a successful proof run establishes

The default `proofs` treatment records proof information without extracting or
checking the final proof. `proof-extraction` also materializes and simplifies
the proof; `proof-testing` additionally verifies it. A recording-only timing
therefore does not measure the cost of returning a checked proof.

Strict checking validates the contradiction's derivation against the lowered
egglog program, including the encoding rules. It is not a separate proof that
the disequality compiler pass implements the paper's semantics. The
[small-fixture tests](../../egglog-experimental/tests/disequality.rs) cover
consistent inputs, congruence, multiple sorts, and rule-generated disequalities
under both encodings.

## What the measurements do not establish

The [September 2026 measurement record](https://github.com/saulshanabrook/egglog-encoding/blob/3db715cd29159196118bd744248061ea4dedf8f0/benchmarks/disequality/PERFORMANCE.md)
preserves the original timings, executable hashes, environment, and validation
history. In its full-size NE proof-recording run, frontend work and action
execution dominated; the private NE ruleset counters summed to less than 1 ms.
That ruleset timing excludes the preceding term construction, unions, and
term-encoding equality maintenance. It is not the cost of the whole encoding.

The same record documents a memory fix in
[`process_program_internal`](../../egglog/src/lib.rs): execution no longer
accumulates resolved command trees merely to return them to a caller that
discards them. The proof-checking history is still retained. Removing those
redundant copies does not remove the memory cost of that history or the proof
database.

Those measurements are historical observations, not expected runtimes or a
ranking of NE and EE. In particular, the full-size EE proof timing was stopped
before completion; it supplies neither a runtime comparison nor evidence that
EE proof checking fails.
