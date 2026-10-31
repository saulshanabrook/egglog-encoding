# EgglogSemantics

A Lean 4 model of egglog's semantics and proof encoding, originally ported from the
Redex model in [egglog PR #324](https://github.com/egraphs-good/egglog/pull/324).
The reference interpreter targets the extended egglog implementation in this workspace.

## Language and semantics

The language is untyped and has no declarations. A program is a schedule, built from
runs of rule lists, saturations and sequences nested as in egglog's `run-schedule`, and
one check that decides its outcome; applying any name to any arguments builds a
term, and an initial fact is a run of an empty-query rule. A rule's query is a
conjunction of term patterns, equalities and disequalities, and its actions build terms,
assert equalities with `union`, and `subsume` rows. egglog's named rulesets are resolved by
the parser: a run of a ruleset fires the rules registered in it so far.

A state is an e-graph: a set of equations and a set of subsumed rows. Reflexive equations
record which terms exist, and congruence is derived over the terms the equations mention.
A query looks rows up and matches no subsumed row, in any spelling; a query variable is
bound to the representative of a class, its least stored spelling in the term order, as
egglog binds a variable to an e-class. A round fires every rule it names against the
pre-state and adds every write and every subsumed row, in no particular order. Definitions
and brief rationale are in [Spec/Step.lean](EgglogSemantics/Spec/Step.lean).

## Encoding passes

The congruence compiler translates source programs, which use neither `subsume` nor
disequality, into an explicit union-find relation maintained by rules that subsume
a stale row and write its replacement; the output has no merge function. It handles query
flattening and rebuilding, with one id column per relation. The provenance pass adds a
firing log, one relation per rule recording the values each firing bound, and proofs are
reconstructed from the log afterwards. Proof lifting turns them into source proofs that
both the Lean and Rust checkers accept. The [encoding guide](ENCODING.md) describes the
encoding, the log, and the rationale.

Compiler correctness is stated in
[Congruence/Correctness.lean](EgglogSemantics/Congruence/Correctness.lean): well-formed
source programs in the fragment and their compilations have exactly the same outcomes and
the same divergence, over mathematical databases. Its proof for the view-free encoding is
open and the congruence gate checks it executably on the corpus. The
specification-level proofs, the interpreter refinement (subsume-free programs, and
union-free programs with subsumption such as the compiler's output), and the certificate
soundness proofs are ported to the declaration-free specification; `EgglogPaper.lean`
lists the theorems the paper relies on. Brief certificate notes live with the
[source checker](EgglogSemantics/SourceProof/Checker.lean) and
[relational checker](EgglogSemantics/Provenance/Checker.lean).

## Layout

| Directory | Contents |
| --- | --- |
| `EgglogSemantics/Spec/` | Syntax, databases, congruence, evaluation, matching, relational steps, scope |
| `EgglogSemantics/Impl/` | Finite reference interpreter |
| `EgglogSemantics/Source/` | The source fragment the compiler accepts, and the generated names |
| `EgglogSemantics/Congruence/` | Congruence compiler and relational execution |
| `EgglogSemantics/SourceProof/` | Source proof format and checker |
| `EgglogSemantics/Provenance/` | Firing-log instrumentation, proof format, checker, and extraction |
| `EgglogSemantics/Resugar/` | Proof lifting to source proofs, fixtures, and JSON export |
| `EgglogSemantics/Proofs/` | Theorems about the specification, checker and lifting soundness; the compiler proofs there predate this encoding |
| `EgglogSemantics/Tests/` | Executable regressions, `.egg` parsing and emission, and proof rendering |
| `tests/` | Hand-written `.egg` programs with snapshots of their encodings and lifted proofs |
| `DiffTest.lean` | Curated and generated comparisons with egglog and encoding/checker probes |

Start with [Syntax.lean](EgglogSemantics/Spec/Syntax.lean),
[Eval.lean](EgglogSemantics/Spec/Eval.lean), and
[Step.lean](EgglogSemantics/Spec/Step.lean), then read
[Congruence/Encode.lean](EgglogSemantics/Congruence/Encode.lean) and
[Congruence/Correctness.lean](EgglogSemantics/Congruence/Correctness.lean).

## Validation

From the workspace root:

```sh
make check                 # Python and Rust formatting, checks, and tests
make lean-check            # Lean build, proof-hole audit, corpus gates, Rust certificate check
cargo build --release -p egglog
make lean-difftest          # compare Lean and egglog per-function row counts
make lean-compiled-difftest # run the compiled programs in egglog and compare e-node censuses
make paper-sync             # regenerate the semantics section of ../extended-egglog-paper
```

Additional executable probes, from `semantics/`:

```sh
lake build difftest
.lake/build/bin/difftest congruence 64
.lake/build/bin/difftest provenance 64
.lake/build/bin/difftest resugar 64
```

The toolchain is pinned in [lean-toolchain](lean-toolchain), and Mathlib in
[lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json). Install `elan`,
then run `lake exe cache get` from this directory when setting up a fresh checkout.
