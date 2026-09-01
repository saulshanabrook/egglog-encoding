# Inductive Prover

This copy also supports the `egglog-ee`, `egglog-oee`, `egglog-nee`, and
`egglog-de` variants and can emit outcome-preserving chronological host replays.
Cached Vec terms are the runtime default; `--term-language direct` selects
source-shaped constructors and `--no-template-cache` retains the cold-schema ablation. See
[`../EGGLOG_INTEGRATION.md`](../EGGLOG_INTEGRATION.md) for architecture,
validation scope, and reproduction commands. The remainder of this file is the
artifact's original Propel documentation.

This folder contains all the artifacts produced for the evaluation of e-graphs
in the context of inductive theorem proving. The evaluation compares two
variants of e-graphs for encoding disequalities, namely disequality edges (`de`)
and equality embedding (`ee`), using **Propel** as the inductive theorem
prover of choice.

In order to perform this evaluation, we implemented two artifacts. First, we
modified Propel to use e-graphs internally. Second, we provide some scripts to
collect the performances of the new Propel binary.

## Propel Modification

This section elaborates on how Propel was modified to use e-graph internally
for the evaluation.

### Background

Propel [[DOI](https://doi.org/10.5281/zenodo.10949342)] is an existing inductive
theorem prover, specialized in the proofs of algebraic properties, such as
idempotency, commutativity, and associativity.

During its proofs, Propel gradually discovers the terms inside a program,
maintaining sets of equalities and disequalities among them. Consequently,
Propel can act as a source of equalities and disequalities for evaluating an
e-graph implementation.

### Implementation

The modified source code of Propel is available inside the `propel/` folder.
The main changes to the code concern three different approaches to e-graphs
with disequalities (`de`, `ee`, and `nee`), the integration of these e-graphs
in the solving procedure of Propel, and the collection of data for evaluating
their performances.

> Note: since Propel is a large artifact, we decorated the source code with
commented TODO/DONEs to make it easier for the reader to follow and jump to the
important parts of the code. Only the packages mentioned in the following
sections have been modified.

#### EGraph Implementations

For easier integration, we implemented the three e-graph variants from scratch
using the Scala programming language, which is the same language used for
implementing Propel.

The concepts of an e-graph are implemented inside the `propel.evaluator.egraph`
package, which includes the following definitions:
- `Element`: anything that is bound to a unique identifier
- `EClass`: an equivalence class, that is a set of equivalent `Element`s
- `ENode`: a unique `Operator` applied to 0 or more `EClass`es
- `Language`: an interface that can be implemented to adapt any language to the
  language of `ENode`s and `EClass`es. In particular, it is a parser from terms
  to `ENode`s, generally relying on an e-graph to generate `EClass`es.

The actual e-graphs variants are implemented in the
`propel.evaluator.egraph.mutable` package, which includes the following
definitions:
- `UnionFindOps`: a type-class defining the operations supported by a generic
  union-find
- `UnionFind`: implementation of a union-find
- `EGraphOps`: a type-class defining the operations supported by a generic
  e-graph. This type-class has also been extended to support the encoding of
  disequalities.
- `EGraph`: implementation of two `EGraph` variants, namely
  `DisequalityEdgesEGraphOps` (`de`) and `EqualityEmbeddingEGraphOps` (`ee`),
  All e-graph variants implement deferred maintainance of congruence-invariance,
  similarly to the `egg` library.

> Note: an additional `EGraph` variant has been implemented following a
reviewer's suggestion. You can find it under the name of
`DisequalityEmbeddingEGraphOps` (`nee`). The approach is similar to `ee`, but
it encodes disequalities instead of equalities as `ENode`s.

##### Disequality Edges

In the implementation of `de`, disequalities are represented as edges, encoded
as a set of disunioned `EClass`es for each `EClass`. In the code, this set is
called `forbids`. In particular, if an `EClass` belongs to the `forbids` set of
another `EClass`, it means that the two `EClass`es are `unequal`.

Two `EClass`es can be disunioned by calling `disunion` on the `EGraph`. This
method updates the `forbids` set of the former `EClass` to include the latter,
and viceversa.

When two `EClass`es are unioned by calling `union` on the `EGraph`, their
`forbids` sets are also unioned into one.

Finally, the `EGraph` is inconsistent (or `hasContradiction`) if the `forbids`
set of any `EClass` contains the `EClass` itself, meaning that an e-class is
different from itself. This condition is checked any time a `forbids` set is
updated, that is after any `union` or `disunion`. After the first time an
`EGraph` is found to be inconsistent, a flag is set to avoid future checks.

##### Disequality Embedding

In the implementation of `ee`, disequalities are represented as additional
`ENode`s. In detail, equality is represented as a binary function `Equal`, so
that two `EClass`es are `equal` if the application of `Equal` to them is in the
same equivalence class of `True`. Instead, two `EClass`es are `unequal` if the
application of `Equal` to them is in the same equivalence class of `False`.

In these `EGraph`s, calling `disunion` is the same as putting the application
of `Equal` to two `EClass`es in the same equivalence class of `False`.

Similarly, calling `union` is the same as putting the application of `Equal` to
two `EClass`es in the same equivalence class of `True`.

Care must be taken to preserve the algebraic properties of equality and
disequality. In particular, the `EGraph` is kept saturated at three points in
the implementation:
- During the `add` method, it is enforced that every new `EClass` is `equal` to
itself.
- During the `union` method, it is enforced that any two unioned `EClass`es are
`equal`. Additionally, symmetry of equality is preserved.
- During the `disunion` method, it is enforced that any two disunioned
`EClass`es are `unequal`. Additionally, symmetry of disequality is preserved.

The `EGraph` is considered inconsistent if any pair of `EClass`es `(x,y)` is
both `equal` and `unequal`, that is `Equal(x,y)` is both in the equivalence
class of `True` and `False`. In particular, this condition is only ever
satisfied when the equivalence class of `True` is the same as `False`.

#### Integration

After implementing the e-graph variants for the evaluation, we integrated them
into the solving procedure of Propel, using it as a source of equalities and
disequalities.

The module of Propel that keeps track of equalities and disequalities is
`propel.evaluator.equality`. Here, we changed the implementation so that any
operation concerning equalities and disequalities is delegated to an underlying
`EGraph`. In particular:
- Any equality or disequality discovered by Propel is relayed to the underlying
  `EGraph` (performing a `union` or a `disunion`)
- Any query for equality or contradiction in Propel is delegated to the
  `EGraph` (querying an `equal`, an `unequal`, or a `hasContradiction`).

In the implementation, the `Equalities` class, which was originally used to keep
track of equalities and disequalities, now wraps an `EGraphEqualities` class,
which contains the underlying `EGraph` and reacts to any change or query to the
wrapping `Equalities`.

#### Saturation

In Propel, many equalities and disequalities are used implicitly by leveraging
the semantics of terms in the propel language, which include properties of common
language constructs (e.g., constructors) and algebraic properties encoded in
types.

Traditionally, `EGraph`s are not aware of the semantics of their `ENode`s. As a
consequence, an `EGraph` may not capture the whole information that is actually
known by Propel.

To counter this problem, we applied a selection of saturation rules to the
`EGraph`s during the solving procedure of Propel. In particular, this saturation
is performed every time a new term is added to the underlying `EGraph`
(see `EGraphEqualities.saturateSemantics`). The main goal of the saturation step
is to maximize the amount of equalities and disequalities known by Propel that
are actually encoded in the `EGraph`s.

#### Statistics

For the evaluation, we needed to collect some data from the e-graphs created by
Propel. To do so, we introduced a global variable
`EGraphEqualities.EGraphStats.Global`. This variable is updated every time an
`EGraph` is consumed, in the sense that it won't ever be updated again. In
particular, this update happens at the end of each iteration of Propel, in
`propel.evaluator.symbolic.eval`.

The data collected from each `EGraph` includes the number of `EClass`es and the
number of `ENode`s. Before extracting this information, the `EGraph` is rebuilt,
restoring congruence-invariance.

Finally, at the end of the execution of Propel (see `propel.propel`), the sum of
all collected data is printed to the standard output, so that it can be captured
by other programs.

### Compilation

You can generate the modified binary of Propel from the source code inside the
`propel/` folder. Compilation requires `sbt`, which is already installed in the
image.

To generate the modified binary, you can run the following command inside the
`propel/` folder:
```
sbt nativeLink
```
Then, you will find the new binary at the following path
`propel/.native/target/scala-3.4.2/propel`.

To make it easier, we generated and included the modified binary already in the
`$PATH`, so you can run `propel` from anywhere.

### Execution

You can execute the modified binary of Propel to type-check any file with
extension `.propel`. To do so, you can run the following command:
```
propel -f your_file.propel
```

A new command line argument has been added to the original binary, namely
`--variant VARIANT`. This argument allows to switch between one of the
implemented `EGraph` variants as follows:
- Disequality Edges (Default): `./propel -f your_file.propel --variant de`
- Equality Embedding: `./propel -f your_file.propel --variant ee`
- Disequality Embedding: `./propel -f your_file.propel --variant nee`

At the end of the execution, the standard output should like the following:
```
...                         // original propel output
✔ Check successful.         // success
sum;49;738.0;808.0          // e-graph data: sum;#e-graphs;#e-classes;#e-nodes
```
or
```
...                         // original propel output
✘ Check failed.             // failure
sum;166;20873.0;21479.0     // e-graph data: sum;#e-graphs;#e-classes;#e-nodes
```

> Note: some files may be too complex and take a very long time to type-check.

## Evaluation Script

In the `benchmarks/propel/` folder, we provide a set of benchmarks to
evaluate the modified binary of Propel. These include the TIP benchmarks used in
the paper.

For running the evaluation, we provide a bash script, namely `run.sh`.
The script iterates over the TIP benchmarks, executing the modified binary of
Propel with a default timeout of 60 seconds, and extracting the performances of
`de` and `ee` for every benchmark. The overall output of the script is in `CSV`
format and can be redirected to produce a `.csv` file.

To run the evaluation, you can use the following command inside this folder:
```
./run.sh
```
The evaluation may take a few minutes to finish, so we also provided a
pre-computed output inside the `precomputed-results.csv` file.

Finally, we provide an additional Python3 script, named `gen-table.py`. This
script can be used to analyze the results of an evaluation in `.csv` format,
generating the ratios between `de` and `ee` as shown in the evaluation section
of the paper.

You can execute the script by running the following command:
```
python3 ./gen-table.py your_results_file.csv
```

At the end of the execution, you will see an output similar to the following:
```
Average Ratio DE/EE of E-Nodes: 0.338239
Average Ratio DE/EE of E-Classes: 0.759140
Average Ratio DE/EE of Time: 0.634692
```

These results address the claim that `de` is generally better than `ee` for
encoding disequalities in e-graphs.

## Custom Experiments

We encourage the reviewers to run some custom experiments with the modified
binary of Propel. To facilitate the process, we provided an interface over such
binary. You can find it in the form of another Python3 script, called
`scripts/run.py`.

### Implementation

The script relies on five submodules, contained in the `scripts/modules`
directory:
- `benchmark.py`: define utilities for selecting `propel` benchmarks
- `experiment.py`: define the logic for running an experiment on a set of
`propel` benchmarks
- `performance.py`: define a model for describing and combining performances
obtained on `propel` benchmarks
- `printing.py`: define utilities for logging information during the evaluation
- `util.py`: define a few general utilities used by the other modules

### Execution

In order to run a custom experiment, you can use the following command
(execution may take several minutes depending on the configuration):
```
python3 scripts/run.py
```

The `run.py` script can be configured with the following command line arguments:
- `-h` (`--help`): a flag for displaying the information contained in this
section, instead of executing the program.
- `-b` (`--binary`): which binary for `propel` to use for the evaluation.

  Defaults to `/usr/local/bin/propel`.
- `-v` (`--variant`): which e-graph variant to evaluate. It must be either `de`,
`ee`, or `nee`.

  Defaults to `de`.
- `-d` (`--disable-disequalities`): a flag that disables disequalities inside
  `propel` (and its e-graphs), when specified.

  Disequalities are enabled by default.
- `-t` (`--timeout`): the number of seconds reserved for the evaluation on each
  benchmark. After the timeout has expired, the result obtained on the benchmark
  is considered to be `Timeout`, otherwise it is either `Success` or `Failure`.

  Defaults to `60`.
- `-i` (`--input`): the set of benchmarks used for the evaluation. It must be
  either a directory containing a set files with `.propel` extension, or one of
  the following builtin benchmarks:
  - `@builtin`: the set of benchmarks defined inside the `propel` binary.
  - `@tip`: the subset of `@builtin` containing only tip benchmarks.
  Defaults to `/inductive-prover/benchmarks/propel`.
- `-o` (`--output`): the output directory for the artifacts generated by the
  script.

  Defaults to `./.output`.
- `-f` (`--filename`): the name of the output files generated by the script.

  Defaults to a pseudo-unique identifier based on local time.
- `-j` (`--build-json`): a flag that enables the generation of a JSON file
  encoding the results of the evaluation, when specified.

  By default, no JSON file will be produced.
- `-c` (`--build-csv`): a flag that enables the generation of a CSV file
  encoding the result of the evaluation, when specified.

  By default, no CSV file will be produced.

#### Example

Consider the following directory:
```
inductive-prover/
    scripts/
        run.py
        ..
    benchmarks/
        propel/
            ..
    my-propel-bin
```

Inside the `/inductive-prover` directory, you can execute the script as follows:
```
python3 scripts/run.py
    --binary ./my-propel-bin
    --variant de
    --disable-disequalities
    --timeout 60
    --input ./benchmarks/propel
    --output ./.output
    --filename propel-de-nodis-t60
    --build-json
    --build-csv
```

At the end of the execution, the directory will look like the following:
```
inductive-prover/
    /.output
        propel-de-nodis-t60.csv
        propel-de-nodis-t60.json
        propel-de-nodis-t60.txt
    ..
```

Inside each `propel-de-nodis-t60` file, you can find a different
representation of the results of the evaluation.
