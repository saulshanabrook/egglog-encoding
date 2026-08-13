
# Dis/Equality Graphs

Artifact for the paper #309 "Dis/Equality Graphs"



# Claims Addressed By This Artifact

This artifact addresses the following claims made in the paper:

1. The changes to `egg` described in Section 4 (p. 12) are sufficient to
   implement disequality edges.

2. The Inductive Theorem Prover setup described in Section 5.1 (p. 14) is
   accurate.

3. The column in Table 1 (p. 14) about the Inductive Theorem Prover case study
   can be reproduced.

4. The EUF Solver case study described in Section 5.1 (p. 14) is accurate.

5. The column in Table 1 (p. 14) about the EUF Solver case study can be
   reproduced.

6. The Parameter Analysis setup described in Section 5.2 (p. 14-15) is accurate.

7. The plots in Figures 4(a), 4(b), and 4(c) (p. 15) can be reproduced.




# Reusable E-Graph Implementations with Support for Disequalities

The artifact contains the implementation of disequality edges into the
widely-used `egg` library, which can be used under the open-source MIT license
as a drop-in replacement for `egg`, which other researchers can reuse,
repurpose or experiment with in other projects.

The artifact further contains e-graph and die-graph implementations in Scala
(used for the case study on the Propel inductive theorem prover), which can be
reused under the open-source Apache license by other researchers and in other
projects.

The directory for the `euf-solver` (using `egg` with and without disequalities)
and directory for the `inductive-prover` (using the Scala implementation with
and without disequalities) contain additional README files describing the
respective tools.




# Getting Started

## Loading the Docker Image

We provide you with `die-graph.tar.xz`, which is a pre-built container image.
To load, run the following command:
```
$ docker load < die-graph.tar.xz
```

## (Optional) Building the Docker Image

Further, you can build the container anew. To build, run the following command
which takes between 5 and 10 minutes:
```
$ docker build -t die-graph .
```

**WARNING** On Apple machines building the image may produce a corrupted
`propel` executable that throws a runtime error when executed. We recommend
rebuilding the image in a x86-64 Linux operation system.

## Using the Docker Image

We recommend starting a new bash session inside the container, in which to
execute all the commands suggested later. To do so, the reviewer can run the
following command:

```
docker run -it --rm die-graph bash
```

**WARNING** All changes done by the reviewer are lost after a bash session is
terminated.




# Contents of the Artifact

## Disegg: The modified `egg` Rust E-Graph Implementation with Disequality Edges

We built `disegg` on top of the `v0.9.5` tag of `egg`.

* The `disegg` source code is in `/disegg`.
* The patch file applied on top of `v0.9.5` tag of `egg` in `disegg.patch`.

## Propel: An Inductive Theorem Prover Case Study

The relevant files to this case study are in `/inductive-prover/`

* The Propel source code in `propel/`.
* A native `propel` binary that is already in the `$PATH`.
* The TIP benchmarks in `benchmarks/propel/`.
* A CLI wrapper for Propel in `scripts/`.
* A CSV file containing the precomputed evaluation results in
  `precomputed-results.csv`.
* A bash script to run (and generate) the results in CSV format in `run.sh`.
* A python 3 script that summarizes the CSV results and generates the numbers in
  Table 1 (p. 14) of the paper in `gen-table.py`.
* A `README.md` file that documents in greater detail the die-graph of
  Propel.

## EUF Solver: An SMT Solver Case Study

The relevant files to this case study are in `/euf-solver`

* The source code in `euf-solver.rs`.
* The relevant Rust cargo files in `Cargo.lock` and `Cargo.toml`.
* The native `euf-solver` binary in `target/`.
* A CSV file containing the precomputed evaluation results in
  `precomputed-results.csv`.
* A bash script to run (and generate) the results in CSV format in `run.sh`.
* A python 3 script that summarizes the CSV results and generates the numbers in
  Table 1 (p. 14) of the paper in `gen-table.py`.
* A `README.md` file that documents in greater detail the solver.

## Parameter Analysis

The relevant files for this evaluation are in `/parameter-analysis`

* The Rust project that implements the Disequality Edges approach in `de/`.
* The Rust project that implements the Equality Embedding approach in `ee/`.
* A list of 60,000 random S-expressions in `exprs.in`.
* A python 3 script to generate random S-expressions in `rand_exprs.py`.
* A CSV file containing the precomputed evaluation results in
  `precomputed-results.csv`.
* A bash script to run (and generate) the results in CSV format in `run.sh`.




# Step-by-Step Instructions for Artifact Reviewers

In this section we describe the steps that the reviewers should follow to
validate all the claims listed earlier.



## 1. The changes to `egg` are sufficient to implement disequality edges.

`disegg` is the implementation of e-graphs with disequality edges that we
describe in Section 4. It is built on top of the latest released version of
`egg`, a mature and popular e-graph implementation in Rust.

`egg` is open-source and developed publicly at https://github.com/egraphs-good/egg.git
and it is well-documented at https://docs.rs/egg/0.9.5/egg/

For more details we refer the reviewers to the POPL 2021 artifact in which `egg`
is described: https://doi.org/10.5281/zenodo.4072013

The reviewers can check our claims as follows:

1. Navigate to the `disegg` implementation: `cd /disegg`
2. Check the development history by running `git log` and checking that `HEAD`
   points to `v0.9.5`, i.e. check that `disegg` builds on top of the latest
   released version of `egg`.
3. Check that the changes done are as described in Section 4 by examining the
   small diff produced by `git diff`

Alternatively, the reviewer can check the steps done by `/setup-container` (the
script that builds this artifact) to create `/disegg` and check that the patch
file `/disegg.patch` contains the changes described in Section 4.

`disegg` can be used under the open-source MIT license as a drop-in replacement
for `egg`, which other researchers can reuse, repurpose or experiment with in
other projects.


### Explanation of differences

The code shown in Section 4 is sufficient to implement disequality edges but
it is not the most efficient. The performance issue lies in the nested loops in
the `fn is_consistent(&self)` function.

The key observation that improves the performance is that the check
`self.find(*id) != cid` can be done while adding disequalities in `disunion`.

This is done by adding a boolean `inconsistent` flag to the `EGraph` struct.
For an empty e-graph the flag is set to `false`. Then, whenever a new
disequality is added, the search happens as described and documented in the
`fn set_inconsistent_or_add(..)` function.


### Compiling and Using disegg

Both `egg` and `disegg` are libraries and do not expose a binary that can be
used immediately by the reviewer.

However, both the EUF solver case study and the Parameter Analysis evaluation
directly use `disegg`.

Therefore, compiling and using `disegg` will be done by these evaluations.



## 2. The Inductive Theorem Prover setup is accurate.

Here we describe the experimental setup and the relevant changes made to the
existing source code of the automated inductive prover Propel.

### The provenance of the TIP benchmarks

The 39 TIP benchmark files used by this artifact are `/inductive-prover/benchmarks/propel/tip_*.propel`

The original TIP benchmarks are available here: https://github.com/tip-org/benchmarks/tree/master/benchmarks/tip2015

The 39 TIP benchmarks chosen are those that can be proven using Propel, i.e.
those that check one of these properties: commutativity, idempotency,
associativity, (ir)reflexivity, (a)symmetry, antisymmetry, and transitivity.

The original TIP benchmarks are expressed in smt2 format, however Propel does
not accept smt2 files. Therefore, we ported these benchmarks to the format that
Propel accepts.

The reviewer is invited to inspect the two formats and check that the propel
benchmarks share the same semantics with the corresponding smt2 benchmarks.

### The source code

Our modified Propel lives in `/inductive-prover/propel`. In particular, the
die-graphs and e-graphs are implemented in the `evaluator.egraph` Scala module,
which lives in `/inductive-prover/propel/src/main/scala/propel/evaluator/egraph/`.

We refer the reviewer to the solver's detailed documentation in
`/inductive-prover/README.md` to learn where e-graphs are used in Propel, where
disequalities are handled, how they are handled, and how to use Propel.

The Scala implementation of the die-graphs and e-graphs do not depend on the
rest of the Propel source code, and thus can be reused under the open-source
Apache license by other researchers and in other projects.


### Compiling

The implementation can be compiled by executing:

```
cd /inductive-prover/propel; sbt compile nativeLink
```

This step is optional since the image already includes the release binary. If
the reviewer wishes to recompile the solver they must execute `sbt clean` first
inside `/inductive-prover/propel`.

**WARNING** The binary resulting from compiling in a Docker instance running on
an Apple machine is likely corrupted and will produce a runtime error.

**WARNING** Compiling Propel may take between three and six minutes.

The resulting binary is `/inductive-prover/propel/.native/target/scala-3.4.2/propel`.


## 3. The column in Table 1 about the Inductive Theorem Prover can be reproduced.

### Using the Precomputed Results

The precomputed results are in `/inductive-prover/precomputed-results.csv`.

The numbers in Table 1 column "Inductive Prover" (p. 14) can be found by running:

```
python3 /inductive-prover/gen-table.py /inductive-prover/precomputed-results.csv
```

The reviewer is invited to inspect the short `/inductive-prover/gen-table.py`
script to check that the numbers are computed correctly from the CSV file.

### Generating Results

If the reviewer wishes to generate their own CSV file containing the results of
the evaluation, they can execute:

```
/inductive-prover/run.sh > /inductive-prover/results.csv
```

This command executes the solver with 60 seconds timeout on the 39 TIP benchmarks
located in `/inductive-prover/benchmarks/propel/` twice, once using equality
embedding and the second using disequality edges.

**WARNING** Execution may take between 30 to 60 minutes.

To produce the new Table 1 numbers, the reviewer can execute:

```
python3 /inductive-prover/gen-table.py /inductive-prover/results.csv
```

The produced CSV file contains the following columns:
* `file` is the path to the TIP benchmark file.
* `ee_node_num` is the number of nodes in the e-graph using the equality
  embedding method.
* `ee_class_num` is the number of classes in the e-graph using the equality
  embedding method.
* `ee_time` is the duration that is taken by the equality embedding method. 
* `de_node_num` is the number of nodes in the e-graph using the disequality
  edges method.
* `de_class_num` is the number of classes in the e-graph using the disequality
  edges method.
* `de_time` is the duration that is taken by the disequality edges method.
The durations are in the same format as produced by the `time` cli utility.

If a benchmark times-out then `ee_node_num` and `ee_class_num` are empty, and/or
`de_node_num` and `de_class_num` are empty.



## 4. The EUF Solver case study is accurate.

Here we describe the experimental setup and the source code of the EUF solver.

### The provenance of the benchmarks

The SMT-LIB UF non-incremental benchmarks, which the paper uses for its EUF solver,
live in `/euf-solver/benchmarks/smt-uf-non-incremental`.

All files are taken as-is from: https://zenodo.org/records/11061097/files/UF.tar.zst

### The source code

The source code of the solver is a singular large Rust file
`/euf-solver/euf-solver.rs`, which uses `egg`, `disegg`, and `minisat` as can be
inspected in `Cargo.toml`.

We refer the reviewer to the solver's detailed documentation in
`/euf-solver/README.md` to learn where e-graphs are used in the solver, where
disequalities are handled, how they are handled, and how to use the tool.

### Compiling

The implementation can be compiled by executing:

```
cd /euf-solver; cargo build --release
```

This step is optional since the image already includes the release binary. If
the reviewer wishes to recompile the solver they must execute `cargo clean`
first.


## 5. The column in Table 1 about the EUF Solver case study can be reproduced.

This step presumes that compilation has happened.

### Using the Precomputed Results

The precomputed results are in `/euf-solver/precomputed-results.csv`.

The numbers in Table 1 column "SMT-LIB EUF" (p. 14) can be found by running:

```
python3 /euf-solver/gen-table.py /euf-solver/precomputed-results.csv
```

The reviewer is invited to inspect the heavily-documented `/euf-solver/gen-table.py`
script to check that the numbers are computed correctly from the CSV file.

### Generating Results

If the reviewer wishes to generate their own CSV file containing the results of
the evaluation, they can execute:

```
/euf-solver/run.sh > /euf-solver/results.csv
```

This command executes the solver with a 1 second timeout on every benchmark twice,
once using the equality embedding approach and a second time using disequality
edges.

**WARNING** Execution may take between two to three hours.

To produce the new Table 1 numbers, the reviewer can execute:

```
python3 /euf-solver/gen-table.py /euf-solver/results.csv
```

The produced CSV file contains the following columns:
* `method` is either `ee` or `de` and describes the disequality handling technique.
* `file` points to the SMT-LIB benchmark file used.
* `status` is the SAT status the solver produced.
* `egraph setup time` is the time required to setup the e-graph.
* `full time` is the time from the start of the program till finding the sat
  status, i.e. the whole runtime of the solver.
* `sat solution` is the sat iteration as all sat solutions may be needed.
* `nodes` is the number of nodes in the iteration's e-graph.
* `classes` is the number of classes in the iteration's e-graph.
* `sat time` is the time spent in the sat solver for that sat iteration.
* `egraph time` is the time spent in the e-graph for that sat iteration.


## 6. The Parameter Analysis setup is accurate.

Here, we describe how the experimental setup is recreated and verified, including
the examination of relevant source-code.

### The Input

The 30K pairs of s-expressions that we have generated are in
`/parameter-analysis/exprs.in`. This file contains 60K expressions, each on its
own line. Thus, a pair of s-expressions is a pair of lines.

This file was generated using the python 3 script
`/parameter-analysis/rand_exprs.py`. Precisely, to generate a new random set of
30K pairs the reviewer can execute:
```
python3 /parameter-analysis/rand_exprs.py > /parameter-analysis/exprs.in
```

The python 3 script is short (13 lines of code) and documented. The reviewer is
free to change the number of pairs by modifying the `EXPR_COUNT` constant in the
file and re-generating the `exprs.in` file.


### The logic that builds the two e-graphs

#### Disequality Edges

The disequality edge implementation is a Rust application in `/parameter-analysis/de/`.
The implementation uses `disegg` and the reviewer may check this by examining
the `Cargo.toml` file.

The source code is 70 lines long and lives in `src/main.rs`. The reviewer is
invited to check that `disegg` is used, that the relevant functions are
called to add equalities and disequalities, and that no other disequality
treatment is present.

#### Equality Embedding

The equality embedding implementation is also a Rust application in
`/parameter-analysis/ee/`. The implementation uses only `egg` version `v0.9.5`.

The source code is similarly short at 70 lines long and lives in `src/main.rs`.
The reviewer is invited to check that a disequality `e1 != e2` is represented by
equating `(eq e1 e2)` and `false`, and that a saturation step is done.


### Compiling

Both implementations can be compiled by executing:

```
cd /parameter-analysis/de; cargo build --release
cd /parameter-analysis/ee; cargo build --release
```

This step is optional since the image already includes the release binaries.
If the reviewer wishes to recompile the binaries they must clean the projects
by running `cargo clean` in each folder.



## 7. The Parameter Analysis plots can be reproduced.

This step presumes that compilation has happened.

### Using the Precomputed Results

We invite the reviewers to copy the `/parameter-analysis/precomputed-results.csv`
file out of the container and plotting using their preferred plotting tool.

To generate Figure 4(a) you must:
1. Select only the rows with `method=ee`.
2. The y-axis is generating by computing `number_nodes / number_classes`.
3. The x-axis is `ratio`.
4. Plot the table to get the EE graph.
5. Repeat with `method=de` in Step 1 to get the DE graph.

To generate Figure 4(b) you must:
1. Select only the rows with `method=ee`.
2. The y-axis is `time_to_find_contradiction` (note the time unit).
3. The x-axis is `ratio`.
4. Plot the table to get the EE graph.
5. Repeat with `method=de` in Step 1 to get the DE graph.

To generate Figure 4(c) you must:
1. Select only the rows with `method=ee`.
2. The y-axis is `full_time` (note the time unit).
3. The x-axis is `ratio`.
4. Plot the table to get the EE graph.
5. Repeat with `method=de` in Step 1 to get the DE graph.

### Generating Results

The reviewer can also generate their own CSV results file by running:
```
/parameter-analysis/run.sh > /parameter-analysis/results.csv
```
The output file can be inspected as described earlier.

The produced CSV file contains the following columns:
* `method` is either `ee` or `de` and describes the disequality handling technique
  used to generate the numbers.
* `ratio` is the ratio of s-expression pairs treated as disequalities.
* `contradiction` is either `Y` or `N` and signals whether a contradiction has
  been found in the e-graph or not.
* `time_to_find_contradiction` is the time to query the populated e-graph to find
  whether a contradiction exists.
* `full_time` is the total time to populate, rebuild, and query the e-graph.
* `number_nodes` is the final number of nodes in the e-graph after populating it.
* `number_classes` is the final number of classes in the e-graph after
  populating it.
