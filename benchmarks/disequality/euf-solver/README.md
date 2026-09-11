# EUF Solver

This document documents in greater detail the EUF solver.  First we document the
building step, then the CLI arguments.  We present example uses that reviewers
can execute that allows them to check their own files.  Next we describe on a
high-level the components of the source code.  Finally, we highlight where
e-graphs and die-graphs are used.



# Building

The image already contains a release build of the solver.  If the reviewer
wishes to compile their own they must first run `cargo clean` and then run
`cargo build --release`.



# CLI Arguments

The resulting binary can be executed directly by calling the
`/euf-solver/target/release/euf-solver` or by running `cargo run --release`.

The tool requires one argument: the path to the smt2 file to check.

The tool offers two flags that can be switched on:

* `-d` or `--disegg` which uses disequality edges instead of the default
  equality embedding,

* `-s` or `--stats` which prints on the console additional statistics instead of
  the just `sat` or `unsat`.



# Example usages

In this section we guide the reviewer through checking their own files.

To that let's consider the following SMT use-case:

1. Two uninterpreted datatypes (or sorts) are assumed to exist, `S` and `T`,
   which are not parametrized.

2. Two constants `x` and `y` of type `T` are assumed to exist.

3. A binary function `f` taking two `T` values to an `S` is assumed to exist.

4. We assert that either `f` is not commutative at `x` and `y`, or that `f(x,x)`
   is not equal to `f(y,y)`.

5. We assert that `x` and `y` are equal.

6. We check if these constraints are satisfiable.

This use-case is expressed in SMT syntax as follows:

```
; Declare two sorts S and T with 0 parameters
(declare-sort S 0)
(declare-sort T 0)

; Declare the constants x, y as nullary functions
(declare-fun x () T)
(declare-fun y () T)

; Declare f
(declare-fun f (T T) S)

(assert (or (distinct (f x y) (f y x))
            (not (= (f y y) (f x x)))))

(assert (= x y))

(check-sat)
```

The reviewer is free to save this file in the image and use with the
`euf-solver`.  In the rest of this section we assume this file exists in
`/tmp/test.smt2`.

The simplest command is to use `cargo run --release -- /tmp/test.smt2`. The output
should be:

```
/tmp/test.smt2: unsat
```

To see some of the statistics you may use `cargo run --release -- /tmp/test.smt2 -s`.
Which produces the output:

```
file,status,egraph setup time,full time,sat solution,nodes,classes,sat time,egraph time
test.smt2,unsat,103.759µs,1.478ms,0,27,3,23.828µs,456.372µs
test.smt2,unsat,103.759µs,1.478ms,1,22,3,2.613µs,344.595µs
test.smt2,unsat,103.759µs,1.478ms,2,22,3,6.449µs,338.130µs
```

The format is CSV and described in the `/README.md`.  But what is clear is that
the internal SAT solver, minisat, was queried three times.  This is because the
first asserting is a disjunction of two propositions which can be satisfied in
three ways.  The e-graph always had 22 e-nodes and 3 e-classes, and roughly
340-450 microseconds were spent in the e-graph.

This command uses equality embedding strategy which is less efficient than the
`eq_axioms` strategy. To see this you may run
`cargo run --release -- /tmp/test.smt2 -s -d`. This produces:

```
file,status,egraph setup time,full time,sat solution,nodes,classes,sat time,egraph time
/tmp/test.smt2,unsat,23.431µs,154.898µs,0,10,2,10.897µs,14.813µs
/tmp/test.smt2,unsat,23.431µs,154.898µs,1,10,2,742.000ns,8.531µs
/tmp/test.smt2,unsat,23.431µs,154.898µs,2,10,2,3.181µs,6.328µs
```

It is clear the e-graph, for each case, has 12 fewer e-nodes and 1 fewer
e-class and that 30-50x less time in spent in the e-graph.



# Source Code Overview

The SMTLIB format that the tool partially supports is documented here:
https://smt-lib.org/papers/smt-lib-reference-v2.6-r2021-05-12.pdf

The tool only implements the subset of the format that is used by the EUF
benchmark in `/euf-solver/benchamrks/`.

The full source-code of the solver is ~1k lines of code in
`/euf-solver/euf-solver.rs`.  Its dependencies are the following:

* minisat: the internal SAT solver
* egg: the popular and optimized e-graph Rust implementation
* disegg: our modification of egg with disequality edges (see `/README.md`)
* clap: parse and handle command line arguments

While disegg is a drop-in replacement for egg, i.e., any egg code will run as-is
with disegg, the solver depends on both for a single reason: in the code where
equality embedding is used we wish to have the *static* guarantee that it's
impossible to use disequality edges.

## Utilities

Until line 67, utilities are defined. Most notably an `Assoc<S,T>` data
structure that represents an association, or a partial bijection, between values
of type `S` and `T`. It is implemented as two hashmaps with necessary methods to
maintain the `Assoc` invariants.


## Tokenizing SMT2 Files

The tokenizer is implemented from line 67 to 218.

`tokenize` accepts a vector of characters (as we assume smt2 files are all
ASCII-encoded) and produces an iterator of tokens.

`parse_script` accepts this iterator and produces all the s-expressions.


## Parsing SMT2 Files

The only s-expressions to manipulate are bool propositions that are asserted.
These are represented by the `Term<UF, N, E, T>` struct. The various parameter
indicate the possible shapes a term may have.

The `UF` parameter is the type decorating the `UnFun` uninterpreted function
application constructor. It is expected to be either `String` or `Void`. The
`String` case is the name of the function being called. Of more interest is
the`Void` case means that the `UnFun` constructor is not possible to create as
`Void` has no constructor. In other words, this term will not have calls to
uninterpreted functions in it.

The `N` parameter describes which data types can be negated in the term.

The `E` parameter describes which types can be equated in the term.

Finally, as `Term` is not recursive, the `T` parameter describes the type of
subterms.

This choice of parameters allow us to express all the intermediary data
structures (discussed in the next section) quickly and easily.

Quantified terms are represented with the `QuantTerm<T>` struct.

These structs are defined from line 219 to 253.


## AST Transformations

An s-expressions goes through a sequence of transformations that convert it to
CNF which can be checked with the SAT solver. This section describes this
pipeline.

The intermediary datatypes are defined from lines 254 to 290.

1. `SExpr` to `Term_FQ_FN_UF_E`: this is the most general term where any term
   can be negated, any quantification is allowed, any two terms can be equated,
   and function calls are allowed. The translation function is defined in line
   291 to 489. This is also where the subset of SMTLIB term format is
   implemented.

2. `Term_FQ_FN_UF_E` to `Term_FQ_FN_E`: defined from lines 490 to 560. These
   terms eliminate calls to uninterpreted functions. The step simply collects
   all UF calls and replaces them by a fresh identifier and records that
   aliasing in an `Assoc` structure that it returns. *This aliasing is later
   represented as an equality in the e-graph*.

3. `Term_FQ_FN_E` to `Term_FQ_RN_E`: defined from lines 563 to 610. This
   transformation pushes negation all the way down term until only identifiers
   can be negated.

4. `Term_FQ_RN_E` to `Term_RN_E`: defined from lines 614 to 654. This
   transformation removes universal quantification and skolemizes the
   existential quantification, i.e. every existentially quantified variable is
   replaced by a fresh function call to all previously universally quantified
   terms. This new function call is added to the `Assoc` datastructure that
   UF-elimination produced. *This aliasing is also later represented as an
   equality in the e-graph*.

5. `Term_RN_E` to `Term_RN`: defined from lines 663 to 699. It removes all
   equalities from the term by lifting them out and returning them as separate
   associations. *These associations are later represented as an equality in the
   e-graph*.

6. `Term_RN` to `CNF`: defined from lines 716 to 771 and is standard.


### A note on handling universal quantification

The handling of universal quantification is very naively done. The variable is
simply treated as it if it was declared. While this has an effect on the
correctness of the SAT status that the solver produces, it allows us to quickly
makes progress in the implementation to benchmark the disequality treatment
in the different e-graphs.

Non-naive approaches would inspect the sort (type) of the quantified variable,
and expand the quantified term as a conjunction of all possible instantiations
of the variable with values of its type. This is only possible when the
inhabitants of that type are finite, e.g. `Bool`.
When the sort is not finite then all the expressions occurring in the program of
that type can be collected and substituted. At his point, a satisfiable formula
must report instead "unknown".



# Solving

## CNF Solving

Solving a CNF formula consists of serializing the `CNF` struct into a format
that minisat accepts. This is done in lines 785-829.

Since minisat does not support iterating through multiple solutions, we
implement this feature by adding the negation of a given previous solution and
requesting a new solution, until the formula can no longer be satisfied.

## EUF Solving: E-Graphs and Die-Graphs

The SAT solution must be analyzed and checked whether it is consistent with the
UF and equality terms that the original formula had.

This is done through either the `check_sat_ee` function defined between lines
870 and 945 or by `check_sat_de` defined between lines 947 and 1012. The choice
of which is determined by the `--disegg` CLI flag.

Both functions share very similar code. We purposefully duplicated the code here
as this is where `egg` or `disegg` are imported and we wish to keep a lexical
boundary between the two functions to *statically* prevent the possibility of using
disequality edges where equality embedding should be used.

Where they differ is in the following. Recall that all equality terms are lifted
from the term and substituted by a fresh variable. If the SAT solver assigns
this variable the value `false` then the equality is false, i.e. the assertion
of disequality is true. The treatment of this disequality is handled differently
in both functions.

In `check_sat_de` this can be seen by inspecting lines 977-984. This check does
not exist in `check_sat_ee` as it is not needed! The aliasing of the equality
term and the fresh variable is already embedded in `check_sat_ee` on lines
889-894. The embedding does not exist in `check_sat_de`.
