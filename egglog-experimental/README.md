# egglog-experimental

This repo implements several experimental extensions to the core [`egglog`](https://github.com/egraphs-good/egglog).
Currently, this can be thought of as a standard library to `egglog`.

The [test documentation](tests/README.md) describes the Herbie rewrite workloads and their origin.

You can use the egglog [Zulip](https://egraphs.zulipchat.com/#narrow/stream/375765-egglog) to ask questions and suggest improvements to this repo.

## Trying it out

The easiest way to try out `egglog-experimental` is to use the [web demo](https://egraphs-good.github.io/egglog-demo), which builds on top of latest egglog-experimental.

To install egglog-experimental binary locally, you need to install `cargo` and run

```
git clone git@github.com:egraphs-good/egglog-experimental.git
cargo install --path=egglog-experimental
```

To use it in a Rust project, you can add it as a dependency in a `Cargo.toml` file.

```
egglog-experimental = "3.0"
```

## Slotted e-graphs

In this workspace, `egglog-experimental --slotted FILE.egg` transforms the slotted
source language into ordinary egglog before evaluating it through the normal CLI.
`--slotted-no-aliasing` selects compatibility with the reference nested matcher;
`--mode desugar` shows the lowered program. The transformation lives entirely in
this crate. See [the source language](src/slotted/LANGUAGE.md) and
[the encoding](src/slotted/ENCODING.md) for its supported syntax and semantics.

Run `cargo run -p egglog-experimental -- --slotted --proofs file.egg` to print checked
proofs over source terms. See [Getting proofs](src/slotted/LANGUAGE.md#getting-proofs)
for usage and [the proof guide](src/slotted/PROOFS.md) for supported forms and the format.

## Documentation

Check out the crate documentation (built locally) for the current list of implemented extensions, API details, and demo links.
Releases are coordinated with compatible releases of egglog.

## Disequality and separate injectivity

`(disequal a b)` asserts a disequality. The root query pattern
`(known-disequal a b)` matches asserted or inferred positive evidence; a missing
match means unknown. `(contradiction)` matches when an asserted disequality's
endpoints have become equal, or a separate-injectivity promise conflicts with
native primitive values. Both disequality operands must have the same unionable
equality sort.

Use `(separately-injective F)` after declaring an ordinary constructor to promise
injectivity in each coordinate while all other inputs are fixed:

```lisp
(datatype Term (A) (B) (C) (Add Term Term) (Exp Term))
(separately-injective Add)
(separately-injective Exp)
(disequal (A) (B))
(Exp (Add (C) (A))) (Exp (Add (C) (B)))
(check (known-disequal (Exp (Add (C) (A))) (Exp (Add (C) (B)))))
```

For binary `F`, equal outputs `F(a,b) = F(a,c)` imply `b = c`. Positive
`b != c` implies unequal existing outputs `F(a,b)` and `F(a,c)`. Both rules
require the other input to agree. Equality of `F(a,b)` and `F(c,d)` alone
unions neither pair of inputs. No rule propagates output disequality downward,
and different constructor names imply no disjointness. Unmarked constructors
generate no structural rules. Native primitive fields use native `!=` as
positive evidence; containers and nonunionable equality sorts cannot be marked.
For a marked unary constructor `Num : i64 → Term`, n distinct inputs can generate
n(n − 1) ordered disequalities. The pass materializes this evidence eagerly.

The pass saturates its private rules after each user run, including runs nested
in sequences, repetitions, and saturations. It also closes pending top-level
assertions, constructor rows, and unions before checks, proof requests, schedules,
and observations. User run budgets and pre-step `:until` checks are preserved.
Generated joins include subsumed rows and create no constructor applications.
They support ordinary execution, term encoding, and proof testing.
With `--slotted`, injectivity/disequality lowers to constructors and
`rewrite :when` before slot encoding. From Rust, configure this composition with
`slotted::Compiler::new(options).with_source_macros(disequality_source_macros())`.
Slotted requires the full multipattern matcher, excludes cross-sort term patterns,
and cannot express injectivity promises for rigid `Var` arguments. Its
[schedule restrictions](src/slotted/LANGUAGE.md#run) also apply.

The [paper overview example](tests/slotted/overview.egg) eliminates a summation
using inferred disequality and binder-independence guards. Its
[checked source proof](tests/snapshots/slotted_proofs__overview.snap) is snapshot-tested:

```sh
cargo run -p egglog-experimental -- --slotted --proofs egglog-experimental/tests/slotted/overview.egg
```

The two query patterns are supported only as whole facts in checks, rule bodies,
rewrite conditions, and run-until conditions. They expose ordinary relation
dependencies to seminaive rules. Nested expressions and action uses are rejected.
The encoding is incomplete for logical disequality; an absent row remains unknown.

Executable examples cover [fixed-coordinate cancellation](tests/injectivity/injectivity-basic.egg),
[recursive propagation](tests/injectivity/injectivity-recursive.egg),
[mutually recursive datatypes](tests/injectivity/injectivity-datatypes.egg), and
[positive disequality queries](tests/injectivity/injectivity-disequality.egg).
