# egglog-experimental

This repo implements several experimental extensions to the core [`egglog`](https://github.com/egraphs-good/egglog).
Currently, this can be thought of as a standard library to `egglog`.

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

## Documentation

Check out the crate documentation (built locally) for the current list of implemented extensions, API details, and demo links.
Releases are coordinated with compatible releases of egglog.

## Constructor injectivity

Mark a constructor with `:injective` to infer equal arguments when two of its
results are equal. Schedule the shared `injectivity` ruleset explicitly:

```lisp
(datatype Term (Leaf String))
(constructor Wrap (Term) Term :injective)
(union (Wrap (Leaf "a")) (Wrap (Leaf "b")))
(run-schedule (saturate injectivity))
(check (= (Leaf "a") (Leaf "b")))
```

Datatype variants also accept the annotation, for example
`(datatype Term (Leaf String) (Wrap Term :injective))`. It combines with
`:cost` and `:unextractable`. Equality-sort arguments are unioned; differing
primitive arguments trigger a panic when the ruleset runs. Container arguments
are currently rejected at declaration. Injectivity applies within each marked
constructor and does not require different constructors to have different
results. The generated rules support term encoding and proof testing.

Executable examples cover [mixed arguments](tests/injectivity/injectivity-basic.egg),
[recursive propagation](tests/injectivity/injectivity-recursive.egg), and
[mutually recursive datatypes](tests/injectivity/injectivity-datatypes.egg).

`(known-disequal? left right)` queries known disequality on demand. Both operands
must have the same equality sort; the predicate returns `Unit` when it finds a
finite witness and is undefined otherwise. For example:

```lisp
(datatype Term (Num i64 :injective))
(Num 1) (Num 2)
(check (known-disequal? (Num 1) (Num 2)))
```

For two existing applications of the same marked constructor, any unequal
corresponding arguments establish unequal results. Primitive arguments use native
`!=`; equality-sort arguments use asserted `(disequal ...)` facts or recursive
witnesses. For any constructor, marked or unmarked, unequal results establish
unequal arguments at one position when every other argument is already equal:

```lisp
(datatype Input (Common) (Left) (Right))
(datatype Output (Pair Input Input))
(disequal (Pair (Common) (Left)) (Pair (Common) (Right)))
(check (known-disequal? (Left) (Right)))
```

This reverse rule follows from congruence and needs no injectivity annotation.
It accepts a unionable equality-sort output and focused argument with primitive
or unionable equality-sort siblings. Containers and custom function tables are
outside this fragment. Two unresolved positions do not select one unequal pair,
and different constructor names supply no disjointness witness. Only marked
constructors propagate unequal arguments forward to unequal results.

Queries read the current graph without creating constructor applications or
storing derived disequality pairs. They need no saturation; equality propagation
still requires scheduling `injectivity`. Queries use committed sibling equalities
and do not jointly close equality and disequality. Unknown equality supplies no
inequality witness. Cycles terminate, although each structural query scans
eligible rows into a transient parent index and can visit many value pairs. Use
`:naive` for rules whose bodies call this predicate, because its reads extend
beyond the rule's explicit table atoms. The new query currently supports ordinary
execution only; term encoding and proof testing reject it. See the executable
[disequality query example](tests/injectivity/injectivity-disequality.egg).
