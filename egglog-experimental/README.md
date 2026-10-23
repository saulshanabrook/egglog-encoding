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

## Slotted e-graphs

In this workspace, `egglog-experimental --slotted FILE.egg` transforms the slotted
source language into ordinary egglog before evaluating it through the normal CLI.
`--slotted-no-aliasing` selects compatibility with the reference nested matcher;
`--mode desugar` shows the lowered program. The transformation lives entirely in
this crate. See [the source language](src/slotted/LANGUAGE.md) and
[the encoding](src/slotted/ENCODING.md) for its supported syntax and semantics.

## Documentation

Check out the crate documentation (built locally) for the current list of implemented extensions, API details, and demo links.
Releases are coordinated with compatible releases of egglog.
