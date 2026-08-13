# EgglogSemantics

A Lean 4 model of egglog's semantics, ported from the Redex model in
[egglog PR #324](https://github.com/egraphs-good/egglog/pull/324). The goal is to model
egglog as cleanly as possible for a paper, and then prove things about an implementation.
Proving things about egglog's proof encoding is the eventual payoff, and is **parked**.

**Which egglog.** This models egglog *as extended in this repo*, not a released one. Two
extensions are load-bearing and are part of what the paper discusses:

| extension | upstream `egraphs-good/egglog` | here |
| --- | --- | --- |
| multi-output columns — `(function Pair (Math) (i64 i64) …)` | `parse error: expected output sort` | accepted |
| `set` inside a `:merge` body — `:merge (<action>* <result>)` | `:merge` takes a single expression | accepted |

Checked against upstream `c92a910` (v2.0.0). The second is why M9 makes a merge a *step
relation on databases* rather than a function combining two values — a body that writes
entries cannot be modelled as a fold. `make lean-difftest`'s oracle is this repo's binary,
so it validates against the extended language.

**Picking this up?** Start with [`PLAN.md`](PLAN.md), "Current priority" — what we are
working on now, what is parked, the two interpreter contracts, and how to check a change.

The rest of `PLAN.md` has what the port changes and why, and the milestones.
[`MERGE.md`](MERGE.md) is the `:merge` design (M9). Two files are parked with M11:
[`ENCODING.md`](ENCODING.md), what was learned from the encoding's theorems before they were
deleted, and [`CHECKER.md`](CHECKER.md), what a Lean model of egglog's proof checker would cost.

Two things worth knowing before reading any of it.

**`Spec/` is frozen** at 8 files and ~975 lines. `Impl/` is ported against it, difftest is green,
the whole library builds and **there are no `sorry`s left**. What is open is coverage rather than
proof: `PLAN.md`, "What is covered, and what is not", has the one combination — a `union` together
with a `:merge` function — that neither top-level theorem reaches, and which difftest exercises.

**`Spec/` is append-only and `Impl/` is not.** Nothing is ever removed from `Database.eqs`,
where a function's whole table lives as terms; `Impl/` keeps a `Row` index it re-keys and
deletes from, because egglog does. So the contract between them is a **containment**, not an
equality — except on the constructor fragment, where the merge phase is the identity and
`exec_programStep` still holds.

## Layout

The tree separates *what is being claimed* from *why it holds*, so the first can be
read closely and the second skimmed.

| | contents |
| --- | --- |
| `EgglogSemantics/Spec/` | the semantics — what an egglog program means |
| `EgglogSemantics/Impl/` | the reference implementation, which computes it |
| `EgglogSemantics/Proofs/` | everything proved about the two, one file per subject |
| `EgglogSemantics/Tests/` | example programs as proofs and `#guard`s, and the `.egg` emitter |
| `EgglogSemantics/Encoding/` | **parked M11** — the encoder `encode` and nothing else; its theorems were deleted, and [`ENCODING.md`](ENCODING.md) is what survives them |
| `Scratch/` | one surviving witness file, outside the library and so outside `lake build` — which is how the others were lost; `PLAN.md`, "Checking a change" |

`Spec/` and `Impl/` are **definitions**, with what the language forces inlined rather than
named: `decreasing_by` on `Impl/Closure.lean`'s `closure`, decidability instances. Two
deliberate exceptions, both about the same thing — that a term is present exactly when it is
self-equal. `Spec/Congruence.lean`'s `eqsInTerms_free` is one line and is what lets
`Database.WF` drop a field. `Impl/Interp.lean`'s `toDatabase_*` and `EqsInTerms` lemmas are
the bridge from the interpreter's term list to the diagonal of `Database.eqs`, which every
refinement theorem reads through; they sit beside `toDatabase` because they are what makes
it the right denotation, not a step in a proof.

Reading order for `Spec/`: `Syntax` → `Term` → `Database` → `Congruence` → `Eval` →
`Match` → `Step`, with `Scope` (the front end's static checks) hanging off `Term`. The
split that matters is `Eval` versus `Step`: `Eval` is `Option`-valued and says what a
command computes, `Step` is `Prop`-valued and relational, because merge closure and rule
firing are order- and choice-dependent. Neither has a duplicate on the other side.
`Impl/` has `Closure` and `Interp`, with `Merge` adding only M9's merge phase and `Check`
the two front-end checks that are `Bool` rather than `Prop`.

Each `Proofs/X.lean` is about `Spec/X.lean` or `Impl/X.lean`. Two are not:
`Proofs/Counterexamples.lean` and `Proofs/Lattice.lean` hold compiling witnesses that
particular statements are **false**, so a refuted statement cannot quietly come back.
`Proofs/Interp.lean` holds `exec_programStep`, the biconditional that ties spec and
implementation together.

## Building

```sh
lake exe cache get     # prebuilt Mathlib binaries
lake build
```

or, from the workspace root:

- `make lean-check` — builds and fails on any `sorry`. It passes, over the whole library,
  `Proofs/Counterexamples.lean` and `Proofs/Lattice.lean` included, so any hit is a regression.
- `make lean-difftest` — runs the interpreter and egglog on the same generated programs and
  compares per-function row counts, for the constructor fragment and for M9's `:merge`
  functions. 166 cases, all passing. Needs a release `egglog` binary. It reaches the
  interpreter without going through `Proofs/`, which is why it stays runnable during the
  port.

Requires [`elan`](https://github.com/leanprover/elan); the toolchain is pinned in
`lean-toolchain` and Mathlib in `lakefile.toml` / `lake-manifest.json`.

## Editing with Claude Code

The workspace `.mcp.json` declares a [`lean-lsp-mcp`](https://pypi.org/project/lean-lsp-mcp/)
server pointed at this directory, which gives per-declaration diagnostics without a full
`lake build`, and `lean_verify` for auditing a theorem's axioms — a stronger `sorry` check
than grepping, since it traces into Mathlib. It needs `uvx` and `elan` on `PATH`, and the
server caches imports: after editing a file's *dependency*, rebuild through the server
rather than the shell or its answers go stale.
