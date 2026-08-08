# EgglogSemantics

A Lean 4 formalization of egglog's semantics, aimed at proving things about the
proof encoding in `egglog/src/proofs/` (designed in
`egglog/src/proofs/proof_encoding.md`).

It is a port of the Redex model in
[egglog PR #324](https://github.com/egraphs-good/egglog/pull/324).

**Picking this up?** Start with [`HANDOFF.md`](HANDOFF.md) — what is proved, what is
stated but unproved, what is known *false*, the work queue, and the gotchas.

See [`PLAN.md`](PLAN.md) for what the port changes and why, the milestone list, and the
route to the proof-encoding theorems; [`MERGE.md`](MERGE.md) for the `:merge` design
(M9), which is in progress — its compatibility theorem is proved and its differential cases
pass, but 23 statements in `Proofs/Merge.lean` are unproved (17 of them the `execM`
refinement chain, stated and ready to prove) along with M11's 13 in `Proofs/Encode.lean`,
so `make lean-check` fails on those while `lake build` is clean. Note
that `Spec/` is append-only and `Impl/` is not: the reference implementation deletes
superseded merge rows because egglog does, so the contract between them is a containment
rather than an equality — `MERGE.md` again. See also
[`CHECKER.md`](CHECKER.md) for what a Lean model of egglog's proof checker would cost,
which scopes M11.

## Layout

The tree separates *what is being claimed* from *why it holds*, so the first can be
read closely and the second skimmed.

| | contents | theorems |
| --- | --- | --- |
| `EgglogSemantics/Spec/` | the semantics — what an egglog program means | none |
| `EgglogSemantics/Impl/` | the reference implementation, which computes it | none |
| `EgglogSemantics/Proofs/` | everything proved about the two, one file per subject | all |
| `EgglogSemantics/Tests/` | ported Redex checks, and the `.egg` emitter | a few |

`Spec/` and `Impl/` hold **definitions only** — no `theorem` appears in either. The
one exception the language forces is a proof needed to *make* a definition: the
`decreasing_by` on `Impl/Closure.lean`'s `closure`, and decidability instances. Those
are inlined rather than pulled out into named lemmas, so nothing in `Spec/` or `Impl/`
is there for a proof's sake.

Reading order for `Spec/`: `Syntax` → `Term` → `Database` → `Congruence` → `Eval` →
`Match` → `Step` → `Scope` → `Merge`. `Impl/` has `Closure` and `Interp`, with `Merge`
adding M9's lookup evaluator and merge phase. Each `Proofs/X.lean` is about `Spec/X.lean` or
`Impl/X.lean`; `Proofs/Interp.lean` additionally holds the refinement theorem
`exec_toDatabase`, which is what ties the two together.

## Building

```sh
lake exe cache get     # prebuilt Mathlib binaries
lake build
```

or, from the workspace root:

- `make lean-check` — builds and fails on any `sorry`.
- `make lean-difftest` — runs the interpreter and egglog on the same generated
  programs and compares per-function row counts, for the constructor fragment and for
  M9's `:merge` functions. Needs a release `egglog` binary.

Requires [`elan`](https://github.com/leanprover/elan); the toolchain is pinned in
`lean-toolchain` and Mathlib in `lakefile.toml` / `lake-manifest.json`.

## Editing with Claude Code

The workspace `.mcp.json` declares a [`lean-lsp-mcp`](https://pypi.org/project/lean-lsp-mcp/)
server pointed at this directory, which gives per-declaration diagnostics without a full
`lake build`, and `lean_verify` for auditing a theorem's axioms — a stronger `sorry` check
than grepping, since it traces into Mathlib. It needs `uvx` and `elan` on `PATH`, and the
server caches imports: after editing a file's *dependency*, rebuild through the server
rather than the shell or its answers go stale.
