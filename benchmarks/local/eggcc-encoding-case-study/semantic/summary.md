# Semantic eligibility handoff

Status: first semantic review checkpoint reached. A restricted exact-address-key
analysis is ready for a compiler prototype. The other initial annotation leads
are rejected on semantics or have no incremental benefit established. No real
compiler bug, full-compiler optimization, or performance result is claimed.

## Provenance and scope

- Eggcc source: `/Users/saul/p/eggcc`, commit
  `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`, branch
  `codex/remove-merge-constructors`, origin
  `git@github.com:egraphs-good/eggcc.git`. Existing author files were not edited.
- Encoding fixture worktree:
  `/Users/saul/p/wt/egglog-encoding/eggcc-study`, base
  `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`.
- Reused ordinary-mode CLI:
  `/Users/saul/p/wt/egglog-encoding/injectivity/target/debug/egglog-experimental`.
  SHA-256:
  `46f898796589e8585ecaf1499a9b9d7ee98d31fc45f64d2061c103795d62ecf2`.
- Fixture directory:
  `/Users/saul/p/wt/egglog-encoding/eggcc-study/benchmarks/eggcc-encoding/`.
  Changes are new semantic fixtures, source excerpts/manifest, one proposed Bril
  input, and README only. No runtime/compiler/script edits, builds, commits, or
  pushes were performed by this worker.

`provenance.json` records 14 source-file hashes. `source-snippets.txt` retains
the actual audited source ranges. Tracked `source/manifest.json` identifies the
unmodified copies and concatenated exact excerpts. `runs.json` contains exact
commands, working directory, expected statuses/errors, CLI and input hashes,
stdout/stderr paths, and all final outcomes.

## Exact commands and results

Working directory for every run:
`/Users/saul/p/wt/egglog-encoding/eggcc-study/benchmarks/eggcc-encoding`.
For each row below and each encoding in `nee`, `ee`, the command was:

```sh
/Users/saul/p/wt/egglog-encoding/injectivity/target/debug/egglog-experimental --disequality-encoding ENCODING FIXTURE
```

All runs used ordinary execution, one default thread, and a 20-second subprocess
timeout. No proof/term mode or builds were involved.

| Fixture | NEE / EE exit | Outcome |
| --- | --- | --- |
| `constructor-laws.egg` | 0 / 0 | Concat/Bop/Top counterexamples, Single redundancy, literal positive/unknown controls pass. |
| `literal-conflict.egg` | 1 / 1 | Expected exact injectivity error for seeded unequal primitive argument of `Int`. |
| `constant-guard-controls.egg` | 0 / 0 | Seeded unreachable-branch equality does not merge shared literals or top-level constants. |
| `constant-guard-conflict.egg` | 1 / 1 | Actual existing top-level guard reports its expected unsoundness error. |
| `active-noalias-controls.egg` | 0 / 0 | Existing nonzero-offset successes and forbidden zero/unknown/same-pointer rewrites pass. Branch projection now uses a valid fifth pointer field. |
| `analysis-record-refinement.egg` | 0 / 0 | Legitimate bound refinement equates distinct resolved representations; hypothetical recorded inequality contradicts. Unequal intervals are shown to overlap. |
| `analysis-record-refinement-cancel.egg` | 1 / 1 | Expected injectivity error at `I` after the same refinement; rejected annotations are labeled. |
| `exact-local-address-keys.egg` | 0 / 0 | Baseline absence, query/manual forwarding, eligibility exclusions and normalization consistency checks pass. |

Thus 16/16 expected process outcomes pass, including checking the diagnostic
substring for all six expected process failures. These are correctness probes,
not repeated cost measurements; elapsed times in `runs.json` are diagnostic.

## Candidate assessments

1. **Blanket Concat/Bop/Top injectivity: rejected.** Real source laws in
   `utility/canonicalize.egg:4-5,42-51` and
   `optimizations/peepholes.egg:47` equate applications with unequal fields.
   The reduced law fixture preserves the forbidden argument unions as absent.
2. **Single: existing support.** `utility/util.egg:59` supplies a left inverse.
   The fixture unions wrappers and derives argument equality without adding
   `:injective` to `Single`.
3. **Literal Int/Bool: sound but no incremental compiler case.** Literal data
   equality has the expected primitive payload invariant. The query witnesses
   Int/Bool mismatches and stays unknown across different constructor names.
   Current `type_analysis.egg:41-45` already detects unequal top-level Const
   payloads. Global Const injectivity is rejected: contextual/vacuous equality
   must not export a literal union, type union, or context union.
4. **Active NoAlias: baseline contract reproduced.**
   `optimizations/mem_simple.egg:20-61` relies on strictly nonzero offset bounds;
   `:71-81` consumes NoAlias for write/load commuting. Default scheduling is
   explicit in `schedule.rs:93-101`. Literal/symbolic zero, same-pointer,
   unknown-pointer and unknown-offset cases do not acquire witnesses or the
   forbidden commuting result. Distinct stored values 17 and 99 prevent an
   accidental equal-value success.
5. **Optional analysis-record comparison: rejected in the existing mutable
   representation.** `memory.egg:339-349` waits for two resolved records before
   raw `!=`. Structural witnesses can bypass unresolved tails in a replay,
   but the apparent benefit is unsound when applied to the current records:
   `memory.egg:289-296` repeatedly unions the same PointsToCells result with
   records built from bounds, and `interval_analysis.egg:9-10` narrows those
   bounds. The executed range `[1,2] -> [1,1]` makes the resolved wide and narrow
   maps equal. An annotation chain through Pointees/PointsTo/list/interval/I
   would force primitive `1 = 2`. `Resolved` means structurally available,
   not permanently immutable or a distinct abstract value.
6. **Record inequality as runtime nonalias: rejected.** Source intersection
   rules show the unequal intervals `[1,2]` and `[1,1]` share address offset 1.
   Optional `DontAlias` instead consumes an empty intersection
   (`memory.egg:384-389`), and its rulesets are omitted by default
   (`schedule.rs:101,120`). Runtime allocation freshness differs from static
   IDs: `src/rvsdg/to_dag.rs:272-280,345-351` generates per-function IDs;
   `interpreter.rs:390-400` allocates fresh regions. Inlining preserves original
   IDs (`function_inlining.rs:115-120`), so they are not assumed globally unique.

## Recommended next compiler prototype

**Exact local address keys** are the one positive first-pass lead. The proposed
new immutable constructor is `LocalCell(function, allocation-ordinal, offset)`.
Its injectivity is structural; existing Expr or analysis constructors are not
annotated. The mapping from keys to runtime addresses is used only behind an
enforced restricted domain:

1. The sole state input of an `InFunc` body starts a prefix with count 0.
2. A positive constant-sized allocation extends that prefix, gets its ordinal,
   and propagates explicit LiveAllocation ancestry. Static IDs are ignored.
3. Only constant-integer stores to an already-live exact address extend the
   supported state grammar; no call/free/branch/loop transfer rule exists.
4. Exact constant pointer adds retain the origin and require an in-bounds,
   representable resulting offset before performing addition.
5. Both origins must be live in the same actual consumer state and function.
   Different ordinals then identify different fresh allocations; different
   offsets within one ordinal identify different valid cells. Equal keys do
   not imply runtime aliasing.

The source-derived replay intentionally uses the same static Alloc ID twice.
Unmodified active mem-simple does not forward the original load past the
intervening store to the other allocation. Query and equivalent manual-pair
arms both derive the correct stored value 17, preserving inequality with the
intervening 99. Both arms use the same state/key/liveness analysis. Query
consumers are `:naive`; the equality-injectivity schedule is explicit.

Real source PtrAdd reassociation/constant folding, duplicate/shadowed writes,
and store-forwarded load-state equality run before and during those arms.
No pointer gains conflicting known-different keys, no state has differing
ordinal counts, and no self-NoAlias is produced. Unknown pointers, symbolic
sizes/offsets, zero-sized regions, out-of-bounds/huge offsets, cross-context
offsets, zero/symbolic-zero aliases and unsupported effect/region boundaries
remain excluded by executable checks.

Proposed compiler input: `fresh-allocations.bril`, derived from the real optional
two-allocation test in `memory.rs:439-469`. It prints 17 after storing 17 to one
fresh allocation and 99 to the other. Compiler worker should compare actual
baseline/retarget/query/manual runs with non-null, equal interpreter receipts
and explicit transformation evidence. The optional existing memory analysis
already covers this operation sequence; its activation must be a separate arm.

Remaining integration obligation: confirm all equality/normalization/context
and inlining rules active in the full compiler preserve the prefix/ordinal and
live-origin invariant. The executable conflict checks should be retained in a
prototype. The local replay does not discharge this whole-compiler obligation.
LiveAllocation can itself be expensive, so no asymptotic compactness or speedup
is claimed. A neutral/slower compiler result is acceptable evidence.

## Development-only diagnostics

`first-pass.json` retains initial fixture parse failures, corrected by putting
definitions before rules and moving expected runtime errors to separate files
(`fail (run-schedule ...)` is not supported by this command macro). One early
refinement probe used `[0,1] -> [0,0]`; narrowing then made the analysis output
identical to its own input record, and saturation timed out at 20 seconds.
That subprocess was terminated by the timeout. The final probe uses
`[1,2] -> [1,1]`, preserving the refinement conflict while avoiding that extra
self-feedback. No compiler bug or performance claim relies on the exploratory
timeout. An early exact-key check also reused global `size` where an existential
capacity variable was intended; final input/hash/status receipts replace it.

Stop condition: semantic law and a source-derived intended optimization are now
concrete and reviewable. Further work belongs with the compiler prototype and
whole-compiler validation owner before broader semantic annotations or claims.
