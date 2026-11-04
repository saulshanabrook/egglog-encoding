# Eggcc semantic eligibility fixtures

These fixtures audit candidate laws before compiler changes. They run the actual
injectivity/disequality implementation in ordinary mode under NEE and EE. They
are reduced source-derived replays and proposed analyses, not captured complete
compiler runs. No existing eggcc bug, optimized-program result, or speedup is
claimed here.

The source checkout was eggcc
`15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`, branch
`codex/remove-merge-constructors`; conclusions are specific to that source.
The encoding source was `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`.
The reused debug CLI SHA-256 was
`46f898796589e8585ecaf1499a9b9d7ee98d31fc45f64d2061c103795d62ecf2`.
The semantic worker did not build the compiler or runtime.

`source/` contains unmodified full schema/mem-simple copies and exact source
excerpts. [Its manifest](source/manifest.json) identifies source revisions,
whole-file hashes, excerpt ranges, and copy hashes. Inline rules in the other
fixtures name their source ranges; proposed rules and seeded faults are labeled.

## Run

From this directory, use an existing feature CLI:

```sh
EGGLOG_EXPERIMENTAL=/Users/saul/p/wt/egglog-encoding/injectivity/target/debug/egglog-experimental
"$EGGLOG_EXPERIMENTAL" --disequality-encoding nee exact-local-address-keys.egg
"$EGGLOG_EXPERIMENTAL" --disequality-encoding ee exact-local-address-keys.egg
```

Run each fixture with both `nee` and `ee`. Five files should exit 0:
`constructor-laws.egg`, `constant-guard-controls.egg`,
`active-noalias-controls.egg`, `analysis-record-refinement.egg`, and
`exact-local-address-keys.egg`. Three files should exit 1 with the stated error:

| Fixture | Required error substring |
| --- | --- |
| `literal-conflict.egg` | `injectivity violation in constructor ` followed by the constructor name `Int` |
| `constant-guard-conflict.egg` | `Unsoundness detected: const values differ at top level` |
| `analysis-record-refinement-cancel.egg` | `injectivity violation in constructor ` followed by the constructor name `I` |

An arbitrary process failure is not a passing negative test. The final recorded
run checks both status and error substring. There are 16 expected process
outcomes across the eight fixtures and two encodings. Do not enable term/proof
mode: `known-disequal?` does not support those modes.

Raw receipts are under the primary checkout's ignored
`benchmarks/local/eggcc-encoding-case-study/semantic/`: `runs.json` records the
exact commands, transitive input hashes, binary hash, statuses, expected errors,
and stdout/stderr paths. `provenance.json` and `source-snippets.txt` retain the
audit sources. One-shot elapsed times are diagnostics, not performance evidence.

## What is established

| Candidate | Executable observation | Assessment |
| --- | --- | --- |
| Arbitrary `Concat` | Associativity and empty identities equate results with unequal corresponding arguments. | Reject blanket injectivity. |
| Generic `Bop` / `Top` | Addition commutativity and `Select(pred,x,x)=x` erase different fields. | Reject blanket injectivity. |
| `Single` | Equal wrappers already cancel through the existing `Get(Single(x),0)=x` rule. | Equality power is redundant. |
| Literal `Int` / `Bool` | Primitive mismatches supply witnesses; seeded unequal literal merging panics when injectivity runs. | Sound data wrappers, no incremental compiler benefit established. |
| Global `Const` | A seeded vacuous equality in an unreachable `InIf` context leaves shared literal data unequal; the existing guard rejects a seeded top-level merge. | Preserve the context guard; reject global cancellation. |
| Active `NoAlias` | Positive/negative nonzero offsets commute; zero, symbolic zero, same pointer and unknown pointer pairs do not. | Current active contract reproduced. |
| Mutable points-to records | Bound refinement makes distinct resolved records equal through the same analysis application. | Reject the proposed structural annotation chain. |
| Exact local address keys | Restricted query/manual arms both forward 17 past a store of 99 to a separate fresh allocation; baseline active rules do not. | Promising compiler prototype, currently replay-only. |

Unknown query results remain undefined. Distinct current e-class IDs are not
asserted disequalities. The fixtures require no constructor-disjointness or
multiargument reverse inference; query rules use `:naive`, and equality
injectivity is explicitly scheduled.

## Mutable-record falsifier

The real `PointsToCells(PtrAdd(p,i), aps)` rule reads `lo-bound` and `hi-bound`,
then unions its output with the resulting points-to record. The bound tables
merge by maximum/minimum. In `analysis-record-refinement.egg`, changing the
offset range from `[1,2]` to `[1,1]` legitimately yields a second representation
of the same analysis output. The resolved wide and narrow maps become equal.

The deliberately proposed record annotations would first find a structural
inequality witness. Recording that hypothetical constraint then reports a
contradiction after refinement; scheduling cancellation panics at primitive
`I(1)` versus `I(2)`. This rejects the annotations, not the baseline compiler.
The same fixture shows why dropping `Resolved-Pointees` looked attractive: a
known differing field can give a witness before an unrelated tail resolves.
That power does not make mutable analysis records immutable identities.

The source interval intersection rules also show that `[1,2]` and `[1,1]`
overlap. Unequal record representations do not establish disjoint possible
addresses. The optional production `DontAlias` rule uses empty intersection,
not record inequality; it is outside the default schedule.

## Exact-key prototype boundary

`exact-local-address-keys.egg` adds a new immutable data sort
`LocalCell(function, ordinal, offset)` and relations over a restricted state
prefix. It does not annotate existing expression or points-to constructors.
The rules enforce:

- A sole `StateT` input in an `InFunc` context starts the prefix.
- Direct positive constant-sized allocations extend it and increase the
  ordinal. Static `Alloc` IDs are ignored. Inherited `LiveAllocation` facts
  connect each pointer's allocation origin to the exact consumer state.
- Only stores of constant integer values to already-live exact addresses
  preserve the prefix. Calls, frees, branches, loops, and unknown effects have
  no transfer rule.
- Constant pointer offsets are accepted only when the resulting offset stays
  in `[0,size)`. The guards establish representable arithmetic before addition.
- A consumer compares keys only for origins live in that same state and
  function. It uses the existing write/load commuting consequence and existing
  store forwarding.

Within that grammar, induction on the prefix gives distinct fresh regions for
distinct ordinals, and distinct valid cells for different offsets within one
region. Key equality is not used as a runtime-alias assertion. Key inequality
outside the consumer's guarded domain has no nonalias meaning.

The fixture deliberately repeats static allocation ID 0. Both query and
equivalent materialized-pair arms still succeed. Negative checks exclude
zero/symbolic-zero offsets, unknown pointers, symbolic sizes, zero-sized
allocations, invalid/huge offsets, cross-context offsets, and allocations after
calls/frees or in branches/loops. Source pointer-add reassociation, integer
folding, duplicate/shadowed writes, and load-state equality run before and
during the comparison. No pointer acquires conflicting keys, no state acquires
different ordinal counts, and no self-`NoAlias` is derived.

The state-prefix/ordinal invariant must survive every equality rule enabled by
an eventual full compiler treatment, including context reconstruction and
inlining. The replay checks the applicable local normalization rules; it does
not complete that whole-compiler obligation. `LiveAllocation` may cost more
than the old pair relation. No compactness, speedup, or broad alias-analysis
replacement claim follows.

[fresh-allocations.bril](fresh-allocations.bril) is the next proposed compiler
input, based on the real optional two-allocation DAG test. Full baseline and
feature compiler runs must validate interpreter equality, actual forwarding,
and a comparison against the same new key analysis with manual pair storage.
The optional memory analysis already supports this operation sequence, so its
activation must remain a separate treatment.
