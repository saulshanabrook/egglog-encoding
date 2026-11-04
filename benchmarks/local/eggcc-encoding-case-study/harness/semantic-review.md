# Independent read-only review: exact local address keys

**Decision support:** a guarded, opt-in experimental compiler prototype is a
reasonable next step for the proposed straight-line two-allocation case. I
found no concrete semantic counterexample within the stated prefix grammar and
the local memory/state equalities reviewed here. This is not a whole-compiler
soundness guarantee, and absence of the two conflict relations alone would not
establish one. Root owns the integration decision; the compiler worker owns the
actual hook/schedule audit and compiler runs.

No code was changed, no build was started, and no fixture or compiler command
was run during this review.

## Review basis

- Accepted `facts.md` and `plan.md` under
  `/Users/saul/p/egglog-encoding/goals/eggcc-encoding-case-study/`.
- `/Users/saul/p/wt/egglog-encoding/eggcc-study/benchmarks/eggcc-encoding/exact-local-address-keys.egg`,
  SHA-256 `6201e363a637ca21097dedeaf56146a2f2fde60f5b8d22a0096010954a881e3e`.
- The same directory's `fresh-allocations.bril`, SHA-256
  `a5c0281dc49b93af37a696a26d8b65811883bb3d3d99165a6fad9e9fd80be16a`,
  and the README once it became available.
- Relevant current source in
  `/Users/saul/p/wt/eggcc/encoding-study-retarget/`: `interpreter.rs`,
  `schema.egg`, `type_analysis.egg`, `optimizations/mem_simple.egg`,
  `optimizations/non_weakly_linear.egg`, state passthrough rules, source
  peepholes, context/substitution transitions, `schedule.rs`, and the allocation
  translation in `src/rvsdg/to_dag.rs`. Eggcc HEAD was
  `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`; compatibility edits elsewhere in
  that worktree are not a semantic validation result from this review.
- The marked-constructor/query contracts in encoding `injectivity.rs` and
  `disequality.rs`, at encoding HEAD
  `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`.

## The defensible law

`LocalCell(function, ordinal, offset)` is an immutable structural descriptor.
Its injectivity as data is unobjectionable: equality of descriptors determines
their three primitive fields. It is not an annotation on `Expr`, contextual
`Const`, or refining points-to records. Structural descriptor inequality has
memory meaning only through the guarded consumer invariant.

For one applicable function invocation and a valid serial prefix, maintain:

1. `FreshState(s, name, n)` describes an allocation/store prefix rooted at that
   invocation's sole input state, with the next allocation rank `n`.
2. `LiveAllocation(s, origin, name, k)` says the particular local allocation
   origin is still live at that same prefix state.
3. `ExactLocalAddress(p, origin, LocalCell(name,k,o), size)` identifies an
   in-bounds cell of that origin, with `0 <= o < size`.

The consumer requires both origins to be live at the same pre-store state and
in the same function. Under those conditions, different ranks identify
different fresh live regions, and different valid offsets of one region name
different cells. Thus descriptor inequality supports universal nonalias over
the defined executions in this domain. It is not merely a test of different
current e-class IDs. The manual comparison correctly uses primitive integer
inequality on the same guarded descriptors, rather than raw `Expr !=`.

Ranks are not globally unique runtime allocation IDs. Different alternative
prefixes can assign the same rank to different origins; equality of their keys
must remain conservative and must never assert runtime aliasing. Across calls
or loop iterations, the same static origin can execute again. The proof above
is local to the invocation/prefix; it cannot be extended by treating the
function name as an allocation epoch.

The runtime source reinforces the relevant distinction: DAG evaluation caches
by shared expression identity within a region (`interpreter.rs:369-371`) and
resets that memo for a new region (`358-366`). `Alloc` ignores its static ID and
advances the allocator on each actual evaluation (`390-398`). The translation
does generate static IDs, but those IDs are not dynamic freshness witnesses.
The replay's deliberately repeated ID is therefore the right control.

## Guards and transformations

The allocation rule accepts only positive constant sizes. Writes preserve the
prefix only when the pointer is already exact and its origin is live; the
stored value is a constant integer and adds no hidden effect dependency. There
is no transfer through calls, frees, prints, branches or loops. Those stops are
essential to the lifetime/invocation argument, not incidental missing features.

The offset guards are arithmetically sound under the maintained bounds:
`delta >= -offset` and `delta < size-offset` establish a new offset in
`[0,size)` before evaluating `offset+delta`. Since size is a positive i64 and
the old offset is in that range, both guard subtractions and the resulting
addition are representable. This does not prove that an arbitrarily enormous
total allocation can execute successfully; the result is scoped to defined,
successful allocation executions. The actual one-cell Bril case avoids that
resource/address-space issue.

The reviewed existing local equalities preserve the intended invariant:

- Constant folding and nested pointer-add reassociation preserve an established
  valid address. Symbolic zero may normalize to the same key as zero, which
  must not give nonalias.
- Duplicate/shadowed writes change neither allocation count nor lifetime.
- Store forwarding and the existing non-weakly-linear equality
  `Get(Load(p,s),1) = s` change no allocation count or live region. The CLI
  enables the non-weakly-linear treatment, so this equality must be included in
  real compiler validation, as the README now acknowledges.
- The proposed write/load commute consequence is the existing active memory
  consequence with a stronger restricted premise. In the supplied Bril case,
  both allocations precede the stores; the first store initializes `p` to 17,
  and the intervening store writes 99 into separate live `q`. Commuting the
  load of `p` past that store should enable the existing forwarding rule.

Direct `InIf`/`InLoop` allocation controls are excluded by the seed/context
patterns. That is useful negative evidence, but it is not a proof about every
equality exposed later by inlining, substitution, context reconstruction or
loop transformations. In particular, relations accumulate facts over e-class
representatives: co-liveness and rank consistency must continue to refer to a
common valid prefix after those unions. No single global name/rank argument
discharges that whole-schedule obligation.

## Acceptance conditions and useful negative tests

Before accepting a prototype output:

1. Preserve the restricted rules exactly, including origin-specific liveness
   and the same-state/same-function consumer join. Do not turn an arbitrary
   descriptor inequality into a global `NoAlias` fact.
2. Run the relevant analysis/consistency closure after the actual source
   equalities and reject any `ConflictingKey` or `ConflictingOrdinal`. Run the
   marked injectivity and explicit disequality contradiction checks as well.
   A successful query result is not a replacement for those consistency gates.
   The gates must run before each pass's output is accepted, including after
   the consumer has created new equalities.
3. Establish that the guard machinery actually rejects a deliberately seeded
   pointer merge between different keys and a deliberately seeded unequal-rank
   state merge. The reviewed fixture checks that the relations stay absent on
   its good cases; those absence checks alone do not test the rejection path.
   Label these as seeded corruption controls, not eggcc bugs. A cyclic corrupt
   state graph may keep generating ranks before saturation, so incomplete or
   timed-out runs must also be rejected rather than accepted as guard-free.
4. Validate actual reconstructed full-compiler output, equal non-null
   source/optimized interpreter receipts, and a visible optimization effect.
   Keep same-pointer, zero/symbolic-zero offset, bounds, free/call, unknown and
   contextual exclusions as negative controls. The replay's synthetic unknown
   `Arg` expressions are graph controls; they are not by themselves well-typed
   full Bril regression programs with the sole-StateT input contract.

Conflict guards are useful rejection checks, not completeness proofs. They can
catch observed competing descriptions of a pointer or competing rank counts
of a state; they do not prove arbitrary source unions preserve runtime
allocation identity, universal co-liveness, or size consistency. Broadening the
grammar or adopting additional allocation/free/state equalities requires a new
argument and controls. Current source inspection found no rule that simply
erases a positive allocation into its input state, and no such equality is
assumed here.

The current evidence justifies trying the bounded prototype and measuring it
only after correctness succeeds. It establishes neither a real compiler bug
nor a speedup, and the optional existing memory analysis already covers the
operation sequence. A fair analysis-replacement contrast must preserve the
new domain/liveness contract in both query and materialized-pair arms, while
keeping optional-memory activation separate.
