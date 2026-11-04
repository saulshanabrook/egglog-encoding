# Bounded encoding review of the provisional plan

**No encoding-law, schedule, storage, fragment-scope, or verification blocker
identified.**

This review compared the current `../plan.md` with the completed
`encoding.md` source-discovery note for feature revision
`392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`. It did not scan or evaluate the
consumer/measurement implementation domains. Only this review file was written;
no source edits, builds, tests, or benchmarks were performed.

The plan correctly preserves the following essential distinctions:

- Remaining-child disequality follows from congruence when every other
  corresponding input is equal. It applies to an unmarked constructor;
  equal-output cancellation and child-difference-to-parent-difference remain
  annotation-gated. Two unresolved children do not justify selecting either.
- The first implementation fragment is explicitly bounded to constructor
  tables with unionable equality-sort output/focus and primitive or unionable
  equality-sort siblings. Direct primitive query/assertion operands, containers,
  and arbitrary function tables remain excluded. Primitive sibling equality
  does not create a new primitive-disequality storage API.
- Reverse schema discovery must include unmarked input sorts and must not rely
  accidentally on EE representation tables. The read-only contract rules out
  persistent derived-pair storage, new applications, unions, or query graph
  growth; transient indexes remain a cost to assess.
- A query's witness search is closure over the committed graph, distinct from
  equality production and persistent assertion normalization. The plan does
  not misdescribe `check-contradiction` as joint closure with injectivity or
  consumers. `:naive` consumers, reruns after hidden dependencies change, both
  scheduler paths, and audits inside generative saturation are retained.
- Any materialization/public-closure facility is a separately reviewed,
  consumer-driven extension. It is not silently introduced as part of the
  query change or treated as an existing public API.

The proposed verification covers the discriminating cases from the source note:
unmarked cross-sort binary positives; marked-only forward negatives;
unary/ternary/ambiguous positions; mixed primitive siblings; late equality and
scheduled injectivity; lifecycle/subsumed/cyclic behavior; contradictions;
read-only row/table stability; NEE/EE and core/extended scheduling. The focused
integration targets and `make check` are actual source-verified entrypoints.
The existing query mode-rejection test is in the listed
`injectivity_disequality` target, so the no-new-proof-support boundary has a
regression entrypoint as well.

The finite iterative oracle is appropriately presented as evidence for a
precisely stated fragment, with no unrestricted completeness claim. During
implementation its reference model should fix the equality partition, existing
typed applications, asserted seeds, and normalization stage as described in the
linked source note. This is an implementation detail already supported by the
plan, not a requested plan correction.

The plan also correctly separates an encoding-coverage improvement from the
impact objective. None of the reviewed encoding claims turns a newly available
witness, fewer rows, or an existing congruence contradiction into a speedup or
genuine baseline compiler bug claim.

Review stops here; consumer ranking, measurement treatment design, and ordinary
integration work in progress are left with their owners.
