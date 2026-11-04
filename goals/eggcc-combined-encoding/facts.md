# Accepted facts

- Prioritize a real EggCC case where injectivity and disequality affect the same check or optimization; show the role of each mechanism rather than an unrelated optional query.
- A claimed richer positive case exercises equality-sort cancellation, multiple arguments, structural propagation, or a comparably substantive interaction beyond the existing unary Boolean-wrapper primitive mismatch.
- A new genuine compiler bug, newly enabled optimization or measured speedup is preferred, but a validated richer integration can qualify without those additional outcomes.
- Compare each implemented case with existing EggCC checks and an equivalent direct or hand-written mechanism, explaining what the encoding adds without requiring that it be impossible to hand-code.
- Every constructor law and disequality inference has an explicit semantic justification, including relevant context, feasibility, effects and refinement; previously rejected global Expr/Concat or mutable-analysis annotations are not reused without a new justification.
- Allow bounded immutable representations, scoped analysis values, compiler integration and encoding improvements needed by a concrete case; avoid a wholesale IR redesign, new proof support, Lean work or paper edits.
- Implemented cases have automated positive, negative and feature-contribution checks through actual EggCC consumers, including source-versus-optimized execution where supported; illustrative graphs, new workloads and replay-only results are labeled separately.
- Any claimed baseline bug has a valid minimized reproducer and a sound violated invariant; any claimed speedup has matched controls, validated outputs and repeated per-workload measurements with explicit time and memory boundaries.
- Preserve the completed case studies, frozen evidence and existing author changes; use isolated source changes and retain exact inputs, revisions, patches, commands, configurations and machine-readable experiment results.
- Deliver a collaborator-readable explanation and compact reference showing one connected inference path, the actual rules before and after, existing/manual behavior, observed results and encoding limits, with reproduction instructions kept separately.
- A documented negative for the investigated joint-encoding scope is acceptable after targeted experiments and an independent review explain the disposition of the promising candidates; retain richer single-feature findings as secondary results and do not claim universal impossibility.
- The existing Boolean observation checker remains a valid small fallback, but repeating it alone does not establish the richer joint-encoding result sought by this goal.
