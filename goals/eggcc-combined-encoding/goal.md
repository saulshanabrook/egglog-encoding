# Find a richer joint encoding case in EggCC

Explore EggCC for a reproducible case where injectivity and disequality contribute to the same compiler check or optimization, exercising more of the encoding than the existing Boolean observation checker. Prefer a genuine bug, newly enabled optimization or measured speedup, while accepting a validated richer integration or an independently reviewed negative for the investigated scope.

Use [facts.md](facts.md) as the shared understanding and [plan.md](plan.md) as the approved execution plan. The plan begins with structural type disequality in EggCC's existing mismatch check, then investigates the remaining promising candidates as needed.

The goal is done when the accepted facts have been audited and either a richer joint case is validated through an actual EggCC consumer, with existing/manual comparisons and checks of each mechanism's contribution, or targeted experiments and independent review justify a scoped negative. Deliver reproducible inputs and evidence, a collaborator-readable explanation, a compact reference and separate reproduction instructions. Preserve the prior case study as a fallback; repeating it alone does not satisfy the richer result. Claim a new bug or speedup only with the evidence required by the facts and plan.
