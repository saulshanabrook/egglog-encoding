# Read-only creative audit: nontrivial EggCC injectivity/disequality payoffs

Act as a divergent but source-grounded research collaborator. Inspect the current workspace, especially:

- `goals/eggcc-encoding-payoff/`
- `goals/eggcc-combined-encoding/`
- `goals/eggcc-encoding-impact/`
- `goals/eggcc-encoding-case-study/`
- the current injectivity/disequality implementation and tests under the relevant Egglog worktree
- current EggCC source in `/Users/saul/p/eggcc` or referenced EggCC worktrees

Do not edit files, run builds/tests, access the network, or claim an experiment occurred. Distinguish verified source facts from hypotheses.

We need a successor study whose success requires both:

1. **Nontrivial generic mechanism.** Injectivity or disequality must derive an equality/disequality over equality-sort children, and a separate real EggCC consumer must use that intermediate fact. A treatment that only notices one constructor around unequal primitive fields and directly panics/guards is disqualified. A larger faithful manual multi-rule implementation is a fair comparator and does not automatically disqualify the generic mechanism.
2. **Real payoff.** A qualifying endpoint is a new compiler bug that pre-exists the integration in a fresh pinned EggCC baseline, or a correctness-preserving repeated end-to-end compilation/generated-runtime speedup. A new analysis, cleaner encoding, changed IR, or unmeasured optimization is insufficient.

Known completed/disqualified work includes primitive ObservedBool conflicts for Mul/Add/Sub interval bugs, the structurally rich but payoff-free nested type checker, the no-speedup LocalCell example, the tested CSR/matrix NoAlias domain, and the E1-only branch-hoisting regression.

First challenge and refine these known leads:

- scoped fixed-shift equality/disequality propagation into false-Eq/If elimination;
- same-mask Bitand reverse disequality followed by fixed-shift propagation;
- fixed-split tuple cancellation beyond projection closure;
- genuinely fresh live-region NoAlias with a blocked hot consumer.

Then search creatively for additional families in the actual EggCC representations and optimizations. For every proposed family provide:

- exact constructor law and why it is sound;
- the equality-sort intermediate fact;
- actual or likely EggCC producer and downstream consumer;
- a concrete valid source-program shape or independently checkable compiler invariant;
- why a one-constructor primitive-conflict rule cannot reproduce the endpoint;
- knockout, mediation-rescue, downstream-consumer, manual-comparator, and negative controls;
- earliest cheap falsifier;
- whether it is likely to expose a baseline bug or a measurable speedup;
- implementation scope, especially whether it requires a major EggCC refactor.

Rank the strongest families. Recommend a finite but broad search strategy that keeps ideating after each family, stops when source-backed leads are exhausted or remaining options require a major refactor, and records failure rather than treating a negative study as success.
