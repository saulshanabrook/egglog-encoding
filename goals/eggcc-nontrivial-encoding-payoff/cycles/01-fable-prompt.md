You are a read-only research collaborator auditing an active compiler experiment. Use the supplied current EggCC source and retained evidence, but do not edit files, run builds, or claim facts that you cannot tie to source or an evidence artifact.

Goal: find a genuine pre-existing EggCC bug or a reproducible generated-program or end-to-end compiler speedup that materially uses generic equality-sort injectivity/disequality. A primitive `ObservedBool(true) = ObservedBool(false)` contradiction, a constructor-specific direct check, a correct integration without payoff, an unmeasured code-shape opportunity, or a failed search does not count. Prefer a chain using both equality and disequality across multiple constructors and an existing compiler consumer.

Pinned untouched EggCC source: `/private/tmp/eggcc-nontrivial-encoding-payoff-u0` at `a0bbec127f83249074a46af3fd6f6126c90fe0fb`.

Read these evidence summaries first:

- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/scoped-screen/report.md`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/findings/alias-screen.md`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/findings/tuple-census.md`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/hypotheses.jsonl`

Resolved evidence:

1. Fixed-translation cancellation leaves a redundant EggCC conditional, but LLVM eliminates it; close that exact generated-runtime lead.
2. Dynamic same-mask disequality survives LLVM: `(x&m)!=(y&m)` implies `x!=y`, then injective fixed translation makes `(x+7)!=(y+7)`. The manual branch fold removes a compare/select from native code. It is not measured yet; a hot-loop screen is underway.
3. A stronger alias microcase survives LLVM: the same-mask fact can imply distinct translated indices and distinct cells, allowing existing `mem-simple` NoAlias consumers to remove a hot store/store/load pattern. The one-line manual comparator eliminates the loop, but contextual and loop transport into the exact consumer scope are not yet proved.
4. A six-fixture tuple census found no same-split Concat producer among 250 alternatives. Do not repeat generic Concat injectivity.

Tasks:

1. Independently inspect the current EggCC source for 3-6 genuinely new hypothesis families. Each must state the mathematical law, exact EggCC producer and existing consumer, why it requires generic equality-sort reasoning rather than a primitive or one-constructor rule, likely endpoint payoff, and the cheapest decisive falsifier.
2. Look especially for existing relations or manual rule clusters that generic disequality/injectivity could replace or unlock: pointer/region analyses, contextual branches, loop invariants, tuple projections other than generic Concat, enum/tagged constructors, fixed-width bit operations, and extraction guards. Reject unsound contrapositives and partial/effectful constructors.
3. Challenge the two surviving leads. For same-mask, propose a valid hot workload that keeps the redundant check per iteration and cannot be constant-folded/hoisted by LLVM. For aliasing, trace the exact current EggCC context/loop plumbing and say whether a private side graph could soundly export the needed local `NoAlias`, or whether that requires substantial bespoke redesign.
4. Rank all candidates, including the two survivors, by probability of producing a qualifying measured speedup or genuine bug. State which one you would run next and why.
5. Identify any apparent existing EggCC bug implied by source rules, but distinguish a source suspicion from a reproduced failure.

Use exact file paths and line numbers or rule names for source claims. Be adversarial: close weak leads, flag missing premises, and do not count code-shape differences as speedups. Keep the response under 3,000 words and make it usable as a hypothesis ledger input.
