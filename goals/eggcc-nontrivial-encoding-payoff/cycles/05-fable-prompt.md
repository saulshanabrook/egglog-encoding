# Read-only EggCC injectivity/disequality payoff audit

You are the independent Claude Fable source-analysis pass in an evidence-first compiler investigation. Work read-only. Do not edit files, invoke shells, compile, time programs, or manufacture a result. Use Read, Grep, and Glob to inspect the listed evidence and the pinned EggCC source. Treat every prior claim as a hypothesis until checked against source or retained receipts.

The controlling goal is stronger than demonstrating that an encoding derives a fact. It requires a genuine pre-existing EggCC compiler bug materially found through injectivity/disequality, or a reproducible generated-runtime or end-to-end compilation speedup. A result is ineligible if the same graph and seeds can be replaced by one constructor-specific check that compares primitive fields and directly emits the final panic/guard/fact. The old `ObservedBool(true)=ObservedBool(false)` Add/Sub/Mul findings are excluded. Prefer chains over equality-sort children that combine cancellation, disequality, and an actual consumer.

Read these first:

- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/facts.md`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/hypotheses.jsonl`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/cycles/04-codex-refresh.md`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/report.md`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/report.md`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/affine-integration/report.md`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/route-integration/report.md`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/sort-integration/report.md`
- pinned unmodified EggCC U0 source at `/private/tmp/eggcc-nontrivial-encoding-payoff-u0`

Current dispositions to challenge:

- Same-mask is a qualifying constructed generated-runtime result around a 2% effect, but a specialized contextual law can reproduce it.
- Parts32 is the strongest mechanism candidate: `x!=y`, equal low halves, marked `Parts32`, representation identities, and sibling-guarded reverse disequality derive unequal high halves and eliminate a hot-loop branch. Its frozen two-session timing confirmation has not yet produced samples.
- Affine, tagged Route, and order-tagged sorting all reach actual emitted/native code through cancellation, unmarked Add reverse disequality, and marked odd-multiply forward disequality. They have causal knockouts and Manual parity. They remain supporting because they have no measured endpoint payoff; Affine also has validation/lint defects, while Route/Sort end on the same 13 unaccepted dependency-retarget snapshots.
- The fresh-region alias lead was closed because existing allocation identity is primitive and no bounded dynamic producer plus blocked consumer survived.

Produce one collaborator-readable audit with these sections:

1. **Current-result audit.** State whether Parts32, Same-mask, Affine, Route, and Sort genuinely exceed the simple primitive-conflict exclusion, which generic encoding steps each uses, and any unsupported or overstated claim. Distinguish mechanism evidence from measured payoff.
2. **Fresh source-backed hypotheses.** Search the pinned U0 source for additional bounded leads. For every eligible lead give exact source file and symbol/rule locations, a total sound law for the actual types/semantics, the actual producer and actual blocked consumer, the dynamic equality-sort intermediate chain, why primitive-only comparison cannot reproduce it, novelty versus the five completed candidates, and the cheapest concrete falsifier. Reject a lead immediately if it requires a wholesale alias/effect/path redesign, relies only on primitive metadata, is already derived by ordinary projection/congruence, lacks a feasible producer, or LLVM/current EggCC already removes the endpoint.
3. **Disposition and stop boundary.** Rank at most three survivors. It is acceptable and preferable to report no new eligible source-backed lead. Explicitly list attractive-looking families you reject and why. Say whether the retained evidence now supports closing the bounded source search once Parts32 timing is resolved, or name the exact smallest additional probe still required.

Do not propose generic brainstorming without source citations. Do not count a smaller restatement of Parts32, Route, Sort, Affine, or Same-mask as new. Do not infer performance from instruction count. Keep the answer concise enough to audit, but include the concrete source evidence needed for independent validation.
