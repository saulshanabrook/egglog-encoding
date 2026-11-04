# Final read-only EggCC injectivity/disequality payoff audit

You are the independent Claude Fable source-analysis pass in an evidence-first
compiler investigation. Work read-only. Do not edit files, invoke shells,
compile, time programs, access the network, or manufacture a result. Use only
Read, Grep, and Glob. Treat every prior claim as a hypothesis until checked
against the cited retained evidence or the pinned unmodified EggCC source.

The accepted goal requires a genuine pre-existing EggCC compiler bug materially
found through injectivity/disequality, or a reproducible generated-runtime or
end-to-end compilation speedup. A qualifying result must exceed one
constructor-specific comparison of primitive fields that directly emits a
panic, guard, or final fact. The old `ObservedBool(true)=ObservedBool(false)`
Add/Sub/Mul findings are excluded.

Read these first:

- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/facts.md`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/hypotheses.jsonl`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/cycles/05-codex-audit.md`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/cycles/05-stop-boundary-audit.md`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/report.md`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/final-r1/inspection.json`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/actual-binary-inspection-r1.json`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/independent-verification.json`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/report.md`
- `/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/report.md`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/findings/pack32-screen.md`
- `/Users/saul/p/egglog-encoding/goals/eggcc-nontrivial-encoding-payoff/findings/alias-screen.md`
- pinned unmodified EggCC U0 source at `/private/tmp/eggcc-nontrivial-encoding-payoff-u0`

Current results and open dispositions to challenge:

- QR7 is the strongest substantive-consumer result. Exact quotient/remainder
  guards, lossless `K7` representation identities, generic marked cancellation,
  ordinary address congruence, and a bounded `Qr7MustAlias` bridge enable store
  forwarding. The fixed workload's generated program measures Encoding/U0
  `0.55055`, complete-block bootstrap 95% `[0.54710,0.55750]`; the process main
  changes from 91 instructions/two internal backedges to 55/zero. This is
  injectivity-only, does not prove unique logical power, and does not establish
  compiler-time, suite-wide, or general alias-analysis performance.
- Parts32 is the strongest combined result. Marked forward disequality,
  representation equality, and equal-sibling reverse disequality eliminate an
  impossible comparison. Encoding uses 7.5% to 8.6% less elapsed time than U0
  in every one of six separately reported workload/session cells.
- Same-mask is a smaller measured combined-chain replication. Affine, Route,
  and Sort are actual-host mechanism results without measured payoff.
- Q1 QR7 now has a terminal qualifying ledger row. P1 Pack32 and A1 same-region
  `NoAlias` remain open. P1 may be superseded only if the compared laws,
  producers, intermediate chain, and consumer establish that existing completed
  integrations cover its distinct mechanism. A1 has an apparently distinct
  `NoAlias` commute/store-forward consumer and a proposed guarded
  loop-invariant transport; do not call it false or subsumed without source
  evidence.

Produce one collaborator-readable audit with these sections:

1. **Current-result audit.** Verify whether QR7 and Parts32 meet the accepted
   nonprimitive mechanism and measured-payoff gates. Name each generic encoding
   step and actual compiler consumer. Identify any unsupported or overstated
   claim, especially around primitive-only reproduction, pointer reasoning,
   compiler versus generated runtime, LLVM phase ordering, or disequality.
2. **P1 and A1 lifecycle.** For P1, compare its exact law, source producer,
   intermediate equality/disequality chain, and final consumer against Parts32,
   Affine, Route, and Sort, then state whether an evidence-backed terminal
   supersession is justified. For A1, inspect the retained graph and current U0
   memory rules. State whether one bounded actual-host probe remains both sound
   and materially distinct, whether a concrete source fact falsifies it, or
   whether finishing it necessarily crosses the accepted wholesale
   alias/effect/path/loop-memory redesign boundary. Give the exact cheapest
   decisive probe if it remains eligible.
3. **Fresh source-backed hypotheses and stop boundary.** Search U0 for at most
   three additional materially distinct bounded leads. An eligible lead needs
   exact source locations, a total law for actual types, a feasible producer,
   a blocked actual consumer, a dynamic equality-sort intermediate chain,
   novelty beyond completed cases, a primitive-only null, and a cheap
   falsifier. Reject generic brainstorming, primitive metadata checks, facts
   already supplied by projection/congruence, infeasible triggers, endpoints
   already removed by EggCC/LLVM, and wholesale redesigns. It is acceptable and
   preferable to report no new eligible lead. State exactly what remains before
   the finite search can close; do not claim global impossibility.

Use exact paths and line/symbol names where possible. Clearly label retained
facts, source-validated conclusions, and proposals. Keep the audit concise
enough for independent human review.
