# Read-only divergent audit after the native opportunity screens

Act as a skeptical compiler researcher. Read only; do not edit files, run builds,
launch workloads, or use network tools. Inspect the exact local sources and evidence
listed below. Distinguish confirmed facts from proposals.

The strict goal is in `goals/eggcc-encoding-payoff/goal.md` and its accepted facts
and plan. Success requires a genuine encoding-found EggCC bug or a reproducible
encoding-backed endpoint speedup. Manual-only opportunities and primitive Boolean
conflict checks do not qualify.

Primary live candidate:

- Candidate source: `/private/tmp/eggcc-same-mask-candidate/dag_in_context/src/scoped_reasoning.rs`
- Host hook: `/private/tmp/eggcc-same-mask-candidate/dag_in_context/src/lib.rs`
- Cold causal matrix: `benchmarks/local/eggcc-nontrivial-encoding-payoff/candidate-same-mask/matrix-results.json`
- Hot attempt-0 receipts are under the same candidate evidence directory.
- Manual pilot: `benchmarks/local/eggcc-nontrivial-encoding-payoff/scoped-screen/hot-same-mask/report.md`

The live law is: on the false branch of
`(x & m) == (y & m)`, ordinary reverse disequality with the common sibling gives
`x != y`; fixed wrapping addition is injective, so `(x+7)!=(y+7)`. The private NEE
graph proves only that target fact and exports the exact local Boolean predicate as
false. Cold Encoding/Manual produce the same native code; Off, SeedOnly,
annotation-off, query-off, and bridge-off retain baseline code. Annotation-off
still proves the child disequality but not the translated target. The hot case
initially produced no query because literal 7 is loop-carried. A new narrow induction
admits a loop slot only from a literal initial projection and exact same-index output
passthrough in both branches; focused negative tests are being added. No hot result or
timing is yet claimed. The prospective confirmation gate is 32 balanced four-arm
cycles and upper-95% paired Encoding/U0 runtime ratio below 0.99.

Other current evidence:

- `goals/eggcc-nontrivial-encoding-payoff/findings/pack32-screen.md`
- `benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-screen/report.md`
- `goals/eggcc-nontrivial-encoding-payoff/findings/alias-screen.md`
- `goals/eggcc-nontrivial-encoding-payoff/findings/tuple-census.md`
- `goals/eggcc-nontrivial-encoding-payoff/findings/fresh-source-hypotheses.md`
- `goals/eggcc-nontrivial-encoding-payoff/hypotheses.jsonl`

Please return one concise Markdown report with:

1. A soundness audit of the private-graph translation, loop-constant induction,
   context boundary, Bottom handling, and export. Name exact source lines or shapes.
2. A causal audit: whether the ablations really establish material use of generic
   disequality plus injectivity rather than a disguised direct rewrite.
3. A measurement audit of the four-arm screen/confirmation gate and any missing
   control that could invalidate an encoding-backed runtime claim.
4. Three to six genuinely distinct, source-backed EggCC hypotheses that remain
   after the retained/closed screens. Each must name an exact producer, consumer,
   mathematical law, cheapest falsifier, and why primitive comparisons or a single
   constructor-specific rule are insufficient. Prefer existing corpus triggers.
5. Challenge each proposed survivor yourself and explicitly reject weak variants.

Do not treat unsupported `Shr`, the known ObservedBool bugs, a manual-only speedup,
or an integration alone as goal success.
