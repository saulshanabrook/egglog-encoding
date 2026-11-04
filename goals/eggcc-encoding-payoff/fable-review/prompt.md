You are an independent technical editor. Audit the current file
`goals/eggcc-encoding-payoff/report.md` as a fresh, standalone document. Treat
that file as the sole editorial baseline. Do not consult, compare against, or
mention earlier drafts, chat history, or prior editorial audits.

Read the official Diataxis explanation guidance at
https://diataxis.fr/explanation/. The intended document type is an explanation:
it should help a reader who already understands egglog and e-graphs understand
why the mechanism works, how each inference reaches a real EggCC consumer, and
why the observed generated-code and runtime changes follow. Detailed commands,
artifact inventories, and exact identities belong in the linked reference and
experiment records rather than interrupting the causal explanation.

The report describes ordinary optimization-time inference in EggCC. Use terms
such as derived fact, inference, private sidecar graph, query result, and
representation invariant. Do not introduce terminology that suggests a
separate formal-derivation subsystem or optional compilation mode.

For each main case, check that a new reader can follow this exact chain without
guessing:

1. source program and path facts;
2. case-specific private terms and why the marked constructor is sound;
3. the generic generated rule or disequality search edge;
4. each intermediate equality or disequality;
5. the narrow fact returned to EggCC;
6. the existing or added EggCC consumer;
7. the emitted Bril change;
8. the native-code change;
9. the measured runtime comparison and causal controls.

Distinguish the reusable encoding from the case-specific sidecar and from the
bounded EggCC consumer. Make clear whether QR7 and Parts32 use the same
mechanism, which parts differ, and why Parts32 requires both injectivity and
disequality. Check that the report explains the direction of the read-only
`known-disequal?` query and does not imply that its intermediate propositions
are stored. Check that the compact examples are clear mathematical or schematic
fragments rather than misleading executable egglog.

Fact-check proposed changes against current primary sources when needed:

- `egglog-experimental/src/injectivity.rs`
- `egglog-experimental/src/disequality.rs`
- `goals/eggcc-encoding-payoff/reference.md`
- the QR7 and Parts32 files linked from the current report
- `/private/tmp/eggcc-qr7-candidate-nits-r2`
- `/private/tmp/eggcc-parts32-candidate`

Do not edit any file. Return:

1. a candid verdict on whether the current report stands alone as a Diataxis
   explanation;
2. the remaining specific comprehension gaps, ranked by impact;
3. exact patch-ready replacement prose for each material gap;
4. a short list of factual claims in your proposed prose that need human
   source verification.

Preserve supported numeric claims and explicitly flag any claim you cannot
verify. Prefer a few precise edits over a wholesale rewrite. Do not discuss the
document's revision history.
