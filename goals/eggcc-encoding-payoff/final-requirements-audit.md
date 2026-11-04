# Final requirement-by-requirement audit

This is a read-only completion audit of this goal's governing
[`goal.md`](goal.md), [`facts.md`](facts.md), and [`plan.md`](plan.md) against
the retained cycle-06, correctness, measurement, and validation evidence. The
only file written by the audit is this one. It ran no build, test, compiler,
native program, timing campaign, or network command.

## Conclusion

The strict substantive success condition is met. Parts32 is a
correctness-preserving generated-runtime speedup that materially uses both
injectivity and disequality. It has matched U0/B1/Manual/Encoding treatments,
fixed-input causal ablations and rescues, exact outputs, three separately
reported workloads, two prospectively balanced 90-cycle sessions, and an
independent verifier whose speed, identity, output, and placebo gates all pass.
QR7 independently supplies a larger injectivity-only result through an actual
memory consumer. Neither result depends on the excluded primitive-Boolean bug
route.

The goal should **not yet be marked complete from the state read by this
audit**. Four completion tasks remain:

1. reconcile the acceptance map with the fact set that actually governs this
   goal;
2. decide the isolated EggCC host-validation gate without weakening whichever
   accepted fact set is selected;
3. bring `STATUS.md`, `acceptance.md`, and `acceptance.json` up to the completed
   cycle-06/search/validation evidence; and
4. run final independent semantic/novelty/claim, documentation, acceptance,
   and preservation review against the resulting final files.

No additional timing campaign is required. The retained independent timing
verifiers already satisfy the empirical confirmation requirement. A final
measurement review should check the claims in the edited documents against
those retained records; it need not execute native programs or collect new
samples.

## Governing-contract mismatch

This goal explicitly says that its adjacent `facts.md` controls acceptance,
and the approved plan repeats that statement. The plan was created against
local-facts SHA-256
`cabf4e7ec192658a1d7932c901cb380aab1af3a9f9ea8ebc98a14f95d3257092`.
The current `acceptance.json`, however, declares
`goals/eggcc-nontrivial-encoding-payoff/facts.md` as its source. That is a
different, stronger 18-fact contract with SHA-256
`bcccd6016850ca12340079a33cf6e3daa8f6e48bf1f29f0dfe6923f51539c70f`.
Its acceptance IDs do not form a one-to-one machine-readable map of the 14
facts in this goal.

This is a completion blocker, not a cosmetic path typo. The final acceptance
record should either:

- map every local fact explicitly and treat the stronger follow-on facts as
  additional gates; or
- explicitly adopt the stronger contract and include a crosswalk proving that
  every local fact is still covered.

The stronger requirements reflect the user's later steering and should not be
silently discarded merely because the adjacent goal file is older. Conversely,
the plan's requirement for machine-readable evidence for every automated fact
is not met by a map whose declared source is a different file.

## Local accepted-fact audit

| Local fact | Current evidence | Status before final review |
| --- | --- | --- |
| Strict bug-or-speedup success | Parts32's frozen verifier reports both sessions passing, all 18 primary speed comparisons passing, exact outputs, code identities, and placebo validity. Ratios are 0.91398–0.92504 across three workloads and two sessions. QR7 independently reports Encoding/U0 `0.5505494231`, bootstrap 95% `[0.5471011571,0.5575021727]`. | **Proven by the speedup route.** |
| Prefer both encodings; either may qualify | Parts32 requires marked forward disequality plus equal-sibling reverse disequality. Removing the forward annotation or reverse edge restores baseline code. | **Proven; the preferred combined route is available.** |
| Qualifying bug evidence | No compiler bug is claimed as the qualifying result. | **Not applicable**, provided acceptance records the speedup route rather than counting any excluded bug. |
| Exclude old, planted, malformed, tooling, and integration-only findings | The report excludes ObservedBool, earlier Mul/Add/Sub results, retarget failures, Shift typing, and unsuccessful P1/A1 probes. Cycle-06 source validation corrects unsupported novelty and source-census claims. | **Supported**, subject to the final novelty/claim review. |
| Reproducible measured speedup | Parts32 retains frozen design, raw sessions, explicit process-runtime boundary, exact output per row, complete-block bootstrap intervals, separate workloads/sessions, and independent verification. QR7 retains a separate screen and 112-cycle confirmation. | **Proven.** |
| Actual consumer and fair causal/manual comparison | Parts32 has U0/B1/SeedOnly baseline parity, Manual/Encoding winning parity, primitive-only null, six essential knockouts, an exact high-child rescue, and an exact target consumer. QR7 separately isolates its relation, added bridge, and consumer. | **Proven.** |
| Sound laws, types, contexts, paths, effects, and refinement | The Parts32 arithmetic reconstruction, private-graph scope, typed projection transport, Bottom/unknown boundary, equal-sibling reverse law, and exact export are documented and source-reviewed. Cycle-06 validation rejects treating `ContextOf` as a lifetime proof and rejects unsupported exhaustive-census and LLVM-pass claims. | **Substantively supported; final independent semantic/claim review is still required by plan.** |
| Bounded adaptation; no redesign/proof/paper/commit/push | The successful cases use private sidecars and exact bridges. The broader alias/effect/path work is excluded. No proof or paper work is claimed. | **Supported; final preservation/scope audit remains.** |
| Tests, oracle, boundaries, native coverage, explicit unknowns | Parts32 retains registered mechanism tests, interpreter checks, 200 native checks, semantic and context negatives, exact outputs, and explicit unsupported outcomes. QR7 retains six focused mechanism tests, 37 compiler cases, and 177 native outputs. P1 and A1 remain explicit fail-closed negative attempts. | **Supported for the qualifying cases.** The separate full-validation issue below still needs an acceptance decision. |
| Preserve studies, author work, and exact identities | Source archives/manifests, patches, binaries, inputs, commands, configurations, rejected attempts, and timing rows are retained. The final validation rechecks frozen entries and receipt streams. | **Strong evidence exists; a final post-edit preservation audit is still required.** |
| Honest per-workload measurement | Parts32 reports each of six workload/session cells rather than pooling. QR7 reports its neutral zero-trip control without imposing a speed gate. Compiler-time diagnostics are explicitly descriptive and separate from generated-runtime claims; failed process-admission attempts remain excluded and retained. | **Proven.** |
| Hypothesis/falsifier discipline | The append-only ledger now includes terminal QR7, P1, and A1 rows. P1's later 93-row fail-closed actual probe is recorded after its portfolio supersession; A1 records its one allowed revision and terminal admission failure. Fresh Codex and authenticated Fable passes plus independent source validation find no new bounded eligible lead. | **Proven for the bounded search; no global impossibility claim is supported.** |
| Memory-pressure policy | All ten reviewed final-validation receipts record the benchmark memory guard absent. Timing retained errors and finite bounds. The heavy `raytracewithscreen` host test was filtered and no timing workload uses raytracing. | **Proven.** |
| Explanation, reference, and reproduction guide | `report.md`, `reference.md`, and `reproduce.md` now describe the connected successful cases, negative probes, exact rules, consumers, timing boundaries, identities, commands, and limits. | **Draft deliverables are present.** Final documentation/readability/link/claim review must occur after acceptance and status are reconciled. |

Primary authorities for this table are:

- `benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/final-reviewed/inspection.json`
- `benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/timing/independent-verification.json`
- `benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/report.md`
- `benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/final-r1/inspection.json`
- `benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/actual-binary-inspection-r1.json`
- `benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/timing-r1/independent-verification.json`
- `benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r1/final-validation-summary.json`
- `goals/eggcc-nontrivial-encoding-payoff/cycles/06-codex-audit.md`
- `goals/eggcc-nontrivial-encoding-payoff/cycles/06-fable-audit.md`
- `goals/eggcc-nontrivial-encoding-payoff/cycles/06-fable-validation.md`
- `goals/eggcc-nontrivial-encoding-payoff/hypotheses.jsonl`

## Full-validation decision

The final validation evidence is internally clear:

- this repository's required root `make check` exits zero;
- the isolated selected encoding engine's complete `make check` exits zero;
- the isolated EggCC DAG suite passes all 70 tests, including six QR7 tests;
- the isolated EggCC root test command exits one after all 31 unit and 2,420
  file-test bodies pass because 13 snapshots remain unaccepted; and
- isolated EggCC nits exits two at an inherited U0 Clippy diagnostic before
  later nits stages run.

All 13 snapshot bodies match the dependency-retarget controls; no snapshot was
accepted. The Clippy file is byte-identical to U0 and the same diagnostic
reproduces there. This proves that QR7 did not introduce those failures, but it
does not turn either host command green.

Under this goal's local plan, that evidence can satisfy validation: the plan
requires the complete compiler targets to run, explicitly says to retain
failures, and requires fresh U0 attribution rather than an automatic waiver.
The runs and attribution now exist, and no new QR7-specific failure was found.

Under the stronger fact file currently named by `acceptance.json`, the answer
is less clear. Its full-validation fact says implemented candidates have the
repository's required full validation “without accepting unrelated snapshots
or waiving new failures.” Cycle-06 Fable source validation expressly classifies
the isolated host as a failed full-validation gate, not an unconditional pass.
If that stronger fact remains governing, an acceptance reviewer must resolve
this conflict explicitly. Merely changing `validation` from pending to pass
while retaining two nonzero host commands would weaken the accepted fact.

There are two defensible outcomes:

1. treat the successful root and engine checks as the repository-required
   validation, retain the external EggCC host failures as fully attributed
   integration limits, and have an independent reviewer affirm that this is
   consistent with the accepted wording; or
2. keep completion pending until the candidate EggCC host's required full
   checks pass without accepting the unrelated snapshots or waiving the
   inherited/new failures.

This audit does not choose between those interpretations. It identifies the
decision as the only potentially substantive completion gate remaining after
the measured payoff itself.

## Which final independent audits are still required

The plan explicitly requires machine-readable evidence for every automated
fact plus semantic, novelty, and claim review. The current acceptance files
also promise final semantic, measurement, documentation, acceptance, and
preservation audits. These obligations can be covered by a small number of
combined read-only reviews; they do not require one file or one agent per word.

1. **Semantic/novelty/claim review: required.** Review the final report,
   reference, acceptance map, mechanism laws, causal attribution, novelty
   boundary, and host-validation decision. The cycle-06 Codex/Fable reviews
   establish the bounded search stop and correct several overclaims, but they
   predate the final acceptance/status transition and are not a final review of
   the whole deliverable.
2. **Measurement review: required at the claim level; no new measurements are
   required.** Recheck every reported ratio, interval, workload/session count,
   output claim, timing boundary, placebo statement, and exclusion against the
   two independent verification JSON records and frozen designs. The existing
   verifiers provide the independent empirical confirmation.
3. **Documentation review: required.** After all edits, verify Diátaxis roles,
   collaborator readability, relative links, exact before/after rules, the
   connection from encoding to consumer, negative-result separation, and the
   reproduction commands. The older `findings/final-review.md` reviews the
   excluded Add/Sub primitive-observation result and hashes older documents; it
   cannot close this current review.
4. **Acceptance/requirements review: required.** Resolve the fact-source
   mismatch, map every governing fact, require no pending blocker, and verify
   machine-readable status counts and evidence paths against the final files.
5. **Preservation review: required after all writes.** Recheck source and
   evidence identities, append-only ledger history, prior/frozen artifacts,
   snapshot nonacceptance, dirty-author-work preservation, and absence of
   unauthorized commit, push, PR, proof, or paper changes.

The documentation, acceptance, and preservation reviews must happen after the
remaining edits; reviews of an earlier draft cannot authorize later substantive
changes. A final combined reviewer may cover several areas if its evidence and
verdict are explicit.

## Exact remaining checklist

- [x] Qualifying measured speedup with both encodings.
- [x] Fair Manual and U0/B1 comparisons, fixed-input ablations, rescues, and
  primitive-only exclusion.
- [x] Independent timing confirmation and machine-readable verifier output.
- [x] QR7, P1, A1, Codex, and Fable lead dispositions recorded; no new bounded
  eligible lead remains.
- [x] Repository-root and selected-engine checks executed successfully; host
  failures retained and attributed.
- [ ] Resolve which accepted fact source governs and add an explicit crosswalk.
- [ ] Resolve the stronger full-validation interpretation if the stronger
  facts remain governing.
- [ ] Update stale `STATUS.md`, `acceptance.md`, and `acceptance.json`; at audit
  time they still say Fable was unauthenticated, P1/A1 were open, final
  validation was pending, and six acceptance facts were pending.
- [ ] Run final independent semantic/claim, measurement-claim, documentation,
  acceptance, and preservation audits against the final state.
- [ ] Address any binding review finding, rerun only checks made stale by that
  change, and then perform one last requirement-by-requirement completion
  audit before changing the goal status.

If the fact-source and validation decisions are resolved and all final reviews
return pass, the existing evidence is sufficient to mark the goal complete.
If the stronger full-validation fact is interpreted as requiring a green
isolated EggCC host, that non-green host remains a blocker even though the
speedup result itself is valid.
