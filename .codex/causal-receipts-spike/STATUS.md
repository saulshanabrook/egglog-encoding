# Causal Receipts Spike

## Steering frame

- Mission: make one causal treatment faster than full `proofs` on Math, Eggcc,
  Pointer, Hardboiled, and Luminal without proof extraction or workload
  dispatch.
- Current hypothesis: compact exact causes recorded during native execution,
  sliced before elaboration, can avoid whole-trace evidence construction and
  per-firing selector searches.
- Non-goals: benchmark-harness changes, proof extraction, a new proof checker,
  global minimum proofs, or general support for every Egglog semantic feature.
- Starting checkpoint: `d98c112955e2e817c9005e42287011224798679c`.
- First frontier: exact receipt-only capture and backward reachability for small
  relation/constructor/union/check-root canaries representing Eggcc and Math.
- Stop signals: full binding or syntax capture before slicing, recreated search
  or typechecking, benchmark-specific cases, copied merge/container semantics,
  or growth that cannot replace current selector/elaboration machinery.

## Active roster

| Circle | Domain | Aim | Stop condition |
|---|---|---|---|
| receipt implementation | `core-relations` join/commit support | reviewable receipt-only canary and patch | focused tests pass or native hook requires a forbidden shortcut |
| replay seam | existing EGraph/bridge proof execution | decision-complete direct-replay call map | smallest implementation slice is identified |
| measurement | existing `./bench.py` and normal `.reports.jsonl` | quick one-round protocol | exact fresh-row commands are recorded |
| coordinator | integration, review, final gates | preserve scope and accept only measured progress | target flips or evidence establishes a stop condition |

## Experiment ledger

### E1: receipt-only native capture

- Status: rejected at the semantic and complexity gate.
- Smallest repro: reduced positive relation/constructor/union check canaries.
- Confirming prediction: exact retained support is small and capture does not
  elaborate every match into source bindings or syntax witnesses.
- Disconfirming prediction: exact support requires replay-oriented recovery,
  disabling normal native execution, or work proportional to every named
  binding before slicing.
- Acceptance: native visible state is unchanged, the positive check resolves
  to exact support, focused tests pass, and the patch exposes the next replay
  seam without implementing another evaluator.

#### Result

The narrow relation/union canaries passed. For a projected join over
`A(1,10)`, `A(1,11)`, and `B(11)`, the receipt selected only `A(1,11)` and
`B(11)` as support for `Out(1)`. A second no-op run promoted no receipt. A
direct applied union also sliced to its source row, while its redundant rerun
did not promote a union.

That evidence is insufficient for Egglog semantics. Independent adversarial
review found normal operations that change visible state without a usable
receipt:

- constructor/default and conditional inserts have no compact match origin;
- a function merge can apply a union while losing the proposing match;
- replacement and custom-merge outputs omit the prior-row dependency;
- unions from distinct displaced tables are conflated because the receipt has
  no table identity;
- effectless positive checks cannot become slice roots;
- facts from earlier waves are reclassified as source facts;
- rebuild/container effects and panic-safe sink cleanup are absent.

Fixing these failures would require transporting existing mutation, merge,
rebuild, constructor, and check semantics into a second receipt system. That
is exactly the experiment's stop condition. The all-match implementation also
copies complete premise rows and runs the full traced action path while
discarding its application details, so it is not a plausible performance
candidate for Math's roughly 944,000 pending firings.

Validation of the diagnostic worktree before rejection:

- compact receipt canaries: 2 passed;
- all `egglog-core-relations` unit and doc tests: passed;
- focused Clippy, formatting, and `git diff --check`: passed.

The diagnostic production patch is intentionally left uncommitted.

### E2: direct exact-row replay

- Status: canary passed; production integration rejected.
- Hypothesis: an exact native premise receipt can bypass a one-off rule query
  and execute the existing compiled head suffix directly.

An isolated core canary validates every `(AtomId, exact row)` against one
shared prestate, derives compiled bindings without running the join, executes
only the existing head instruction suffix, and merges once. Missing or altered
premises reject the complete batch before any head mutation. The focused test,
all core-relations tests, Clippy, formatting, and `git diff --check` passed.

The seam does not cross into the proof database:

- the compact receipt discarded `AtomId`, while the canary requires it;
- ordinary table, atom, row, equality, and many value identities are local to
  one database;
- proof instrumentation replaces source atoms with proof-view atoms and adds
  proof columns plus action-side proof lookups;
- those residual lookups make the canary fail closed rather than replay an
  incomplete head.

Bridging that gap requires a new source-to-proof occurrence/value mapping and
new schedule or direct-execution plumbing through proof instrumentation. It
would not be a small reuse of the native receipt seam.

The exact-replay canary is therefore diagnostic code and is intentionally left
uncommitted.

### Stop decision

The plan stops before frontend integration and before benchmarking. No public
`causal-proofs` path used the new code, and the receipt path was already known
to be semantically incomplete, so a `./bench.py` comparison would only measure
the unchanged old implementation or invalid behavior. The existing five-file
baseline remains the applicable performance result: causal proofs win on
Pointer and Luminal, regress on Math and Eggcc, and regress sharply on
Hardboiled.

The experiment falsified the proposed compact-receipt/direct-replay route under
the stated complexity constraint. Continuing would mean duplicating existing
Egglog merge/rebuild/proof semantics or adding search and special-case
translation—the explicit signs to stop.
