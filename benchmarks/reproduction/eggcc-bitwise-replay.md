# Eggcc Bitwise Operations replay query

The generalized source-handle adaptation now passes the **complete native
Bitwise optimizer and all six ordinary replay sessions**. The current capture
is `complete/f6fa81b0f48cd1f778d23e9b5bad5d2736254652b8a607438ac40b01158fb757/attempt-0001`
and validation is
`validate/766ce4ae41b3d887d9a73ca4f7c5462089ca7778893fa8bcb4eeb0e2a9a408cf/attempt-0001`,
both under `benchmarks/local/reproduction/stages/eggcc-bitwise-ops--statewalk/`.
The native run took15.52 seconds. These are reproduction diagnostics, not
performance observations.

The adapter retains existing initializer values in fresh zero-argument ordinary
functions. It grounds those values through unique typed constructor rows in the
actual native graph. Result checks refer to the retained input/context/type
values while preserving every selected constructor, edge and root equality.
The previously expensive third check becomes234 facts, including all226 selected
facts. No selected result is inserted or assumed.

The original raw export remains unchanged. The augmented replay and source
mapping are recorded separately. Unsupported source shapes or ungrounded values
retain explicit structural fallbacks; conflicting identities fail. A reached
constructor deletion prevents grounding across that table's lifetime. The
adaptation adds observation tables, so it does not claim execution-cost equality
with the original source file.

The earlier six-table diagnostic passed unchanged-primary-table counts and a
wrong-existing-input negative control. The generalized15-table version also passed these gates under the guard:
primary table counts match before checks, after two checks and after all six;
each observation table remains a singleton. Replacing only the loop input
handle with the existing `main` value fails precisely the third check, after
the first two succeed. Evidence is retained in
`benchmarks/local/reproduction/diagnostics/eggcc-general-anchors-0001/probes-0001/`.
These counts detect drift; they are not a proof of full graph identity.

## Historical structural-query limitation

The complete original Statewalk optimizer succeeds in16.09 seconds, including
all three optimization/reconstruction passes. The ordinary replay of pass1
(loop inversion) timed out at300 seconds, peak838MiB. No incomplete workload
from this parent is admitted.

A60-second diagnostic used exactly the same replay and engine bytes, adding
only `RUST_LOG=egglog=info`. It records completion of every original schedule
and the first two generated result checks. The third check, for
`loop_subroutine`, does not complete. Thus the observed timeout occurs in the
added native-result witness, not the original optimization schedule.

The witness has1,110 facts:345 seed facts,538 original-node closure facts,226
selected-node facts and one root equality. Preserved loop-inversion context
includes a208-node cyclic component. This is a concrete validation-cost issue;
it does not establish a source artifact failure or an incorrect native result.
Dropping context/type constraints or inserting target expressions would weaken
the validation and is not an accepted repair. A subsequent 60-second diagnostic moved the existing fresh-context constraint
and root equality to the front of this check. It asserted an identical multiset
of all 1,110 facts and unchanged bytes for every other command. It also timed
out after only the first two checks. This ordering did not resolve the cost;
no query-order change is applied to the corpus adapter.

Evidence: `benchmarks/local/reproduction/diagnostics/eggcc-bitwise-stage-boundary-0001/`
contains the exact command, engine/file hashes, logs, guard result and
interpretation. The original full capture is
`benchmarks/local/reproduction/stages/eggcc-bitwise-ops--statewalk/complete/bf40de2ca9fd20e09f23100c85921ecfde2971e9afba91328ad0a67f8d1d1507/attempt-0001/capture-result.json`.
These are acquisition diagnostics, not performance measurements.

The equivalent-order probe and preservation assertions are retained in
`benchmarks/local/reproduction/diagnostics/eggcc-bitwise-query-order-0001/`.
Both diagnostics leave the parent excluded; they do not weaken the check.

## Orders follow-up: existing-row lookup diagnostic

The source-anchored Orders parent completed, but its third optimization replay stalled on the first added 279-fact result check. A separate immutable diagnostic at `benchmarks/local/reproduction/diagnostics/eggcc-orders-dag-lookups-0001/probes-0001` breaks the exact selected DAG into bottom-up existing-row lookups, writing only fresh auxiliary observation tables. All six actual output checks passed in 0.209 seconds. A wrong existing input and a wrong selected edge each failed at the third check after two successes. Original and source-anchor table counts remained unchanged; all 738 observation keys were present in the positive and wrong-input runs, and exactly one was absent for the wrong-edge control. These are ordinary diagnostic gates only: generalized exporter integration, complete replay validation, and proof compatibility remain separate. The original timeout evidence is retained.


## Integrated DAG lookup gate — 2026-09-25

The reviewed adapter now preserves every selected typed edge and literal through
exact existing-constructor lookups, retaining source handles and selected-DAG
sharing. The original rules and schedules remain intact. New observer functions
copy only matched existing values; they cannot add a selected constructor or union.

Fresh complete Orders, Palindrome, and Bitwise source runs and all18 ordinary
sessions pass. The native parents took6.14s,10.53s,15.23s; the slowest replay
session per parent took0.212s,0.209s,0.352s. The immutable source/validation
snapshot is `benchmarks/local/reproduction/diagnostics/eggcc-integrated-three-current-20260925.json`.
These are diagnostic durations, not observations in the performance cache.

`eggcc-integrated-dag-gate-0001` verifies that the integrated producer reproduces
the previously reviewed Orders controls exactly, ignoring only diagnostic
`print-size` commands. It then runs all four variants under the memory guard:
correct outputs pass all six checks; a wrong existing input and a wrong selected
edge each fail specifically at check three. Primary and source-anchor table counts
do not change. The correct variant covers all738 observer keys; the absent-edge
control has exactly one missing key. Counts detect changes but do not establish
full graph identity. Prior diagnostic packages remain unchanged.

These gates validate ordinary replay fidelity only. The observational `:no-merge`
functions are not yet supported by proof encoding, so this does not establish
proof-mode benchmark admission. Full-family reproduction remains in progress.

## Finite literal and derived type grounding

The Max-subarray and Cholesky logging-only diagnostics in
`benchmarks/local/reproduction/diagnostics/eggcc-failure-phase-0001/` preserve
the original replay and engine hashes. All schedules finished; Max-subarray
stalled on its first appended check, and Cholesky after six successful checks.
The adapter fell back to structural queries because it could not ground a
derived `TupleT`, and in Cholesky because source `0.00001` was printed as
`1e-5` in the native graph.

Typed `f64` source literals now match native literals by exact finite binary64
bits, recording both spellings, the bits and native class. Signed zero stays
distinct; nonfinite or ambiguous values retain explicit structural fallback.
For an erased `TupleT` with a grounded source `TypeList`, a separate rule queries
the existing constructor row after all original schedules and copies only its
result into a strict observer table. It never constructs a missing type. Missing
rows leave the observer empty, so dependent checks fail. Other ungrounded shapes
retain their structural constraints. The emitted rule, handles and hashes are
included in capture metadata.

Fresh complete Max-subarray and Cholesky parents and all twelve ordinary replay
sessions pass. The eleven guarded probes in
`benchmarks/local/reproduction/diagnostics/eggcc-finite-grounding-gates-0001/probes-0001/`
also pass: correct outputs succeed, changing only an input or selected Function
edge fails at the intended check, and original table counts remain unchanged.
Small controls using the exact generated type-observer rule fail when the row is
absent or has the wrong child. These are ordinary replay checks, not proof-mode
validation; table counts detect changes but do not establish graph identity.

## Proof-compatible observer declarations

Generated DAG and derived-type observers now use `:merge old`. Each constant
observer key identifies one fully grounded constructor or alias, so constructor
functional dependencies make the result unique modulo equality. The rules copy
existing values; they never insert a selected constructor or assert its equality.
This change is restricted to generated observers, not arbitrary source functions.

Term/proof instrumentation also preserves the observers' existing
`:internal-include-subsumed` flag. Dropping it hid a selected, subsumed `If` row in
Armstrong's first optimization pass. A standalone regression covers ordinary,
term, proof-recording, and strict-proof modes, including an unflagged rule that
must still exclude the subsumed row.

Both Armstrong inputs reported as `3fe46e…` and `2f31a4…` pass ordinary execution,
proof recording, proof extraction, and strict proof validation after these fixes.
Logs and original binary/input identities are retained in
`benchmarks/local/no-merge-observers-20260930/`. These are diagnostic checks, not
timed cache observations or a claim that every expanded workload passes proofs.

`scripts/eggcc_observer_compat.py` prepares existing replays with only these
declarations changed, under new content hashes. Its immutable receipt links the
original publications and source aliases; the projected catalog selects the new
files without altering historical inputs or `.reports.jsonl`. Changed executable
and workload hashes require fresh timed samples through `make figures-expanded`.
