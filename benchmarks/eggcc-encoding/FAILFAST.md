# Exact-key fail-fast extension

This is a separate extension to the original eight-fixture, 16-outcome semantic
checkpoint. The original `.egg` inputs and `semantic/runs.json` are unchanged.
The new extension has seven fixtures, tested with NEE and EE in ordinary mode:
**14/14 expected outcomes pass**.

The original CLI has been copied independently to
`/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/semantic/bin/egglog-experimental-392b6d6b-debug`.
Its SHA-256 remains
`46f898796589e8585ecaf1499a9b9d7ee98d31fc45f64d2061c103795d62ecf2`.
`semantic/bin/manifest.json` records the source and copy. This frozen path is
used by the new receipts, so a later encoding build can replace the original
target binary without invalidating the retained bytes.

## Audited protocol

The tested query schedule is stored verbatim in
[source/exact-local-audited-query-schedule.egg](source/exact-local-audited-query-schedule.egg):

```lisp
(run-schedule
  (saturate
    (saturate exact-addresses injectivity exact-audit)
    peepholes
    interval-analysis
    mem-simple
    (saturate exact-addresses injectivity exact-audit)
    exact-query
    exact-audit))
```

Every `exact-addresses` item performs one propagation step. The direct audit
must occur **inside** its saturation loop. Saturating ordinal propagation first
and checking afterward can keep generating counts when a state has been merged
with its allocation successor. The initial audited closure catches preexisting
faults before source consumers; the second catches invariants exposed by source
normalization before the proposed query consumer. The final audit checks unions
made by that consumer. The manual control substitutes
`exact-manual-pairs`, `exact-manual-consumer` for `exact-query` with otherwise
the same order.

[source/exact-local-audit.egg](source/exact-local-audit.egg) inspects the current
tables directly and rejects:

- One pointer e-class with two known-different address keys:
  `exact-address rejection: pointer has incompatible keys`.
- One state/function pair with unequal ordinal counts:
  `exact-address rejection: state has unequal ordinal counts`.

It does not wait for the older `ConflictingKey` / `ConflictingOrdinal` marker
rules to run on a later propagation step. The key audit uses `:naive` because
its `known-disequal?` read follows constructor witnesses. Scheduled `injectivity`
also rejects a seeded union of incompatible primitive `LocalCell` payloads.

The proposed rule snapshot
[source/exact-local-analysis.egg](source/exact-local-analysis.egg) comes from the
original fixture's declarations/rules. Its manifest records the one additional
root guard: `FunctionHasType` must state the exact sole-`StateT` input type,
matching the approved compiler prototype contract. Setup and consumers otherwise
retain the restricted local-address/state/liveness analysis.

Unsupported nodes have no **direct transfer rule**. This is not an absolute
barrier against all e-class propagation: production load-output-state equality,
for example, can legitimately expose the same supported input prefix after
source rewriting. The original fixture already checks store-forwarded load-state
equality. All ordinals and keys must be audited after such equalities.

## Executable rejection controls

| Fixture | Expected exit | What must happen |
| --- | --- | --- |
| `exact-key-failfast-controls.egg` | 0 | Audited query and manual schedules forward 17 past 99, preserve absence of self-nonalias/conflicts, and reject undeclared or non-state-only input roots. |
| `exact-key-reject-pointer.egg` | 1 | A seeded merge of two fresh pointer results is rejected within four propagation/audit rounds. |
| `exact-key-reject-key.egg` | 1 | A seeded merge of incompatible immutable key payloads causes the `LocalCell` injectivity diagnostic. |
| `exact-key-reject-state-count.egg` | 1 | Terminal states from separate length-one and length-two chains are merged; unequal counts are rejected. These terminal states are not ancestors of each other. |
| `exact-key-reject-cycle.egg` | 1 | A seeded state/allocation-successor equality is rejected within four propagation/audit rounds. |
| `exact-key-reject-cycle-saturate.egg` | 1 | The same cyclic equality is rejected under the actual audited fixed-point schedule, without timing out. |
| `exact-key-cycle-growth-control.egg` | 0 | With audit deliberately omitted for exactly four steps, counts 0,1,2,3 and conflict markers appear; no consumer runs. This bounded diagnostic explains the audit placement. |

Each rejection file installs an unconditional consumer sentinel with a different
panic message. The receipt requires the invariant-specific error and forbids
`consumer reached before invariant rejection`. Thus an arbitrary error, timeout,
or accidentally running the consumer is not a passing rejection.

For every fixture and encoding, the command was the frozen CLI followed by
`--disequality-encoding nee|ee FIXTURE`, run from this directory with a
three-second subprocess timeout. Exact commands, hashes, expected statuses and
diagnostics, and stdout/stderr are in
`benchmarks/local/eggcc-encoding-case-study/semantic/failfast/runs.json` under the
primary checkout. All ten expected rejections completed without timeout; the
largest observed one-shot diagnostic wall time was about 0.031 seconds. These
times establish prompt rejection in this probe, not a performance result.

All faults here are deliberately seeded controls. They establish executable
rejection and scheduling behavior; they do not identify a baseline compiler bug
or validate the full compiler prototype.
