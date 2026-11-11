# Bitwise source-handle diagnostic

Prepared only: **no native probe has run for this handoff**. This directory is
ignored and contains no production adapter changes. `prepared/` contains the
reviewable source variants, the original replay, identity assertions, and hashes.

## Exactly what changes

The driver pins the original replay, capture receipt, native Tiger graph event,
previous diagnostic intent, and ordinary engine. It regenerates all six original
checks from that graph and source initializer, then resolves all 345 source locals
through unique constructor/child-class lookups in the captured graph.

Six fresh ordinary zero-arity functions retain initializer locals:

| Local | Sort | Purpose |
|---|---|---|
| `__tmp10` | Assumption | Existing lowercase `InFunc "dummy"` context |
| `__tmp98` | Type | Selected erased type |
| `__tmp136` | Type | Selected erased type |
| `__tmp196` | Type | Selected erased type |
| `__tmp250` | Type | Selected erased type |
| `__tmp306` | Expr | Original `loop_subroutine` input |

They use `:merge old`, not constructors, defaults, or `:internal-let`. The six
declarations occur immediately before the original initialization rule; the six
sets are appended after all its original actions. Each assignment copies a bare
existing local value. The initializer body is empty and its ruleset runs once.
No selected target is evaluated or inserted by these assignments.

The other required context already has the global `DUMMYCTX`. The driver verifies
both its original `(InFunc "DUMMY")` definition and its native class identity.
It must not be confused with the lowercase `"dummy"` context above.

Only the third check is replaced. Its 234 facts consist of:

- One input-handle lookup and six erased-field identities.
- All 226 original selected-node facts, byte-for-byte and in order.
- The original input/output root equality, byte-for-byte.

Every selected type/context variable must be covered by those six identities.
The 345 seed-pattern facts and 538 recursively serialized auxiliary closure facts
are replaced with source-backed handles. This is **identity preservation**, not
an assertion that the old and new fact-token multisets are identical. No selected
node, selected edge, type/context requirement, or root equality is discarded.

The driver verifies that removing only the six declarations, six appended sets,
diagnostic `print-size`, and the approved third-check replacement restores every
original command byte-for-byte. All active rules/schedules and the other five
checks remain unchanged. Native class IDs are metadata used for validation; none
is inserted as an Egglog constant.

## Root invocation, with the exclusive heavy-process slot

The output directory must be fresh. This invocation launches the probes; omitting
`--run-probes` only prepares a fresh output directory and launches nothing. A
prepared-only directory is not reused as a later run directory. Assertions are
mandatory: the driver refuses Python optimization mode.

```sh
cd /Users/saul/p/egglog-encoding
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python \
  /Users/saul/p/wt/egglog-encoding/reproduction-eggcc-churchroad/diagnostics/eggcc-bitwise-source-anchors-0001/run.py \
  --root /Users/saul/p/egglog-encoding \
  --output /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/diagnostics/eggcc-bitwise-source-anchors-0001 \
  --run-probes
```

The runner takes the existing exclusive heavy-job lock. It runs these three
processes serially, each with one job, a 60-second timeout, a 5-GiB process-group
RSS cap, mandatory memory supervision, and a 10-GiB disk reserve. Warning-pressure
tolerance is explicit; critical pressure and host-reserve checks remain active.
There are no automatic retries and no later probe after an unsuccessful gate.

1. **Baseline counts:** the unchanged original initialization and entire original
   optimization schedule, followed by `print-size`. It intentionally ends before
   the first check; this is a diagnostic state observation, not source/corpus
   admission or another retry of the known slow query.
2. **Anchored complete replay:** the instrumented source, `print-size` at the same
   boundary, and all six checks. Require successful exit, six completed checks,
   identical counts for every visible original table, and exactly one row in
   each of the six auxiliary tables.
3. **Negative control:** the same anchored replay, changing only the input
   assignment from `__tmp306` to existing `__tmp74` (`main`). Their captured
   classes must be distinct. Every check remains identical to the positive case.
   Require unchanged table counts, a normal check-failure exit, and exactly two
   completed checks before the third fails. A crash or timeout is not a passing
   negative control.

Table counts are a drift check, **not proof of full graph identity**. Auxiliary
tables add observation/rebuild work, so this is not performance evidence for the
unaltered workload. Success still requires separate review and normal complete-
parent validation before any production adaptation or corpus admission. Proof
validation and native extraction cost/legality are outside this diagnostic.

## Receipts and preparation validation

The fresh output retains the exact original and three variants, native graph
event, capture receipt, previous intent, and runner source. `intent.json` records
all hashes, helper/engine identities, 345 resolved source classes, selected-fact
hash, six field mappings, assignments, and limits. Each probe retains its command,
bounded-process receipt, stdout, and stderr. `interpretation.json` reports the
three gates and always sets `admitted: false`. A heavy-job lock refusal starts no
process but leaves the prepared directory intact; use no automatic retry.

Preparation validation: four pure transformation tests pass, covering the pinned
234-fact output, ambiguous source-row rejection, incorrect global-provenance
rejection, and changed selected-fact rejection. Ruff and focused mypy pass.
Independent source review found no blocking soundness or runner issue. None of
these checks called the driver's `main` or launched an engine.

```sh
cd /Users/saul/p/wt/egglog-encoding/reproduction-eggcc-churchroad
PYTHONDONTWRITEBYTECODE=1 .venv/bin/pytest -q -p no:cacheprovider \
  diagnostics/eggcc-bitwise-source-anchors-0001/test_run.py
```
