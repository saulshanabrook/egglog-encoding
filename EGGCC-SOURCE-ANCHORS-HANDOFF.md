# Eggcc general source-anchor adaptation

Ready for root review/integration; no native execution in this slice.

## Files and integration

Patch: `EGGCC-SOURCE-ANCHORS.patch` (SHA-256 `42debce7681e9ae1aa870274c98fe88c4ad0152ef72d3ac8f778b3d3d3b5e8a5`).
Only three implementation/test files differ from `.baseline/eggcc-source-anchors`, and each baseline was checked byte-for-byte against current live source at handoff:

- `scripts/eggcc_churchroad_complete.py`
- `scripts/suite_capture_eggcc_churchroad.py`
- `tests/test_suite_capture_eggcc_churchroad.py`

`eggcc_sessions` keeps native `program` intact and separately returns `replay_program` plus `source_anchors`. The adapter writes the original raw file, applies its existing compatibility transform to the augmented replay, and retains anchor/root metadata in its capture receipt. Existing command-position/check contracts bind the resulting exact checks and prefix. Existing direct-CLI validation defaults and coordinator-only validation path are unchanged.

## Soundness boundary

The mapper grounds only constructor applications from original initializer locals (or independently verified original globals), using unique typed constructor rows in the actual native graph. It requires one empty-body initializer rule and its one immediate run. New zero-argument ordinary functions retain existing local values in that original action; no selected value is constructed or unioned. Every Tiger-selected node/edge, erased-field eclass, root equality, and duplicate native root request is preserved. Original selected-fact token sequences are identical.

Unknown source expressions, absent retained constructor rows, and ungrounded derived fields retain the structural query with explicit reasons. Ambiguous native FD identities, conflicting types/arity, and namespace collisions fail closed. Source lifetimes that can include constructor deletion prevent grounding of that constructor and dependent locals. Named and combined reached rulesets are considered; unscheduled rulesets do not execute. Subsumption preserves constructor lookup identity. Scope changes/table reconstruction (including nested push/pop/keep-best) and unknown top-level macros select the unchanged structural path. The gate intentionally does not interpret arbitrary source execution.

## Evidence

103 lightweight tests passed across adapter, validator and coordinator suites. Ruff formatting/check and three-file mypy passed. Independent read-only review found no remaining concrete blocker. These are transformation/protocol tests, not native optimization results.

`EGGCC-SOURCE-ANCHORS-OFFLINE.json` records the retained Bitwise source/event paths and hashes, complete plan and all six roots. Its offline materialization resolves all 345 source locals, uses 15 auxiliary singleton tables plus one verified existing global, and preserves every selected fact. Removing only the auxiliary declarations and assignments restores source bytes exactly.

| Native root | Selected nodes | Query facts | Original-field closure before / after |
|---|---:|---:|---:|
| main | 79 | 84 | 32 / 3 |
| mod2 | 32 | 36 | 11 / 2 |
| loop_subroutine | 226 | 234 | 538 / 6 |
| OR | 29 | 33 | 23 / 2 |
| AND | 29 | 33 | 23 / 2 |
| XOR | 33 | 37 | 23 / 2 |

The earlier six-table diagnostic passed all six checks, original-table counts and wrong-input negative control under root execution. This implementation generalizes to all six roots (15 tables); that earlier result does not substitute for the next native gate.

## Root-owned next gate

After integration, run the existing guarded coordinator with current settings and the one case:

```sh
.venv/bin/python -m scripts.suite_reproduction --case eggcc-bitwise-ops--statewalk --stage all
```

Use the centralized heavy slot and existing guard environment. The changed adapter hash creates a fresh immutable attempt. Require the complete source parent, all optimization/reconstruction sessions, all native root checks and sole coordinator ordinary validation. For the first generalized materialization, also recheck original primary table counts and auxiliary singleton counts plus the wrong-input negative control; the diagnostic alone does not admit a corpus workload. Historical successful attempts remain immutable. No claim is made yet for Orders or Palindrome.
