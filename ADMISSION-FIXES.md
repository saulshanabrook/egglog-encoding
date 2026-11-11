# Admission and evidence fixes

Implemented only in this isolated mirror. The live versions of all twelve edited
files still match `.baseline/admission-fixes/` at handoff. `admission-fixes.patch`
contains the complete diff against those baselines. No native optimization,
compilation, containers, or benchmark generation was run.

## Changes

1. Capture admission requires an eligible terminal capture status and an explicit
   complete-materialization marker with expected/materialized session counts.
   Native parent success cannot promote a blocked prefix. Eggcc/Churchroad and
   DialEgg now prepare every session before replay; ordinary failures retain all
   session paths and contracts for a later validation attempt. HardBoiled, MISAAL,
   and SpEQ emit the same accounting marker. Zero-root helper sessions count
   toward parent completeness but remain outside the validation workload list.
2. Query-only native contracts retain every ordered check's exact tokens, command
   index, and hash of all preceding commands. The aggregate check hash is verified.
   HardBoiled/MISAAL additionally require each native selected-root check immediately
   after its corresponding original extraction. Checks are never synthesized from
   current ordinary outputs and no selected term is inserted.
3. Shared validator/helper sources are hashed for every family and validation
   attempt. Changes to the imported parser, matcher, or guarded launcher invalidate
   reused evidence.
4. MISAAL requests are verified before identity/cache lookup. They must name the
   selected `case_id`, `source`, and `configuration` exactly; the selected generator
   source must appear in `source_hashes`. Referenced backend, llvm_as, Python,
   generator, pinned source files and optional `identity_paths` are part of identity.
5. Report/inventory refresh current success identities and all retained capture/
   validation artifact hashes. Stale rows become `pending` with
   `historical_status: success` in both report and index. Immutable stage attempts
   remain unchanged. Reports never launch native or replay jobs.

## Integration interfaces

- `write_report(cases, index, population, settings)` now needs current settings and
  mutates stale index rows; the CLI persists that refreshed index. Corpus publication
  should use this refreshed report/index, and still require a successful validate
  stage independently of a successful capture stage.
- Every complete capture records `materialization = {complete: true,
  expected_sessions: N, materialized_sessions: N}`. `N` includes all fresh/native
  sessions, including setup helpers. For SpEQ, the single persistent session has N=1.
- Retriable ordinary statuses are `ordinary-validation-pending` and
  `ordinary-validation-failed`; safety-stop propagation is unchanged.
- `native_check_contract(source, checks, roots)` receives explicit `(command_index,
  exact_check_text)` pairs at materialization time. The validator verifies retained
  positions rather than searching for a matching query elsewhere.
- Existing receipts without the new markers/contracts remain historical. This is
  intentional invalidation, not a migration or admission of older partial exports.
- DialEgg term/cost/variant comparison is unchanged. The separately diagnosed
  equal-cost tie-selection policy is outside this patch.

## Validation

143 focused tests pass across coordinator, validation, immutable stages and all
affected adapters. Regression coverage includes late materialization failure,
first replay failure after all sessions are prepared, missing/changed/moved/
reordered queries, duplicate checks at separate states, changed imported helper
identities, MISAAL wrong case/source/config or changed referenced binaries/source,
and stale settings or missing replay evidence during report-only refresh.

Ruff format/lint and mypy pass for all twelve changed Python files. An independent
read-only review by the DialEgg/SpEQ agent found no blocker in this five-fix scope.
These tests use protocol doubles/tiny fake tools and do not establish native
reproduction success. Root retains the actual native/runtime validation gates.

## Edited files

- `scripts/dialegg_speq_complete.py`
- `scripts/misaal_reproduction.py`
- `scripts/reproduction_validation.py`
- `scripts/suite_capture_eggcc_churchroad.py`
- `scripts/suite_capture_hardboiled_misaal.py`
- `scripts/suite_reproduction.py`
- `tests/test_dialegg_speq_complete.py`
- `tests/test_misaal_reproduction.py`
- `tests/test_reproduction_validation.py`
- `tests/test_suite_capture_eggcc_churchroad.py`
- `tests/test_suite_capture_hardboiled_misaal.py`
- `tests/test_suite_reproduction.py`
