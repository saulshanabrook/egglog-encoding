# Churchroad declaration-time globals

Independently reviewed by root with no blocker; no native jobs or root source edits.

The complete adapter now retains the alias map between source parts, and rewrites expression references only after the matching top-level binding. This preserves earlier rule locals, ?variables, literal/comment text, operators, rule metadata and schedules. Unsupported binding scopes fail closed. Existing Eggcc DAG code in `scripts/eggcc_churchroad_complete.py` is unchanged.

Write set: `scripts/suite_capture_eggcc_churchroad.py, tests/test_suite_capture_eggcc_churchroad.py, benchmarks/reproduction/churchroad-environment.md`.

Patch: `review/adapter.patch`
SHA-256: `e7e6adfed256b8dfa0cc26aaea65dc2f94cedc5368aabfd39730920ba1e07d6f`
Exact root baselines and result hashes: `review/handoff.json`. All four baseline pins still match root when this handoff was generated.

Validation: 132 lightweight capture, validation and Churchroad preparation tests passed; Ruff and mypy passed. Regression cases cover same-part and cross-part declaration order, later rule global references, ?locals, protected syntax positions, unsupported scopes and contracts over the translated replay.

`review/offline-captures.json` reconstructs both actual retained captures. Each changes exactly twelve a/b tokens in two later rules, preserving all 5/14 checks and 3/5 schedules. wide_mul is byte-identical to the root-native-passed diagnostic candidate (0.343496 seconds, all fourteen checks). Generated replays are retained in review/. No capture receipt was changed.

Root integration: check every baseline, review/apply the three-file patch, run fresh simple_mul and wide_mul source parents plus ordinary validation under final implementation identity. No proof validation or admission is claimed. The historical phase-prefix path and unrelated MISAAL/guard work are untouched. Root independently reviewed the three-file diff and found no blocker. `git apply --check` passed against the live root baseline.
