# Preserve declaration-time Churchroad globals

The native-passed twelve-token probe proves that later bare references to pre-existing Churchroad globals must retain their global meaning after syntax translation. Keep alias state across complete replay parts, apply each binding only after its declaration, preserve earlier rule locals and distinct ?variables, and preserve literal/comment/operator spellings. Fail closed on unsupported binding scopes rather than guessing.

Write set: scripts/suite_capture_eggcc_churchroad.py, tests/test_suite_capture_eggcc_churchroad.py, benchmarks/reproduction/churchroad-environment.md. scripts/eggcc_churchroad_complete.py is baseline-pinned but will remain unchanged unless unavoidable. No MISAAL, guard, source, schedule, selected-check, catalog, cache or proof-engine changes.

Checks: focused declaration-order/part-boundary/global-reference/local-variable/operator/literal regressions; current lightweight adapter tests; Ruff/mypy; offline reconstruction from both retained real complete Churchroad captures, with wide_mul exactly matching the native-passed candidate and all original check tokens/schedule tokens unchanged. Seek independent read-only review when a slot is available.

Stop after a reviewed, hashed patch and handoff. No native jobs, builds, root edits or commits. Root owns fresh native parents and ordinary validation at the final integrated identity.
