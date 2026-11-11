# Fresh MISAAL family preparation

Implementation-only handoff, 2026-09-25. No native commands ran in this slice.

`scripts/reproduction_preparation.py` now prepares the common pinned44ff
MISAAL environment, followed by original x86, ARM and Hexagon targets in that
order. It calls the existing in-process APIs and never takes a nested heavy-job
lock. Every selected inventory ID is initialized before source preparation.
Each target gets its exact inventory subset, source/configuration identities
are checked, and all target outcomes remain in immutable
`preparation-{x86,arm,hexagon}.json` receipts.

ARM/HVX reuse the actual CMake executable recorded by common Halide preparation,
even if CMake is absent from PATH, and the Boost tree under `seed.preparation`.
The ARM API's own default was corrected to the same stable location; a
relocated x86 plugin no longer changes the inferred Boost path.

After all safe preparation steps finish, ready request JSON files are copied
byte-for-byte into one `attempt/requests` directory. Case/source/configuration
and recorded request SHA must still match. Changed requests become explicit
case blockers. Published settings retain the native backend, Python, LLVM,
libraries and declared request/runtime identities. Original target settings and
request receipts are not rewritten. Partial ordinary compiler/dependency
failures can publish usable settings for the other cases, with exact per-case
configuration blockers and evidence. This status does not claim source
optimization has completed.

A nested guard status or saved guard receipt stops all later target launches
and prevents combined settings publication. The target's successful prefix and
all inventory rows remain evidence. Launch refusals fail closed as a resource
stop. Shared dependency failure reaches no target generator recipe.

ARM also now verifies original full-file source pins before selector generation:
actual frontend semantics, original selector generator, raw metadata dictionary,
metadata reader, intrinsic metadata and original wrapper LLVM. Their SHA-256
values were calculated from `git show <pin>:<path>` only after verifying both
Git repository roots; full revision/blob/SHA evidence is in
`MISAAL-ARM-SOURCE-PINS.json`. All six working files match those immutable blobs.
Actual read-only ARM inspection still finds1152 concrete targets and5026
required wrapper definitions, all present.

`scripts/suite_reproduction.py` includes ARM/HVX preparation and the HVX lowering
helper in preparation implementation identity. It also binds both catalog and
paper-population manifest hashes. Regression tests show each
changed module or manifest invalidates a cached fresh MISAAL preparation while preserving
old receipts; no source captures launch during preparation.

Changed implementation files (all have retained baseline bytes):

- `scripts/reproduction_preparation.py`
- `scripts/reproduction_prepare_misaal_arm.py`
- `scripts/suite_reproduction.py`
- Corresponding `tests/test_reproduction_preparation.py`,
  `tests/test_reproduction_prepare_misaal_arm.py`,
  `tests/test_suite_reproduction.py`

Validation:93 focused mocked orchestration/ARM/coordinator/x86/HVX tests pass;
Ruff and Mypy pass on the six changed source/test files. Tests cover partial
failure, every-target guard stops (including wrapped receipts), all-case shared
failure, no-ready-request failure, changed requests, explicit CMake/Boost reuse,
ARM source pin drift, relocated plugin paths and implementation invalidation.
No native build, source optimization, device execution or performance cache
access occurred. Live shared files were copied into the isolated mirror solely
to match imports during tests; only the six listed files are changes for parent
integration.
