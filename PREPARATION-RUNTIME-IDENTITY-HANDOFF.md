# Preparation runtime identity patch

Ready for integration after the active native canary ends. No native programs, builds, source acquisitions, or settings edits were performed. Live root files were not changed.

## Owned files

- `scripts/reproduction_stages.py`
- `scripts/reproduction_preparation.py`
- `tests/test_reproduction_stages.py`
- `tests/test_reproduction_preparation.py`

Fresh root baseline: `.baseline/preparation-runtime-identity/`. Patch: `PREPARATION-RUNTIME-IDENTITY.patch`. The baseline includes the DialEgg preparation branch. Read-only dependency copies used to resolve mirror imports are not integration files.

## Behavior

Stage receipts have an optional `artifact_directories` mapping from absolute logical root path to SHA-256. Directory identities include relative member names, file/directory kind, symlink spelling, referenced file bytes, and empty directories. Only `.git` and `__pycache__` entries are ignored. Directory symlinks are followed; active-ancestor cycles, missing members, and nonregular members reject reuse or block a newly recorded success. File and directory aliases remain logical paths so retargeting is observed. Changed dependencies cause a fresh immutable attempt; earlier receipts are untouched.

Existing receipts without the optional field retain their original file-only contract. Updating the preparation implementation itself changes coordinator preparation identity, so newly run preparations gain the stronger contract. No performance cache is read or edited.

Preparation binds all settings `identity_paths` and the source checkout as files or complete directory trees, in addition to existing explicitly retained principal binaries. Build object/cache roots remain excluded unless a preparer expressly declares them as identity paths. Root separately added HardBoiled `build/include` to its declared identity paths; this patch's generic path handling binds every header/member there.

The integration test exposed and fixes existing self-invalidation: initial coordinator `attempt/stage.json` was being added to preparation artifacts and then overwritten when the stage finished. Only that root receipt is excluded; native child receipts remain retained.

## Principal binary and directory reasoning

- Eggcc: compiler and Tiger are explicit `record.artifacts`; the external LLVM library is now included from `identity_paths`.
- Churchroad: compiler/plugin are explicit artifacts even where disposable build trees are omitted; declared prefix, Racket sources/runtime, package trees, tools and linked libraries are checked as actual bytes/membership rather than only receipt hashes.
- HardBoiled: native library and sidecar are explicit settings file paths; root's declared `build/include` captures header changes. Full object directories are unnecessary for the actual capture contract.
- DialEgg: existing explicit backend artifact and declared runtime/link dependencies remain preserved by the generic mechanism.

## Verification

- `python -m pytest -q tests/test_reproduction_stages.py tests/test_reproduction_preparation.py`: 20 passed.
- Ruff lint and format check: all four owned files passed.
- `mypy --follow-imports=silent` on the four owned files: passed. Default recursive mypy was not used as a clean gate because this isolated mirror retains unrelated older/missing adapter modules; no errors were suppressed inside the changed files.
- Independent read-only review by `prove_extract_design_review`: no concrete blocker found.

Tests cover unchanged reuse, modified/deleted identity-only file, newly added runtime member, changed native binary/header, directory member bytes/removal/empty directory addition, external symlink target bytes, transient metadata exclusion, cycle rejection, immutable prior receipts, and optional-field legacy compatibility. These are mocked preparation fixtures; they establish cache behavior, not successful native reproduction.
