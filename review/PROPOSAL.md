Narrow source-pinned repair: preserve Eggcc16be006 and experimental08771f9;
backport the exact PR914 initial commit patch into a fresh Git checkout of core
ebba7bb. Patch fixture includes original regression. Override only the three
core packages used directly by experimental; preserve all nine core package
versions and remove only their Git source fields in the derived Eggcc lock.
Run upstream regression under core's original lock, then the Eggcc build under
its derived lock. Publish explicit repair/source/lock/command provenance.

Continuation verifies the successful old preparation, every prepared source and
product, then reuses its pinned original archive and privately clones its Cargo
target with macOS copy-on-write. Fresh Cargo home receives checksum-verified
locked registry archives and matching sparse-index records, plus independent
Git databases. Every write is within fresh output/target paths; old source,
Cargo home, lockfiles, executables and receipts remain unchanged. Core has its
own Git metadata so build.rs cannot report an ancestor repository revision.

Write set: scripts/reproduction_prepare_eggcc.py,
tests/test_reproduction_prepare_eggcc.py,
benchmarks/reproduction/eggcc-preparation.md,
benchmarks/reproduction/fixtures/eggcc-core-row-order.patch.
Checks: mocked guarded command flow, exact source/patch/lock pins, continuation
hash refusal/immutability, private cache behavior, no nested lock, original
regression preservation, Ruff/Mypy. Stop before any Cargo/build/native job.
Root owns regression/build/Cordic and ordinary replay validation.
