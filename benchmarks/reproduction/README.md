# Source adaptations

The canonical source inventory is [../sources.json](../sources.json).
Run `make reproduce-benchmarks` from the repository root to acquire prerequisites,
capture complete Egglog work, and produce the manifest consumed by `bench.py`.
See [../README.md](../README.md) for workload boundaries and collection.

The checked-in `patches/` diffs show compiler export hooks and compatibility
repairs against the pinned sources. Preparation checks and applies them in the
order specified by each adapter, retaining their exact bytes and hashes in its
logs. Generated-content transformations, such as syntax modernization and
extraction roots, remain in Python. Fixtures contain focused ABI and repair
oracles; neither patches nor fixtures are measured programs.

Generation preserves the authors' actual Egglog inputs and schedules. It stops
before unrelated code generation or synthesis, except where native intermediate
results are needed to produce a later Egglog pass. Manifests retain source
revisions, adaptations, aliases, and unavailable cases.

Historical acquisition attempts and campaign reports remain at Git ref
`archive/pr96-before-reduction-20261002`; they are not prerequisites for current
preparation. Existing local captures and logs are preserved separately.
