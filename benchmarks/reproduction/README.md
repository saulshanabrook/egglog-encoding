# Source adaptations

The canonical source inventory is [../sources.json](../sources.json).
Run `make reproduce-benchmarks` from the repository root to acquire prerequisites,
capture complete Egglog work, and produce the manifest consumed by `bench.py`.
See [../README.md](../README.md) for workload boundaries and collection.

The fixtures here are source repairs and ABI oracles used by the preparation
recipes. They are not measured programs or substitutes for running the authors’
exporters. Generated manifests record the source revision, adaptations, aliases,
and diagnostics for each resulting workload.

Historical acquisition attempts and campaign reports remain at Git ref
`archive/pr96-before-reduction-20261002`; they are not prerequisites for current
preparation. Existing local captures and logs are preserved separately.
