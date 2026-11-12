# Slotted optimization stack: benchmark evidence

Six cumulative optimization commits on top of merged PR #203, starting at
`155b6812c334bca00f91d8ecc33ac14acf873c86`. Each plot compares its own commit with its immediate
parent and with the fixed native nested Slotted reference.

These are three-sample PR comparison pilots on a shared host: CPU 22, 500-second
timeout, 16 GiB allocator/address-space cap. Native multipattern comparisons are
omitted at the user's request. The encoded multipattern comparisons remain.
No benchmark exclusions were added or modified.

Ratios below 1 mean lower runtime. Suite time is the sum of workload means;
large workloads dominate it. Intervals are independent Fieller 95% intervals.
The pilot does not account for all temporal or shared-host effects.

| Layer | Suite | Child / parent | 95% interval | Interpretation |
|---|---|---:|---|---|
| [1/6] Avoid temporary maps in slotted leader reconciliation | Nested | 0.920× | 0.878–0.963 | 8.0% lower measured suite time |
| [1/6] Avoid temporary maps in slotted leader reconciliation | Multipattern | 0.808× | 0.690–0.971 | 19.2% lower measured suite time |
| [2/6] Reuse slotted substitutions across application phases | Nested | 1.011× | 0.870–1.156 | direction inconclusive in this pilot |
| [2/6] Reuse slotted substitutions across application phases | Multipattern | 0.996× | 0.813–1.182 | direction inconclusive in this pilot |
| [3/6] Reuse the execution graph parser for slotted compilation | Nested | 0.974× | 0.852–1.132 | direction inconclusive in this pilot |
| [3/6] Reuse the execution graph parser for slotted compilation | Multipattern | 1.115× | 0.885–1.420 | direction inconclusive in this pilot |
| [4/6] Store native slotted renamings in compact sorted maps | Nested | 0.970× | 0.865–1.080 | direction inconclusive in this pilot |
| [4/6] Store native slotted renamings in compact sorted maps | Multipattern | 0.803× | 0.697–0.945 | 19.7% lower measured suite time |
| [5/6] Fast-path slotted shapes with identity child groups | Nested | 0.886× | 0.770–1.020 | direction inconclusive in this pilot |
| [5/6] Fast-path slotted shapes with identity child groups | Multipattern | 0.946× | 0.887–1.007 | direction inconclusive in this pilot |
| [6/6] Store slotted variables and binders directly as integer columns | Nested | 1.048× | 0.948–1.169 | direction inconclusive in this pilot |
| [6/6] Store slotted variables and binders directly as integer columns | Multipattern | 0.970× | 0.915–1.031 | direction inconclusive in this pilot |

Validation: Combined optimized Rust at `3db51461` matches the production Rust in the rebased tip. Its `make check` run passed nits, 1,163 Python tests, the ordinary Rust suite (including all 197 slotted proof fixtures), and 511 paper cases. The final MTTKRP-2 group was manually stopped in confirmed native multipattern after over 50 minutes, applying the requested scope; this is explicitly a partial full-suite run. Both encoded treatments and both nested native policies for that same input then passed separately, as did the remaining paper-package tests (including frozen differential pairs) and 25 Vega tests. The exact rebased tip also passed nits, 1,167 Python tests, and 25 Vega tests. No ignore-policy changes were added.

`plots/` contains the six PNG/SVG/PDF images, bound Vega-Lite specifications,
and results with selected observations and exact provenance. PDF fonts were
checked for embedding. `data/report-grouped.json` is the public benchmark
export, including historical observations outside the selected graph scope.
Raw tool-owned JSONL is not included. `reports/` contains public CLI tables.

See [protocol](reproduction/protocol.txt), [source plan](reproduction/pr-plan.json),
and [validation](validation/publication-validation.json). Reproduction scripts
retain the original absolute paths. To rerun elsewhere, create worktrees at
the recorded commits, update paths in a copy of the manifest, and choose a
fresh report path. `collect.py` without `--run` prints the public CLI commands;
those commands can be run directly and build their own executables. The
`--run` campaign wrapper also requires matching prepared-build markers; the
included markers describe the original binaries and must be regenerated for
a new build. The original prebuild script and toolchain versions are included.
To inspect or
share the measured result, the rendered PDFs/PNGs/SVGs and embedded bound
specifications require no source checkout or measurement cache.

The global shape memo experiment was discarded after an inconclusive ablation;
it is not in these six commits. Stage 6 changes physical encoded slot columns,
so saved `--slotted-encoded` programs must be regenerated from source.
