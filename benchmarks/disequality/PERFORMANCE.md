# Disequality performance and validation

These are diagnostic local measurements, not a reproduction of the paper's
native timings. The native artifact is not built or timed. Generation and seed
selection are outside the benchmark boundary; execution includes parsing and
compilation.

## Avoidable command retention

The first full-size strict-proof attempt reached a 50.3 GB physical footprint
while still processing input and was stopped on this 16 GiB machine. It did
not finish, so it provides neither a runtime nor proof-validation result.

`process_program_internal(run_commands=true)` retained both the pre-proof and
instrumented resolved command trees in return fields that `run_program`
discarded. Execution now retains only the history required by the proof
checker; resolve-only callers still receive both representations. This does
not alter command execution, proof numbering, union-find, or desugaring output.

The isolated change was measured in before/after/after/before order on seed
2026 with 10,000 equalities and 1,000 random disequalities, plus ten numeral
disequalities. This probe deliberately omits the final check to isolate
ingestion under `--proofs`; it is not the full benchmark or a proof-extraction
measurement. Both binaries exited successfully in all four runs.

| Order | Version | Wall seconds | Peak physical footprint (decimal GB) |
| --- | --- | ---: | ---: |
| 1 | Before | 74.96 | 10.861 |
| 2 | After | 58.94 | 2.908 |
| 3 | After | 59.96 | 2.908 |
| 4 | Before | 61.81 | 10.864 |

Memory fell approximately 73% in both orders. Runtime changed substantially
between baseline runs; two observations per endpoint on an interactive machine
do not establish a precise speedup. The smaller probe does not establish that
the full-size workload fits in memory.

The experiment used macOS 26.6 (25G72), Apple M4, 16 GiB RAM, CPython 3.13.11,
release builds, and `/usr/bin/time -l`. The exact measured binaries at the
memory-fix boundary (before the subsequent block-inference fix) were:

- Before SHA-256: `fd82d3bc7a5f90fcc09c7f3083fb5f378cff7d9b354cfc15f7703d391de91602`.
- After SHA-256: `f9da5604afe1f04b3eed3c1fc14deeddff80ad9fba66f7a57b0afd36cacf42de`.
- Probe source SHA-256: `ccbce02846fd662db66ed3bd73d357f9b93d4e3d5bffb6a6f5ffd500e5e59c7e`.
- Invocation: `/usr/bin/time -l BINARY --mode no-messages --proofs INPUT.egg`.

Recreate the probe from the hash-verified generator using `expressions(generator,
2026, 22000)`, followed by `source_program(terms, 2026, 10000, 1000)` with only its
final `(check-contradiction)` line removed. Use CPython 3.13.11 to preserve the
recorded source header and hash. Raw process output and diagnostic samples are
kept under `/tmp`, not committed.

## Full-size validation

On 2026-09-16 (America/Los_Angeles), both encodings completed normal execution
and strict proof extraction/checking on the full seed-2026 fixture. The validated
release executable SHA-256 was
`6059a6fdb61a0374bcae16e89e8834dc2a557fcea0693e4c680f6f2d87da8983`.
Seed 2025 was consistent in both normal modes; 2026 was the first contradictory
candidate. Regeneration independently reproduced the complete file hash and
100,000 equality/10,010 disequality counts. No pair was injected or filtered.

The validation command was:

```sh
uv run --locked python benchmarks/disequality/generate.py --seed 2026 --max-attempts 1 --timeout 1800
```

Strict validation was not a controlled timing experiment. The NE run was
observed at 22.3 GB peak physical footprint while still ingesting input; this
is a lower bound, not its final peak. macOS compression makes maximum RSS
different from physical footprint, so RSS alone understates memory demand.

Single-round benchmark measurements: pending.
