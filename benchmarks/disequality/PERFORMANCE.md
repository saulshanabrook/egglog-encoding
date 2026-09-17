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
do not establish a precise speedup. The first baseline briefly overlapped focused
validation work; the memory claim, not a timing speedup, is the result of this
probe. The smaller probe does not establish that
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

Full-size term-only execution also passed under both encodings. Small fixtures
separately exercise every CLI treatment, including standalone proof extraction.

## Timing scope

The requested comparison is NE ordinary execution, NE proof recording, and EE
ordinary execution. EE proof timing is intentionally omitted. A later EE
recording-only timing attempt was stopped on request after about 6m49s, with an
observed lifetime physical-footprint maximum of 17.76 GB at that point. It was
not a timeout, an out-of-memory failure, or a proof-correctness failure. Its
partial duration is not included as a measurement.

The full workload remains in the default `./bench.py` suite, but CI's
`make benchmark-smoke` explicitly selects small Math and disequality fixtures.
No large proof benchmark, extra swap, or longer timeout is added to CI.

The review follow-up re-ran the full ordinary workload successfully: NE 32.835s
and EE 31.905s, with executable SHA-256
`fb45e02d3f32ae6d4255aebbb4c20f1f828131066f65df47ed506fbfe672eee8`.
These are single observations, not evidence of an encoding ranking. Small
fixtures passed all proof treatments; full proof timings were not repeated.

## Pre-review full-size measurements

These measurements precede the review change that checks EE's `true = false`
directly instead of deriving an extra contradiction fact. They are retained
with their original executable hash, not presented as timings of the revised
EE implementation. The review follow-up revalidates the small proof fixtures;
it does not repeat the long proof timing runs.

Measured on 2026-09-17 (America/Los_Angeles), using the environment above and
the validated executable SHA-256 `6059a6fdb61a0374bcae16e89e8834dc2a557fcea0693e4c680f6f2d87da8983`.
Source commit: `7e6b123e1c11df187a0e627e7835f28bea1370a6`; only documentation
and CI smoke selection were dirty. Fixture SHA-256:
`88ea961380031ea7cd46f805888bdba638d3a86cb8da67191938044abdae83f3`.
The measurements ran sequentially in the order shown, without concurrent builds
or tests. Each is one observation, with one engine thread and a 1,800s limit.

| Encoding | Treatment | Wall seconds | Maximum RSS (decimal GB) |
| --- | --- | ---: | ---: |
| NE | Ordinary (`off`) | 32.855 | 5.804 |
| NE | Proof recording (`proofs`) | 621.071 | 6.515 |
| EE | Ordinary (`off`) | 32.413 | 6.775 |

NE recording took 18.9 times ordinary execution in these observations. The two
ordinary timings are close; one round on an interactive machine does not establish
an encoding ranking or confidence interval. Maximum RSS is not total memory
demand under macOS compression; see the larger observed physical footprint above.
Proof extraction and strict checking are validated separately, not included in
the recording-only timing. Initial smoke timings that overlapped validation
are excluded from this table.

Reproduce the requested matrix with:

```sh
./bench.py benchmarks/disequality/parameter-analysis.egg --rounds 1 \
  --treatment proofs --compare-treatment off \
  --disequality-encoding nee --compare-disequality-encoding nee \
  --format markdown
./bench.py benchmarks/disequality/parameter-analysis.egg --rounds 1 \
  --treatment off --compare-treatment off \
  --disequality-encoding ee --compare-disequality-encoding nee \
  --format markdown
```

The default cache reuses matching observations across both commands, including
the shared NE ordinary endpoint. Use `--force-run` to collect fresh observations.
Build, generation, and runner setup are outside the process timing; parsing and compilation of the
complete `.egg` input are inside it. Raw JSONL and process logs are not committed.

### Where the NE proof time goes

The measured phase counters attribute 283.755s to typechecking, 67.738s to
frontend parsing, 128.322s to other frontend work, and 127.907s to action execution.
Parsing includes frontend-generated program processing, not just reading the
input file. The private NE ruleset's assembly/search/apply/execution/merge counters
sum to less than 1ms. This does not include term-encoding equality maintenance
or the earlier work of creating and unioning terms.

The next performance investigation should target per-action typechecking,
proof lowering, and command/history allocation, not optimize the tiny NE
propagation rule first. The verified retention fix removes one avoidable cost;
it does not solve the remaining proof frontend and memory overhead.
