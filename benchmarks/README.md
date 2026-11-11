# Paper experiment inputs and correctness

| Source | Responsibility |
| --- | --- |
| [`egglog/`](../egglog) and [`egglog-experimental/`](../egglog-experimental) | Integrated engine and encoding implementations, with their Rust tests |
| [`figures/catalog.json`](../figures/catalog.json) | Workload globs, timed treatments, correctness-only `checks`, rounds and timeout |
| [`benchmarking/`](../benchmarking) | Runner, cache, reports, figures and nightly collection |
| [`benchmarking/native_memory.py`](../benchmarking/native_memory.py) | Startup policy shared with independent reproduction tools; Rust enforces the cap |
| [`benchmarks/`](.) | Frozen disequality, published-corpus and slotted inputs, provenance, and shared exclusions |
| [`benchmarking/tests/`](../benchmarking/tests) | Python tooling tests |
| [`benchmarks/paper-tests/tests/paper.rs`](paper-tests/tests/paper.rs) | Actual catalog inputs/schedules, source-visible per-table sizes, stable outputs, exact extracted terms/variant order/costs, strict proof checks and family oracles |
| [`benchmarks/paper-tests/tests/slotted_differential.rs`](paper-tests/tests/slotted_differential.rs) | 122 frozen semantic differential cases, including guards, aliases, substitution, and a pinned known limitation |
| [`slotted-reference/`](../slotted-reference) and [`egg-math-benchmark/`](../egg-math-benchmark) | Native algorithms shared by Rust tests and workload drivers |
| [`benchmark-memory/`](../benchmark-memory) and [`egraph-isomorphism/`](../egraph-isomorphism) | Allocator support and the independent graph-isomorphism library/CLI |
| [`benchmarks/reproduction/`](reproduction) | Explicit historical acquisition and fixture regeneration, outside routine tests/figure collection |
| [`semantics/`](../semantics) and [`paper/`](../paper) | Independent Lean model, differential-test scripts and its formal-semantics writeup |

The paper test target compares ordinary, term-encoded and strict proof-testing
runs of each enabled input. It excludes internal encoding/proof tables from the
size map. Both fixture harnesses share extraction checks for actual returned
terms, costs and exact variant lists. Read-only DAG lookup requires returned and
comparison terms already represented in the requested root e-class, after normal
once-only root/count evaluation. Proof-enabled extraction verifies certificates
for the exact returned terms in order,
including a checked connection to the requested source root. Supplementary
extraction checks use a clone and do not mutate the workload being observed.
One explicit normalization handles equal-cost best-term ties: a different single
best expression is accepted only when its reported cost matches and the alternate
expression is checked equal to the requested root in the ordinary configuration
at that command boundary, or by a checked source proof in strict mode.
Proof checking also proves that equality. The suite reports each accepted tie and its
count; raw outputs and certificate right-hand sides remain exact. Variant order,
variant counts and costs are not normalized. Paper inputs must expose their
extractions at top level so every extraction is intercepted.

Native Math uses the frozen twelve-round witness, its eleven-round negative
boundary, and logical constructor/class counts. Native disequality checks the
prescribed contradiction against the four original drivers. Slotted tests use
matched-policy class/node counts; timing pairs also check their prescribed
targets. Syntactic and snapshot substitution can produce different graphs.
Count equality is a size check and does not establish graph isomorphism.
Matched snapshot comparisons require their encoded count oracle; shared
exclusions must name both members when that oracle is unavailable.
The second-phase BATAX multipattern pair is deferred across profiles after a
fresh local-cap failure; uncapped validation is unestablished. Its nested timing
and matched-count configurations remain separate checks on the full input.
The full parameter-analysis NEE strict-proof configuration exceeds the local
cap even in a fresh process and is explicitly deferred across profiles; it has
not been certified uncapped. The proofs-off figure is unaffected. General NEE
pass composition is checked in the smaller semantic cases, which do not
certify that excluded full workload. Math12 strict modes are excluded only under
the local cap and have separately passed the actual uncapped correctness trial.

The slotted benchmark suite has 23 frozen `.egg`/`.ref` pairs: ten full-rule SDQL
kernel/phase inputs, eleven array parameter counts, and two logic fixtures.
Its 122 small semantic pairs live beside them in `benchmarks/slotted/correctness`.
The `.ref` JSON stores executable native-reference inputs: `multi` for
multi-pattern matching and optional `nested` for nested matching. Each test runs
the native algorithm again and compares it with the corresponding encoding.
The semantic fixtures also keep `probes` and authored `expect` assertions beside
those inputs. Probe partitions group zero-based indices: `[0,1][2] missing[[]]`
means the first two probes are equal and the third is separate. The `missing`
suffix lists any probes absent from the native graph; here that list is empty. The
[`Expect` fields](paper-tests/tests/slotted_differential.rs) document additional
guard, aliasing, count and known-limitation assertions. An empty `expect` still
requires live partition/count agreement. Ordinary command-output and proof
snapshots continue to use Insta in `egglog-experimental/tests/files.rs`, with
shared ordinary/proof extraction parity checks alongside those snapshots; slotted
compiler snapshots use it in `egglog-experimental/tests/slotted_files.rs`.
Routine commands read these bytes. Regeneration is explicit:

```bash
python -m benchmarks.reproduction.slotted.generate --check
python -m benchmarks.reproduction.slotted.generate_differential --check
```

The reusable `egraph-isomorphism` library/CLI retains its independent tests. Paper
correctness does not require an isomorphism search. See the
[slotted source guide](../egglog-experimental/src/slotted/LANGUAGE.md) for the
language and [encoding explanation](../egglog-experimental/src/slotted/ENCODING.md)
for policy details.

The Python suite includes a real CLI integration test on small Math and
disequality fixtures. It uses a temporary report and checks successful runtime/RSS
observations through the same public runner.

The [LMFAO case study](lmfao/README.md) compares slotted and ordinary egglog with
LMFAO, then checks and times the generated C++ programs. Follow its setup guide
before running `./bench.py figures` or the focused `./bench.py figures lmfao`.
Its Python and Rust tests are included in `make check`.

For a disposable three-round verification preview:

```bash
./bench.py figures --rounds 3 --memory-limit \
  --report /tmp/egglog-paper-preview.jsonl --output-dir /tmp/egglog-paper-preview
```

All entrypoints share the timeout and allocator/address-space guards from
`benchmarking/config.py` (500 seconds and 16 GiB). `--timeout-sec N` and
`--memory-limit-gib N` override them; `--no-memory-limit` removes the cap.
The Rust paper parent reads these defaults once; trials remain Rust tests.
Native Math correctness comparisons run in a separate child without the memory
guard, including the off execution used as their count oracle. The Math source
term/proof checks retain the configured cap. Benchmark measurements retain their
selected memory guard for every treatment.
Peak RSS is measured separately. Completed cached observations remain reusable
even after lowering a guard. Timeouts and allocation-limit outcomes retry only
after their corresponding guard increases. Cached reruns collect missing work.

[`benchmarks/ignore.json`](ignore.json) is the shared exclusion policy
for Rust tests, comparisons, and figures. Each entry records a reason and
evidence; optional treatment selectors narrow it. A resource entry
with `memory_limit_bytes` applies only when the selected cap is no larger than
that recorded bound. It never excludes an uncapped run. Entries without a cap
selector apply across profiles. Excluded conditions remain visible in reports and figure
coverage, and are never observations or successful correctness checks. A
cap-specific resource entry does not hide a complete cached set of successes.

Known table-size bugs use `kind: "expected-failure"` with an issue and exact
`expected_table_sizes` pairs in `[ordinary, candidate]` order. Rust still executes
the case and checks every other table, output, extraction and proof. An unexpected
pass or a different failure fails the suite. The affected condition cannot supply
verified figure measurements, even if older successful timing rows are cached.
The current count discrepancy is tracked in
[issue #164](https://github.com/saulshanabrook/egglog-encoding/issues/164).

The normal Rust paper suite uses the local cap. To run that same suite uncapped:

```bash
PAPER_TEST_MEMORY_LIMIT_BYTES=none make check
```

Use `./bench.py figures --no-memory-limit` for uncapped final collection.
The catalog supplies ten observations and baseline-only cohort selection. The
final collection uses a clean environment with allocator and thread overrides
unset; retain its machine/environment description with the data. The
three-round preview is implementation validation and does not replace paper
figures or performance numbers. Outputs are `disequality-runtime`,
`math-runtime`, `corpus-congruence-cdf`, `corpus-proof-recording-cdf`,
`corpus-proofs-cdf`, `slotted-runtime`, and `slotted-multipattern-runtime`,
each in PDF/SVG/PNG form.
