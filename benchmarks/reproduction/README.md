# Recreate the prepared corpus

This directory owns source acquisition, pinned author adaptations, complete-call
capture and explicit validation. Measurement and figure rendering consume the
saved `../corpus/` files independently. The source inventory is `sources.json`;
small ordered patches are in `patches/`, with focused repair oracles in
`fixtures/` and `tests/fixtures/`.

From the repository root:

```sh
uv run --locked python -m benchmarks.reproduction.suite_reproduction
# Limit a preparation attempt to an existing source case:
uv run --locked python -m benchmarks.reproduction.suite_reproduction --family luminal --case luminal-llama
# Strictly check saved inputs with an already built controlled executable:
uv run --locked python -m benchmarks.reproduction.validate_benchmarks --binary target/release/egglog-experimental
uv run --locked pytest -q benchmarks/reproduction/tests
```

Both native commands require the native memory-limit prerequisite. Controlled
ordinary replay and strict validation use its fixed sixteen-GiB policy. Author builds,
Python, Racket and compiler processes are bounded by time/output/process cleanup;
this does not claim to cap their memory. Native exhaustion is a per-workload
outcome; failed limit setup or process control stops the attempt. Retained-root
descendant cleanup additionally requires Python's `waitid`/`WNOWAIT` APIs; an
unsupported interpreter refuses that stage before launching it.

Preparation first reuses exact published `.egg` sources where available. Other
families preserve real author graphs and schedules. Eggcc uses ordinary extraction
of original nullary function roots, which does not establish Tiger effect or
linearity constraints. Churchroad stops at mapping and circuit output extraction.
Stateful backend calls stay grouped; independently completed calls survive a
later parent failure. An incomplete source prefix or reconstruction helper is
not a benchmark workload. Necessary syntax, ABI and extraction adaptations are
recorded in the manifest and apply to every measured condition.

Source checkouts, compiler products, captures and identity-bound receipts remain
under ignored `../local/`. Portable input identities, aliases and unavailable
cases are published in `../corpus/manifest.json`; mutable resume and validation
records live in `../corpus/.local/`. A regeneration implementation change creates
a new identity. Older receipts remain evidence of their original implementation
and are never re-stamped as a new run.

Strict validation is explicit and records outcomes separately from timing. It
can select manifest-relative files before `--binary`; it neither builds an engine
nor modifies prepared input bytes. It uses `--proof-testing`, while ordinary
source validation checks the captured native output contract. Neither command is
an implicit prerequisite of collection or cache-only rendering.

Memory exhaustion and timeouts record safety deferrals and continue independent
inputs; failed resource setup or process control halts validation. Semantic proof
failures veto checked results for the same input, executable and encoding across
timeouts, until a later strict success clears them.

The recipe tests use pinned fixtures and fake tools; running them does not acquire
sources or rebuild author toolchains. The legacy single-fixture materializer and
SPEQ recorder are also located here, independently of the prepared population.

The relocated legacy fixture tools preserve their original generated provenance
headers so `--check` continues to match the merged example files byte for byte.
Use the module paths above for new invocations.

The frozen Math12 paper fixture is additive to the original Math11 source
recipe. Its seven seeds and 24 rules are identical; its terminal equality is a
new distribution instance from the integration-by-parts closure. The complete
fixture hash selects native `--math12`, which fixes both the twelve-round
schedule and that equality. Math11 remains admitted unchanged. The corpus now
has 488 saved inputs: 486 application replays and two standalone Math fixtures.

Math12 graph parity is an explicit correctness check, separate from collection:

```sh
CARGO_BUILD_JOBS=2 make math-parity
```

The ignored Rust test compares Egg and Egglog with proofs off at exactly twelve
rounds. It checks the frozen equality, logical constructor and class counts,
and query non-insertion, dropping the native graph before building the Egglog
graph. The check runner supplies the shared sixteen-GiB native allocation limit
and allocator startup policy, then leaves success and failure reporting to the
normal Rust test runner. This large test remains excluded from ordinary Cargo
runs; benchmark timings come from the regular CLI collection path.
