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
ordinary replay and strict validation use its fixed eight-GiB policy. Author builds,
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

The recipe tests use pinned fixtures and fake tools; running them does not acquire
sources or rebuild author toolchains. The legacy single-fixture materializer and
SPEQ recorder are also located here, independently of the prepared population.

The relocated legacy fixture tools preserve their original generated provenance
headers so `--check` continues to match the merged example files byte for byte.
Use the module paths above for new invocations.

The frozen Math12 paper fixture is additive to the original Math11 source
recipe. Its seven seeds and 24 rules are identical; its terminal equality is a
new distribution instance from the integration-by-parts closure. The complete
fixture hash determines native `--iterations`, `--check-left`, and
`--check-right` arguments. Math11 remains admitted unchanged. The corpus now
has 488 saved inputs: 486 application replays and two standalone Math fixtures.

Math12 boundary validation is an explicit diagnostic, separate from collection:

```sh
CARGO_BUILD_JOBS=2 cargo test --locked --release -p egg-math-benchmark --no-run --message-format=json
# Use the test executable path printed in the compiler-artifact JSON:
uv run --locked python -m benchmarks.validate_math \
  --test-binary /path/to/egg_math_benchmark-test --output /tmp/math12-validation
```

Each sequential subprocess installs the eight-GiB native allocation
limit and has a 300-second timeout. Logical constructor and class counts,
terminal-query non-insertion, and the eleven/twelve equality boundary are
checked in both engines with proofs off and fully checked. Failed conditions
remain explicit; the diagnostic continues independent conditions after a cap
or timeout and never retries a capped condition. Twelve-round graphs are
excluded from the normal Cargo test run.
