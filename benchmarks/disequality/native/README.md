# Native parameter-analysis drivers

The four files under `authors/` are byte-identical copies from the
published [`parameter-analysis` bundle](https://zenodo.org/records/23166731).
They run directly on the complete checked-in [native corpus](../parameter-analysis.in). There is no driver patch,
input adapter, custom result protocol, or timed conversion.
The separate `egg-nee-proofs` driver described below adapts NEE to produce proofs;
it does not replace or modify these author files.

The drivers, native corpus, and generated Egglog translation
are distributed under [Apache 2.0](../LICENSE-APACHE), as confirmed by George
Zakhour. See the [Dis-Equality Graphs artifact](https://zenodo.org/records/23166731)
for attribution and citation. The separately pinned DE dependency retains Egg's
MIT license and the public artifact's explicit MIT grant for Disegg.

## Input and execution

```sh
cargo build --release --locked \
  --manifest-path benchmarks/disequality/native/Cargo.toml \
  --target-dir benchmarks/local/parameter-native/target
benchmarks/local/parameter-native/target/release/egg-ee \
  benchmarks/disequality/parameter-analysis.in 100000 10000
```

The other binaries are `egg-de`, `egg-nee`, and `egg-oee`.
NEE uses `nee-no-saturation/main.rs`; OEE uses `nee-with-saturation/main.rs`.
The manifest also supports `--profile profiling` with debug information.
Cargo resolves the pinned dependencies and the benchmark runner builds these
targets automatically.

The original CLI is `BINARY INPUT.in EQUALITIES DISEQUALITIES`. Each expression
occupies one line; consecutive expressions form a pair. Drivers first add six
numeral constraints, then the requested equality pairs, then disequality pairs.
Their loop `for y in x+1..5` excludes numeral 5: the fixed pairs are `(1,2)`,
`(1,3)`, `(1,4)`, `(2,3)`, `(2,4)`, and `(3,4)`. This behavior is preserved.

At `100000 10000`, drivers assert the first 220,000 of the corpus's 400,000
expressions. They read and split the remaining lines but do not assert them.
The full corpus remains unchanged, including that input-reading work.
The ordinary CSV output reports `Y` or `N`; a consistent result is a normal
process exit in the authors' implementation. Diagnostic runs of all four
unchanged drivers returned `Y` on this corpus. This is separate from Egglog
proof validation.

## Corpus and conversion

The native file is byte-identical to `parameter-analysis/exprs.in` in the
[public artifact](https://zenodo.org/records/23166731).
The 46,346,326-byte native file has SHA-256
`6e9114194d92079a14272c25c11012ddf21753f655d5d39178fbba96b150dd3d`.

```sh
python benchmarks/disequality/native/generate.py
```

This deterministic conversion writes [parameter-analysis.egg](../parameter-analysis.egg)
from the checked-in native input. Numerals `1` through `5` become constructors
`N1` through `N5`; `f`, `g`, and `h` retain arities one, two, and three.
It mirrors the six fixed constraints and equality-first pair order, then adds
`(check (contradiction))`. It performs no random generation, pair filtering,
seed selection, engine execution, or proof checking.

The archive's `parameter-analysis/run.sh` fixes 100,000 equality pairs and sweeps
0 through 10,000 disequality pairs in increments of 500 across all four methods.
The figure replicates its final parameter setting, comparing DE with extlog;
it does not reproduce the full sweep or the paper's published timings.
The current archive's corpus and all four drivers are byte-identical to the
previously supplied files already in this repository.
[The provenance record](provenance.json) gives the exact archive members, hashes,
and verification scope; no input or driver replacement was needed.

## Dependency and source provenance

EE, NEE, and OEE use Egg 0.9.5. DE requires the authors' changes to Egg's e-class
and e-graph implementation; vanilla Egg cannot run its `disunion` calls.
Cargo pins [commit `09d7789`](https://github.com/saulshanabrook/egg/commit/09d7789439b26e131fab7be55a5a3719bbf55216)
on `saulshanabrook/egg`'s `codex/disegg-artifact-0.9.5` branch. It applies the
unchanged [public artifact](https://zenodo.org/records/23166731) patch to
upstream Egg `v0.9.5` (`c590048817a35236ce9910e7c1e0b1fac670822c`). The commit's
three-file diff is byte-identical to that patch; provenance is recorded in the
commit message. The published `setup-container` recipe clones the same upstream
version and applies that patch; the installed container tree was not inspected.
The fork hosts the patch without further changes. No local dependency
preparation is needed.

The integration manifest points directly at the original drivers. Its lockfile
retains the supplied EE lock's transitive versions and adds the pinned DE
package and the optional proof driver's allocator dependencies. The supplied DE
manifest's absolute `/disegg/` path and stale standalone
lock metadata are not used. Builds do not use the root workspace's newer Egg.

| Original driver | SHA-256 |
| --- | --- |
| `de/main.rs` | `cfa787ff01e39bd37f66763d7dd0909b7c02a184a5aeef2ecd2e8fe28bb402b9` |
| `ee/main.rs` | `c5eeb9c43a58489ef24053b539c7e5597517b627ac4939cc7ee57e917bbcd7c2` |
| `nee-no-saturation/main.rs` | `8856152bc715f61743cdb3732a3a354a908c15da3d8f67003817c6a6c59c0549` |
| `nee-with-saturation/main.rs` | `b914e54ebcadb62b7c06c5767a1e257b3541184b78c038bd81a5b16270e68c33` |

Focused tests check source identity, deterministic conversion, assertion order,
and runner integration without executing full-size workloads:

```sh
uv run pytest -q benchmarking/tests/test_parameter_input.py benchmarking/tests/test_parameter_native.py
```

`make check` builds the original author drivers and runs the actual figure
workload through the catalog-driven Rust paper target. It checks the four native
CSV count/contradiction oracles and enabled Egglog modes, including term encoding.
Full-input NEE strict proofs exceeded the local cap in a fresh process and are
explicitly deferred in the shared exclusion file, including uncapped validation.
These correctness runs do not write measurements.
The catalog and shared `benchmarks/ignore.json` make any unsupported or resource
exclusions explicit. For a focused rerun after building the author drivers:

```sh
cargo build --locked --release --manifest-path benchmarks/disequality/native/Cargo.toml --target-dir benchmarks/local/parameter-native/target --bins
cargo test --locked -p paper-tests --test paper -- parameter-analysis.egg --nocapture
```

The same trial retains the native contradiction and consistent canaries from the
former standalone Python gate, using frozen inputs in `../correctness/`.
`egglog-experimental/tests/disequality.rs` exercises relation-based Egglog NEE
with ordinary, term and proof modes. It is the sole Egglog disequality encoding.

## NEE proof-producing reference

[`nee_proofs.rs`](nee_proofs.rs) adds Egg 0.9.5 explanations to the original
non-saturating NEE algorithm. Label this configuration **NEE + Egg explanations**,
not an unchanged proof-producing benchmark from the published artifact.
The driver retains the full input read, the six initial numeral constraints,
the equality-first assertion order, one rebuild, and the `(ne ?a ?a)` query.

The contradiction certificate consists of one asserted disequality `u != v`
and an Egg explanation of `u = v` from the input equality assertions and
congruence. It is an encoding-level certificate; it adds no source-language
lifting or proof pretty-printing. A consistent query still exits normally with
`contradiction=N` and no certificate.

Production mode (`--proof-mode extract`) records explanations and materializes
the certificate's flat equality proof in memory, without verification or
serialization. Checked mode (`--proof-mode check`) additionally checks the
witness's input membership, explanation endpoints, and exact input equality
axioms. Unknown proof reasons are rejected explicitly: Egg's generic
[`check_proof`](https://github.com/egraphs-good/egg/blob/c590048817a35236ce9910e7c1e0b1fac670822c/src/explain.rs#L387)
accepts reasons omitted from its rule table.
Input unions therefore use uniquely named ground `union_instantiations`,
rather than the author's call-site-labeled `union`.
Explanation-length optimization is disabled, as in the Math proof reference.

The proof driver alone opts into the shared controlled allocator; the original
four binaries retain their allocator and default build behavior.
Build it in a separate invocation:

```sh
cargo build --release --locked \
  --manifest-path benchmarks/disequality/native/Cargo.toml \
  --target-dir benchmarks/local/parameter-native/target \
  --features proof-driver --bin egg-nee-proofs
env MIMALLOC_ARENA_RESERVE=0 MIMALLOC_DISALLOW_ARENA_ALLOC=1 \
  MIMALLOC_RESERVE_OS_MEMORY=0 MIMALLOC_RESERVE_HUGE_OS_PAGES=0 \
  benchmarks/local/parameter-native/target/release/egg-nee-proofs \
  benchmarks/disequality/parameter-analysis.in 100000 10000 \
  --memory-limit-bytes 17179869184 --proof-mode check \
  --proof-summary /tmp/egg-nee-proof-summary.json
```

The CSV columns retain the original order, with method `nee-proofs`.
The optional JSON summary uses schema 1 and reports success, executed check
requests, produced certificates and verified certificates; extraction requests
are zero because this workload asks for a contradiction rather than term
extraction. An early input/setup failure does not fabricate a zero-count summary.
Production runs and separate checked runs use the same workload and resource
profile. The full-size reference must be validated under that profile before
its timings support a proof-production comparison.
