# Native parameter-analysis drivers

The four files under `authors/` are byte-identical copies from the
author-supplied `parameter-analysis` bundle. They run directly on the complete
checked-in [native corpus](../parameter-analysis.in). There is no driver patch,
input adapter, custom result protocol, or timed conversion.

The author-supplied drivers, native corpus, and generated Egglog translation
are distributed under [Apache 2.0](../LICENSE-APACHE), as confirmed by George
Zakhour. See the [Dis-Equality Graphs artifact](https://doi.org/10.5281/zenodo.13938877)
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

The native file is the decompression of the supplied `exprs.in.xz`, whose
SHA-256 is `c0f0628522dfb5e13b641155350ef5ad3d5a981a91da0e07804f680a3d356146`.
The 46,346,326-byte native file has SHA-256
`6e9114194d92079a14272c25c11012ddf21753f655d5d39178fbba96b150dd3d`.

```sh
python benchmarks/disequality/native/generate.py
```

This deterministic conversion writes [parameter-analysis.egg](../parameter-analysis.egg)
from the checked-in native input. Numerals `1` through `5` become constructors
`N1` through `N5`; `f`, `g`, and `h` retain arities one, two, and three.
It mirrors the six fixed constraints and equality-first pair order, then adds
`(check-contradiction)`. It performs no random generation, pair filtering,
seed selection, engine execution, or proof checking.

The supplied corpus and four-method drivers differ from the public Zenodo
archive's older 60,000-expression, two-method parameter analysis. This is an
author-supplied workload comparison, not a reproduction of that older archive's
inputs or the paper's published timings.

## Dependency and source provenance

EE, NEE, and OEE use Egg 0.9.5. DE requires the authors' changes to Egg's e-class
and e-graph implementation; vanilla Egg cannot run its `disunion` calls.
Cargo pins [commit `09d7789`](https://github.com/saulshanabrook/egg/commit/09d7789439b26e131fab7be55a5a3719bbf55216)
on `saulshanabrook/egg`'s `codex/disegg-artifact-0.9.5` branch. It applies the
unchanged [public artifact](https://doi.org/10.5281/zenodo.13938878) patch to
upstream Egg `v0.9.5` (`c590048817a35236ce9910e7c1e0b1fac670822c`). The commit's
three-file diff is byte-identical to that patch; provenance is recorded in the
commit message. No suitable public author revision was found, so this fork
hosts the patch without further changes. No local dependency preparation is
needed.

The integration manifest points directly at the original drivers. Its lockfile
retains the supplied EE lock's transitive versions and adds the pinned DE
package. The supplied DE manifest's absolute `/disegg/` path and stale standalone
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
uv run pytest -q tests/test_parameter_input.py tests/test_parameter_native.py
```

`make parameter-test` separately builds the six release implementations and
checks native positive/negative cases, full-corpus native CSV results, and both
Egglog contradiction checks. These normal-mode checks do not write measurements.
