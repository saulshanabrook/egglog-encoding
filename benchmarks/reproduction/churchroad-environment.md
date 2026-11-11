# Churchroad host optimization environment

Native preparation and the first complete optimization canary succeeded on
2026-09-24, on macOS ARM with Racket 9.2 CS. The private Bitwuzla, Rosette/yaml,
Lakeroad, full Yosys, plugin, and instrumented Churchroad driver are built and
checked. No simulator or target-device execution was performed.

The executable preparation recipe is `scripts/reproduction_prepare_churchroad.py`;
`scripts/reproduction_continue_churchroad.py` completed the final driver build
from the retained third attempt with one recorded ownership repair. Every native
step used the single guarded heavy slot, serial jobs and a 10-GiB disk reserve.
The failed attempts remain available. Preparation success is distinct from
source optimization and standalone replay success.

## Measured preparation and first canary

- Attempts 0001 and 0002 exposed a missing Ninja prerequisite and Racket 9.2's
  rejection of a duplicated test-only ellipsis binding. The retained fixes pin
  Ninja 1.13.0 and rename the unused outer binding in Lakeroad's `module+ test`.
- `churchroad-attempt-0003` passed real solver smoke, Lakeroad compile/help,
  full Yosys/plugin/pass gates and dependency locking. Its final Rust build found
  a moved `spec_filepath` in capture instrumentation.
- `churchroad-continuation-0001` snapshots the failed receipt, source, preparer,
  capture patch and prerequisite output hashes, then applies only the borrowed
  argument repair. Incremental driver compilation succeeded in 1.052 seconds
  (observed group peak 339,427,328 bytes), followed by driver/help and native
  library inventory gates. Prior solver/Yosys/plugin/model/lock and failed-receipt
  hashes were verified unchanged. Its explicit per-child cap was 5 GiB.
- Prepared settings are at
  `/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/preparation/churchroad-continuation-0001/settings.json`;
  the adjacent `continuation.json` records commands, guards, logs and hashes.
  Driver SHA-256 is `fde371354d872a064b68e2716b598268d61fe6bb9905956cc27d19d15532e58d`.
- `churchroad-simple_mul` completed through the normal coordinator: native parent
  1.234 seconds; separate ordinary replay 0.069 seconds. The complete-stage
  identity is `a04c3c091bce9a8d3fa83d7986ca7a4ee89e4a86ddae0a0f3b13f875c2d5de01`;
  validation identity is `bd4c22a9478b6c76c9e5f9a6528651f7d4089243d0396c72052b247fb88f3d07`,
  both under `benchmarks/local/reproduction/stages/churchroad-simple_mul`.
  The capture accounts for six original successful engine calls, one actual
  Lakeroad synthesis, both Yosys translations, and the final `out` root. One
  persistent replay combines all five active calls; the sixth contains only
  the explicitly omitted dead module-enumeration declarations.
- Independent read-only checking matched the synthesis output plus the native
  DSP port stub to the second Yosys input, both Yosys outputs to their following
  engine calls, and final Verilog to the terminal completion event. The replay's
  four mapping queries precede synthesis reinsertion at command positions
  93–96; its final selected output query at 157 binds the original `IsPort` row.
  The exact ordered query/state contract was rederived from the replay.
  These are query-only membership/equality checks, not inserted witnesses or an
  optimality proof. Replay SHA-256 is
  `6b74b89a3c4be27171ff3d3c7c49cba986c2d8431c9adf432416f51574b2f7d5`.
- `wide_mul` completed its native parent and retained three successful
  syntheses and one full persistent replay; the original standalone replay
  exhausted its guard. A later complete capture (`ae146d6f…/attempt-0001`)
  finished the source parent in 2.006 seconds. A logging-only replay probe
  localized the slowdown to the original mapping schedule before any check.
  The adapter had renamed input globals `a`/`b` without updating references
  inside later rules, turning those references into unrestricted variables.
  The pinned native engine resolves bare names using globals already declared
  when each command is processed; earlier rule locals and `?a`/`?b` stay local.
  Complete replay now carries that declaration-time scope across source parts.
- The isolated `churchroad-wide-mul-replay-scope-0001/probe-0001` diagnostic
  changed only twelve proven global-reference tokens in that retained replay.
  The same ordinary engine completed all original schedules and fourteen
  unchanged checks in 0.343496 seconds (51,838,976-byte observed group peak),
  under the shared guarded heavy slot. The diagnostic, manifest and mechanical
  diff remain under `benchmarks/local/reproduction/diagnostics/`; prior receipts
  remain unchanged. This establishes the specific scoping repair, not final
  admission. Fresh complete parents and ordinary validation at the integrated
  adapter identity subsequently passed for both circuits: simple_mul replay
  0.227s and wide_mul replay 0.142s. The artifact-rehashed snapshot
  `diagnostics/churchroad-complete-current-20260925.json` retains both results. Strict proof validation has not run for
  either canary; no proof-engine change is part of this repair.

## Required dependency closure

Use the Churchroad pin already used by capture,
`9f82ca23b273a5a500cc6a1ca60b30d3c33c5721`. Its Git tree pins the Lakeroad
submodule to **`7a69047ad20cad54e5c78d68d397b716b42ff462`**. Downloading a
Churchroad archive alone does not populate that gitlink. Fetch Lakeroad explicitly
over HTTPS; recursive SSH submodule checkout also tries to acquire a private
repository which this run does not need.
[Churchroad tree](https://api.github.com/repos/gussmith23/churchroad/git/trees/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721),
[submodule declaration](https://github.com/gussmith23/churchroad/blob/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721/.gitmodules).

| Component | Acquisition identity | Required role |
| --- | --- | --- |
| Churchroad | `9f82ca23b273a5a500cc6a1ca60b30d3c33c5721`, plus retained complete-capture patch | Native Rust optimization driver and `churchroad.so` |
| Yosys | `f8d4d7128cf72456cc03b0738a8651ac5dbe52e1` | Churchroad lowering/reinsertion, Lakeroad Verilog-to-BTOR and JSON-to-Verilog |
| Lakeroad | `7a69047ad20cad54e5c78d68d397b716b42ff462` | Actual host synthesis, not a replay dependency |
| Bitwuzla | `9e5d7d82b0a0bfd3dc838eb3c3936acad500dc97` | The single default solver used by the native call |
| Racket | Host currently has **9.2 CS**; retain executable hash and version. Linux may use its own native Racket >=8.1 with recorded package identity | Racket runtime and bytecode compiler |
| Rosette | Observed prepared pin `373c8c35e4a7667f38fce10cf0b74ae17de07f1d` | Lakeroad's required Rosette and SMT adapter modules; upstream did not pin this package |
| Racket yaml | `b60a1e4a01979ed447799b07e7f8dd5ff17019f0`, repo `esilkensen/yaml` | Architecture descriptions |
| Meson | `1.2.0`, as in Lakeroad requirements | Bitwuzla build; Ninja, C/C++17 compiler, GMP headers and Python also needed |
| Rust | `1.88.0`, as selected by our existing preparation | Build instrumented native driver; preserve resulting Cargo.lock |

The Yosys and solver pins come from
[Churchroad dependencies](https://github.com/gussmith23/churchroad/blob/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721/dependencies.sh)
and [the exact Lakeroad dependencies](https://github.com/gussmith23/lakeroad/blob/7a69047ad20cad54e5c78d68d397b716b42ff462/dependencies.sh).
The recorded Rosette package index resolved to the prepared commit and its package
requires Racket >=8.1; yaml's package index gives its checksum.
[Rosette package](https://pkgs.racket-lang.org/package/rosette),
[Rosette dependencies](https://github.com/emina/rosette/blob/373c8c35e4a7667f38fce10cf0b74ae17de07f1d/info.rkt),
[yaml package](https://pkgs.racket-lang.org/package/yaml).

Lakeroad `bin/main.rkt:81,242–252` selects **Bitwuzla only** by default. Churchroad
passes no `--solver` option. Loading the other Rosette adapter modules does not
require running/installing their binaries. STP, Yices, CVC5, Boolector, Verilator,
LLVM/lit, fmt, Vivado and Lakeroad's Yosys plugin are not in the required direct
driver path. They are present in the upstream all-purpose Dockerfile for broader
testing/use. Preserve Bitwuzla selection and the native 120-second synthesis
timeout; installing a solver portfolio or changing the solver is a separate
recorded configuration.
[Lakeroad CLI](https://github.com/gussmith23/lakeroad/blob/7a69047ad20cad54e5c78d68d397b716b42ff462/bin/main.rkt#L81),
[Churchroad host call](https://github.com/gussmith23/churchroad/blob/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721/src/lib.rs).

The public checkout includes the 8,244-line generated DSP48E2 Rosette model.
`main.rkt:381–390` supplies that function to the interpreter. The interpreter
uses the HDL path as an association key, not as a request to load a proprietary
model. Thus the private submodule and proprietary HDL are unnecessary for the
specified synthesis path. They are used by simulation/import workflows which are
outside this goal. Do not regenerate primitive models or invoke `--simulate`.
[Generated model](https://github.com/gussmith23/lakeroad/blob/7a69047ad20cad54e5c78d68d397b716b42ff462/racket/generated/xilinx-ultrascale-plus-dsp48e2.rkt),
[interpreter](https://github.com/gussmith23/lakeroad/blob/7a69047ad20cad54e5c78d68d397b716b42ff462/racket/interpreter.rkt#L72).

## Concrete preparation order

The commands below retain the original source-backed recipe. They are illustrative;
the two recorded preparation modules own the exact commands and compatibility
repairs used above. Use a **new dedicated source/build prefix** supplied by the
coordinator. `CR_ENV`, `CR_SOURCE` and `CR_EVIDENCE` must be absolute paths
without spaces because the pinned native code constructs some shell commands.
`CR_SOURCE` is the instrumented Churchroad checkout, not the live source mirror.
Retain downloaded source hashes, package inventory and every command receipt.

1. Resolve the execution platform first. At initial inspection macOS ARM had
   Racket 9.2 CS, clang, Cargo and Docker, but no Bitwuzla/Yosys on PATH or private
   Rosette/yaml environment. The successful preparation now supplies those
   dependencies through its isolated launcher. No Linux-container package
   inventory was performed here. Native Linux ARM is a valid first attempt: the source
   build recipes contain no required x86 executable. The old x86-only OSS suite
   download in Lakeroad's Dockerfile is commented out. Do not set
   `--platform=linux/amd64` merely because that obsolete block exists.

2. Install ordinary native build prerequisites. On a dedicated Ubuntu 22.04/24.04
   container, the proposed minimal package command is:

   ```sh
   apt-get update
   apt-get install -y --no-install-recommends ca-certificates git curl build-essential \
     bison flex pkg-config libgmp-dev libreadline-dev libffi-dev zlib1g-dev \
     python3 python3-venv ninja-build racket
   python3 -m venv "$CR_ENV/python"
   "$CR_ENV/python/bin/pip" install meson==1.2.0
   export PATH="$CR_ENV/bin:$CR_ENV/python/bin:$PATH"
   ```

   Record the resolved image digest, `uname -m`, OS package versions and Racket
   version. The upstream PPA is not intrinsically required if the distribution's
   Racket meets the version requirement. On macOS, use the existing Racket and
   install native missing Ninja/GMP/Meson/build prerequisites with their versions
   retained; do not mix an x86 Yosys with an ARM plugin.

3. Acquire exact source commits (the archive/SHA machinery already used by the
   adapter can replace these illustrative checkouts). Do not initialize private
   submodules.

   ```sh
   git clone https://github.com/gussmith23/lakeroad.git "$CR_ENV/lakeroad"
   git -C "$CR_ENV/lakeroad" checkout --detach 7a69047ad20cad54e5c78d68d397b716b42ff462
   git clone https://github.com/bitwuzla/bitwuzla.git "$CR_ENV/bitwuzla-src"
   git -C "$CR_ENV/bitwuzla-src" checkout --detach 9e5d7d82b0a0bfd3dc838eb3c3936acad500dc97
   git clone https://github.com/emina/rosette.git "$CR_ENV/rosette"
   git -C "$CR_ENV/rosette" checkout --detach 373c8c35e4a7667f38fce10cf0b74ae17de07f1d
   git clone https://github.com/esilkensen/yaml.git "$CR_ENV/yaml"
   git -C "$CR_ENV/yaml" checkout --detach b60a1e4a01979ed447799b07e7f8dd5ff17019f0
   ```

4. Build Bitwuzla with one build job, using its exact dependency wraps. Its pinned
   CaDiCaL 1.7.4, GMP 6.3.0 and Kissat 3.0.0 archive wraps include hashes; SymFPU
   is pinned to `22d993d880f66b2e470c3928e0e61bdf61419702`. Retain fetched wraps
   and actual selected system-vs-vendored dependencies in the build evidence.

   ```sh
   cd "$CR_ENV/bitwuzla-src"
   python3 configure.py --prefix="$CR_ENV"
   ninja -C build -j1
   ninja -C build install
   bitwuzla --version
   ```

5. Install Racket packages in a dedicated user package directory so host package
   state remains separate, and record transitively resolved package checksums.

   ```sh
   export PLTUSERHOME="$CR_ENV/racket-user"
   raco pkg install --deps search-auto --batch --no-docs --name rosette "$CR_ENV/rosette"
   raco pkg install --deps search-auto --batch --no-docs --name yaml "$CR_ENV/yaml"
   raco pkg show --all --long > "$CR_EVIDENCE/racket-packages.txt"
   export LAKEROAD_DIR="$CR_ENV/lakeroad"
   raco make "$LAKEROAD_DIR/bin/main.rkt"
   racket "$LAKEROAD_DIR/bin/main.rkt" --help
   ```

   Rosette's installer attempts Z3 4.8.8 even though this native run selects
   Bitwuzla. Its current installer has no Linux ARM prebuilt Z3 URL, but handles
   that exception and reports Rosette as installed. Distinguish this warning from
   failed Rosette compilation. If package setup actually needs Z3, provide a
   native system/source-built Z3 and a symlink at `rosette/bin/z3` **before**
   installation; the install hook explicitly honors a custom symlink. Record its
   version; do not switch Lakeroad's solver to Z3.
   [Installer and architecture dispatch](https://github.com/emina/rosette/blob/373c8c35e4a7667f38fce10cf0b74ae17de07f1d/rosette/private/install.rkt).

6. Build a full Yosys command set at Churchroad's pin, then build its plugin with
   that exact installation. `ENABLE_ABC=0` is acceptable for the traced calls;
   **do not use `SMALL=1`** from the earlier prefix capture. Full Lakeroad needs
   `proc`, `flatten`, `clk2fflogic`, `write_btor`, `read_json`, and `write_verilog`
   in addition to Churchroad's original `prep`/plugin commands.

   ```sh
   git clone https://github.com/YosysHQ/yosys.git "$CR_ENV/yosys-src"
   git -C "$CR_ENV/yosys-src" checkout --detach f8d4d7128cf72456cc03b0738a8651ac5dbe52e1
   cd "$CR_ENV/yosys-src"
   make config-gcc
   make -j1 PREFIX="$CR_ENV" ENABLE_ABC=0 ENABLE_TCL=0
   make PREFIX="$CR_ENV" ENABLE_ABC=0 ENABLE_TCL=0 install
   yosys-config --build "$CR_SOURCE/yosys-plugin/churchroad.so" \
     "$CR_SOURCE/yosys-plugin/churchroad.cc"
   ```

   On macOS use `make config-clang` instead. `yosys-config --build` exists at the
   pin and supplies the platform-specific compiler/linker settings; this is the
   portable replacement for the adapter's hardcoded `-undefined dynamic_lookup`.
   The plugin and Yosys must share compiler/ABI/architecture. Do not build the
   separate Lakeroad Yosys plugin: this driver launches Racket directly.
   [Plugin build constraint](https://github.com/gussmith23/churchroad/blob/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721/yosys-plugin/README.md),
   [Yosys build helper](https://github.com/YosysHQ/yosys/blob/f8d4d7128cf72456cc03b0738a8651ac5dbe52e1/misc/yosys-config.in).

7. Build the instrumented Churchroad driver using the existing retained capture
   patch and serde_json/standalone-workspace change. Its compile-time
   `CARGO_MANIFEST_DIR` embeds the plugin location, so keep the source directory
   at that location for the run. Its Egglog importer also requires the same
   runtime environment variable.

   ```sh
   cd "$CR_SOURCE"
   cargo +1.88.0 build -j1 --bin churchroad
   export CARGO_MANIFEST_DIR="$CR_SOURCE"
   export CHURCHROAD_DIR="$CR_SOURCE"
   export LAKEROAD_DIR="$CR_ENV/lakeroad"
   export PATH="$CR_ENV/bin:$CR_ENV/python/bin:$PATH"
   export PLTUSERHOME="$CR_ENV/racket-user"
   ```

## First gates and repair boundaries

Before a case, record executable hashes/versions, plugin hash, Cargo lock, patch,
full Racket package checksums, DSP48E2 model hash and architecture YAML hash. Use
guarded `yosys -m "$CR_SOURCE/yosys-plugin/churchroad.so" -Q -T -p 'help write_churchroad; help write_btor; help clk2fflogic; help read_json; help write_verilog'`
and the Racket compilation/help checks as dependency gates. A version/help gate
alone is not source optimization completion.

Then use the complete adapter with `--checkout "$CR_SOURCE" --binary
"$CR_SOURCE/target/debug/churchroad"`, first case `churchroad-simple_mul` (confirm
the exact selected catalog ID), then `wide_mul`. The native equivalent is
`churchroad --filepath tests/integration_tests/simple_mul.v --top-module-name mul
--architecture xilinx-ultrascale-plus --out-filepath OUTPUT.v`, with no simulate
flag. Admission still requires captured Lakeroad synthesis, every reinsertion,
all output roots, final Verilog and successful ordinary equality checks. Neither
a Lakeroad help check nor a plugin-only prefix can be counted as a completed case.

If the original Bitwuzla pin fails in this environment, upstream Lakeroad now
pins `fc8610fcfad12902d4eae4741ceb386524cf9b10`, a concrete SMT2 let-binding
shadowing fix. Current Lakeroad itself resolves to
`c5c5a9ac4efc250374df7f9a37d59087a6cc7ba1`. First retain the original failure; prefer
the narrow solver update, with a new toolchain identity, before changing the
entire Lakeroad source. Neither alternative was built or validated here.
[Current dependency file](https://github.com/gussmith23/lakeroad/blob/c5c5a9ac4efc250374df7f9a37d59087a6cc7ba1/dependencies.sh),
[solver fix](https://github.com/bitwuzla/bitwuzla/commit/fc8610fcfad12902d4eae4741ceb386524cf9b10).

The originally missing native prerequisites and driver build are now resolved
by the measured preparation above. The remaining required gate is the full
`wide_mul` standalone replay; later extra designs require their own actual source
population and completion evidence. The canary establishes a working native ARM
path without private models or device execution. It does not establish proof
validity, custom-extractor optimality, or completion of any unrun design.

The actual `wide_mul` ordinary replay exhausted its 300-second guard; its
complete native synthesis/translation evidence is retained, but it is not
admitted as a successfully validated standalone workload. The smaller
`simple_mul` source and replay passed.


### Replay phase diagnostic — 2026-09-25

The logging-only30-second rerun in
`benchmarks/local/reproduction/diagnostics/churchroad-wide-mul-phase-0002`
did not reach any output check. It remained in the original repeating
mapping/typing/transform schedule; the last completed mapping iteration alone
spent8.748seconds searching. This disproves the proposed explanation that the
added final structural output query accounts for the observed early stall.
The native source parent had completed in2.006seconds. The difference needs
engine/adaptation investigation; it is not evidence that the source artifact
failed to generate its complete workload. This diagnostic adds no source changes
or performance-cache rows and does not admit the timed-out ordinary replay.
