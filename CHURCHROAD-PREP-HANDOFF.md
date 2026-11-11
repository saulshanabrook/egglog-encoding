# Runnable Churchroad preparation

New owned files: `scripts/reproduction_prepare_churchroad.py` and
`tests/test_reproduction_prepare_churchroad.py`. Existing capture, coordinator and
other-family files were not modified in this slice.

The module implements the pinned recipe in `CHURCHROAD-ENV.md`: Churchroad,
Lakeroad, full Yosys, Bitwuzla, Rosette and yaml each use an exact Git revision;
Rust 1.88.0 and Meson 1.2.0 are isolated. It retains source-file manifests,
the downloaded Meson wheel, command receipts/logs, the native capture patch,
Cargo.lock, Racket package inventory and package-file hashes, and Meson's resolved
dependency metadata. Racket's existing installation paths and linked native
libraries also enter runtime identity. No private submodules or target-device
execution are requested.

Each subprocess uses the shared native guard, a 10-GiB free-disk reserve, the
authorized warning-pressure policy, and serial build flags. The CLI holds the
coordinator's exclusive heavy-job lock; the in-process function deliberately does
not take another lock, so it can run inside a coordinator prepare stage. Source
and environment files stay below a fresh `benchmarks/local/reproduction` directory;
`--build-root` can select a separate fresh disposable directory.

The recipe builds full Yosys with ABC/Tcl disabled and uses its installed
`yosys-config --build` for the Churchroad plugin on Linux or macOS. It checks the
required synthesis passes, compiles/loads real Lakeroad, sends an actual tiny
bitvector query through Rosette/Bitwuzla, and builds the instrumented Rust driver
with the retained lock. Only after those gates does it publish `settings.json`.
Preparation success is not benchmark success.

A generated `churchroad-capture` launcher sets its own PATH, LAKEROAD_DIR,
PLTUSERHOME and compile-time-source location. This overrides the legacy capture
adapter's optional prefix-only Yosys PATH and preserves the real native binary's
arguments. The native binary/plugin, runtime source/package directories, package
inventories and linked libraries are all named by emitted `identity_paths`.

## First guarded command after root grants the heavy slot

From the live root after copying the two new files:

```sh
uv run --locked python -m scripts.reproduction_prepare_churchroad \
  --output benchmarks/local/reproduction/preparation/churchroad-attempt-0001 \
  --egglog target/release/egglog-experimental \
  --timeout-sec 1200
```

Do not wrap that CLI in another process-group guard; its individual commands own
the guard. Its lock prevents concurrent coordinator heavy work. A failed step
retains its receipt and stops before starting another command. Use a new attempt
directory for a deliberate retry; existing source/evidence is never overwritten.

The script requires installed native build tools, Racket >=8.1, GMP/readline/ffi/
zlib headers and Python with venv support. Missing executable prerequisites are
reported before acquisition. It records build-tool versions and checks GMP via
pkg-config. Install system prerequisites through the already approved host or
container preparation path; this script does not modify the system package DB.
No assumption of an x86 host is made. On macOS a modern Homebrew bison/flex path
may be needed; actual build failures remain evidence rather than silently changing
source pins. Rosette's optional Z3 setup uses an existing native Z3 if available;
Lakeroad's selected solver remains Bitwuzla.

After preparation succeeds, merge or supply the emitted family settings, then:

```sh
uv run --locked python -m scripts.suite_reproduction \
  --settings benchmarks/local/reproduction/preparation/churchroad-attempt-0001/settings.json \
  --family churchroad --case churchroad-simple_mul --stage all
```

`churchroad-wide_mul` is the next required parent. Both still need native host
synthesis, reinsertion, all final roots/Verilog, complete materialization and
ordinary standalone query checks. No native build or canary ran in this slice.

## Validation and source checks

11 focused tests pass on a simulated Linux and macOS command protocol. They check
pins, full portable builds, package/source isolation, all guard options, source
revision/model/solver-configuration/pass failures, safety-stop propagation,
immutable destinations, and withholding settings until all dependency gates pass.
Ruff and mypy pass both new files; public CLI help renders. Tests mock all native
commands and make no claim of compiler/solver compatibility.

The command/API details were rechecked against primary source:

- [Pinned Churchroad dependencies](https://github.com/gussmith23/churchroad/blob/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721/Cargo.toml)
- [Bitwuzla configure script](https://github.com/bitwuzla/bitwuzla/blob/9e5d7d82b0a0bfd3dc838eb3c3936acad500dc97/configure.py): its ignored Meson exit status requires checking `build.ninja` explicitly.
- [Rosette Bitwuzla adapter](https://github.com/emina/rosette/blob/373c8c35e4a7667f38fce10cf0b74ae17de07f1d/rosette/solver/smt/bitwuzla.rkt)
- [Racket parallel compilation](https://docs.racket-lang.org/raco/Running_raco_make.html), [setup](https://docs.racket-lang.org/raco/running.html), and [runtime directory discovery](https://docs.racket-lang.org/raco/dirs.html)
