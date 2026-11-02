# Evaluating Churchroad's DSP mapping

`./churchroad-eval.py` measures the normal Churchroad DSP pipeline and a slotted
mapping adapter. It is independent of `bench.py` and never reads or writes its
cache. It does not generate proofs. The earlier bounded module-discovery
prototype remains available through `python3 -m slotted.churchroad`.
The new `./churchroad-eval.py discovery` subcommand separately measures actual
e-graph module enumeration; see [DISCOVERY.md](DISCOVERY.md).

```sh
./churchroad-eval.py --output-dir /tmp/churchroad-eval --samples 3
# Mapping without Lakeroad or hardware validation:
./churchroad-eval.py --output-dir /tmp/churchroad-mapping --mapping-only
```

The output directory must be fresh. The default is the paper's unsigned
16-by-32-bit multiply, truncated to 32 bits. `--case simple-mul` selects the
16-bit example; `--verilog FILE --top MODULE` selects a local combinational
source. The adapter supports inputs, constants, multiply, add, shifts, concat,
extract, and zero extension. Unsupported operators and proposals outside the
output cone fail explicitly. General sequential circuits are outside this scope.

The driver builds two release-mode measurement workers, records binary/source
hashes, rotates treatment order across samples, and saves `report.json`. Raw
phase events, complete graph exports, canonical signatures, runnable requests,
Lakeroad specifications, output RTL, commands, and validation logs remain in each
trial directory. Status and the final table go to stderr. `--no-build` explicitly
reuses workers. Exit status is 0 for successful requested work, 1 for a trial or
parity failure, and 2 for setup errors. Mapping-only success does not validate RTL.

## What is compared

| Treatment | Engine and mapping representation |
| --- | --- |
| `native` | Pinned Churchroad and its original Egglog dependency, original mapping/typing/transform rules and schedule |
| `named` | Current ordinary Egglog; the same native IR, rules, and schedule, with syntax/global-name adaptation |
| `typed-named` | Current ordinary Egglog; widths specialized into patterns, inputs represented by string names |
| `slotted` | Current slotted Egglog; the same specialization, inputs represented by slots and bound output interfaces |

Compare **typed-named with slotted** to isolate the representation change from
width specialization. Native versus named also changes Egglog version. Slotted
versus native alone conflates both changes.

Vanilla Churchroad imports Verilog through Yosys, saturates arithmetic and DSP
proposal rules, extracts a specification for each proposal, invokes Lakeroad,
reimports synthesized RTL, and extracts structural Verilog. Its experimental
module-enumeration rules and custom `debruijnify` primitive are **not scheduled
by this normal pipeline**. Consequently this evaluation does not measure removal
of a running `debruijnify` bottleneck.

For example, the representations of an eight-bit input product are schematically:

```lisp
;; Native: names and widths in Var, width facts in HasType.
(Op2 (Mul) (Var "a" 8) (Var "b" 8))
;; Typed named control: widths are explicit at every expression boundary.
(W 8 (Mul (W 8 (V "a")) (W 8 (V "b"))))
;; Slotted: the body uses slots; the root binds the original input order.
(Root "out"
  (Bind 0 $a (Bind 1 $b
    (W 8 (Mul (W 8 (V $a)) (W 8 (V $b)))))))
```

`Bind` uses the existing slotted binder mechanism; it does not introduce another
substitution implementation. The DSP3 rule uses a multipattern to join an add
with an equivalent zero-extended multiply. Width guards are enumerated over the
source and generated widths because the slotted surface language does not expose
the native payload arithmetic/guard interface. Both specialized treatments run
to graph stability, with a separately timed export comparison between iterations.
Exhausting `--max-iterations` is a failure, not successful saturation.

The pinned native engine resolves bare `a` and `b` in two rules to existing input
globals when those globals exist. Both adapters preserve that behavior. Turning
them into fresh pattern variables would silently change the workload.

Parity compares every output-reachable expression node, its width and operands,
the equality grouping, the port mapping, and every DSP proposal. Slotted edges
are instantiated through their renaming maps and bound input positions. This
distinguishes `a*b` from `a*a` even when the operands share an alpha-equivalent
e-class. Matching candidate counts alone is insufficient.

For full non-native runs, the mapped graph is reconstructed in the original
engine and passed to its unchanged Lakeroad/spec-extraction/final-extraction
functions. This continuation has explicit bridge timings. It establishes an
executable mapping boundary; it is not a complete slotted rewrite of downstream
Churchroad. Reconstruction uses finite behavioral representatives, because
temporary `Wire` representatives interfere with the native spec extractor's
node-ID-based selection.

## Timing and validation

The report separates frontend import, encoding/lowering, rule loading,
saturation, convergence exports, graph normalization, synthesis, reinsertion,
and final extraction/code generation. `pipeline_wall_sec` includes process
startup, instrumentation, exports, and the native continuation where applicable.
Builds and whole-design validation are outside that time. Completed pipelines
retain their timings even when their RTL fails validation; the success count
remains zero in that situation.

Each child command has `--timeout` seconds and a 16-GiB address-space cap; the
supervisor kills remaining descendants. `max_child_rss_kib` is GNU time's maximum
RSS across waited-for children, **not** the sum of concurrent process memory.
Engine graph counts describe exported representations, not all internal tables.
The Python supervisor also acts as a Linux child subreaper while a command runs,
so terminated orphaned solvers are waited for even under a container PID 1 that
does not reap children.

Tool wrappers observe Yosys and Racket. A small Racket loader observes Rosette's
existing `encode` and `solve` reporter events. `solve` includes `check-sat`, model
reading, IPC, and possible lazy process startup; it is not pure solver CPU time.
These intervals are contained within Lakeroad's duration and must not be added
to it. Solver executables are invoked directly: Rosette manages their PIDs and
may kill persistent solver processes during cleanup. The source programs, solver
arguments, and synthesis constraints are unchanged by instrumentation.

After synthesis, Yosys normalizes the source and mapped RTL, treating DSP48E2 as
a black box. Icarus executes Lakeroad's original DSP48E2 simulation model,
preserving its delays, and compares all outputs on zero, all-ones,
one, and deterministic random inputs (256 vectors, seed 0 by default). This is
simulation, not whole-design formal equivalence. The paper example additionally
requires two DSP instances. Failures preserve the testbench and counterexample
output and return a nonzero exit status.

## Toolchain

Linux, GNU `time`, `prlimit`, Rustup, and the native frontend are required.
Prepare the frontend using the [existing recipe](README.md#rebuild-the-native-churchroad-frontend),
then use that directory with `--toolchain` (the default is
`benchmarks/local/reproduction/slotted-churchroad`). Source/toolchain paths must
not contain spaces or shell syntax because the native frontend does not quote
them. The preparation recipe requires a release `egglog-experimental` binary.

Full synthesis additionally requires Racket, Rosette, YAML, Bitwuzla, and Icarus:

```sh
sudo apt-get install racket iverilog time meson ninja-build libgmp-dev
TC="$PWD/benchmarks/local/reproduction/slotted-churchroad"
git -C "$TC/sources/churchroad" submodule update --init lakeroad
raco pkg install --auto --batch rosette yaml
git clone https://github.com/bitwuzla/bitwuzla.git "$TC/sources/bitwuzla"
git -C "$TC/sources/bitwuzla" checkout 9e5d7d82b0a0bfd3dc838eb3c3936acad500dc97
(cd "$TC/sources/bitwuzla" && ./configure.py --prefix "$TC/prefix" --no-testing)
ninja -C "$TC/sources/bitwuzla/build" install
raco make "$TC/sources/churchroad/lakeroad/bin/main.rkt"
```

These setup commands are for fresh dependencies. Reuse existing installations
when present. Bitwuzla's build downloads its pinned SAT-solver dependencies.
The evaluation itself does not install packages or update source revisions.

The native pins are Churchroad `9f82ca23b273a5a500cc6a1ca60b30d3c33c5721`,
Yosys `f8d4d7128cf72456cc03b0738a8651ac5dbe52e1`, and Lakeroad
`7a69047ad20cad54e5c78d68d397b716b42ff462`. The driver checks Churchroad/Lakeroad
revisions and records executable/model hashes. Rosette and YAML are not pinned
by this harness; their installed checksums and the Racket version are recorded.
The initial run used Racket 8.10, Rosette
`373c8c35e4a7667f38fce10cf0b74ae17de07f1d`, and YAML
`1f131712adbb1dca3b98a39400569c8209ac1944`.

The supplied simulation model has a Xilinx “All Right Reserved” header. It stays
in the ignored external checkout and is not redistributed here. The upstream
integration test instead refers to `lakeroad-private/DSP48E2`, which is not
available in this checkout. Availability and redistribution of that model are
an unresolved dependency for reproducing that exact validation configuration.
The separately modified import model has an Apache-2.0 header; these are distinct
files. Bitwuzla's checkout carries an MIT license.

## Initial measurements and reproduction blocker

Three sequential samples per treatment on the paper's wide multiply produced
the same complete mapped graph: **12 expression classes, 16 expression nodes,
three DSP proposals**. All twelve full pipelines completed and emitted two
DSP48E2 instances. Median seconds on this host were:

| Treatment | Mapping saturation | Lakeroad total | Rosette solver queries | Pipeline before validation |
| --- | ---: | ---: | ---: | ---: |
| native | 0.00330 | 8.354 | 2.138 | 8.784 |
| named | 0.00129 | 8.314 | 2.117 | 8.797 |
| typed-named | 0.00295 | 8.305 | 2.135 | 8.783 |
| slotted | 0.04498 | 8.329 | 2.136 | 9.091 |

These are instrumented diagnostic timings, not a successful end-to-end
reproduction or a statistical speedup claim. All twelve final RTL simulations
failed at `a=0xffff, b=0xffffffff`: expected `0xffff0001`, observed unknown bits.
The native baseline fails before any slotted adaptation is involved. A concrete
multiply-add DSP configuration from that run also disagrees between the pinned
generated Rosette model and the supplied simulation model: for inputs
`A=B=65535, C=D=65536`, the Rosette model returns low 32 bits `0xffff0001`, while
simulation has unknown bits. The wide case's plain-multiply configuration agrees
between the models.
An earlier diagnostic that flattened the simulation model through Yosys instead
returned `0x00010000`; final validation preserves the original model body. The
native specs passed to Lakeroad were the intended two multiplies and
multiply-add. The harness reports this as a validation failure and preserves
mapping parity independently.

On this workload, saturation accounts for about **0.038%** of native pipeline
time. Lakeroad accounts for about 95%, with its solver-query intervals accounting
for about 24% of total pipeline time. The remainder includes Racket startup,
symbolic execution, translation, and subprocess overhead; this measurement does
not separate those further. Eliminating saturation would therefore have little
effect on this example's total runtime. The slotted adapter is slower than the
typed named control here, including higher rule-loading costs. The experiment
currently provides no evidence of a speed benefit from slots in normal DSP
mapping. The separate [discovery experiment](DISCOVERY.md) runs module-enumeration
rules and reports its own candidate parity and performance results.

Regression coverage is in `tests/test_churchroad_eval.py`; `make check` also
builds/lints the current Rust measurement worker. The external native worker,
Lakeroad, and vendor-model simulation are exercised by the public CLI and are
not dependencies of ordinary CI.
