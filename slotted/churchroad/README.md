# Churchroad modules with slots

This prototype imports Churchroad's combinational circuit IR, discovers bounded
single-output and two-output modules, and emits Verilog that instantiates shared
module definitions. Module inputs use `BindInput`; application uses the existing
capture-avoiding `subst`. Half-adder and shared-input slice-pair recognition use
multipatterns. The root Egglog workspace supplies the execution engine.

The original command described below enumerates candidate cuts in Python before
entering the slotted e-graph. Its counts are not native Churchroad measurements.
The new [module-discovery evaluation](DISCOVERY.md), invoked with
`./churchroad-eval.py discovery`, instead runs discovery inside Egglog and compares
complete candidate sets against native Churchroad on the same frozen input and
round budget. It includes native, vector, and slotted performance controls.

The separate [DSP evaluation](EVALUATION.md), invoked through
`./churchroad-eval.py`, now measures native DSP mapping against matched named and
slotted adapters, compares complete mapped graphs, and continues through
Lakeroad with solver profiling and RTL simulation. Its measurements and native
validation blocker are documented separately; the claims above concern this
bounded module-discovery prototype.

Run from the repository root:

```sh
cargo build --release -p egglog-experimental
python3 -m slotted.churchroad --case ripple-adder \
  --output-dir /tmp/churchroad-ripple
```

The built-in `half-adder`, `ripple-adder`, and `wide-mul` cases replay saved
Churchroad frontend inputs without installing a hardware toolchain. The output
directory must be fresh. It contains the input, runnable `slotted.egg`, extracted
`modules.json`, `original.v`, `mapped.v`, command/log files, and `report.json`.
The report includes input/engine/program hashes and explicit validation status.

To independently check the emitted hardware, supply `--yosys /path/to/yosys`.
Yosys SAT checks the mapped circuit against the imported circuit and, for the
ripple-adder and wide-multiply cases, against the upstream Verilog source. This
needs no ABC, Lakeroad, vendor DSP models, or FPGA tools. Without Yosys, the report
says `not-run`; successful Egglog equality checks do not imply the SAT check ran.

## Relationship to vanilla Churchroad

At the pinned Churchroad revision, the normal executable imports Verilog through
Yosys into an Egglog e-graph, saturates typing, arithmetic transformation, and
mapping rules, and collects proposed DSP interfaces. For example, it can split a
wide multiply into smaller operations and propose two-input or three-input DSP
interfaces. It then asks Lakeroad to synthesize implementations, inserts successful
results into the e-graph, and extracts structural Verilog.

The source also contains an experimental `enumerate-modules` ruleset. This really
does enumerate inside the e-graph: for each operator, rewrites either abstract a
child into a hole or incorporate an already discovered child module. The resulting
`apply(MakeModule(graph, indices), args)` is equated with the original expression.
The Rust `debruijnify` primitive canonicalizes the argument e-classes and records
which hole occurrences share an argument. The normal executable imports these
rules but does not schedule `enumerate-modules`; its DSP proposals are a separate
mechanism. See the pinned upstream
[driver](https://github.com/gussmith23/churchroad/blob/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721/src/main.rs),
[enumeration rules](https://github.com/gussmith23/churchroad/blob/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721/egglog_src/module_enumeration_rewrites.egg),
and [primitive implementation](https://github.com/gussmith23/churchroad/blob/9f82ca23b273a5a500cc6a1ca60b30d3c33c5721/src/lib.rs).

This prototype instead imports the frontend's concrete combinational DAG, chooses
bounded cuts in Python, and inserts those candidates into the slotted e-graph.
The e-graph provides alpha-equivalence, multipattern recognition, substitution,
and application equality checks. The Python exporter groups extracted templates
and chooses module instances. It does not run Churchroad's arithmetic expansion,
DSP mapping, or native enumeration schedule.

Consequently, the report's `legacy_unique_templates` and
`legacy_partition_matches` fields refer to a local Python Graph/Hole/index-vector
reference applied to the same preselected candidates. They are not observations
from a native Churchroad run. The reference additionally includes widths and
ordered output bundles; upstream's experimental `Graph` has untyped holes and
represents a single result. Matching this reference checks representation identity,
not completeness relative to Churchroad's search.

The native driver was smoke-tested through its mapping phase on `simple_mul.v`,
using the existing capture patch to stop before Lakeroad. That establishes that
the original mapping code runs, but supplies neither a candidate-set comparison
nor an end-to-end synthesis result.

For this original Python-selected search, no native speed comparison has been
measured. The report's
`egglog_wall_sec` measures one supervised slotted-engine process, including startup,
parsing, rewriting, checks, extraction, and supervision overhead. It excludes
Python candidate enumeration/export, frontend import, and Yosys verification.
Single-run observations of approximately 0.15 s (half-adder), 0.50 s (ripple-adder),
and 0.15 s (wide multiply) are execution diagnostics, not a comparative benchmark.

The separate [discovery harness](DISCOVERY.md) now implements that native/slotted
comparison for single-output modules. Multi-output recognition remains an
extension in this original prototype. Connecting the enumerated modules to DSP
mapping and Lakeroad remains further work.

## IR and matching

Churchroad represents abstract modules as `MakeModule(Graph, IVec)`, with anonymous
`Hole` nodes in the graph and a `debruijnify`-computed vector identifying repeated
arguments. Here the same interface is a sequence of binders over an operator body:

```lisp
(BindInput 1 $a
  (BindInput 1 $b
    (OutputCons 1 (Xor 1 $a $b)
      (OutputCons 1 (And 1 $a $b) (NoOutputs)))))
```

`OutputCons` records ordered module outputs. The first integer in an operator is
its result width. Each `BindInput` records the width of its formal input. Repeated
references to one input use the same slot; distinct formal inputs retain distinct
slots. Alpha-equivalent modules share their representation even though the source
generator deliberately gives each occurrence different binder names.

The [language](../../egglog-experimental/tests/slotted/languages/churchroad.egg)
uses one slotted carrier and specializes Churchroad's `OpN(Op, ...)` constructors
into `And`, `Xor`, `Mul`, and other operator constructors with integer payloads.
The adapter checks widths before insertion and checks extracted module signatures
and expressions again before Verilog export.

Application to an arbitrary circuit uses beta reduction:

```lisp
(rewrite (Apply (BindInput width $x body) arg)
         (subst body $x arg))
```

Nested `Apply`s instantiate multiple inputs while avoiding capture. Native slot
maps rename variables; substitution plugs compound circuits into formal inputs.
Every generated candidate is applied to its original boundary circuits, and an
Egglog check requires equality with the original ordered outputs.

Half-adder recognition joins the two output expressions through shared arguments:

```lisp
(rewrite (OutputCons 1 sum (OutputCons 1 carry (NoOutputs)))
         (HalfAdder 0 a b)
         :when ((= sum (Xor 1 a b)) (= carry (And 1 a b))))
```

The output bundle anchors the join to one circuit occurrence. Merely finding an
`And` template somewhere in a slotted graph does not establish that the actual
design uses the corresponding carry output. A second rule handles carry-first
interfaces. Slice-pair recognition similarly joins two `Extract` roots through
one shared input invocation. Both rules allow repeated inputs and preserve the
output order.

Concrete wires and ports remain in the adapter's instance graph. Only the chosen
cut boundary becomes formal slots. Equal-height output pairs with a shared child
are considered, together with individual operator roots. Equal heights ensure
that contracting a pair into a module cannot create a dependency cycle. Defaults
are depth two, four inputs, and 256 candidates. `--max-depth`, `--max-inputs`, and
`--max-candidates` change those limits; reaching the candidate cap is reported
explicitly. This is bounded cut discovery, not exhaustive anti-unification.

The module identities are checked against a separate Graph/Hole plus index-vector
reference representation of the same candidates. This comparison establishes
partition parity; it is not a timing comparison with Churchroad's original
enumeration engine. Extraction favors compact multi-output constructors; selection
then uses recognized bundles and recurring templates to produce module instances.
The exporter currently optimizes representation reuse, not FPGA area or timing.

On the pinned two-bit ripple adder, the prototype's default search finds 34
candidate occurrences and 22 unique templates in both local representations.
These are not counts from Churchroad's native enumeration. The emitted circuit
uses eight module instances and six definitions, including two half-adder instances
and two slice-pair instances. Both Yosys equivalence checks pass. Wide multiply
checks mixed input widths and zero extension; it has no repeated modules under
these bounds, so the exporter preserves its direct circuit.

## Rebuild the native Churchroad frontend

The existing preparation recipe pins Churchroad to
`9f82ca23b273a5a500cc6a1ca60b30d3c33c5721` and Yosys to
`f8d4d7128cf72456cc03b0738a8651ac5dbe52e1`, builds matching Yosys/plugin binaries,
and builds Churchroad's original Rust driver with the mapping capture patch.

On Ubuntu, the additional frontend prerequisites are:

```sh
sudo apt-get install bison flex pkg-config libreadline-dev libffi-dev zlib1g-dev
rustup toolchain install 1.88.0
python3 -m benchmarks.reproduction.reproduction_prepare_churchroad \
  --output benchmarks/local/reproduction/slotted-churchroad --timeout-sec 2400
```

Use a fresh preparation directory if that path already exists. Include Rustup's
`~/.cargo/bin` in `PATH`. The recipe keeps source, build products, and receipts in
the ignored `benchmarks/local/reproduction/` tree.

The original Rust driver can also run its mapping phase without synthesis. Set
`CARGO_MANIFEST_DIR` to that Churchroad checkout and `EGGLOG_REPRO_CAPTURE_DIR`
to a fresh, existing directory, then invoke the generated
`prefix/bin/churchroad-capture` launcher with `--filepath`,
`--top-module-name`, and `--architecture xilinx-ultrascale-plus`. The capture
patch stops after mapping; its ordered event files retain the native computation.

Then regenerate the input through the actual plugin and check the full round trip:

```sh
python3 -m slotted.churchroad --case ripple-adder \
  --yosys benchmarks/local/reproduction/slotted-churchroad/prefix/bin/yosys \
  --plugin benchmarks/local/reproduction/slotted-churchroad/sources/churchroad/yosys-plugin/churchroad.so \
  --output-dir /tmp/churchroad-ripple-native
```

Supplying the plugin changes built-in Verilog cases from saved replay to fresh
capture. Arbitrary supported designs use `--verilog design.sv --top module_name`
with the same two tool paths. Existing frontend output uses `--input design.egg`;
if it lacks `IsPort`, provide `--outputs output_binding ...`.

The importer accepts circuit construction, wire aliases, ports, the frontend's
typing/misc schedules, and extraction requests. It rejects optimization rules or
other executable schedules instead of silently skipping them. It supports the
combinational operators declared in the language. Sequential feedback, reachable
registers, and black-box hardware instances need further work; `--outputs` can
select an explicitly combinational root before a register. Signed operations
are limited to the explicit `SignExtend` representation; the pinned frontend
itself does not fully model Verilog signedness. Native source equivalence checking
is particularly useful when importing new designs.

## Fixtures, tests, and licensing

[Fixture provenance](fixtures/provenance.json) records source paths, revisions,
and hashes. Original source files retain their upstream contents. Generated
frontend fixtures only remove comments and normalize s-expression whitespace,
making their hashes independent of the source checkout's absolute path.

```sh
python3 -m slotted.churchroad.fixtures --check-native \
  /tmp/churchroad-ripple-native/input.egg --case ripple-adder
python3 -m slotted.churchroad.fixtures --write
make check
```

The generated cases under `egglog-experimental/benches/slotted/churchroad/` run in
the ordinary Rust slotted fixture suite. Additional regressions cover capture
avoidance, renamed instances, repeated arguments, and mismatched output roots.
Python tests check the importer, exhaustive two-bit addition, width-sensitive
semantics, interface rejection, bounded enumeration, and fixture provenance.

The included Churchroad examples use its MIT license, preserved in
[LICENSE-Churchroad-MIT](fixtures/LICENSE-Churchroad-MIT). The Intel permuter is
excluded: its Verilog header restricts use to Intel FPGAs/CPLDs, and the upstream
file questions its own license compliance. Its derived Egglog fixture is also
excluded. No proprietary simulation models are needed by the included cases.

Proof production and Lakeroad synthesis are outside this case study's current
implementation. The adapter provides a concrete module-discovery and Verilog
round-trip integration point for Churchroad; it does not replace its full driver.
