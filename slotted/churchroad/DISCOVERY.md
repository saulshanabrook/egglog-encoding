# Evaluating Churchroad module discovery

`./churchroad-eval.py discovery` measures Churchroad's experimental
`enumerate-modules` pass. Candidate construction runs inside Egglog in every
treatment. Python imports the source circuit, generates rules, and compares
results after timing; it does not pre-enumerate candidates.

```sh
./churchroad-eval.py discovery --output-dir /tmp/discovery-2bit
./churchroad-eval.py discovery --case ripple-generated --bits 4 --copies 1 \
  --rounds 8 --samples 5 --output-dir /tmp/discovery-4bit
./churchroad-eval.py discovery --case ripple-generated --bits 8 --rounds 9 \
  --samples 3 --treatments native vector slotted --timeout 120 \
  --output-dir /tmp/discovery-8bit
./churchroad-eval.py discovery --input design.egg --outputs out \
  --output-dir /tmp/discovery-local
```

The default is the saved two-bit ripple-adder frontend fixture. `half-adder`
and `wide-mul` also replay saved inputs; `ripple-generated` scales the gate
topology of the MIT-licensed two-bit example. It is explicitly a generated
workload, not an additional published benchmark. No Yosys, Lakeroad, SMT solver,
vendor model, or proprietary Intel fixture is needed for these measurements.
The native treatment needs the existing pinned Churchroad checkout/toolchain;
current-engine-only selections do not. All workers are built in release mode.

## Search and representations

This experiment isolates discovery on a **frozen combinational DAG**. The same
operators, constants, source identities, and fixed number of discovery rounds
are supplied to every treatment. Arithmetic expansion and the frontend's
typing/misc schedules do not run during discovery. This avoids the slice/concat
e-graph cycles that caused unbounded growth in the earlier native survey.
The finite input and budget are part of the workload; these timings are not
claims about saturation or discovery on arbitrary cyclic e-graphs.

| Treatment | Implementation |
| --- | --- |
| `native` | Original Churchroad engine and unchanged enumeration rules, `MakeModule(Graph, IVec)`, argument occurrence vectors, and `debruijnify` |
| `vector` | Current Egglog, the same graph/index-vector representation and cut choices, with flat candidate relations and canonical integer source identities |
| `slotted-eager` | Current slotted encoding, canonical open template bodies and slot maps, with generic maintenance after every discovery round |
| `slotted` | Same slotted candidates, with slot invariants maintained directly during canonical construction |

The vector control omits native `egraph.find` calls because source identities
are already canonical in the frozen graph. Comparing it with slots controls for
the engine upgrade and relational organization. A native/vector improvement
alone cannot be credited to slots.

An example native module stores a graph such as `And(Hole,Hole)`, an alias vector
such as `[0,0]`, and concrete arguments such as `[a,a]`. The slotted equivalent
stores `And($x,$x)` and one mapping `$x -> a`. Parent construction composes child
slot maps through the existing `node-shape` primitive. It does not rebuild a
full argument-occurrence vector and call `debruijnify` for every application.

The discovery adapter uses ordinary Egglog multipattern joins over the lowered
slotted representation. It does not extend the slotted surface language with
relations, containers, or named rulesets. Templates have ordered constructors
and no equality rewrites, so canonical children and canonical slot maps produce
canonical parents directly. Initialization runs once per template, setting its
exact public slots, identity symmetry group, and leader relation. This avoids
repeating metadata writes for every application. The existing logical exporter
independently checks the resulting invariants. Applying this optimization to
templates with additional equations would require general maintenance again.

After measurement, `templates.egg` closes each discovered template with
`BindInput` in first-occurrence input order. These interfaces are untyped,
matching native Churchroad's untyped `Hole`; typed hardware export and synthesis
remain separate integration work. The earlier `python3 -m slotted.churchroad`
prototype provides typed interfaces and Verilog export for its different,
Python-selected candidate search.

## A native matching restriction

The pinned native rules contain multiple patterns like
`(MakeModule graph0 _)` and `(MakeModule graph1 _)` in the same rule. In that
engine, `_` is a **shared variable**, so incorporating both child modules requires
their index vectors to be equal. A child with interface `[0]` cannot combine
with an incorporated child having interface `[0,1]`. Treating these as independent
wildcards changes the search: on the two-bit fixture at eight rounds, it produces
11,167 candidate occurrences instead of 511.

All treatments preserve this restriction. The slotted adapter therefore keeps
an interface-occurrence trace **once per template** to implement that join.
Its small `interface-rename` primitive transports already numbered slots through
an existing map; it neither looks up source e-classes nor assigns fresh numbers.
Consequently this is not a claim that every vector operation disappears.
Changing the native restriction should be evaluated as a separate semantic change.

Native `Var` and `Var_` also remain distinct boundary identities. Native rules
construct an empty vector by creating and popping `Var "unused" 0`, which itself
acquires an identity module. Only this implementation sentinel is excluded from
candidate comparison; unexpected candidates outside the source graph fail.

## Validation and measurement

Parity compares the complete set of **source root, module structure and aliases,
and ordered boundary occurrences**. Matching counts is insufficient. Raw exports,
normalized signatures, requests, source and binary hashes, per-round phase
events, current-engine rule profiles, and command logs remain in the fresh output
directory. Missing or failed samples cannot establish parity or contribute to
successful timing medians. `report.json` is independent of the benchmark cache.

Treatment order rotates across samples. `discovery_sec` includes enumeration,
interface traces, and slot maintenance. Setup/lowering/rule loading, export,
normalization, and supervised process wall time are reported separately.
Worker RSS includes export and is a process high-water mark. The supervisor's
polling resolution makes wall times for tiny cases coarse; use the internal
phase times for discovery comparisons. The timeout and 16-GiB address-space cap
apply to each worker, and the Linux supervisor reaps orphaned descendants.

`make check` includes pure Python regressions and 72 live vector/slotted searches
against an independent explicit-tree oracle, including all operator arities,
shared inputs, renamed copies, constants, and several round budgets. It also
checks that exported `BindInput` interfaces are closed. Native parity is checked
by the public evaluation CLI, since CI does not require the external checkout.

## Measured results and larger workloads

The two-bit fixture is too small to be the main performance case: native
discovery takes a median 4.48 ms at eight rounds (five samples, 511 candidates,
176 templates). Generated adders provide longer e-graph workloads without
invoking synthesis. A native-only scaling pilot measured about 0.44 s for
eight bits/eight rounds, 1.44 s for nine rounds, and 4.25 s for ten rounds.
The ten-round pilot constructed 793,297 raw applications, including the native
sentinel; it was a timing survey without full cross-engine validation.

The completed **eight-bit, nine-round** comparison has **304,878 candidates and
125,014 templates**. Every selected sample has the same complete signature hash.
Release builds, one Rayon thread, CPU affinity 124–125, three samples per
treatment, and a 120-second worker timeout were used on the shared Linux host.
The medians below were collected on 2026-11-02:

| Treatment | Discovery | Setup + discovery | Worker wall | Worker peak RSS |
| --- | ---: | ---: | ---: | ---: |
| Native Churchroad | 1.697 s | 1.706 s | 8.329 s | 1,059.8 MiB |
| Current vector control | 1.821 s | 1.825 s | 14.138 s | 3,252.7 MiB |
| Optimized slotted | 5.217 s | 5.242 s | 16.051 s | 3,821.3 MiB |

Worker wall time and RSS include graph export. Python normalization additionally
takes median 27.0, 24.5, and 37.0 seconds respectively; it is outside both worker
wall and discovery time. Thus full validation is much more expensive than the
phase being measured, and RSS is not a discovery-only memory measurement.

The native/vector samples came from a rotated three-treatment run. The final
slotted samples were collected afterward, following the change to initialize
metadata once per template. Before reusing the controls, the frozen source,
limits, affinity, sample count, current worker binary, and complete generated
native/vector requests were verified identical. This sequential measurement is
diagnostic evidence, not a confidence-interval or statistical speedup claim.

Per-template metadata initialization reduced the slotted median from 5.788 s to
5.217 s, about 10%. It remains **3.07 times slower than native**, so this experiment
does not establish a Churchroad speedup. The current-engine profile puts most of
the slotted time in enumeration rule application, rather than matching. Removing
native name canonicalization has not outweighed slot-map/template construction
costs. Profiling those result-construction paths is the next performance step.

Raw results are in `/tmp/churchroad-discovery-long-8bit/report.json` and
`/tmp/churchroad-discovery-long-optimized/report.json`; the verified combined
comparison is `/tmp/churchroad-discovery-long-comparison.json`. These local
artifacts are disposable. The eight-bit command above regenerates the complete
comparison with the current implementation and a fresh output directory.

## Research connection

The earlier [library-learning proposal, §4](https://arxiv.org/html/2404.00786v1#S4)
motivates discovering reusable subcircuits as synthesis candidates. The later
[Churchroad paper](https://arxiv.org/html/2411.11036v2#S2) also performs discovery,
using targeted DSP-proposal rules. This experiment improves and measures the
general module-enumeration component; it does not yet connect discovered modules
to Lakeroad or reproduce an end-to-end result from the later paper.
