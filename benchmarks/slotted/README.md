# Slotted benchmark inputs

The shared runner collects these inputs through its ordinary executable builds,
append-only observations, cache selection, and Vega-Lite rendering:

```sh
./bench.py figures slotted-runtime
./bench.py benchmarks/slotted/inputs/array/goal-2d-4f-N0.egg \
  --compare-treatment slotted-ref-multi --treatment slotted
python -m benchmarks.slotted.generate
```

`inputs/` contains the complete generated source `.egg` programs and their sibling
`.ref` JSON native protocols. Each source includes its declarations, rules, initial
terms, rewrite schedule, and ordinary terminal equality check. Includes are expanded,
so the `.egg` hash covers the whole source workload. The native endpoint hashes its
own physical `.ref` file. No generation or graph verification occurs during collection.
`make check` verifies exact regeneration and exercises the native benchmark CLI.

The generators and pinned author fixtures remain in [`slotted/benchmarks/`](../../slotted/benchmarks/),
with shared preparation in [`slotted/workloads.py`](../../slotted/workloads.py).
This freezes all workloads selected by that upstream harness: Figure 8's eleven
functional-array inputs (0–10 extra parameters, six rewrite rounds), ten SDQL
kernel/phase combinations using the full 44-rule library and existing per-workload
budgets, and both logic fixtures. SDQL source provenance and the distinction between
the paper's cost criterion and these stronger syntax goals are documented in
[`slotted/benchmarks/sdql/README.md`](../../slotted/benchmarks/sdql/README.md).

The paper's `slotted-runtime` figure selects only the ten SDQL cases. It compares
`slotted-no-aliasing` with `slotted-ref-nested`, the original nested matcher's
syntactic-substitution performance baseline. These treatments have different
substitution semantics; these performance measurements are not equivalence
certificates. Its upper panels report whole-process runtime and peak RSS from
the same selected executions, with arithmetic means and 95% Student-t intervals.
Lower panels show encoding/native ratios with Fieller-style 95% intervals.

The broader inputs remain available through ordinary benchmark file selection.
`slotted` (Egglog's full encoding) and `slotted-ref-multi` (the native multipattern
matcher) both use deterministic snapshot substitution. The two logic fixtures
require multipattern rules. Unsupported nested selections are rejected before
building or timing. Existing observations remain cached for both comparisons.

The reference binary is `slotted/xmulti`, pinned to the revision in its Cargo
manifest and built with `--no-default-features`. It uses the same native allocator
limit and same-process timing-summary interface as the other controlled engines.
Whole-process runtime includes input I/O, source parsing/lowering, rewriting, and
the ordinary terminal goal check. Missed goals remain failed observations. Reference
phase summaries distinguish input parsing and goal checks; the remaining reference
work is reported as other commands rather than inventing search/apply measurements.
The native Slotted library is an independent implementation, not an Egg fork.

For separate correctness work, `python3 slotted/check.py` retains the checked
reference build, graph export, class/node counts, and exact isomorphism comparisons.
Its optional `ref-nested-snapshot` treatment supplies the matching substitution
policy required by the compatibility encoding's equivalence checks.
