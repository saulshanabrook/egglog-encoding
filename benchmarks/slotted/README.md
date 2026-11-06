# Slotted inputs and semantic coverage

`inputs/` contains the 23 paper benchmark pairs and their provenance manifest.
`correctness/` contains 122 small frozen semantic pairs, including conformance
and edge cases rather than a list of known bugs. Both are read by normal
Rust workspace tests; the shared figure catalog selects the paper SDQL inputs.
The top-level `benchmarks/ignore.json` is the sole exclusion policy.

GitHub collapses the generated `.egg`/`.ref` pairs by default. Review the
[input manifest](inputs/manifest.json) and [case definitions and generators](../reproduction/slotted/);
expand individual pairs to inspect their frozen bytes.

| Prior Python check | Current coverage |
| --- | --- |
| Curated multipatterns | 59 toy pairs; class partitions and validated counts |
| Array rules, free-slot cases, load-bearing guards | 20 array pairs including five guard-stripped partners |
| SDQL binding/substitution and known limitation | 28 pairs; expected partitions and the recorded differing answers |
| Nested matching and aliasing | 12 pairs; both matched-policy references and the expected node-count difference |
| Substitution refresh, coset direction, complete refinement | Three eval pairs, retaining the 5/8 and 77/280 count expectations |
| Substitution policy selection | Native library and workload-driver Rust tests |
| Raw slot maps, groups, edges and row invariants | Validating Rust export plus existing maintenance/export unit tests |
| Paper array/SDQL/logic goals and iteration budgets | Actual frozen inputs in the catalog-driven Rust paper target |
| Artifact hashes, capture guards and operator correspondence | Static Python tooling tests and inspectable manifests |
| Original active rule library correspondence | Explicit `python -m benchmarks.reproduction.slotted.reference_rules` reproduction check |
| Slotted proof translation | Rust proof corpus checks supported frozen inputs and proves the differential fixtures' observed probe equalities |

The previous Python runner/progress/protocol tests disappear with that runner.
Paper graph-isomorphism obligations and generated random campaigns are retired;
the independent Rust isomorphism crate retains its own validation. Named semantic
cases remain frozen. Round budgets are compared at the same cutoff; a reference
`saturated=false` after a one-round fixture does not request another user round.

The pure case tables and renderers are retained under
`benchmarks/reproduction/slotted/`. Regeneration and byte comparison are explicit:

```sh
python -m benchmarks.reproduction.slotted.generate --check
python -m benchmarks.reproduction.slotted.generate_differential --check
```

Routine tests and figure collection never acquire historical artifacts, invoke
these generators, or use a smaller workload to certify an excluded paper case.
