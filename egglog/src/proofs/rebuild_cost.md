# Where the encoding's rebuild time goes

Measurements against `5cc4dc1` (PR #39's head), serial (`--threads 1`), release,
`bench.py` with 3–6 rounds per endpoint. Two questions: is clearing `@UF` every
iteration worth it, and what makes the encoded rebuild slower than native's.

## Clearing `@UF` every iteration does not pay

The union-find's only readers are the maintenance rules, so once the rebuild loop
saturates every row a query, `delete`, or `subsume` can reach is canonical and the
edges that got it there are dead. Deleting them is *sound* — with a
delete-everything ruleset running last in the maintenance schedule, all 801
`--test files` cases pass and every proof snapshot is byte-identical.

It is not *faster*, at 6 rounds:

| | baseline | clear | ratio |
| --- | ---: | ---: | ---: |
| `math-microbenchmark` wall | 4483 ms | 4511 ms | 1.006 |
| `eggcc-2mm-pass1` wall | 9709 ms | 9971 ms | 1.027 |
| `eggcc-2mm-pass1` peak RSS | 525 MiB | 568 MiB | 1.082 |

Per ruleset, the clear costs `+134 ms` while `@parent` saves `-27 ms`, and
`@rebuilding` does not move outside noise. The reason is that the rebuild rule is
`:unsafe-seminaive` and its driving `@UF` atom is therefore already restricted to
the delta: the rows a clear removes are ones the join never visits. `@parent`
joins `@UF` against itself, so its full side does shrink — which is the whole of
the measured win, and it is 0.6% of one benchmark.

The ceiling is low regardless. Time in `@parent` on the baseline is 3.0% of wall
on `math-microbenchmark`, 1.2% on `herbie`, and 0.2% on `eggcc-2mm-pass1`, so a
clear that cost nothing could not win more than that.

Two things also break, which is why the knob is off by default:

- **Canonicalizing a value from an earlier iteration stops working.**
  `find_canonical` and proof extraction's fall-back read `@UF` outside rebuilding
  to resolve a value that predates this iteration. Surface syntax never needs it
  (queries read views, which are canonical, and `(extract e)` interns `e` first),
  but a Rust-API caller holding a `Value` across a union does, and native
  resolves those.
- **`saturate` can stop terminating.** `(rule ((Same x y)) ((union x y)) :naive)`
  under `(saturate ...)` terminates normally and hangs with the clear on: once
  `x` and `y` are canonically equal the re-firing rule writes the self-edge
  `v -> v`, which `:internal-identity-vals 1` normally makes an idempotent
  no-op. After a clear the row is absent, so the re-`set` is a fresh insert and
  the loop always reports a change. Adding `(!= x y)` fixes that program, and
  suppressing self-edges at the source would fix the class — a `@UF` row whose
  key is its own parent carries no information, since a term with no row is
  already its own representative.

A whole-table `clear_table` fast path (already present end to end, from
`Database::clear_table` through `EGraph::clear_function`) would remove the
`+134 ms` but not the reason there is nothing to win, and would not help the
termination case at all, where the change is reported by the re-*insert*.

## The encoded rebuild is ~4.5x native's, and always takes the incremental branch

Encoded proofs against native (`--treatment proofs` vs `off`), fastest of 3:

| file | native | proofs | ratio | native rebuild | `@rebuilding`+`@parent` |
| --- | ---: | ---: | ---: | ---: | ---: |
| `math-microbenchmark` | 1035 ms | 4502 ms | 4.35x | 386 ms | 1679 ms |
| `eggcc-2mm-pass1` | 2717 ms | 9783 ms | 3.60x | 581 ms | 2682 ms |
| `herbie` | 130 ms | 564 ms | 4.34x | 5 ms | 47 ms |
| `hardboiled_conv1d_32` | 323 ms | 1127 ms | 3.49x | 0 ms | 33 ms |
| `luminal-llama` | 1120 ms | 8238 ms | 7.35x | 6 ms | 13 ms |

Rebuild excess is 30–37% of the encoding's total overhead on the two files where
rebuilding matters, and search is the larger half of it: rebuild search on
`math-microbenchmark` is 890 ms, itself 2.3x native's entire rebuild. As a share
of all search time, maintenance is 79% on `math-microbenchmark`, 55% on `herbie`,
21% on `eggcc-2mm-pass1` — and 0.5% on `luminal-llama`, whose 7.35x is the worst
of the set and has nothing to do with rebuilding.

Rebuild is not the whole of the search gap, and on most files it is not even the
larger part. Search time only, native against encoded:

| file | native | encoded | of which user rules | of which maintenance |
| --- | ---: | ---: | ---: | ---: |
| `luminal-llama` | 28 ms | 1683 ms | **1674 ms** | 9 ms |
| `eggcc-2mm-pass1` | 1659 ms | 2933 ms | **2323 ms** | 609 ms |
| `hardboiled_conv1d_32` | ~0 ms | 317 ms | **300 ms** | 16 ms |
| `math-microbenchmark` | 221 ms | 1129 ms | 240 ms | **890 ms** |
| `herbie` | 16 ms | 42 ms | 19 ms | 23 ms |

Maintenance dominates search on `math-microbenchmark` and `herbie` only. Elsewhere
the cost is in the rewritten *user* queries — most sharply on `luminal-llama`,
where encoded user-rule search is 60x native's entire search while its rebuild is
9 ms. Whatever the encoded rebuild is made to cost, that file does not improve.
The two are separate problems and the rest of this note is about the smaller one.

The user-rule cost is **not** join width. Comparing the two desugared programs
suggests it is — `matmul_backend`'s bodies go from a median of 13 top-level forms
to 38 — but that comparison is invalid. `GenericExprExt::to_query` in `core.rs`
flattens every nested `Call` into one atom per subterm, so native's

```text
(= ?cast (Op (Cast ?size (F32)) (ICons ?matmul (INil))))
```

compiles to the same four atoms the encoding writes out longhand. Native's
desugared *text* keeps the nesting; the encoding's does not. On the rule
`"cublaslt bf16 matmul cast f32 output"` both come to eleven real atoms —
`Op`, `cublaslt`, four `Bf16`, `Op`, `Cast`, `F32`, `ICons`, `INil` — and the
encoding adds two `(= ?matmul <fresh>)` aliases a compiler substitutes away.
Body shape and atom count therefore match, and the 60x is elsewhere.

Rebuild churn is not the explanation either: `num_matches_per_rule` totals 12550
under both, so every rule fires the same number of times and no extra deltas
exist. The e-graph is identical too (129 functions, 15127 rows, no table
differing).

It is the **query planner's tree decomposition**. With `--no-decomp` the plans
become the same 14/15 stages in the same order, and the encoded time reaches
parity: over the 254 rules present in both, search+apply is 523 ms native vs
1225 ms encoded with decomposition, and **166 ms vs 158 ms without**. With
decomposition on, the encoded plan covers the 1301-row `@IConsView` in its outer
loop where native's covers the 12-row `FusionEnd`.

Turning decomposition off is a large win on its own, for native as much as for the
encoding — `luminal-llama` goes 1019 ms to 487 ms native and 3845 ms to 2404 ms in
term mode — but it is not uniform: `math-microbenchmark` is slightly worse without
it. The heuristic is also unstable under small changes to a query, which is what
makes the next section's result so hard to read.

## A real bug in `remove_dup_vars`, and why it is not landed

`remove_dup_vars` implements egglog's FD-based duplicate elimination: two atoms
over one function with equal inputs must agree on the output, so one is dropped
and an equality recorded. It splits the **last** argument as the output and keys
on the rest, which assumes a single value column. A tuple-output function has two,
so the key keeps the e-class — and two reads of one row bind that to different
variables, so no group ever forms. Every one of the encoding's FD views is
tuple-output, so repeated subterms are never shared: native's plan reaches one
`@INil1236` from both `ICons` probes where the encoding has two variables.

Keying on the inputs and unifying every output column fixes it, and does what it
should: the encoded plan for `grow-FE-B-lhs-Mul` becomes structurally identical to
native's, sharing one variable across both probes. It is **not** landed, because
the planner's sensitivity turns it into a loss where it matters:

| geomean vs `5cc4dc1`, 3 rounds | ratio |
| --- | ---: |
| native (`off`) | 1.010 |
| term encoding | 0.943 |
| proofs | ~1.09 |

Native is flat on five of six files but `herbie` is reproducibly **1.087** at 8
rounds (127 ms to 138 ms). Proofs regresses on `luminal-llama` (8073 ms to
11462 ms) — the same file and the same change that term mode runs 23% *faster*.
Isolating it on that file shows the fix is a real 8% win and decomposition is what
punishes the new query shape:

| `luminal-llama`, proofs | decomposition on | `--no-decomp` |
| --- | ---: | ---: |
| baseline | 8126 ms | 6950 ms |
| with the fix | 11397 ms | 6410 ms |

Pairing the fix with `--no-decomp` is not uniform either: `hardboiled_conv1d_32`
runs 0.829 in term mode and 1.422 in proofs. Per-file swings of ±40% in both
directions from one change are the signature of a plan heuristic being chosen by
luck, so the decomposition and costing work has to come first. The fix is one
commit, reverted in place, and worth re-applying against a planner that costs
these queries stably.

Native picks per table, per round, between scanning only the recently-updated
subset and scanning the whole table, at `diff > table_size / 8`
(`core-relations/src/table/rebuild.rs`). Tracing that choice:

| workload | decisions | fullscan | median `diff/table_size` |
| --- | ---: | ---: | ---: |
| `math-microbenchmark` | 429 | **93.2%** | 1.000 |
| `eggcc-2mm-pass1` | 336340 | **99.8%** | 0.800 |

So native almost always scans, and the encoding has no way to: its rebuild rule
is driven by the `@UF` delta joined against a declared occurrence index, and an
index atom is probed rather than scanned by construction. On these workloads the
encoding therefore pays twice — maintaining an index native would not consult,
then probing it per delta row instead of making one sequential pass.

Scanning the index is not the fix: `(any 0 1 2)` holds one entry per row *per
listed column*, so scanning it visits each row three times. The scan has to be
over the view, which makes it a different rule body rather than a different plan
for the same rule — no cost-based planner change can reach it.

The shape that scan wants already exists in the encoding, as the container
rebuild rule: `:naive`, canonicalize in the body, guard on the column having
moved. Two ways to choose between the shapes, neither needing the backend to
recognize a rule:

- A body guard that is cheap and fails fast — a primitive comparing the `@UF`
  delta against the view's size, ordered first so a losing round never reaches
  the scan.
- A per-view scan rule per column (which is what the index-driven rule replaced),
  costing one scan per column rather than one per view.

The higher-ceiling option is a bulk view-rebuild primitive that does the scan and
the canonicalization in Rust and mints the proof rows itself, which is what
`proof_container_rebuild.rs` already does for containers. That is the only option
that also removes the interpreted-join overhead, rather than trading one join
shape for another.

`EGGLOG_REBUILD_TRACE=1` prints native's per-table branch and its two inputs.
