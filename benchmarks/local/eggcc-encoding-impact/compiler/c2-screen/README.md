# C2 default NoAlias production/consumption screen

Verdict: **no promising final pair-storage or current distinct-address commute hit in these two source-derived small diagnostics**. Do not implement a new key domain for this screen alone. This is a scoped cardinality/applicability result, not a timing/memory result or an exhausted candidate search.

The original csrmv header is 750; the diagnostic header is 8. Mat-mul is 135 versus 4. Only the first header line changes; new fixtures live under the new compiler worktree's `tests/encoding_impact/c2/`, with original/small archived copies and hashes here. Four export invocations verify **byte-identical complete pass-0 prologue/initialization/schedule** between each original and small header. This establishes identical compiler inputs at that boundary, not all later graph determinism. Source interpretation at original large headers was not run.

Two small correctness invocations use frozen engine-only B SHA `6c30c8cb28768f3c461666b0370ff5c249fe6ba1f8f58a1a1d6c78e2df3e638f`, its frozen sibling greedy Tiger SHA `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`, enabled contexts, default parallel passes 0/1/2 and non_weakly_linear=true. Non-null original/result outputs match: csrmv `963\n`, mat-mul `2446272\n`. Three serialized graphs are retained per case. No optimization source, key/consumer, native runtime adapter, or timing cohort was added.

## Guard and process identity

`manifest.json` pins current-primary processes.py and memory_guard.py, copied unchanged into an isolated runner overlay. Their relative models/engines imports use the selected encoding worktree's existing sources directly; those sources are pinned and unchanged, with no current-model/current-engine transplantation. The stdlib-only adapter runs under isolated Python 3.13.11. The import/guard smoke confirms explicit `EGGLOG_BENCH_MEMORY_GUARD=1`, the 10-GiB group cap, 2-GiB headroom reserve, normal pressure, and a successful trivial process. A synthetic over-cap check tests the threshold without launching a large allocation.

Actual invocations are sequential, 120 seconds each, with the existing runner's timeout/process-group cleanup/memory guard unchanged. An untimed shell `exec "$@"` redirection retains successful stdout/stderr inside the guarded process group; exact runner and target argv, cwd and environment overrides are in receipts. The helper's timing fields are discarded. All six compiler commands succeeded with exit 0, no resource stop and no timeout. The later state recovery checked the original session's terminal exit and OS process state; **no workload was restarted**. No group/process remains active.

## Snapshot definitions and results

`cardinalities.json` and `cardinalities.md` define the joins and six per-case/pass rows. Counts include serialized subsumed nodes. NoAlias is a set of canonical **ordered** pointer-class pairs (including symmetry). A present write/load demand is the source mem_simple:71–73 body join: a Top Write class is the state argument to a Bop Load. Unique pointer pairs and complete six-field body instances are recorded separately. NoAlias intersection supplies the current complete commute premise.

| Case | Pass | Final nodes | NoAlias pairs | Present demand pairs | Matched pairs |
| --- | ---: | ---: | ---: | ---: | ---: |
| csrmv | 0 | 35,976 | 2 | 0 | 0 |
| csrmv | 1 | 71,796 | 0 | 0 | 0 |
| csrmv | 2 | 629,463 | 10 | 4 | 0 |
| mat-mul | 0 | 15,901 | 0 | 0 | 0 |
| mat-mul | 1 | 31,597 | 0 | 0 | 0 |
| mat-mul | 2 | 43,631 | 0 | 0 | 0 |

All four csrmv final demand pairs are **same-address**; `demand-details.json` retains class/instance identifiers. Its one DidMemOptimization row is the string `store forward`, an existence marker, not a firing count. No commute marker is present. Every final NoAlias pair has an InIf→InIf context shape and matches a nonzero-shift producer shape in the final graph; four also match the same-base plus/minus-difference form. Labels can overlap. Mat-mul has no NoAlias rows or markers in any pass.

Final snapshots do not count cumulative offered/fired rule work, all historical demands, peak graph/RSS or CPU time. A retained pair could have been useful earlier; zero current intersection does not prove every pair was always useless. The at-most-ten stored pairs among these large graphs give no compelling storage-impact case, and zero distinct-address demand gives no current commute target for a new same-anchor key query. This does **not** prove general NoAlias processing is free or that no other workload can benefit.

## Exact next mechanism proposal (no implementation yet)

Deprioritize C2 key/pair replacement for these two inputs. If pursuing runtime impact next, first use one guarded untimed emitted-Bril capture for the already-validated CSR small input and inspect whether res[rid]'s load/store still lies inside the nonzero loop. This is a **new proposed diagnostic**, not coverage already established by final graph rows. If already promoted/hoisted, reject that target.

If the loop remains, the relevant mechanism is C3: carry an accumulator scalar through the inner loop, hoist the initial res[rid] load and sink its final store across loads from proven-disjoint input arrays. New keys alone cannot make the present adjacent write/load rule perform that loop transformation. A reviewed law must establish loop-input pointer invariance, live distinct-region provenance at the actual call site, no intervening write to res except its accumulator update, valid/bounded indices and nonoverflow induction, zero-iteration behavior, termination/effects and any call/free constraints. Generic formal argument names/static Alloc ids are not certificates. The current CSR final graph retains 14 Call nodes, so no call-free whole-program assumption is available.

Mat-mul's final snapshot has zero Call nodes and five Alloc nodes, so allocation visibility improved after inlining, but its array loads vary by index and dest stores occur across loop regions. It still needs a concrete residual redundant-memory consumer, not only a claim of disjoint arrays. Diagnose that target before proposing summaries or new rules.

Alternatively prioritize the separately proposed feasible-point observation checker for the confirmed arithmetic miscompile after semantic review. That connects a real bug to an injective observed-literal contract with an equivalent manual oracle, without pretending these C2 snapshots establish speedup. No source integration, broad stress screen or native preparation is authorized by this screening artifact itself.

## Reproduction

- Import/guard smoke: `uv run --no-project --python 3.13 python adapter.py` from a fresh copied artifact directory with its manifest sources available.
- Compiler capture: `uv run --no-project --python 3.13 python run.py`; it refuses to overwrite existing stage directories. Use a fresh artifact directory and repin destinations before rerun. Six exact child argv arrays are retained in their receipts.
- Snapshot analysis only: `uv run --no-project --python 3.13 python analyze.py`; this reads retained graphs and writes the diagnostic counts, without invoking a compiler.
- `verification.json` checks pinned modules, frozen binaries, one-line input differences, export identities, complete matching interpretation, six graph hashes and terminal status. `checkpoint.json` pins all source/output/script/receipt hashes for review.
