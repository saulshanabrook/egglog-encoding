# Order-tagged sorting reaches the combined encoding in EggCC

The bounded K3 integration changes actual emitted Bril and ARM64 code while preserving all tested outputs. The retained chain uses marked-key cancellation over dynamic equality-sort children, sibling-guarded reverse disequality for an **unmarked** Add, and marked forward disequality through multiplication by 3. It exports only the exact contextual target `Eq=false`. Both true intermediate-fact rescues work. This is supporting mechanism/native-code evidence: no pre-existing compiler bug or measured speedup is claimed, and full host validation is reported below without accepting snapshots.

The isolated host is `/private/tmp/eggcc-sort-candidate`, based on pinned U0 `a0bbec127f83249074a46af3fd6f6126c90fe0fb`. The selected engine is `/private/tmp/encoding-sort-candidate`. All 771 admitted U0 source hashes are verified; the candidate archive has 774 files including generated runtime objects. Only `dag_in_context/src/lib.rs` and the new `dag_in_context/src/scoped_reasoning.rs` change semantics. Cargo paths and lockfiles account for the four other differences. There were zero semantic/import revisions, no root-source or shared-ledger edits, and no commit, push, PR, proof, paper change, or timing collection.

## Law and import boundary

For signed i64 values define

```text
O(a,b) = (smin(a,b), smax(a,b), select(a<b,1,0)).
```

The tag reconstructs `(a,b)` as `(min,max)` when 1 and `(max,min)` when 0. Ties correctly use tag 0; signed MIN/MAX require no arithmetic or overflow assumptions. Therefore `O` is injective for every signed i64 pair. Multiplication by 3 is a bijection modulo `2^64`; Add and Mul use EggCC's wrapping-i64 semantics.

Import admits only three nested true integer-Eq guards over the exact min, max, and literal orientation expression for the same ordered pair. It follows branch-input substitutions to one lexical root and checks expression contexts and integer argument fields. It then requires the false branch of `Eq(Add(c,z),Add(a,w))` and the exact `Eq(Mul(z,3),Mul(w,3))` target. Only supported total pure scalar expressions enter the private Word abstraction. No arbitrary order analysis, floating sorting, effects, loops, heaps, or bounds are inferred. Rooted opaque words can forget aliases but do not assert disequality; the universal proof remains sound under their actual substitution.

## Actual private graph and consumer

All six payloads, six key fields, mixed sums, and odd products are equality-sort values. The finite graph contains these exact source seeds and representation identities:

```text
Kab = OrderKey(a,b)        Kcd = OrderKey(c,d)       marked binary constructor
Pab = Triple(Min(a,b),Max(a,b),Tag(a,b,1,0))          unmarked product
Pcd = Triple(Min(c,d),Max(c,d),Tag(c,d,1,0))
Kab=Pab, Kcd=Pcd                                     representation identities
Min(a,b)=Min(c,d), Max(a,b)=Max(c,d), Tag(a,b)=Tag(c,d) true source guards
Add(c,z) != Add(a,w)                                 false source guard
```

Generic congruence makes `Pab=Pcd`, hence `Kab=Kcd`. Generic marked-constructor cancellation derives `a=c` and `b=d`. The mixed-Add result disequality now has canonically equal first children, so generic reverse congruence derives `z!=w`. Marked forward reasoning derives `OddMul(z,3)!=OddMul(w,3)`. Min, Max, Tag, Triple, and Add remain unmarked. The only materialized OddMul coefficient is the admitted fixed odd coefficient 3.

The host exports this final witness as the exact target Boolean predicate, united with false in EggCC's main graph. Dynamic word equalities never leave the private graph. U0 and B1 retain `cmp x4,x5` and the native `99` selection in `__main`; Encoding and Manual remove them. Application instructions change from 29 to 25. These are code-generation observations, not performance measurements.

Manual independently computes a finite least fixed point over the same generic constructor rows, primitive fields, identities, and source seeds. It includes congruence, marked cancellation/forward propagation, and sibling-guarded reverse propagation. Encoding never calls this manual closure. Exact emitted-program and native-entry hashes match between Manual and Encoding; no unique logical power is claimed.

## Causal matrix

Every role uses the same positive fixture and ten fixed rows (nine distinct tuples). “Baseline” means exact emitted Bril and the combined native main-entry hash match U0; “optimized” means exact Encoding parity.

| Role | Retained causal fact / controlled step | Code |
|---|---|---|
| U0 / B1 (`off`) | No private derivation or export | Baseline |
| SeedOnly | Same private graph, annotations, identities, primitive fields, and dynamic source seeds; no saturation or queries | Baseline |
| PrimitiveOnly | Same seed graph; external primitive-column comparison pass executes without equality-sort reasoning | Baseline |
| Cancellation off | `Kab=Kcd`, no `a=c` | Baseline |
| Identity off | `Pab=Pcd`, no key equality or `a=c` | Baseline |
| Reverse off | `a=c`, `b=d`, Add-result disequality; no `z!=w` | Baseline |
| Forward off | `z!=w`; no odd-product witness | Baseline |
| Query off | Final witness deliberately unqueried | Baseline |
| Bridge off | Exact final witness present; export disabled | Baseline |
| Application off | Witness and export present; only main-graph target union disabled | Baseline |
| Cancellation rescue | Key marking disabled; seed only intermediate `a=c`; `b=d` remains unknown | Optimized |
| Reverse rescue | Reverse reasoning disabled; seed only intermediate `z!=w` | Optimized |
| Manual / Encoding | Complete dynamic chain, exact target export and application | Optimized |

The rescues assert neither the final target disequality nor a constant source result. The application knockout retains the internal proof and export decision while restoring U0 exactly, identifying the actual consumer union as causal.

Rust PrimitiveOnly carries the complete unchanged seed graph and performs no dynamic inference. The **separately executed** `primitive_null.py` derives primitive columns from the actual serialized constructor schemas and compares corresponding columns for every pair of same-constructor applications. The graph matches Encoding after removing only scheduling, and matches SeedOnly exactly. All 26 committed application occurrences and 12 primitive comparisons are retained in `primitive-null.json`; there are zero mismatches, no equality-sort comparison/propagation, and no primitive target witness. The tag values remain symbolic functions of dynamic payloads. The independent audit recomputes this null and binds source, graph, binary, and command hashes. Thus this null is more than simply labeling SeedOnly with another mode name.

## Correctness and negatives

The completed matrix has **244 passing native output checks and 244 source/emitted interpreter checks**: 160 positive/causal native runs, 56 semantic-negative runs, 20 disabled-context runs, and eight deliberate invalid-fold runs. Positive rows cover ascending, descending, tied, signed-extreme pairs, key mismatches, equal-tail exits, and wrapping tails/products. An independent Python oracle computes signed sorting and wrapping arithmetic. A separate reconstruction checker exhaustively covers all 87,376 signed pairs at widths 2–8 and 4,145 boundary/random i64 pairs.

All eight negative families reject import, preserve their U0 emitted/native hashes in B1, SeedOnly, PrimitiveOnly, Manual, and Encoding, and execute `99`. Deliberately changing only the target branch to false executes `7` in both interpreter and native code:

| Rejected evidence/law | Concrete `(a,b,c,d,z,w)` |
|---|---|
| Omit tag; swapped inputs collide without it | `(1,2,2,1,0,0)` |
| Omit min field | `(0,2,1,2,0,0)` |
| Omit max field | `(2,0,3,0,0,0)` |
| Right comparison is `d<c` | `(1,2,2,1,0,0)` |
| Right Select uses `0,1` | `(1,2,2,1,0,0)` |
| Multiplier is 2 | `(1,2,1,2,0,MIN)` |
| Target lies on Add-equality true branch | `(1,2,1,2,0,0)` |
| All key guards absent from the target context | `(1,2,2,1,0,0)` |

The separately named swapped-input/no-tag fixture is byte-identical to the omitted-tag counterexample; it is not counted as an extra run. Reversing both tags would still give an injective key and is not claimed as a semantic negative. Running the unchanged positive fixture without context support creates no sidecar query/export and exactly matches its disabled-context U0 comparator.

## Validation and provenance

Fresh validation passes the two registered causal tests, all 66 DAG library tests in debug, all 66 DAG release tests, formatting, and all 18 registered engine oracle tests. The release DAG run has no pending snapshots. Root and DAG Clippy exit 101 with exactly three pre-existing diagnostics in files byte-identical to pinned U0: one `unnecessary_unwrap` in `src/rvsdg/optimize_direct_jumps.rs:236`, one in `dag_in_context/src/extractiongymfastergreedydag.rs:134`, and `cloned_ref_to_slice_refs` in `dag_in_context/src/fastercbcextractor.rs:991`. There are zero new sidecar diagnostics.

The first full host `make test` passes 31 unit tests and 2,410 file tests, but 11 file tests fail during actual disk exhaustion: ten Tiger invocations report ENOSPC, and `jacobi-1d` reports LLVM output-stream ENOSPC. Those complete command streams and the first 13 pending snapshots are preserved. After inactive debug caches were removed, one exact-command environmental retry uses identical argv, cwd, and explicit environment with unchanged sources/binary. It passes all **31 unit and 2,421 file tests**, with zero functional failures and no ENOSPC. It still exits 2 for **13 unaccepted snapshots** before reaching the Makefile's DAG step. The separately executed complete DAG release suite passes all 66 tests.

All 13 final snapshot names and SHA-256 hashes match both the preserved first run and the frozen Parts32 E1 comparison; these are not U0 baseline snapshots. The previously fresh pinned-U0 release `make test` receipt passes 31 unit, 2,421 file, and 64 DAG tests with no snapshots, and its 771 admitted source hashes remain verified here. No snapshot is accepted and no full-validation failure is waived. The environmental retry resolves only the disk-full failures. Broad host validation therefore remains failed and this result remains **supporting evidence only**.

`identities.json` binds complete source archives, source manifests, binary hashes, every command receipt, argv/configuration hashes, captured streams, inputs, emitted programs, LLVM, assembly, and native results. The selected engine full check is reused only with explicit identity evidence: all 884 retained files match Parts32 E1; 871 source/manifest files equal immutable Git base `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`, five changed/new source files match the frozen Parts32 archive, and eight remaining files are ignored historical output logs. `engine-base-verification.json` retains this check. This is reused Parts32 `make check`, not a fresh sort-engine check.

The evidence-harness ledger records two corrections without candidate changes: comparing archives with U0's runtime files as well as its admitted source manifest, and removing duplicated raw-source interpreter labels. No compiler/native oracle failure was repaired by changing the candidate. See `validation.json`, `failure-ledger.json`, `independent-audit.md`, and the separate [reproduction guide](reproduce.md). Run `python3 inspect.py` in this directory for the final read-only audit.

This bounded acyclic integration establishes the combined mechanism and an actual native difference. Its constructed trigger, unresolved full-validation failures, and lack of a prospectively frozen hot workload prevent a bug or runtime-payoff conclusion. No timing samples were collected.
