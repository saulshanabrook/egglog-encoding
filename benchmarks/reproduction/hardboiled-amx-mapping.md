# HardBoiled AMX: seven paper cells versus five active executables

Source mapping audit, 2026-09-24. The mapping investigation itself ran no
compiler or target code. On 2026-09-25, all five genuine AMX artifact programs
completed native optimization and ordinary replay as part of the 34-case
HardBoiled batch. See [native audit](hardboiled-native-audit.md). This does not
resolve their correspondence to the seven paper cells; shared adapter changes
still require current-identity refresh of those execution receipts.

**The pinned artifact does not contain seven separately selectable AMX table
configurations. One cell has a direct source match (VNNI preload B), two reference
cells have reasonable structural candidates, and four cells lack an unambiguous
active configuration (two loop-order contrasts and two A-preload variants).**
In particular, assigning the two `1x4` files to “loop reordering” and declaring
only two cases missing would turn an inference into a fact.

## Paper population and source identities

[Paper §IV, robustness discussion, p. 6; Table I, p. 8](https://arxiv.org/html/2512.02371v2#S4.T1)
gives seven supported combinations: reference, loop reordering, and preloading A
in both VNNI and standard layouts; preloading B only in VNNI. Standard preload B
and both software-pipelining combinations are unsupported. The discussion ties
these schedules to Intel's manual §20.5.5, but supplies no filenames, dimensions,
data types or command-line mappings. It says standard-layout support inserts
swizzling automatically. These are schedule/layout claims, not seven runtime
input sizes or seven data-type combinations.

The artifact revision is `b99cf0c6400e954a278f697bf3a0596ac3fa4f25`.
[CMake](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/instrsel-benchmarks/CMakeLists.txt)
and [README commands](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/README.md#support-for-schedules-in-amx)
name exactly five executables. All five `main` functions ignore `argc`/`argv`,
hardcode `x86-64-linux-avx512_sapphirerapids`, and call one fixed algorithm.
There is no existing command-line switch selecting a table row or operand type.
The local catalog's five AMX `configuration` objects are empty.

The recovered local files used below were independently checked against the Git
blob hashes in the pinned tree; all five match. SHA-256 identities:

| `instrsel-benchmarks/` file | SHA-256 |
|---|---|
| `matmul_vnni_1x1.cpp` | `22cd030ea52442129c14d8f599f88db1ca243b5fba30d8c30915dd8a9571bfe7` |
| `matmul_vnni_1x4.cpp` | `4f20d96acf3cd7e9ab1dbf38b411968275ea2ed38c9d677247a65dfc93c6c510` |
| `matmul_vnni_1x4_preload_rhs.cpp` | `d1787becc61d8b2635e7037235e099c05fc6efb134eb9a4eaaa7ad8d4fb3e509` |
| `matmul_flat_1x1.cpp` | `325354b7a42252f107f04582c0115f7274a8d022fed95f4bd036702b21e3ef28` |
| `matmul_flat_1x4.cpp` | `28aa9ac70edbe2bc070df3b1ab0ee56a6dc5b33730e4310dc4c6b7927784ebad` |

## What the five programs actually request

`tile_x`, `tile_y`, and `tile_r` below are source constants, before any later AMX
shape normalization. Accumulator counts are source tile factors, not claims about
final physical register allocation. Halide reorder lists are innermost first.

| Active source | Operand and result types/layout | Reduction length; tiles; accumulators | Relevant schedule evidence |
|---|---|---|---|
| [VNNI 1×1, lines 31–77](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/instrsel-benchmarks/matmul_vnni_1x1.cpp#L31) | BF16 × BF16 → f32; B is `(r%2, x, r/2)`, stride 2 | K=32; `(8,8,4)`; one accumulator tile | Update reorder `rri,rxi,ryi,rro,x,y`; no A/B wrapper in AMX memory |
| [VNNI 1×4, lines 31–94](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/instrsel-benchmarks/matmul_vnni_1x4.cpp#L31) | BF16 × BF16 → f32; same packed B layout | K=4096; `(8,8,4)`; **X_ACC=1, Y_ACC=2** | Update reorder `rri,rxi,ryi,cy,cx,rro,x,y`; `cx`, `cy` unrolled; no explicit A/B AMX preload |
| [VNNI preload RHS, lines 30–109](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/instrsel-benchmarks/matmul_vnni_1x4_preload_rhs.cpp#L30) | **signed i8 × unsigned i8 → i32**; B is `(r%4, x, r/4)`, stride 4 | K=4096; `(8,8,8)`; X_ACC=1, Y_ACC=4 | Same update order as 1×4; explicit `B.in().compute_at(mm,rro).store_in(AMXTile)` and three vectorized dimensions |
| [Flat 1×1, lines 20–71](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/instrsel-benchmarks/matmul_flat_1x1.cpp#L20) | f32 input buffers converted to BF16 in A/B Funcs, multiplied into f32; B is `(x,r)` | K=128; `(16,16,32)`; one accumulator tile | A/B conversions `compute_root().tile(...)`; update order matches VNNI 1×1. These root buffers are **not** requested in AMX memory |
| [Flat 1×4, lines 20–80](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/instrsel-benchmarks/matmul_flat_1x4.cpp#L20) | BF16 × BF16 → f32; B is `(x,r)` | K=128; `(16,16,32)`; **X_ACC=1, Y_ACC=2** | Same update order/unrolling as VNNI 1×4; no explicit A/B AMX preload |

Consequences directly supported by source:

- The `1x4` filenames do not describe their active two-accumulator constants.
- Every program contains `.reorder`; that spelling alone does not identify the
  table's loop-reordering experiment. Both `1x4` schedules keep `rro` outside
  `cx`/`cy` in the update nest.
- Flat 1×1's root conversion buffers are not Intel-style A-tile staging.
- The preload-RHS file also defines an inactive BF16 routine at lines 120–199.
  [Main, lines 201–208](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/b99cf0c6400e954a278f697bf3a0596ac3fa4f25/instrsel-benchmarks/matmul_vnni_1x4_preload_rhs.cpp#L201)
  comments out that call and invokes integer `matmul`. Its “bf16” printed banner
  is misleading. Enabling the inactive routine is another graph/type variant,
  not evidence of a missing A-preload or loop-order table cell.

## Seven-cell mapping, with evidence grades

| Supported paper cell | Existing source candidate | Grade and remaining gap |
|---|---|---|
| Reference / VNNI | `matmul_vnni_1x1.cpp` | **Structural candidate.** Packed BF16 multiplication with a single AMX accumulator; no author-provided table mapping. |
| Reference / standard | `matmul_flat_1x1.cpp` | **Structural candidate.** Standard-layout multiplication with one AMX accumulator; source conversion stage differs from the other flat program. |
| Loop reordering / VNNI | `matmul_vnni_1x4.cpp` often looks like the intended candidate by elimination | **Unmapped as a distinct loop-order test.** It changes K and accumulator multiplicity; its K-tile loop is outside accumulator loops. No controlled alternate order is selectable. |
| Loop reordering / standard | `matmul_flat_1x4.cpp` by the same inference | **Unmapped as a distinct loop-order test.** It changes input representation and accumulator multiplicity; same unresolved order issue. |
| Preloading A / VNNI | None in the five active sources | **Missing active source configuration.** No A wrapper is stored in AMXTile. |
| Preloading A / standard | None in the five active sources | **Missing active source configuration.** `A.compute_root` in flat 1×1 is ordinary conversion storage, not the required tile preload. |
| Preloading B / VNNI | Active integer `matmul` in `matmul_vnni_1x4_preload_rhs.cpp` | **Direct feature match.** Explicit source comment and B AMXTile staging. Native optimization and ordinary replay passed in the 34-case batch; exact paper attribution beyond this feature remains separate. |

Do not report “five of seven paper cells reproduced.” Successful execution of the five artifact programs does not establish
the seven-cell correspondence. A safe inventory records the two absent
A-preload cases and two unresolved loop-order cases separately, while preserving
all five genuine artifact programs. Absence of an explicit A-preload request is
not proof that later compiler optimization never hoists or reuses an A load;
that requires inspection of actual generated IR.

## Intel schedule comparison and concrete reconstruction candidates

The separately consulted official [Intel manual v050, §20.5.4–20.5.5.1,
pp. 20-10–20-12](https://cdrdv2-public.intel.com/821612/248966-Optimization-Reference-Manual-V1-050.pdf)
distinguishes the reference's K-outer accumulator nest (Example 20-8), a
K-innermost alternative (20-9), A-tile preloading (20-10), and swapped accumulator
order with B-tile preloading (20-11). A preload loads a tile array before the
other accumulator loop. The earlier [v048, pp. 20-15–20-17](https://cdrdv2-public.intel.com/671488/248966-Software-Optimization-Manual-V1-048.pdf)
uses examples 20-4 through 20-7 for the corresponding discussion. These numbers
are not interchangeable. The v050 content was read through Intel's indexed
excerpts because direct PDF fetching exceeded the web tool's size limit; it has
not been asserted byte-identical to the paper's cited May 22, 2024 edition.

**Proposed adaptations, not discovered author flags or verified implementations:**

1. Retain both existing `1x1` programs as reference candidates. Keep both current
   `1x4` programs as artifact cases rather than silently relabeling or replacing
   them. Record their constants above exactly.
2. Make a separate copy of each `1x4` source with a controlled K-loop-order
   variant. Change only the update list from
   `rri,rxi,ryi,cy,cx,rro,x,y` to `rri,rxi,ryi,rro,cy,cx,x,y`, preserving types,
   K, tiling, vectorization and unrolling. This gives an explicit contrast in
   K's location. The input algorithm is unchanged, but the resulting compiler
   graph and instruction schedule must be inspected. Whether that contrast is
   precisely the authors' table row remains an attribution uncertainty.
3. Make separate A-preload copies for each layout, starting from the BF16
   `1x4` sources. The source-supported mechanism to try is the A analogue of
   the existing B wrapper: `A.in().compute_at(mm, rro)` stored in `AMXTile`, with
   its two dimensions vectorized and, where necessary, tiled into legal shapes.
   Preserve B's original layout and the multiplication algorithm. Capture
   pre/post-lowering IR to prove the A load is staged outside the intended
   accumulator loop. The exact legal tiling is a native canary question; a
   `.store_in` line alone does not establish successful preloading. The existing
   X_ACC=1 setting also makes reuse of A across the x-accumulator axis degenerate;
   a separately declared X_ACC=2, Y_ACC=2 variant would exercise that reuse, but
   is another graph-changing configuration, not an inferred paper parameter.
4. Preserve the active integer VNNI B-preload case. If BF16 coverage is desired,
   separately enable the already-written BF16 routine with its own source hash,
   main-call adaptation, and output contract. Do not count its data type as a
   second schedule/layout cell.

Suggested new inventory identities (names only):
`hardboiled-amx-{vnni,standard}-k-inner` and
`hardboiled-amx-{vnni,standard}-preload-a`.
They would initially be `source-adaptation-proposed`, linked to their original
source and a reproducible patch. There are no existing `-D`, environment, or
runtime flags implementing these names. Using these four additions would
retain **nine source requests** (five originals plus four adaptations), while
the paper still has seven supported cells. Hash-identical graph outputs can be
accounted as aliases after genuine capture, not deduplicated in advance.

The gate is source/IR schedule correspondence, complete AOT parent success,
all reached sidecar inputs and actual outputs, and ordinary checks for every
selected root. No AMX device/SDE execution is needed for this acquisition goal.
Hardware functional correctness from the paper remains a separate claim.

## Historical and upstream checks

The live [main branch](https://github.com/yihozhang/cgo2026-hardboiled-artifact/tree/main)
still resolved to `b99cf0c6400e954a278f697bf3a0596ac3fa4f25` in the public branch API
during this audit. The last AMX-directory modification is
[`19123bff`, “fix amx-flat_1x4”](https://github.com/yihozhang/cgo2026-hardboiled-artifact/commit/19123bff5143d23a76fa611f7048e62c5bc055c4),
already included in the pin. No newer main-branch mapping appeared.

The [November 18 removal](https://github.com/yihozhang/cgo2026-hardboiled-artifact/commit/97fcc7b9f4a3a3380f64a59ed105b7174711061e)
deleted two relevant historical files from its parent:

- [Standard preload B](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/10a2aee77f3e871e3d6f7270238847eea1c31c3c/instrsel-benchmarks/matmul_flat_1x4_preload_rhs.cpp#L11)
  explicitly says it is failing, and stages B at `rro` in AMXTile. This is a
  useful source for the unsupported table cell, not a missing successful case.
- [VNNI 2×2](https://github.com/yihozhang/cgo2026-hardboiled-artifact/blob/10a2aee77f3e871e3d6f7270238847eea1c31c3c/instrsel-benchmarks/matmul_vnni_2x2.cpp#L13)
  uses X_ACC=2, Y_ACC=2 with the same K-outer update order and no explicit A
  preload. Restoring it does not by itself fill either missing A cell.

The older [initial AMX commit](https://github.com/yihozhang/cgo2026-hardboiled-artifact/commit/ed6a3d23f93d360ebfe071929d69c51834386477)
describes one-dimensional tile unrolling and RHS preload, consistent with the
source distinctions above. A bounded check of MatMul files on the
`yihozhang-amx-convolution` branch (`78adab2f…`) and
`yihozhang-temporary-0811` branch (`594e8f52…`) found no explicit `A.in()` or
A-preload implementation. Two other inspected old branch heads lacked the
`instrsel-benchmarks` directory. This is not an exhaustive search of every
historical revision and is not proof that no author ever wrote such a schedule.


## Public-source follow-up, 2026-09-25

A second independent read-only check found no newer mapping source. The artifact
main branch remains `b99cf0c6400e954a278f697bf3a0596ac3fa4f25`; its last
AMX-directory change remains `19123bff5143d23a76fa611f7048e62c5bc055c4`.
The paper remains arXiv v2. All five retained source hashes match this audit.
The one B-preload feature match and two reference candidates do not establish
exact historical cell/configuration identity.

Closing these obligations requires an author-provided Table I cell-to-source
mapping (including intended aliases), the A-preload implementations or original
patches, the precise loop-order variants, and graph-changing parameters such as
operand layouts, reduction length, tile/accumulator sizes and preload placement.
No author contact or substitute program was used.
