# Frozen primary-surface census

This checkpoint-0 census is pinned to
`853fbfd533a3f73b390de364d980f3f939427eae`. It is a static lowering census,
not a runtime-cardinality, performance, or checkpoint-0.5 pass claim. Unless a
paragraph is marked **inference**, counts and classifications come from accepted
source-aware `--mode desugar` output plus direct inspection of the pinned
sources.

The frozen corpus is:

1. `egglog/tests/math-microbenchmark.egg`
2. `egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg`
3. `benchmarks/pointer-analysis-small.egg` and
   `benchmarks/data/pointer-analysis-small/`
4. `egglog/tests/hardboiled_conv1d_32.egg`
5. `benchmarks/luminal-llama.egg`

Both source-aware binaries reported
`egglog 2.0.0_2026-07-28_853fbfd`. Normal and proof desugaring accepted all
five files. Eggcc requires `egglog-experimental`; Pointer requires
`-F benchmarks/data/pointer-analysis-small`.

## Lowered inventory

| Workload | Declared source surface | Normal resolved surface | Proof resolved surface |
|---|---|---:|---:|
| Math | 1 datatype, 13 variants, 24 rewrites | 1 sort, 13 constructors, 24 rules | 74 functions, 100 rules |
| Eggcc | 19 datatypes/69 variants, 9 sorts, 89 constructors, 70 relations, 17 functions, 516 rules + 135 rewrites | 98 sorts, 234 constructors, 18 functions, 651 rules | 1,334 functions, 2,261 rules |
| Pointer | 1 datatype/variant, 3 constructors, 24 relations, 14 rules | 25 sorts, 28 constructors, 23 inputs, 14 rules | 206 functions, 131 rules |
| Hardboiled | 10 datatypes/39 variants, 6 sorts, 38 constructors, 23 relations, 1 function, 107 rules + 68 rewrites + 22 birewrites | 39 sorts, 100 constructors, 13 functions, 219 rules | 586 functions, 803 rules |
| Luminal | 14 datatype sorts/112 variants, 5 relations, 12 functions, 491 rules | 19 sorts, 117 constructors, 1,646 functions, 491 rules | 7,140 functions, 6,508 rules |

Relations lower to hidden sorts plus membership constructors. Hardboiled's 12
globals lower to `() -> Stmt` functions. Luminal's 1,634 globals lower to
`() -> IR` functions, all `:no-merge :internal-let`.

## Workload classification

### Math

- The `Math` equality sort has binary/unary constructors plus `Const(i64)` and
  `Var(String)` (`math-microbenchmark.egg:1-17`).
- All 24 rewrites are unconditional (`:19-24`, `:27-53`). Seven terms seed the
  e-graph (`:54-66`) before `(run 11)` (`:67`).
- No explicit relations, custom functions/merges, containers, `(input ...)`,
  include, unstable-function surface, or active primitives beyond literals.
- The file has no `(check ...)`, so it requests no proof target itself.
- **Kernel inference:** `Add(a,b) -> Add(b,a)` at `:19` is the cleanest broad
  table-scan kernel. A reduced, backend-local fixture for that exact rule now
  passes a production `RuleSpec` main-versus-DuckDB differential. This does not
  imply that the complete Math source program lowers yet.

### Eggcc

- Main IR equality domains are at
  `eggcc-2mm-pass1.egg:10-39`; extraction terms are at `:75-87`.
- Reached built-in containers are `Pair Term i64` (`:267`), `Either i64 bool`
  and `Maybe` (`:546-549`), `Set Expr` (`:750-759`), and
  `Pair IVTPayload i64` (`:926-930`). Reached primitives cover pair
  construction/projection/pair-min, Maybe/Either construction/projection, and
  Set insert/intersect/union/length.
- Seventeen functional schemas use `old`, `new`, scalar min/max, bounded
  min/max, pair-min, and Maybe/Either min/max. Representative declarations are
  at `:88`, `:98`, `:223`, `:268`, `:498-499`, `:548-549`, `:654`, `:720`,
  `:758`, `:834`, `:875-876`, and `:929-930`.
- Reached actions include `let`, `set`, `union`, `subsume`, `delete`, and
  `panic` (`:100-107`, `:262`, `:949-951`). The initialization rule starts
  3,154 local `__tmp` lets at `:1005-1008`.
- There is no `(input ...)` or include.
- There is no `UnstableFn`, `unstable-fn`, or `unstable-app`. Six
  `unstable-fresh!` calls (`:900`, `:905`, `:910`, `:923`, `:938`, `:994`)
  macro-lower to ordinary typed constructors keyed by query variables and a
  call-site index (`egglog-experimental/src/fresh_macro.rs:66-126`).
- **Kernel inference:** `Bop + bop-of-type + HasType x2` at `:166-167` is a
  selective join; the CICM rule at `:945-946` is a later stress-wide join.

### Pointer

- Twenty-three extensional relations and matching `(input ...)` commands are
  at `pointer-analysis-small.egg:10-62`; the derived `alloc_matches` relation
  is at `:76`.
- Extensional fields are `String` except the `i64` index/count fields in
  `function_nparams`, `function_param`, and `call_instruction_arg`.
- `Allocation = A(String)` and three equality constructors are at `:64-68` and
  `:190`. There are no custom functions/merges, containers, unstable functions,
  or includes. Effects are relation inserts and `union`.
- The fact directory contains 23 headerless TSV files and 2,255 rows. Every
  file has 100 rows except `ret_instruction_value.csv` (55). There are four
  unary, sixteen binary, and three ternary files, no blank lines, and exact
  arity throughout. All numeric fields parse as integers; observed ranges are
  `0..7`, `0..6`, and `0..6`.
- **Kernel inference:** the five-way call/parameter join at `:168-176` is the
  cleanest genuinely selective bounded kernel. A reduced fixture source-pinned
  to that rule, including non-matching decoys and a fresh-row/old-row join,
  now passes a production `RuleSpec` main-versus-DuckDB differential. This does
  not imply that the complete Pointer source program lowers yet.

### Hardboiled

- Datatypes cover locations, operators, scalar/vector types, calls, inverted
  indices, and WMMA metadata (`hardboiled_conv1d_32.egg:7-58`, `:645-648`,
  `:1483-1487`).
- Reached built-in containers are `Vec<i64>` and `Vec<Expr>` (`:56-58`); the
  reached vector primitive is `vec-of` (for example `:1055`).
- The sole custom function is `LanesInType(Type) -> i64 :no-merge` (`:251`).
  Reached actions include local lets, `set`, `union`, `subsume`, and `panic`
  (`:251-304`, `:888`, `:1627-1658`).
- `I64ExprBinFn = UnstableFn((i64,i64,Expr,Expr)->Expr)` is declared at `:644`
  and used as a relation column at `:671-695`. There is no `unstable-fn`
  construction or `unstable-app`; therefore this frozen file reaches only the
  schema, not dynamic unstable-function construction/application.
- No input or include. Twelve global `Stmt` seeds are at `:2090-2101`; the
  schedule/check are at `:2106-2134`.
- **Kernel inference:** `IsExpr(Bop(...))` at `:228` is broad; the WMMA pattern
  at `:1627-1658` is selective and join-heavy.

### Luminal

- Four `datatype*` blocks define the expression/list/dtype, IR/op/list, sigmoid,
  and GLUMoE domains (`luminal-llama.egg:20-62`, `:138-215`, `:511-516`,
  `:4494-4516`). `EList` and `IList` are ordinary recursive datatypes, not
  built-in container values.
- All 12 custom functions use `:merge new` (`:120-126`, `:215`, `:516`,
  `:4518-4524`). Five relations are at `:413`, `:1631`, `:4861`, and
  `:5507-5508`.
- Reached actions include `let`, `set`, `union`, `subsume`, and `delete`
  (`:66-68`, `:221-230`, `:246-264`). Scalar primitives include integer and
  floating arithmetic, remainder, min/max, comparisons, and bitwise `&`
  (`:66-74`).
- The 1,634 `t*` globals begin at `:6663`; source-aware lowering confirms each
  is a nullary IR function. `Input` is the IR constructor declared at `:143`,
  not an `(input ...)` command.
- No built-in containers, input/include, or unstable-function surface.
- **Kernel inference:** expression commutativity (`:64-65`) is broad; deep
  batch-matmul constraints (`:367-411`) and kernel specialization (`:246-318`)
  are selective.

## Proof encoding classification

No frozen source declares proof relations. Proof lowering injects ordinary
typed `Unit`-output relations and minted IDs for Fiat, Rule, MergeIdx,
MergeRow, Trans, Sym, Congr, CongrAll, ContainerNormalize, Eval, AST, and list
nodes (`egglog/src/proofs/proof_encoding_helpers.rs:408-460`). Per-sort
union-find/proof mappings are ordinary functions
(`egglog/src/proofs/proof_encoding.rs:560-590`), and every user function gets
a term table, FD view, and delete/subsume marker tables (`:665-780`).

Therefore proof rows must use the same typed schema, input, matching, merge,
generation, and subsumption machinery as every other row. The backend needs no
proof-aware durable metadata or storage branch. Eggcc's user-visible `Term`,
`ListTerm`, and `ExtractedExpr` types are optimization data, not injected proof
relations.

## Checkpoint decision

The five workloads' typed schemas and rule shapes are representable at the
current backend SPI. This is not a claim that checkpoint 1 executes the full
programs: production `RuleSpec` lowering admits only nonempty Live table bodies
with typed variables/literals and exactly one Set into a one-output
`MergeFn::Old` or `MergeFn::AssertEq` target. The reduced Old subset passes the
Math and Pointer differentials described above. One-output AssertEq now checks
intra-stage and existing-row conflicts set-wise in DuckDB before ordinal
consolidation; equal duplicates remain idempotent. Ordinary function tables
have no primary/unique constraints, singleton column, or ART indexes.

Table registration now retains schema, output and identity counts, default,
the complete recursively validated merge tree, subsumption, and name.
Structurally valid merge plans outside the two executable one-output policies
register as explicitly deferred capabilities; native input and one-Set rules
reject a write to them during preflight. This lets all five proof-mode public
paths register their common 23-table prefix (21 AssertEq, one Old, and one
two-output identity Block) without claiming the deferred Block is executable.
The first remaining public failure is the generated `uf_path_compress` rule,
whose four-action head and `!=` primitive are intentionally outside this
slice. The static census still reveals no dynamic `UnstableFn`
construction/application, so it remains schema-only deferred.

The source programs' ordinary scalar declarations use `Id`, `Unit`, `bool`,
`i64`, `f64`, and `String`, but that was not the complete proof-mode storage
surface. Proof instrumentation reaches `BigInt`, `BigRat`, and experimental
`Rational` columns on the public paths. Checkpoint 1 stores DuckDB-representable
values exactly as `BIGNUM`, `STRUCT(numer BIGNUM, denom BIGNUM)`, and
`STRUCT(numer BIGINT, denom BIGINT)` respectively; an integer outside DuckDB's
finite `BIGNUM` domain fails transactionally rather than being rounded or
truncated. Construction uses canonical closed SQL expressions; reads project
canonical decimal text only at the low-volume Rust boundary because safe public
`duckdb-rs` has no BIGNUM value variant. Input literals use one schema-directed
encoder: numeric casts are formatter-produced, and String bytes use UTF-8 hex
plus DuckDB `from_hex`/`decode`, so input ingestion requires no bound parameters
and cannot interpolate user text.

One current `(input ...)` command becomes one heterogeneous `add_values` batch
containing several encoded function IDs. Typed vertical tables therefore use
one transaction with one generated `INSERT ... SELECT FROM (VALUES ...)`
statement per physical target. The scaffold records that boundary rather than
using a host effect dispatcher. `Backend::add_values` is fallible on this
branch: DuckDB returns the transaction result directly, DD returns its native
apply error, and the reference bridge applies each supplied batch atomically
after quiescing pre-existing staged work. The frontend propagates an input
failure before logging success. This supersedes the checkpoint-0 void-method
limitation recorded by the original census.

## Command evidence

All commands ran from the repository root under `/opt/homebrew/bin/gtimeout
115s`; no temporary artifacts were retained.

| Case | Command suffix | Exit | Real time |
|---|---|---:|---:|
| Math normal | `target/debug/egglog --mode desugar egglog/tests/math-microbenchmark.egg >/dev/null` | 0 | 0.34s |
| Eggcc normal | `target/debug/egglog-experimental --mode desugar egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg >/dev/null` | 0 | 0.43s |
| Pointer normal | `target/debug/egglog -F benchmarks/data/pointer-analysis-small --mode desugar benchmarks/pointer-analysis-small.egg >/dev/null` | 0 | 0.27s |
| Hardboiled normal | `target/debug/egglog --mode desugar egglog/tests/hardboiled_conv1d_32.egg >/dev/null` | 0 | 0.38s |
| Luminal normal | `target/debug/egglog --mode desugar benchmarks/luminal-llama.egg >/dev/null` | 0 | 0.39s |

The corresponding `--proofs --mode desugar` commands all exited 0; their
five-command batch completed in 1.8s. Pointer again used `-F`; Eggcc again used
the experimental binary. A diagnostic Eggcc run with the generic binary exited
1 because it lacks `pair-min-by-second-i64`. A diagnostic Pointer proof run
without `-F` exited 1 because `function.csv` could not be found; both were
superseded by the accepted commands above.

Fact-directory checks used `awk -F '\t'` per file for row/arity/blank counts,
`wc -l` for the 2,255-row total, and integer regex/range checks for the three
numeric columns. All exited 0 in approximately 0.1s; the directory was 396 KiB.

### Checkpoint-1 public boundary

After the AssertEq/config/codec slice, the final feature-enabled nonbundled
build completed in 6.43s. Fresh direct invocations used
`target/debug/egglog-experimental --backend duckdb --proofs --mode no-messages`
with the source path below; Pointer also used its frozen `-F` directory. On
macOS, `DYLD_LIBRARY_PATH` pointed at `target/debug/deps`, which contains
Cargo's downloaded `libduckdb.dylib`. Every invocation ran under the
checkpoint's 110-second external cap and exited 1 at the same intentional next
compiler boundary:
`DuckDB rule @uf_path_compress must contain exactly one Set action, found 4
actions`. No case failed during the common table prefix.

| Workload | Wall time |
|---|---:|
| Math | 0.388s |
| Eggcc | 0.418s |
| Pointer | 0.465s |
| Hardboiled | 0.467s |
| Luminal | 0.408s |

### Native path-compression slice

The next vertical slice compiles the shared path rule by typed topology rather
than by any generated rule, table, proof-sort, or variable name. Admission
requires two Live reads of the same one-key/two-value identity-guarded table,
typed `!= (Id, Id) -> Unit`, the ordered head fresh/alias/Trans/UF actions, and
the exact typed merge vocabulary (`proof-of-min/max`, `ordering-min/max`, two
fresh requests, Sym, Trans, and the recursive displaced-parent Set). Opaque
external-function IDs are never executed or used for dispatch.

Execution materializes all scheduled matches before effects, assigns canonical
match ordinals after binding deduplication, reserves every head ID before any
collision ID, and uses per-target temporary queues. Each SQL fold pass selects
at most one candidate per logical key. Every target drains logical wave `w`
before Block-generated UF candidates at `w + 1` become eligible. Equal identity
keeps the complete old tuple and skips all Block effects; an effective old-min
collision still emits Sym/Trans and a displaced edge even when the owner row
remains byte-identical. Rust schedules statements and reads scalar counters,
counts, and booleans only; it never enumerates matches, effects, or merge rows.

The focused nonbundled library gate passes 38/38 tests, including renamed
non-proof IR, new-min and old-min folds, equal-identity payload retention,
same-key candidate ordering, multi-target/global wave draining, multi-wave
self-writes, deterministic allocation, late AssertEq rollback and ID reuse,
head/collision exhaustion, corrupt-owner rejection, and scratch cleanup.

After a fresh feature build, all five capped public proof-mode probes moved to
the same later fail-closed boundary:
`DuckDB rule @delete_rule must contain exactly one Set action, found 2 actions`.
Fresh wall times were Math 0.286s, Eggcc 0.292s, Pointer 0.251s, Hardboiled
0.317s, and Luminal 0.245s. These are boundary-probe times, not workload
benchmarks or a performance claim.
