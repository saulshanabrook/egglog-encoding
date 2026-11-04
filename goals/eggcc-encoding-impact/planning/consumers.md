# EggCC consumers: read-only candidate discovery

Status: provisional goal setup, 2026-10-17. **No implementation permission or experimental result is implied.** No build, test, compiler invocation, benchmark, fetch, or previous-evidence edit was performed. This note ranks source-backed hypotheses and their first rejection checks; it does not claim search exhaustion.

## Source authority and scope

- `/Users/saul/p/eggcc`: HEAD `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. Tracked source is unchanged; pre-existing untracked `.serena/`, `.tmp/`, `experiments/`, `reports/` were preserved. Local `origin/main` is `a0bbec127f83249074a46af3fd6f6126c90fe0fb`; it was inspected without fetching. The baseline branch and upstream differ in bound/container representation and merge policy, so a finding at this HEAD is not automatically an upstream-current bug.
- `/Users/saul/p/wt/eggcc/encoding-study-retarget`: same HEAD plus the completed opt-in prototype. Its four dependency files and compiler feature files remain dirty as previously frozen; no new modification was made. The accepted full patch SHA-256 is `7ab6605cedbdb7e6e44fe7b4a6f1768033b1cb83bb7c4f3ad5aee391f64cb08c`; feature-only patch is `243298fbf886be35e9919d54a73bfa4a973e8da62c7a1361fcf455cc8b913183`. Frozen compiler is `d44a89c2f752aff60b2691d9e055f23e54215fc9dfa74a0db8e956afc713162e`, sibling Tiger `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`.
- `/Users/saul/p/wt/egglog-encoding/eggcc-study`: HEAD `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5` plus the existing staged semantic fixtures/harness. Only revision/status and prior semantic protocol documentation were read here; the semantics agent owns current encoding implementation discovery.
- Facts and authority: [accepted facts](../facts.md), [setup status](../STATUS.md). Applicable user AGENTS guidance was supplied in-session; no additional AGENTS file was found in the compiler checkouts or checked ancestry. A lightweight memory-registry search found no relevant prior EggCC study entry; conclusions below come from current local sources and identified prior study artifacts.

Unless explicitly labeled prototype, line references below name `/Users/saul/p/eggcc` at HEAD 15ee7cba. Default analysis is important: [helpers](</Users/saul/p/eggcc/dag_in_context/src/schedule.rs:93>) saturate canonicalization, interval analysis and `mem-simple`; the optional `memory` optimization is omitted from [cheap optimizations](</Users/saul/p/eggcc/dag_in_context/src/schedule.rs:116>). [Parallel scheduling](</Users/saul/p/eggcc/dag_in_context/src/schedule.rs:213>) has three native passes, with AST inlining in the last; inlining is [bounded to two iterations](</Users/saul/p/wt/eggcc/encoding-study-retarget/dag_in_context/src/config.rs:2>). Keep that schedule/extractor/configuration common between treatments. Included prologue text is not evidence that its ruleset runs.

## Ranked shortlist

Ranking combines cheap falsifiability, a real consumer, and plausible impact. “Potential” below is a hypothesis, not a measured signal.

| Rank | Candidate | Active consumer and proposed impact | Encoding relevance | First rejection gate |
| --- | --- | --- | --- | --- |
| 1 | Signed endpoint/overflow correctness screen | Active comparison canonicalization and interval folding; possible valid-input baseline failure | Separate bug search. Existing top-level Const guard may already detect contradictions; no incremental encoding claim without a distinct sound invariant/contribution | Full baseline output/panic reproducer with fixed-width defined inputs; reject if behavior is correct or only seeded annotations fail |
| 2 | Demand-driven same-root affine offset witnesses | Active `NoAlias` generation versus actual write/load commuting; possible compiler-analysis savings, then extra forwarding | Immutable keys plus a tightly guarded disequality bridge; compare against both materialized pairs and direct on-demand primitive guards | Establish real default NoAlias rows/work first; reject encoding advantage if direct primitive demand wins equally |
| 3 | Call-site fresh-region certificates for existing kernels | Cross-array dependencies in `csrmv`/`mat-mul`; possible load/store promotion or compiler-analysis impact | Distinct live region keys are sound independently of symbolic offsets, but require validated effect/call-context transfer | Screen actual three-pass IR for a hot blocked consumer and prove call/lifetime domain before extending keys |
| 4 | Fixed-split tuple cancellation | Active tuple indexing, passthrough, loop transformations; possible reduction of projection/equality work | A new *conditional* cancellation law, not blanket Concat injectivity | Equal prefix arity/context/types, concrete trigger in real pass, and comparison against existing projection closure |
| 5 | Remaining-child reverse congruence into scoped branch reasoning | Missing false-Eq information could reach equality tests or memory indices | Parent disequality + equal other siblings implies focused child disequality even for unmarked operators; compiler scoping is an additional obligation | Impossible branch must not reject/leak; an additional unknown sibling prevents focused inference; no compiler bridge until scoped bottom is handled |
| 6 | Immutable type/literal/term metadata audit | Active type errors and syntax-term indexing; likely lower-value detection or analysis replacement | Sound free data constructors, unlike mutable analysis results | Identify a mismatch missed by current normalization or a removable material cost; otherwise close as redundant |

## 1. Untested baseline arithmetic suspicions

[Canonicalization](</Users/saul/p/eggcc/dag_in_context/src/utility/canonicalize.egg:14>) equates `x >= y` with **both** `y < x+1` and `y-1 < x`; lines 27–38 similarly rewrite `<=`. No endpoint side condition is present. The [interpreter](</Users/saul/p/eggcc/dag_in_context/src/interpreter.rs:239>) explicitly gives Add/Sub/Mul wrapping i64 semantics, while comparisons use signed ordering. The comparison equations are not identities at signed endpoints. Canonicalization itself is identical in local origin/main; other relevant files have representation differences, so execution/revision attribution still needs its own receipt.

Cheap proposed inputs after goal approval:

1. A tiny well-typed Bril function printing constant `MAX >= MAX`, and the corresponding `MIN <= MIN`, with adjacent non-endpoint controls. Source answer is true. The two expansions can disagree; compile rejection or a changed answer would be a genuine baseline failure if reproduced without injected facts. The [existing top-level Const guard](</Users/saul/p/eggcc/dag_in_context/src/type_analysis.egg:41>) may already turn that disagreement into an unsoundness panic. Adding Int/Bool injectivity to trigger the same panic is **not** incremental encoding value.
2. A parameterized function using only `lt`, `mul`, branches and print: if `0 < x`, print whether `x*2 < 0`; otherwise print false. Proposed argument `x=9223372036854775807` should print true under wrapping i64; `x=1`, `0`, `-1` are controls. [Positive multiplication](</Users/saul/p/eggcc/dag_in_context/src/interval_analysis.egg:159>) infers product >=1 without an overflow bound. [Comparison bounds](</Users/saul/p/eggcc/dag_in_context/src/interval_analysis.egg:213>) and [false folding](</Users/saul/p/eggcc/dag_in_context/src/interval_analysis.egg:78>) could then make the printed comparison false. This is a predicted silent miscompile, **not an observed one**. Negative-product sign rules at 137–200 and Add/Sub interval endpoints at 90–120 are nearby follow-up hypotheses, not a request for broad fuzzing.

The first repro must use the compiler/interpreter's fixed-width semantics, valid i64 literals/arguments, terminating branches and no divide-by-zero, shifts, pointer arithmetic, invalid loads, or assumed mathematical unbounded integers. Confirm any native runtime claim separately against its arithmetic contract. Unary Neg/Abs are not folded into this probe: [their implementation](</Users/saul/p/eggcc/dag_in_context/src/interpreter.rs:337>) uses ordinary Rust negation/abs, so MIN/debug-overflow behavior is a separate question.

Run the exact archived input through original A, engine-only B and prototype Off with unchanged default passes/native Tiger; explicitly compare non-null source/result outputs. If any trigger appears, minimize it and use a targeted source-rule ablation only as a **diagnostic** to isolate the responsible equation, not as the main successful configuration. Preserve a correct small-value control. A baseline crash on a total valid source program can be a real bug finding; a mere wrong algebraic equation in this note is not yet a reproduced bug.

Encoding relevance gate: only claim contribution if a sound constructor/disequality invariant detects or localizes a real baseline failure beyond the existing guard, or if a sound encoding-based analysis demonstrably prevents it. Otherwise report the finding as a separate baseline correctness result and retain zero incremental encoding evidence. Do not annotate bound values or Const globally to manufacture a conflict.

## 2. Active NoAlias storage versus consumption: first encoding-led screen

The exact source producer/consumer boundary is unusually clear:

- [NoAlias](</Users/saul/p/eggcc/dag_in_context/src/optimizations/mem_simple.egg:8>) is a binary Expr relation. Rules at 20–58 produce pairs from nonzero interval bounds on an offset/difference, line 60 adds symmetry, and 10–18 propagates into If arguments.
- The active [write-then-load commute](</Users/saul/p/eggcc/dag_in_context/src/optimizations/mem_simple.egg:71>) is the only uncommented rule in this file consuming NoAlias. It enables existing [store forwarding](</Users/saul/p/eggcc/dag_in_context/src/optimizations/mem_simple.egg:106>) and [shadowed stores](</Users/saul/p/eggcc/dag_in_context/src/optimizations/mem_simple.egg:122>). A comment at 83–95 explicitly withholds the opposite commute because of weak-linearity dependencies.

Proposed domain beyond the completed constant-prefix example: for pointers to one live region, normalize offsets as a **shared integer anchor plus a literal displacement**, with witnesses tied to the same context and memory-consumer state. Within one fixed anchor, wrapping addition is a bijection: `i+c1` and `i+c2` differ for every i when distinct i64 displacements are interpreted modulo 2^64. A structural immutable key may store `(domain, region, anchor, displacement)`, but the consumer must explicitly equate domain/region/anchor before using key disequality. **Different anchor expressions alone do not establish different runtime addresses.** Also, `(anchor, displacement) -> anchor+displacement` is not jointly injective; never mark generic Add or Bop, or a semantic two-field Add wrapper, injective.

The memory bridge additionally needs representable/in-bounds final pointer offsets, common live provenance, integer memory, same contextual input, and no unmodeled free/call/effect crossing. The current [Pointer contract](</Users/saul/p/eggcc/dag_in_context/src/interpreter.rs:38>) checks bounds at access; [PtrAdd](</Users/saul/p/eggcc/dag_in_context/src/interpreter.rs:303>) is separate from wrapping integer addition. Do not use modular integer algebra as a blanket license for wrapping pointer offsets. Existing interval bounds themselves must first survive the overflow correctness screen. Unknown bounds/key equality are not nonalias. Keep constraints local and keep the proven prefix's one-step audit discipline where ordinal generation is retained.

Concrete applicable source forms, coordinated with the workload agent and then checked directly:

- [`csrmv` rowptr reads](</Users/saul/p/eggcc/benchmarks/passing/bril/mem/csrmv.bril:190>) are `p=rowptr+rid; load p; p=p+1; load p`. They match current nonzero-offset NoAlias production after the usual pointer normalization, but contain **no intervening write** needing the commute. This is a real candidate for avoided irrelevant analysis pairs, not a new load-removal claim.
- [`mat-mul` indices](</Users/saul/p/eggcc/benchmarks/passing/bril/mem/mat-mul.bril:82>) contain shared affine pieces `row*size+i` and `row*size+col`, but across different array roots. They do not by themselves satisfy the same-root candidate. The hot loop's actual memory benefit belongs to candidate 3 unless a captured pass exposes a narrower eligible form.

First low-cost experiment: one untimed default full-pipeline diagnostic per named existing input, recording actual NoAlias rows, their nonzero-offset proof shapes, demanded write/load pairs and graph/pass sizes; verify non-null source/result outputs. Reject a workload from this candidate if NoAlias work is absent/negligible, its pairs are needed elsewhere, the domain is not reached, or unrelated extraction dominates. Only then choose one original or clearly labeled source-derived/scale-controlled case with many produced pairs but few consumer demands. No row count alone satisfies the impact objective.

Fair controls must share the *same* normalizer, bounds, context/effect/liveness guards and source closure:

1. Original/default off.
2. Shared witnesses only, no new consumer.
3. Query at actual write/load demand, no materialized pointer-pair table.
4. Equivalent materialized manual pairs.
5. Strongest inexpensive control: the same demand guard using direct primitive displacement comparison (and direct bounds patterns where applicable), without the structural query.

A query/manual speed difference is not automatically due to injectivity: demand placement, added memory/type closure, query-based audits and the witness builder must be matched or reported separately. In particular, primitive displacements may make control 5 as good as or better than the encoding. Retain that rejection; do not hide it behind an unnecessarily expensive pair baseline. Expected impact is compiler/analysis time first. A generated-runtime claim additionally needs an actual newly chosen transformation inside a repeatedly executed region.

## 3. Fresh-region call certificates and loop-memory consumers

This is higher potential generated-runtime work with materially larger proof obligations, **not** an extension already covered by the frozen prototype.

- [`mat-mul` main](</Users/saul/p/eggcc/benchmarks/passing/bril/mem/mat-mul.bril:111>) creates arr1, arr2 and dest through three randarray calls at 117–119, then calls matmul. The hot [loop](</Users/saul/p/eggcc/benchmarks/passing/bril/mem/mat-mul.bril:82>) reads dynamic indices in arr1/arr2 and writes dest at 98–99.
- [`csrmv` main](</Users/saul/p/eggcc/benchmarks/passing/bril/mem/csrmv.bril:239>) allocates rowptr/colidx/values at 246–248, vec at 255, res at 259, interleaved with generators and print calls. [csr_spmv](</Users/saul/p/eggcc/benchmarks/passing/bril/mem/csrmv.bril:169>) zeroes res, then loads indirect input arrays and repeatedly loads/stores res[rid] at 201–211.

A valid live-allocation identity is an immutable injective key. Distinct **live** regions imply nonalias for their valid cells even when the within-region index is symbolic. Static Alloc ids and different formal parameter names are insufficient. Need closed-world, call-site-specific fresh-return/no-free/no-escape or effect summaries; preserve aliasing callers as a negative control. Specialization justified for one proved call site is distinct from adding NoAlias to a generic kernel ABI. Loops can allocate repeatedly, and merging histories must not silently give one pointer conflicting identities.

First screen actual pass-2 inlined/reconstructed IR for allocation visibility, state dependencies and blocked hot memory operations. The two-iteration AST inlining limit may hide allocators/generators; observe, do not assume. If no existing commute/forwarding sequence changes the hot loop, explicitly propose the necessary loop memory consumer (for example scalar promotion of res[rid] across reads of other proven-disjoint arrays). Existing `ExprIsPure` does not classify loads pure; no rule makes promotion automatic. Do not equate a key witness with generated-runtime speedup.

Cheap rejection gates: unknown calls/frees, potentially aliased formal arguments, cross-context provenance, unsupported loop-carried state, out-of-bounds or wrapping indices, missing hot consumer, or an equivalent simple alias guard giving the whole benefit. The raw `mat-mul`/`csrmv` inputs are candidates supplied by the harness domain; neither is currently certified eligible. Keep original workloads plus any labeled specialization/scale variant and the required accompanying changes as distinct treatments.

## 4. Fixed-split tuple cancellation: a new conditional law

[Concat](</Users/saul/p/eggcc/dag_in_context/src/schema.egg:158>) denotes flat tuple append. The associativity/empty rewrites at [canonicalize 41–51](</Users/saul/p/eggcc/dag_in_context/src/utility/canonicalize.egg:41>) still refute unconditional binary injectivity.

There is, however, a sound conditional cancellation law: if `Concat(a,b)=Concat(c,d)` and `len(a)=len(c)=k`, then their prefix k and remaining suffix are equal, hence `a=c` and `b=d`, **within matching contextual/type/tuple semantics**. Equal total lengths alone do not establish the split. Nonterminating/stateful tuple computations require the same evaluation/effect obligations as the existing projection rules; start with finite pure tuples, not StateT.

Real active surfaces are [Get generation](</Users/saul/p/eggcc/dag_in_context/src/utility/util.egg:58>) and [Add-Gets/Add-All-Gets](</Users/saul/p/eggcc/dag_in_context/src/utility/util.egg:74>), plus [passthrough](</Users/saul/p/eggcc/dag_in_context/src/optimizations/passthrough.egg:5>) and loop-invariant new tuple construction at [loop_invariant 65–84](</Users/saul/p/eggcc/dag_in_context/src/optimizations/loop_invariant.egg:65>). Existing projection closure may already supply every useful equality, so this is not a claimed new optimization.

Proposed first probe is a diagnostic of real existing pass graphs for same-result equal-split Concat pairs and repeated projection work. If present, compare an ordinary guarded cancellation rule against the same law represented by **fixed-arity/fixed-split immutable constructors** and the generic encoding. A varying split index cannot be an injected semantic field. Negative gates include an associative unequal-split counterexample, empty tuples, mismatched types/contexts, and state/divergence preservation. Reject if no actual consumer changes or generic type/indexing must still do the same work. Any reverse disequality inference here must distinguish congruence from forward injectivity; see below.

## 5. Remaining-child reverse congruence: valid gap, compiler bridge pending

The semantics agent reports that current reverse query reasoning is unary and marked-only, with a proposed generalized reverse-congruence query path. The valid rule is:

`f(a1,...,an) != f(b1,...,bn)` and `aj=bj` for every j except i imply `ai!=bi`.

This is contraposition of **congruence**, not a requirement that f be injective. It therefore applies to unmarked deterministic Add/Bop constructors in the equality theory. It does **not** license child disequality -> parent disequality for arbitrary Add, or result equality -> cancellation of all operands. For example, from `(a+b)!=(a+c)` one may infer `b!=c`; from `b!=c` one may infer unequal sums only when the fixed common-a addition is justified as a bijection in the intended value semantics. There is no justification for jointly injecting generic Bop fields.

Actual missing source-consumer information is visible at [interval_analysis 379–402](</Users/saul/p/eggcc/dag_in_context/src/interval_analysis.egg:379>): an Eq **true** branch receives equality-derived bounds, while no corresponding false-Eq disequality flow exists. A source-derived future case is an `if ((a+b)==(a+c)) ... else ...` whose else branch compares b/c or accesses same-base array offsets b/c. Reverse congruence could avoid a manual chain of NotEqual relations and feed an equality/memory consumer.

But this requires a scoped pointwise value model. Different Expr functions can coincide for some input; global expression disequality does not justify folding an Eq false or claiming runtime nonalias. Branch values must be transported into that branch's context, and a globally unreachable branch must not introduce a fatal contradiction or leak constraints outward. An `InIf` field on an injective wrapper is not a solution: reverse cancellation can leak the unscoped child. Query unknown must remain unknown. A compiler implementation is blocked until a concrete context-local, bottom-aware design is reviewed.

First vertical sub-probe is engine-only and owned by semantics: binary/ternary focused-child closure with all other siblings equal, no-focus/unknown-sibling cases, redundant paths, cycles and an unmarked Add-shaped constructor. Then use a finite source-derived branch replay that handles both feasible and impossible branches without compiler rejection. Only a successful replay plus an actual compiler consumer justifies integration. Do not claim an engine closure improvement alone is an EggCC impact result.

## 6. Immutable metadata reserve; explicit no-go cases

[BaseType/Type/TCons](</Users/saul/p/eggcc/dag_in_context/src/schema.egg:13>) describe free type data. Same-constructor field cancellation is defensible; cross-constructor disjointness is a separate tagged-data rule, not something injectivity alone supplies. [ExpectType](</Users/saul/p/eggcc/dag_in_context/src/type_analysis.egg:30>) currently relies on helper saturation before e-class `!=`, and many type/context guards compare raw IDs. An immutable, fully normalized type key could provide earlier mismatch witnesses or replace manual shape checks, but unknown must never silently accept an ill-typed expression. TypeList indexing still needs helpers; a claimed speedup requires showing work actually removed.

[Term](</Users/saul/p/eggcc/dag_in_context/src/schema.egg:256>) is a separate syntax tree used by [ExtractedExpr](</Users/saul/p/eggcc/dag_in_context/src/utility/terms.egg:7>) and [CICM indexing](</Users/saul/p/eggcc/dag_in_context/src/optimizations/conditional_invariant_code_motion.egg:6>). Free Term constructors may have structural injectivity even when their denotations do not. In particular, TermConcat is distinct from mutable Expr Concat. However no default Term disequality consumer was found in this scan; ExtractedExpr updates are cost-based and deliberately preserve timestamps at equal cost. Do not replace that guard with “different term” and resurrect the recorded performance problem. Reject this lead without a concrete material consumer.

| Tempting shortcut | Why excluded or conditional |
| --- | --- |
| Global Expr Bop/Top/Concat injectivity | Existing commutativity, Select erasure, tuple associativity/empties refute it. Candidate 4 is explicitly fixed-split and separately guarded. |
| Global Const cancellation, including context/type fields | Unreachable contextual equalities can be vacuous; shared literal payloads are not. Preserve top-level guard. Int/Bool literal wrappers are sound but their seeded-conflict result already exists. |
| Annotating I/MkIntInterval/PointsTo/Pointees in the current analysis chain | Real bound refinement unifies wide/narrow records. Prior [semantic audit](</Users/saul/p/wt/egglog-encoding/eggcc-study/benchmarks/eggcc-encoding/README.md:72>) gives a concrete falsifier. A versioned *new immutable snapshot* is a new representation and needs its own cost/equality proof; no revival by renaming. |
| Different points-to records -> DontAlias | [Optional DontAlias](</Users/saul/p/eggcc/dag_in_context/src/optimizations/memory.egg:369>) requires empty intersection. Overlapping unequal sets are not disjoint. Optional activation changes the treatment. |
| Replace Resolved-Pointees plus != with DQ directly | [Loop continuation](</Users/saul/p/eggcc/dag_in_context/src/optimizations/memory.egg:339>) is optional and currently waits for resolved records. Earlier distinction can disappear under refinement; this is the rejected record law, not a remaining-child fix. Immutable per-epoch snapshots would be a separate, lower-priority redesign. |
| Equality-sort builtin != as a semantic fact | It compares current IDs and may change after unions. Primitive i64 comparison is an appropriate direct control; raw Expr/Type ID inequality is not a persistent constraint. |
| Replace CICM's `!= e1 e2` by semantic DQ | The [guard](</Users/saul/p/eggcc/dag_in_context/src/optimizations/conditional_invariant_code_motion.egg:14>) filters candidate IDs in opposite contexts; it is not a claim of different runtime results. Replacing it can remove intended matches. |
| “Pure” implies safe speculative execution | [Purity](</Users/saul/p/eggcc/dag_in_context/src/optimizations/purity_analysis.egg:6>) includes Div and DoWhile. Prove totality/effect/divergence conditions separately. |
| Scale vsmul as a hot loop kernel | Harness reports no loop backedge; use mechanism-screened csrmv/mat-mul instead. This consumer scan does not reclassify the workload. |

## Proposed first vertical slice and stop rules

After plan approval, do the short arithmetic baseline screen first, keeping it explicitly separate from encoding attribution. In parallel, semantics can validate general reverse congruence in the engine; compiler integration waits for a scoped-value consumer.

For the first **encoding-led** compiler slice, screen the existing csrmv/mat-mul default graphs for candidate 2's produced-versus-demanded alias work and candidate 3's hot blocked memory dependencies. Start with the narrower demand/query/manual/direct comparison if actual analysis work exists. Otherwise document that rejection immediately and choose the call-site fresh-region slice only with a concrete eligible loop consumer and reviewed effect summary. Do not spend a build implementing keys for a kernel the seed cannot reach.

Every accepted case needs unchanged off behavior, positive and same-address/zero/wrap/context/effect negative controls, source-versus-optimized execution checks in the real three-pass native pipeline, emitted transformation checks, and repeated per-workload measurements only after those checks. Use a new worktree/evidence tree; do not alter the hash-bound prior study. Preserve native Tiger/reconstruction and actual non_weakly_linear/context defaults in every label. A source arithmetic bug, reduced replay success, eliminated load, fewer stored rows, or one faster observation alone does not establish incremental encoding speedup.

Stop setup at this shortlist. Search exhaustion is not established: applicability/cardinality diagnostics, fixed-width baseline reproduction, call-summary laws, actual loop promotion support, type/tuple consumer redundancy and scoped remaining-child transfer all remain open. Close each pursued candidate with a concrete reason/evidence before selecting the next; report neutrals/regressions and keep direct/manual controls.

## Read-only discovery command ledger

All commands below ran during setup, with no compiler/build/test execution. Source searches were limited to the compiler analysis domain; the two named kernel excerpts were read after the harness supplied exact forms. An initial `rg --files` against `/Users/saul/p/egglog-encoding/benchmarks/eggcc-encoding` reported that path absent; prior semantic fixtures were then read at the isolated encoding-study checkout.

```sh
# Facts/status and lightweight memory lookup (cwd /Users/saul/p/egglog-encoding)
cat /Users/saul/p/egglog-encoding/goals/eggcc-encoding-impact/facts.md /Users/saul/p/egglog-encoding/goals/eggcc-encoding-impact/STATUS.md
rg -n 'eggcc|encoding.*study|Concat|points.to|remaining.child' /Users/saul/.codex/memories/MEMORY.md
# Python read-only existence/read of AGENTS.md in /Users/saul, /Users/saul/p,
# /Users/saul/p/wt, /Users/saul/p/wt/eggcc, and the two compiler roots found none.

# cwd /Users/saul/p/eggcc
git rev-parse HEAD
git status --short
git log -5 --oneline
git rev-parse HEAD origin/main
git diff --name-only HEAD origin/main -- dag_in_context/src/schema.egg dag_in_context/src/optimizations/mem_simple.egg dag_in_context/src/optimizations/memory.egg dag_in_context/src/optimizations/memory.rs dag_in_context/src/interval_analysis.egg dag_in_context/src/utility/canonicalize.egg dag_in_context/src/type_analysis.egg dag_in_context/src/schedule.rs
git diff HEAD origin/main -- dag_in_context/src/interval_analysis.egg dag_in_context/src/optimizations/mem_simple.egg dag_in_context/src/optimizations/memory.egg dag_in_context/src/optimizations/memory.rs dag_in_context/src/type_analysis.egg
rg -n '!=|distinct|[Nn]o[Aa]lias|[Dd]isjoint|[Dd]isequal|[Nn]ot[Ee]qual|[Ii]njective|:merge|:no-merge' dag_in_context/src --glob '*.egg'
rg -n 'Add|Sub|Mul|Div|Shl|Eq|PtrAdd|wrapping|overflow|Infinite|Infinity|struct Pointer|enum Value' dag_in_context/src/interpreter.rs
rg -n '\(Neg\)|\(Not\)|\(Eq\)|\(Div\)|\(Shl\)|\(Shr\)|\(Bitand\)' dag_in_context/src/optimizations/*.egg dag_in_context/src/type_analysis.egg dag_in_context/src/utility/*.egg
rg -n 'Term(Const|Bop|Top|Uop|Concat|Single|Get)|TypeList|PointerT|IntInterval|PtrPointees|IntOrInfinity' dag_in_context/src --glob '*.rs' --glob '*.egg' | head -120
rg -n '^\(.*(union|rewrite).*Term|union .*Term|Term.*union|\(union .*\(TCons|\(union .*\(Base|\(union .*\(Int |\(union .*\(Bool' dag_in_context/src --glob '*.egg'
rg -n 'include_str|prologue|IntInterval|IntOrInfinity|PtrPointees|Cons-List' dag_in_context/src/lib.rs dag_in_context/src/optimizations/memory.rs dag_in_context/src/schema_helpers.rs
rg -n 'set \(ExtractedExpr|union.*(Term|Base|TCons|TupleT)|\(delete|\(subsume' dag_in_context/src/utility/terms.egg dag_in_context/src/schema.egg dag_in_context/src/type_analysis.egg

# Numbered reads: exact commands used (cwd /Users/saul/p/eggcc)
nl -ba dag_in_context/src/schema.egg
nl -ba dag_in_context/src/schedule.rs
nl -ba dag_in_context/src/optimizations/memory.egg
nl -ba dag_in_context/src/interval_analysis.egg
nl -ba dag_in_context/src/optimizations/mem_simple.egg
nl -ba dag_in_context/src/schedule.rs | sed -n '84,240p'
nl -ba dag_in_context/src/lib.rs | sed -n '180,315p'
nl -ba dag_in_context/src/optimizations/memory.egg | sed -n '1,210p'
nl -ba dag_in_context/src/optimizations/memory.egg | sed -n '210,455p'
nl -ba dag_in_context/src/type_analysis.egg | sed -n '1,160p'
nl -ba dag_in_context/src/utility/context_of.egg
nl -ba dag_in_context/src/utility/subst.egg | sed -n '1,90p'
nl -ba dag_in_context/src/interval_analysis.egg | sed -n '1,245p'
nl -ba dag_in_context/src/optimizations/peepholes.egg | sed -n '1,220p'
nl -ba dag_in_context/src/interpreter.rs | sed -n '15,48p;230,310p;360,440p'
nl -ba dag_in_context/src/optimizations/conditional_invariant_code_motion.egg
nl -ba dag_in_context/src/optimizations/switch_rewrites.egg | sed -n '1,115p'
nl -ba dag_in_context/src/optimizations/ivt.egg | sed -n '1,78p'
nl -ba dag_in_context/src/utility/terms.egg | sed -n '1,160p'
nl -ba dag_in_context/src/utility/canonicalize.egg | sed -n '1,150p'
nl -ba dag_in_context/src/optimizations/hackers_delight.egg | sed -n '1,155p'
nl -ba dag_in_context/src/optimizations/loop_strength_reduction.egg | sed -n '1,145p'
nl -ba dag_in_context/src/optimizations/memory.rs | sed -n '95,150p;165,240p;282,380p'
nl -ba dag_in_context/src/optimizations/memory.egg | sed -n '220,318p'
nl -ba dag_in_context/src/interpreter.rs | sed -n '325,360p'
nl -ba dag_in_context/src/optimizations/purity_analysis.egg | sed -n '1,112p'
nl -ba dag_in_context/src/interval_analysis.egg | sed -n '243,360p'
nl -ba dag_in_context/src/type_analysis.egg | sed -n '166,207p;271,339p'
nl -ba dag_in_context/src/utility/util.egg | sed -n '45,80p'
nl -ba dag_in_context/src/optimizations/passthrough.egg | sed -n '1,155p'
nl -ba dag_in_context/src/optimizations/loop_invariant.egg | sed -n '1,135p'
nl -ba dag_in_context/src/utility/util.egg | sed -n '74,125p'
nl -ba dag_in_context/src/optimizations/memory.rs | sed -n '373,410p'
nl -ba dag_in_context/src/schedule.rs | sed -n '235,285p'
nl -ba dag_in_context/src/optimizations/non_weakly_linear.egg | sed -n '1,180p'
nl -ba dag_in_context/src/lib.rs | sed -n '45,120p'
nl -ba dag_in_context/src/optimizations/body_contains.rs | sed -n '1,125p'
nl -ba benchmarks/passing/bril/mem/mat-mul.bril | sed -n '80,101p;111,132p'
nl -ba benchmarks/passing/bril/mem/csrmv.bril | sed -n '167,216p;239,263p'

# cwd /Users/saul/p/wt/eggcc/encoding-study-retarget
git rev-parse HEAD
git status --short
git diff --stat
rg --files dag_in_context/src | rg '(\.egg$|schema|analysis|optimiz|schedule|lib.rs)'
rg -n 'ExactLocalAddressMode|exact_local_addresses|exact-address|mem-simple|Conflicting' dag_in_context/src/lib.rs dag_in_context/src/optimizations/exact_local_addresses.egg
nl -ba dag_in_context/src/optimizations/exact_local_addresses.egg | sed -n '1,155p'
nl -ba dag_in_context/src/lib.rs | sed -n '380,421p'
rg -n 'FUNCTION_INLINING_ITERATIONS' dag_in_context/src

# cwd /Users/saul/p/wt/egglog-encoding/eggcc-study
git rev-parse HEAD
git status --short
# Other exact read paths, via cat/nl and Python read_text/json.loads:
# /Users/saul/p/egglog-encoding/goals/eggcc-encoding-case-study/{facts.md,source-map.md}
# /Users/saul/p/wt/egglog-encoding/eggcc-study/benchmarks/eggcc-encoding/README.md (nl, sed '1,215p')
# /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-case-study/retarget/prototype/final/checkpoint.json
# Python hashlib.sha256 of the source files listed below, and JSON projection of checkpoint hashes.
```

SHA-256 fingerprints of principal source files read at 15ee7cba (relative to `dag_in_context/src`):

```text
cbf82f3ddb22f60f364ee59e9ecf15ff2bd468f1d561ccb48e93e65a1fd0144b  schema.egg
9fbdab5fb1b738e7e93cad0cc2924a2a440d725903354c5c81a62ccfb8ec10e0  schedule.rs
ff363e2c10c57c2f3f79005d1f883f98091b3a32d023f43265b2ccbb89ce2647  interval_analysis.egg
9924928fa7927189c36f0b65b1cd68d5914850b7fc9e6cfe00f118e39a7c81de  type_analysis.egg
dd991459c2baa77f52ba03a0533147c4b134a2da0ed343f105cb049e415f0491  interpreter.rs
0940158a93383a76733b29512645453e5052d92e899f8130ec284ab7460e98fb  optimizations/mem_simple.egg
64261a909deffc8843acf71a901e013894b0db83d44e90dc31201bf964129c9e  optimizations/memory.egg
1f70760dd9840f6c50189beda65882b6b4fdda8911e70dfffef57a2d02c0cdf0  optimizations/memory.rs
aa7b40cba93c9d51133df7e94fa15f5a4fa3ec1f897c4eb4780f632a4e582c52  utility/canonicalize.egg
21a1e51e1425d1e42fde761ff761c5e8dd3c6e6544da92d9832a8ab1372580d4  utility/util.egg
a6f9ef681a4d551bb321c8d1f40c296b6c20a31920b4c7bbdf05406693d3bdec  utility/terms.egg
bf1e06431911d441cc64f7c4ec9bcdf76b57fbb0d72d3012ab2fb535168bf124  optimizations/purity_analysis.egg
171411a7c2993d47c07cd7cad3b4b1b60d52bb1cc1c49681a16baac42b9108dd  optimizations/conditional_invariant_code_motion.egg
```
