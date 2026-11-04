# Fresh EggCC consumer discovery

Setup-only, 2026-10-17. This is a source-backed proposal, not a validated integration or a new compiler result. No build, test, compiler invocation, benchmark, API call, worktree, or commit was performed. Only this file was authored. The completed `eggcc-encoding-impact` evidence was read for constraints and left unchanged.

## Source authority and ranking

Fresh reads used `/Users/saul/p/wt/eggcc/encoding-impact`, HEAD `15ee7cbabe70d3b2e72d796bcf81cc2604626e7b`. `git status --short` showed the existing dirty dependency manifests, `dag_in_context/src/lib.rs`, compiler entrypoints/utilities, observation implementation/tests, and `tests/encoding_impact/`; they were preserved. References below name that integrated worktree. The surrounding encoding workspace HEAD was `fdd4eac12c1318c578badbf5d1299e0e3eb4e6c0` with extensive existing changes, also preserved. The current facts file has twelve accepted facts; its metadata filename is `facts.meta.json`, rather than `meta.json`.

The strongest first slice is **C6's existing type-mismatch consumer**, with a structural disequality replacement/comparison. It can demonstrate a richer joint integration without claiming a missed default error, a new source bug, or speedup. C4 has a sound restricted law but substantial existing-rule redundancy. C5 has a real optimization endpoint but requires a new scoped value bridge. C3 remains a larger reserve with no fresh eligible producer established.

| Rank | Family | Concrete consumer | First disposition |
| --- | --- | --- | --- |
| 1 | C6 immutable type structure | `ExpectType` plus `HasType` causes the existing mismatch panic; loop in/out type-list checking is a second endpoint | Proceed to a bounded existing-schema proposal, keeping helper normalization and honest baseline equivalence |
| 2 | C4 fixed-split tuple cancellation | Generated `Get` equalities feed passthrough and tuple reconstruction | First screen for a useful equality absent after existing projection closure; reject early if redundant |
| 3 | C5 scoped false-Eq values | Produce a known-false inner Eq, then use existing `interval-rewrite` conditional elimination | Semantic design gate first: pointwise total values, scope separation, and bottom; no Expr disequality shortcut |
| 4 | C3 immutable live pointer keys | Existing `NoAlias` write/load commute, followed by forwarding | Defer unless a concrete fresh/live producer reaches a blocked consumer; static allocation IDs do not suffice |

## 1. C6: structural type disequality in the existing mismatch check

### Existing producer to consumer edge

The declaration and behavior already exist:

- [`type_analysis.egg:31`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:31>) declares `ExpectType(Expr, Type, String)`. Lines 32–38 panic when an expected and actual `HasType` value have different current IDs, with an explicit comment that this requires saturating type helpers.
- [`type_analysis.egg:565`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:565>) turns a real `Function(name,in,out,body)` into `ExpectType(body,out,...)`. Calls similarly produce an argument expectation at 574–580; writes produce one at 355–359. These are concrete compiler checks, rather than a new standalone query.
- Actual types come from `Arg` at 498–502, `Get` at 383–390, `Single` at 417–422, and `Concat` at 424–432. The `Get` and `Concat` rules deliberately create lazy `TypeList-ith` and `TLConcat` values and rely on helper normalization.
- [`schedule.rs:20`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schedule.rs:20>) runs type helpers, type analysis, indexing helpers, and error checking together. Preserve that order; no earlier-than-normalization benefit is established.
- The second existing consumer is [`type_analysis.egg:552`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:552>): a `DoWhile` with differing normalized input and output TypeLists panics at 558. This can exercise mismatch at a deeper tuple position.

The source front end also checks types. [`typechecker.rs:153`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/typechecker.rs:153>) rejects unknown function input/output types and asserts the body return type; lines 518–562 compare If branches and loop input/output tuples. After extraction, [`lib.rs:1095`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/lib.rs:1095>) typechecks the resulting program again. Therefore a deliberately malformed Egglog type-analysis fixture is **an internal compiler-consumer test**, not a valid-source baseline bug. Executable valid-source controls remain necessary for host integration.

### Law and bounded representation

Use the existing Type/BaseType/TypeList schema, not a new semantic Expr wrapper. [`schema.egg:13`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schema.egg:13>) defines four nullary base leaves (`IntT`, `BoolT`, `FloatT`, `StateT`), recursive `PointerT`, `Base`, `TupleT`, `TNil`, and two-field `TCons`. The Rust mirror derives structural equality and ordering for this immutable data at [`schema.rs:10`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schema.rs:10>). Ground finite types denote exact type descriptions, so the structural constructors `PointerT`, `Base`, `TupleT`, and `TCons` are injective. This does not claim anything about runtime pointer identities or values.

**Cross-constructor disjointness is additional semantic evidence.** It is not implied by injectivity or different constructor names. For complete ground-type structural mismatch, explicitly justify and seed only these tag cases over present normalized nodes:

- pairwise distinct nullary base leaves;
- each base leaf versus `PointerT(_)`;
- `Base(_)` versus `TupleT(_)`;
- `TNil` versus `TCons(_,_)`.

This is a finite schema-law inventory; do not turn raw current-ID inequality into seeds. Same-constructor differences then propagate through the marked constructors. Never mark `TLConcat`, `TypeList-ith`, or `TypeListRemoveAt` injective: append, indexing, and deletion are not injective. Their current legitimate normalization unions are [`type_analysis.egg:4`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/type_analysis.egg:4>)–8 and 17–20, and [`canonicalize.egg:122`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/canonicalize.egg:122>)–131. A source scan found no other direct rewrite/union of Type's structural constructors; this is a searched-source observation, not an all-program theorem.

`TmpType` is a deliberate helper sentinel ([`schema.egg:30`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schema.egg:30>)); substitution excludes it from mismatch checking at [`subst.egg:48`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/subst.egg:48>)–56. `Type::Unknown` and symbolic types also exist in Rust printing/construction ([`schema.rs:24`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/schema.rs:24>), [`to_egglog.rs:102`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/to_egglog.rs:102>)). Keep all three outside the first ground-fragment replacement; preserve helper/sentinel behavior. An absent witness is unknown, never evidence that a check passed. A general replacement needs a supported/fully-normalized domain check plus a defined unsupported path, or must retain the existing check outside that domain.

### Proposed connected inference and fair controls

First use a function expectation whose actual and expected tuple types agree except for a pointer's pointee at a non-head tuple position. Both contain the same surrounding tuple structure, tail, and StateT slot. The intended path is:

`IntT != BoolT` (explicit type-tag law) → `PointerT(IntT) != PointerT(BoolT)` (injectivity-backed forward disequality) → nested `TCons` mismatch (multi-argument structural propagation) → `TupleT` mismatch → `ExpectType`/`HasType` mismatch panic.

All parent and differing child values here are equality-sort values. The final query is necessary for the new consumer, and injectivity metadata is necessary for same-constructor forward propagation. Equal-output cancellation need not be artificially forced into this case: the accepted richer scope allows structural propagation/multiple arguments. If additional cancellation coverage is desired, keep it a secondary declared engine/representation check unless genuine compiler data needs it.

Compare: (a) existing normalized raw-ID mismatch checker, (b) equivalent direct/manual structural TypeDQ rules using exactly the same disjointness laws and helper schedule, (c) encoding-backed structural mismatch guard. The default checker is expected to reject the same known ground mismatch; no unique detector or performance advantage is currently supported. Do not preserve the baseline raw-ID guard *inside* the feature-contribution probe and then count its independent panic as encoding contribution.

Minimum planned checks:

- Positive mismatch through the actual Function→ExpectType/body→HasType edge; expected and actual top-level types must not receive an explicit parent disequality seed.
- Equality control with the same nested pointer tuple, including structurally different but helper-equivalent `TLConcat`, indexing, and TypeListRemoveAt forms that normalize to the same type.
- Differing head, differing tail, different length, pointer-vs-leaf, and Base-vs-Tuple checks as explicit coverage cases; the first deeper mismatch must traverse more than a unary leaf wrapper.
- Remove structural injectivity metadata: leaf seed remains known but final structural query becomes unknown and this consumer no longer reports mismatch. Remove the query/consumer bridge: same seeded type graph, no encoding-backed mismatch report. Record unknown/undetected as such, not accepted-type success.
- Missing leaf law, unresolved helper, symbolic/unknown/TmpType, and late normalization/union controls: preserve unknown or the existing deliberate sentinel path; never manufacture a witness or silently weaken the checker.
- Valid source programs containing pointer/tuple/call/loop types through the normal native passes with source/result execution where supported. A deliberately inconsistent nested type union is a separate corruption test, not a baseline source bug.

**First vertical probe and falsifier:** implement only the chosen `ExpectType` guard over normalized ground types and the shared leaf/tag witnesses, then require the nested mismatch and equal-normal-form control to reach the existing consumer correctly in baseline, Manual, and Combined modes. Stop or narrow if the structural query cannot distinguish the required normalized types, a legitimate helper union contradicts a seed, an unsupported form silently passes, or the consumer test merely injects an asserted final mismatch. Keep this a bounded existing-schema integration. A request for general inference over symbolic/recursive types, arbitrary pre-normalization acceptance, or a new type unifier would be a separate solver redesign.

### Term subfamily disposition

[`terms.egg:9`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/terms.egg:9>) computes an extracted syntax term and cost. At 11–12 and 23–26 it deliberately updates only for a lower cost to preserve timestamps. [`conditional_invariant_code_motion.egg:7`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/optimizations/conditional_invariant_code_motion.egg:7>)–20 indexes *equal* Term values across contexts to produce code-motion candidates. Its `!= e1 e2` filters Expr IDs, not semantic inequality. [`term-subst.egg:33`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/term-subst.egg:33>)–69 instantiate a syntax Term as an Expr; they do not identify syntax with denotation. This scan found no concrete Term-disequality consumer. Reject a Term annotation-only exercise as the first host case, and preserve the equal-cost update policy.

## 2. C4: fixed-split tuple cancellation, with an early redundancy gate

The interpreter implements flat append at [`interpreter.rs:400`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interpreter.rs:400>)–410, and schema.egg 158–172 forbids nested tuples. With matching finite pure tuple/context/type semantics, equal concatenated results and equal prefix lengths determine equal prefixes and suffixes. Empty and associative splits refute global binary Concat injectivity; [`canonicalize.egg:41`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/canonicalize.egg:41>)–51 explicitly equates these forms. Any encoding proposal needs fixed split per constructor/domain, not a freely cancellable split field.

The actual consumers are projected output equalities: [`passthrough.egg:5`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/optimizations/passthrough.egg:5>)–14 removes pure loop passthroughs; 41–50 removes shared If arguments. But current [`util.egg:58`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/util.egg:58>)–105 creates all leading projections and propagates them through Concat, then [`canonicalize.egg:98`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/utility/canonicalize.egg:98>)–107 reconstructs/merges subtuples. This is strong concrete redundancy evidence, not a proved global redundancy result.

Proposed first screen after plan approval: one real pass graph containing same-result equal-split tuple representations, asking which downstream Get/passthrough equality remains absent after that closure. Compare guarded manual cancellation with fixed-split encoding only if a consumer is blocked. A structural DQ observer without a genuine affected check does not rescue an absent optimization consumer. Negatives: unequal prefix lengths with equal total length, associative splits, empty tuples, wrong context/type, StateT/effects/divergence. Reject immediately if projection closure already supplies the useful equality or no real same-result pair exists. No such graph has been executed or counted during setup.

## 3. C5: scoped false-Eq reasoning into existing conditional elimination

Fresh source confirms the missing producer: [`interval_analysis.egg:379`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interval_analysis.egg:379>)–402 only transfers bounds from an Eq **true** branch; it provides no false-Eq disequality flow. A real consumer exists: a known-false Boolean bound folds to Const false at 78–85, and [`interval_analysis.egg:254`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interval_analysis.egg:254>)–260 eliminates the If using substitution. This is active in the normal helper/cheap-optimization schedule (schedule.rs 93–96 and 116–122).

A possible bounded proposal uses separate scope-local total-i64 values and unary constructors for *fixed* wrapping-add displacements. [`interpreter.rs:239`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interpreter.rs:239>)–244 defines wrapping Add/Sub, so each fixed displacement is a bijection; a semantic `Add(constant,value)` is not jointly injective. Proposed source-shaped chain: in the true branch of `(x+1)==(y+1)`, and false branch of `x==z`, fold `(y+2)==(z+2)` false. Equal fixed-shift outputs cancel x=y inside the scope; scoped x!=z gives y!=z; injective fixed-shift2 yields differing final operands; a guarded bridge sets only that inner Eq false, then the existing conditional elimination consumes it.

This is a new representation/bridge proposal, not an existing rule or validated missed optimization. Scope-local values must not contain cancellable unscoped Expr children; branch facts are pointwise constraints, not semantic inequality of Expr functions. Infeasible paths become explicit bottom and must not globally panic or leak equalities. The independent engine/semantics owner confirms the fixed-shift law but identifies a stronger integration blocker: current NE/EE assertions are global, and a scope field or a consumer guard after saturation does not prevent impossible-scope constraints from collapsing shared truth or leaking unions. The current query does not read an arbitrary scoped NotEqual relation. Truly isolated domains/egraphs or proved feasibility before assertions would require a separately reviewed bridge and bottom audit. This peer review is not a new compiler execution result.

Restrict any future proposal to total pure integer expressions and actual nested branch refinement; purity alone also includes Div and DoWhile (purity_analysis.egg 7–19 and 86–88) and is insufficient. Compare a direct scoped NotEqual/equality transfer with the same fixed-shift laws. Planned controls include feasible/impossible paths, wrong scope/input, unknown facts, different shifts, wrap endpoints, additional unresolved operands, cancellation off, forward injectivity off, and query/consumer off. Defer until bottom isolation is concrete; no compiler bridge is justified yet.

## 4. C3 reserve: immutable live pointer keys

[`mem_simple.egg:20`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/optimizations/mem_simple.egg:20>)–58 currently produces NoAlias only from bounded nonzero offset/difference cases, and 10–18 transfers it into If regions. [`mem_simple.egg:71`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/optimizations/mem_simple.egg:71>)–81 consumes NoAlias to commute write then load; 106–113 can then forward a same-address store. This is a concrete endpoint, but no fresh live-key producer has been found in this setup. The interpreter uses runtime `next_addr` at [`interpreter.rs:390`](</Users/saul/p/wt/eggcc/encoding-impact/dag_in_context/src/interpreter.rs:390>)–398 and ignores Alloc's static `_id`; a static site is not a live identity.

If revived, require immutable provenance/lifetime-aware keys, valid offsets, a common state/context, and actual blocked demand. Different overlapping sets/intervals/anchors/formals are insufficient. Direct/manual alias guards are the relevant control. Same pointer, zero offset, repeated allocation/calls, unknown/freeing calls, aliasing callers, scope leakage, and bounds violations are minimum negatives. Do not repeat the completed C2 kernel screen or infer that its result excludes this different domain. No new eligible workload or benefit is claimed.

## Checks performed, unknowns, and execution boundary

Performed: read accepted facts and prior constraints/candidate/consumer notes; lightweight memory registry search (no task-specific useful hit); `pwd`; `git status --short`; `git rev-parse HEAD`; `rg --files`; targeted `rg -n`; numbered source reads using `nl -ba`/`sed`. Searches covered schema/type producers/consumers/normalizers, Type/Term rewrite/union mentions, extraction indexing, tuple projection/reconstruction, Eq/context flow, active schedule, memory producer/consumer, and the interpreter's tuple/integer/pointer contracts. A search for nonexistent `dag_in_context/src/term.egg` and an initial prior-artifact search relative to the compiler root reported missing paths; correct files were then read. No resulting runtime evidence exists.

Outstanding: independent semantic review of the tag/injectivity/domain contract; exact query scheduling/API integration owned by the engine study; isolated treatment/control wiring and official gates owned by the harness study; whether any real pass produces a new type mismatch or tuple/branch opportunity; all correctness/output tests and any performance measurement. Parent facts/plan acceptance, rather than this note, decides execution authority. The primary proposal's expected contribution is a richer structural joint integration in an existing check, with explicit redundancy to current behavior.
