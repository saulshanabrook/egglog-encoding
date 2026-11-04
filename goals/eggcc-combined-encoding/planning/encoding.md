# Encoding discovery for a richer joint EggCC case

Read-only plan inputs, 2026-10-17. The twelve [accepted facts](../facts.md) govern this note. This is source discovery and proposed verification, not implementation permission or experimental evidence for a new case. Only this file was authored. Compiler consumer discovery belongs to the separate consumer circle; no compiler sources or workloads were scanned here.

## Source authority

Inspected checkout: `/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding`, branch `codex/eggcc-impact-encoding`, HEAD `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5`, with the retained E1 edits to `disequality.rs`, query tests/README, and untracked finite-oracle module. HEAD alone therefore does not identify the inspected implementation. The relevant start/end hashes agree:

```text
egglog-experimental/src/injectivity.rs                         3eccb019378d11155f8dce27dbd7a6780efe7a4a24233536a9cafc9607cfa281
egglog-experimental/src/disequality.rs                         8d56d53d87d0c21595b765f3aa6a9f7e3bc4752b4f87dfbcc651c108fe11bb3c
egglog-experimental/tests/injectivity_disequality.rs           3da93594215cf562380d0dd9c2391dcf5e184ff3214e60dac80b8c303816251c
egglog-experimental/tests/injectivity_disequality/oracle.rs    18dbe43bf36f530752bca6fd7fbc66222cd3b12d4a3073fe2cef1177a86674ec
```

Other directly read identities: `egglog-experimental/src/lib.rs` SHA `29cc7459d737e6289a68dff6d518ce8c7e82cb70e09c6762952e99f4816a4f07`; `src/scheduling.rs` SHA `629a24986aaef4d1c4cf5b2f7594a4749f89f9c019be9880df58a1c1ca2fce4a`; core `egglog/src/exec_state.rs` SHA `5edfc70985b6a862c55effe4b75016b3a9cc0433bac4c46204927aaf04af456e`. Accepted facts SHA `3dc28ac857ae943453bf257e208ae0df1746fe5461ace6b1fdf55d31cdec8c93`, metadata SHA `ce9e5552cac54307ee556c460278734c8ce22d1f1418fccd24abc8b65a6708c8`.

Source links below name this checkout. Prior semantic exclusions and candidate status are retained in [prior-constraints.md](prior-constraints.md); its SHA at this read is `31feeff5cc3237ffb6e282be7755821d861ce2ee6304238814cf39c389e96da0`. The old planning note's missing n-ary reverse inference has already been implemented; do not plan to rediscover or implement E1 again.

## Verified contracts and limits

| Mechanism | Current source behavior | Consequence for the new case |
| --- | --- | --- |
| Injectivity declaration | [Lowering, lines 114–169](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/injectivity.rs:114) handles constructor flags and datatype variants, including mutual datatypes. It clears the flag and generates ordinary rules; metadata installs only after successful declaration, lines 172–200. | A fresh immutable scalar representation can use existing syntax. The flag is a semantic promise supplied by the embedding, not an inferred theorem about EggCC expressions. |
| Equality cancellation | [Generated rules, lines 222–288](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/injectivity.rs:222) union every equality-sort field when two same-constructor results are equal. Each unequal primitive field independently panics. Rules include subsumed rows and run only when `injectivity` is scheduled. | Equality-sort cancellation can genuinely supply a sibling equality needed by a later query. The earlier Bool example exercised only the primitive branch. No cross-constructor disjointness is generated. |
| Marked signatures | Container arguments and non-unionable equality-sort fields reject before installation, lines 225–241. | Prefer finite free datatypes/scalar fields initially. `Vec`, `Set`, `Map`, `Maybe`/`Either` containers are not made injective by structural appearance. A guarded/conditional law cannot be expressed by a blanket flag. |
| Query result/type | [`disequality.rs:203–250`](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:203) accepts operands of the same unionable equality sort and returns Unit for a witness, undefined otherwise. No term/proof validator is registered. | Unknown is not equality. Direct primitive operands, container operands, non-unionable values and term/proof queries remain outside the interface. Native primitive comparisons can be internal witnesses or direct manual controls. |
| Forward structural disequality | [Lines 361–378](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:361) explore matching marked constructor rows: an equality-sort child adds a witness goal; a native mismatch succeeds immediately. | `a != b ⇒ F(a) != F(b)` needs a valid injectivity contract. Unmarked arithmetic/Expr constructors do not acquire it. |
| Remaining-child reverse congruence | [Eligibility, lines 298–322](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:298), [matching, lines 384–405](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:384): same constructor/position, all other canonical scalar columns equal. Output/focused child must be unionable equality sorts; siblings must be primitive or unionable equality sorts. Custom function tables, containers and private `@disequality-*` representation constructors are excluded. | `F(x,k) != F(y,k')` plus `k=k'` permits `x!=y` without marking F. Two unresolved positions, unequal siblings, different constructor names or missing rows do not suffice. |
| Read-only search/storage | [Lines 270–356](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:270) read explicit assertions and marked metadata, build a per-call parent index, and use typed visited goals; [assertion probes, lines 413–444](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:413) read NEE/EE without creating support. | No derived-pair table, parent application, union or persistent query cache is added. Existing observation/witness/assertion rows still cost storage. Per-call scans/indexing and parent row cross-products can be expensive; no performance advantage follows from the storage contract. |

The public factory [lib.rs:150–169](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/lib.rs:150) already selects NEE/EE and core/extended scheduling; extensions include injectivity at line 196 and disequality at line 168. Existing `parse_and_run_program` accepts initialization, schedules and checks. A first bounded joint case needs no new core API, proof validator, persistent index, materialization command, or generic closure facility.

## Structural forward reasoning can qualify without scheduled cancellation

Consumer-circle interim reports identify actual type-mismatch consumers (`ExpectType`/`HasType`, and loop input/output TypeList checks), with no demonstrated missed default mismatch. These compiler details are coordination inputs, not a duplicate fresh compiler scan. The current raw-ID guard already catches distinct normalized types; a richer integration can qualify under the accepted facts without claiming new coverage, provided both the injectivity contract and disequality query feed the actual check.

One source-shaped **illustration**, not an authorized annotation, is explicit justified `IntT != BoolT` leaf constraints plus marked free `TCons` and `TupleT` constructors. A query on `TupleT(TCons(IntT,TNil))` versus `TupleT(TCons(BoolT,TNil))` follows the leaf constraint forward through two equality-sort fields and supplies the mismatch consumer. This is richer structural propagation; it need not execute equality cancellation or E1 reverse inference. Both leaf names have the same BaseType sort, but their distinct constructor names alone are not a query witness. The explicit leaf constraint needs its own semantic justification, and the compiler owner must first audit all actual unions/normalizations of the selected constructors. Do not mark `TLConcat`, custom merge functions, mutable type approximations, or general analysis records on this basis.

Controls for this route keep the same normalized types and leaf constraints: existing/raw check, structural query with relevant annotations, the same query with those annotations removed, and equivalent constructor-specific manual mismatch propagation. Annotation removal should lose the structural query witness unless another independent path exists; unknown or missing leaf facts must not invent one. A manual rule reaching the same result is expected. If the old check already rejects exactly the same mismatch, describe the outcome as validated integration or representation/rule replacement, not a new bug or new detector power. Record that equality cancellation and reverse congruence were not needed if that is what the selected route shows.

## A finite cancellation-plus-query chain the engine already supports

This is a **schematic reasoning pattern, not a proposed EggCC axiom or demonstrated compiler case**. Let `Seal : Key × Stamp → Certificate` have justified injectivity, and let `Probe : Value × Key → Result` be unmarked. Assume all shown rows already exist and the embedding has sound independent reasons for the two premises:

```text
Seal(k,s) = Seal(k',s')                [valid certificate equality]
Probe(x,k) != Probe(y,k')              [valid scoped result-disequality witness]

scheduled Seal cancellation  ⇒ k = k' (and s = s')
remaining-child query        ⇒ known-disequal?(x,y)
actual consumer              ⇒ the intended check/optimization outcome
```

Neither mechanism substitutes for the other here. Without cancellation, two Probe positions remain unresolved and the query must stay unknown. Without result-disequality reasoning, cancellation gives no fact about x/y. The parent witness may itself require marked forward structural propagation from immutable scalar leaves, but its semantic source must be stated. No native payload conflict is needed for the displayed chain.

The existing engine test [query tests:143–179](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/tests/injectivity_disequality.rs:143) already uses this shape: equality of marked `Wrap(Leaf0)`/`Wrap(Leaf2)` results, unequal unmarked Pair results, then a `:naive` consumer. It explicitly checks no result before scheduled cancellation and a result afterward, under NEE/EE and both schedulers. This is existing engine evidence, **not** a richer EggCC integration or a new result from this read.

The hard compiler obligations remain open: why may the Certificate outputs legitimately be equated without already knowing the required child equality; why is the parent witness a semantic disequality rather than raw ID inequality; does the focused child denote a scoped value or syntax/function; and which actual consumer changes? Merely asserting equal wrappers to force cancellation, or using Expr inequivalence to infer runtime nonalias, would manufacture the example. Existing projections/left inverses may already derive the child equality, making a candidate redundant. A scope field alone does not make cancellation of an unscoped child safe.

## Scheduling is part of the case

`known-disequal?` is a Read primitive. [Core context rules:64–81](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog/src/exec_state.rs:64) admit table reads in top-level checks and `:naive` rule bodies, not seminaive bodies. A consumer must rerun when a hidden parent witness or sibling equality changes. The query never runs cancellation itself.

For a finite, non-generative first case, use the existing test's bounded protocol: seed and commit valid rows; verify the initial unknown/absence; run the equality producer and `injectivity`; rerun the `:naive` consumer, or use `(run-schedule (saturate injectivity consume))` when those are the only mutually relevant finite rules; check the consumer and negative controls. [`check-contradiction`, lines 491–514](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/disequality.rs:491) saturates only private disequality normalization. It does not run injectivity, the consumer, or a general joint closure.

Do not generalize this finite protocol to a generative compiler analysis. Extended `saturate` stops according to [iteration `can_stop`, scheduling.rs:268–287](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/scheduling.rs:268); finite witness search does not prove finite row generation or correct cross-ruleset update reporting. A concrete generative certificate design needs reviewed bounded propagation and interleaved fail-fast audits before consumers, as retained in prior constraints.

## Contribution controls, falsifiers, and bounded possible changes

1. **Existing/manual baseline:** identify the real default check/consumer, any current projection/type/literal rules, and a direct hand-written form of the same law. Match witness construction, semantic guards, context, effects and schedule. Hand-codability is expected, not a rejection by itself; redundancy with an already-running rule or no changed outcome is a meaningful negative.
2. **Shared-witness control:** identical lawful witness rows without the new consumer must preserve baseline behavior. Do not obtain the result by adding different equalities or oracle facts only to the encoded arm.
3. **Feature controls:** combined reasoning reaches the actual consumer. In the cancellation route, omit the necessary cancellation and require the sibling to remain unknown; omit the necessary disequality bridge and require the consumer to remain absent. In the structural-forward route, remove the relevant constructor annotations while retaining the same leaf facts and require loss of that structural witness. Preserve other independent mechanisms and report alternate paths honestly. A direct/manual implementation may still reach the same outcome. Check that a primitive mismatch panic or independent guard does not make the claimed query role optional again; existing/raw behavior is a separate comparison arm.
4. **Soundness negatives:** absent/unequal sibling, two unresolved positions, no disjointness from constructor names, unmarked forward/cancellation absent, unknown stays undefined, scope/type/point mismatches, infeasible context, same-address/aliasing and legitimate refinement as relevant to the chosen family. A bad seed/unsupported parser error is not a meaningful semantic counterexample. Require actual consumer checks and source/result execution where supported; label engine-only graphs and replay separately.
5. **Lifecycle/schedule regressions if encoding changes:** late union/assertion, scheduled child cancellation, subsumed/current canonical rows, push/pop/redeclaration, finite-witness and witness-free cycles, no query row/table growth, both assertion encodings and relevant schedulers. Existing [tests:249–301](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/tests/injectivity_disequality.rs:249) cover native and equality-sort propagation; [tests:464–505](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/tests/injectivity_disequality.rs:464) preserve direct-type and proof/term rejection.

No required runtime change was found for either displayed route. One concrete documentation defect is [lib.rs:42–47](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/src/lib.rs:42), which still describes unary/marked reverse inference; implementation, README and E1 findings support unmarked n-ary reverse. A future implementation slice can correct that small stale description. If a selected consumer genuinely requires a container, conditional cancellation, stored constraints, tagged disjointness, or another excluded feature, first submit its smallest semantic law and falsifier; do not silently expand the fragment. Proof support remains outside the accepted goal.

The consumer circle also proposed fixed-literal unary wrapping shifts in a scoped value layer: `Shift_c(v)=v+c` is bijective for each fixed i64 literal c, unlike jointly injective Add(c,v). Its cancellation/forward-DQ chain is mathematically valid, but branch-local bottom isolation is unresolved. Current NEE/EE assertions are global; EE's private truth values are shared. Seeding an impossible branch's inconsistent local constraints can therefore pollute global state. `known-disequal?` does not read an arbitrary scoped NotEqual relation, and a late consumer guard does not undo leaked unions. An isolated per-scope analysis or a sound pre-seeding feasibility restriction would need a separate concrete design. This is a compiler scoped-value bridge obligation, not a missing arithmetic law or permission to annotate raw Expr shifts globally.

The existing [finite oracle:21–72](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/egglog-experimental/tests/injectivity_disequality/oracle.rs:21) repeatedly closes marked forward and guarded reverse laws over a **fixed equality partition**. It does not model cancellation or arbitrary producer/consumer schedules. If a new mechanism requires an independent oracle, extend only the selected finite semantics and account explicitly for equality evolution; rerunning the old oracle alone would not verify a new joint-closure claim.

## Proposed validation entrypoints and stop terms

These commands were **not run**. Use a new isolated implementation checkout, coordinator-selected compatible target/cache and build slot after plan approval; preserve the inspected prior worktree and frozen artifacts. The package is `egglog-experimental`; Rust is pinned to 1.91.0. Meaningful focused entrypoints already exist:

```sh
# cwd: the new isolated encoding implementation checkout
env RUSTUP_TOOLCHAIN=1.91.0 CARGO_BUILD_JOBS=4 \
  cargo test -p egglog-experimental --test injectivity_disequality \
  naive_consumers_observe_late_equalities_and_parent_assertions_under_both_schedulers
env RUSTUP_TOOLCHAIN=1.91.0 CARGO_BUILD_JOBS=4 \
  cargo test -p egglog-experimental --test injectivity_disequality
env RUSTUP_TOOLCHAIN=1.91.0 CARGO_BUILD_JOBS=4 \
  cargo test -p egglog-experimental --test injectivity
# Final coordinated source gate after accepted changes, not a setup command:
env RUSTUP_TOOLCHAIN=1.91.0 CARGO_BUILD_JOBS=4 UV_PYTHON=3.13 make check
```

[Root Makefile:21–65](/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding/Makefile:21) owns the full Python/Rust gate. Do not add a proof-subset rerun after full success. Compiler consumer/CLI/native tests must be supplied by its owner once a real bridge is selected; this note does not invent those entrypoints.

Stop discovery here: current APIs can express a substantive joint chain, but no new EggCC law or useful consumer is established by this encoding scan. Continue only with the consumer circle's concrete candidate and semantic premises. Reject or retain a scoped negative for unsound premises, existing closure redundancy, unsupported fragment without justified bounded extension, absent real trigger/consumer, or no feature contribution. None proves universal impossibility.

## Read-only command record

Cwd `/Users/saul/p/egglog-encoding`: `cat` accepted facts/metadata; `sed` prior constraints; `shasum -a 256` those three authority files. Cwd `/Users/saul/p/wt/egglog-encoding/eggcc-impact-encoding`: `git rev-parse --show-toplevel HEAD`, `git branch --show-current`, targeted `git status --short`; `shasum -a 256` the listed implementation/test/API/scheduler/Makefile/toolchain files; `rg -n` for declaration restrictions, witness search, test names, schedule and public factories; and `nl -ba ... | sed -n ...` of the exact linked ranges. A root-cwd diff-stat request for feature paths returned no data and is not used as source-status evidence. No shell command executed a compiler, test, build, benchmark, project import or source edit. The only written path is this planning note.
