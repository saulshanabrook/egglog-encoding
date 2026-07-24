# Recorder-cost research report (2026-07-24)

Full synthesis of the recording-overhead investigation, compiled so work can
resume here after end-to-end slicing lands. Sources: three independent
investigations (profile forensics at `deb2ecf`; a 25-paper provenance library
review; a broad program-slicing literature survey), the recorder team's own
ablations, and the empirical probe battery. All local measurements from this
machine, serial (`-j 1`), Math = `egglog/tests/math-microbenchmark.egg` with
the terminal 11-wave check (fixture SHA `7303e72d…`).

---

## 0. How to resume (re-entry checklist)

1. Read §1–§2 for the measured landscape; nothing below matters until a final
   per-file gate (`causal-proofs` vs `proofs`) has actually been LOST on
   recording cost.
2. If a file lost on recording wall: run §5 (journal refactor) with the §5.1
   additions and §5.2 gate.
3. If the journal refactor misses ≤1.5×: run §6 (annotation-only contract) —
   a consented contract amendment with its own canaries.
4. If a file lost on replay/cone cost instead: none of this document's levers
   apply; the levers are cone size (retain redundant unions for shorter
   equality proofs, §8.6) and slicer laziness.
5. RSS-only complaints: §4.3 pack, then §8.10 (mmap arenas).
6. Product pivot toward debugging: §7.1 (eidetic split).

Artifacts: profiles under `/tmp/egglog-causal-profile-f187970/` and the
worktree `.profiles/`; semantic probes under
`~/.claude/jobs/4f831045/tmp/probes/` (E2–E9 necessity battery, subsume/check
visibility, action-lookup prohibition, same-wave ordering, delete-of-missing);
ledger: `.codex/causal-slice-v1/EXPERIMENTS.md`.

---

## 1. Measured state

| Experiment | Native | Causal | Wall × | RSS × |
|---|--:|--:|--:|--:|
| Current exact receipts (deb2ecf), Math | 0.430s | 0.977s | **2.27×** | **3.39×** |
| Count + digest sink (3-round) | 0.412s | 0.398s | **0.97×** | ~1.00× |
| Ablation: no creation-row payload copies¹ | 0.512s | 1.212s | 2.37× | 2.74× |
| Ablation: discard almost all durable history¹ | 0.567s | 1.074s | **1.90×** | 2.06× |
| Eggcc / Hardboiled / Pointer | — | — | 1.27× / 1.22× / 0.90× | 2.07× / 1.38× / 1.36× |
| Luminal | 0.462s | fails closed | — (deletion checkpoint unimplemented; 13 sites: 10 constructor deletes, 3 `:merge new`) | |
| **Instructions retired, Math (ground truth)** | 6.96 G | 13.95 G | **2.00×** | |
| Math full `proofs` (terminal fixture, per round) | — | 7.70–8.44s | ~18× native | |

¹ one-round diagnostic ablations (directional).

Cardinalities (Math, from the sink digest checkpoint): 2,111,697 events;
943,133 candidate = successful lanes; 1,731,581 facts; 350,368 applied unions;
22,216 redundant unions; 439k rekeys; 7,520 batches; 11 waves; 1 check.

**Headroom**: recording as a fraction of the mission denominator (`proofs`):
Math **0.12×**, Eggcc ~0.25×, Hardboiled ~0.26×, Pointer ~0.02×. The 1.5×
recording screen is an intermediate proxy; the final gate is per-file
`causal-proofs < proofs`.

---

## 2. Diagnosis: why 2.27× is intrinsic under the current contract

Three independent lines of evidence agree:

1. **Instructions retired are exactly 2.00×** — the overhead is real work, not
   stalls, dispatch, or layout accidents.
2. **The count-only sink is 0.97×** — observation hooks are free; every cycle
   above 1.0× is record *construction* and attribution bookkeeping.
3. **The black-hole ablation is 1.90×** — even discarding nearly all durable
   history, the live attribution machinery (pending causes, validation,
   merge/rekey organization, publication) still costs ~1.9×. Storage elision
   alone cannot reach 1.5×.

Where the +550 ms/iter goes (normalized self-CPU, off 522 → receipts 1072
ms/iter): receipt-record symbols ≈330 (with a +253 ms/iter long tail of small
helpers), native inflation ≈30, allocator/rehash ≈170 (library allocator share
16.8%→21.9%). Recorder team sampling agrees: receipt-aware insertion subtree
503ms vs 92ms native; rebuild 442ms vs 198ms; receipt/causal API ≈438ms; merge
+ rebuild ≈72% of residual overhead.

**Hypotheses ruled out by code inspection** (do not re-investigate):
- Serial-dispatch tax: none. Both modes run the same monomorphized
  `serial_insert_mode` at `-j 1` (`parallelize_table_op` requires
  `threads > 1`, parallel_heuristics.rs:37; gate at table/mod.rs:1136–1158).
- Producer-index hashing: none on the hot premise path — already a dense
  per-row `Vec<FactId>` sidecar (`FactSidecars`, table/mod.rs:98–169;
  `validated_atom_fact`, execute.rs:3281/3328). `Value` is dense u32
  (common.rs:103).
- Snapshot-time Box-heavy `MatchRecord`/`FactRecord` are NOT built during the
  run (only in `snapshot()`, receipts.rs:6818–6962); live RSS is the columnar
  `ReceiptArena`.

---

## 3. RSS accounting (byte model reproduces measured +550 MB within ~1%)

| Store | Count | B/rec | Tight MB | +1.5× slack |
|---|--:|--:|--:|--:|
| `facts: Vec<Option<DurableFact>>` (72 B: incl. **40 B `Option<FactOrigin>`** sized by the Merge variant) | 1.73M | 72 | 125 | 187 |
| `durable_fact_values` (~3 Values/fact) | 5.2M | 4 | 21 | 31 |
| `durable_matches` | 943k | 40 | 38 | 57 |
| `durable_premises` (u64 FactId) | 2.83M | 8 | 23 | 34 |
| `durable_equalities` (~104 B: proposal + reason) | 350k | 104 | 38 | 57 |
| `durable_causes` (Rebuild variant 48 B) | 400k | 48 | 19 | 29 |
| `rekeys` inline (80 B incl. landmark Box ptr) | 439k | 80 | 35 | 53 |
| per-rekey `Box<[TypedCellEquality]>` (1 alloc each, receipts.rs:5345) | 439k | 56 | 25 | 25 |
| `durable_rebuild_equalities` (**redundant** with rekey boxes) | 250k | 28 | 7 | 9 |
| `merge_reads` + `cause_summaries` HashMaps | 750k | 40 | 41 | 41 |
| structural maps (by_value etc.) | — | — | 20 | 30 |
| **Total** | | | **392** | **≈543** |

Gap-over-ideal decomposition: `FactOrigin` in every fact ~70 MB; Vec doubling
slack ~120–150 MB; u64 ids where u32 fits ~50–70 MB; rekey boxes + redundant
double-store ~30–40 MB; `Option<T>` slot wrappers ~28 MB.

### 3.1 Cheap RSS pack (~220–250 MB, wall −4–6%; LOW/MED effort)
1. Pre-size arena Vecs from prior-wave counts; `shrink_to_fit` at finalize
   (`ReceiptArena::default`, `install_fact` receipts.rs:2717). ~100–150 MB.
2. De-box rekeys: store pairs as `FlatRange` into one shared vec; delete the
   redundant `durable_rebuild_equalities` double-store. ~30–40 MB; kills 439k
   allocs (`Vec::drop` 7 ms/iter + allocator tail).
3. Move `FactOrigin` to a side table keyed by FactId, populated only for
   merged facts (receipts.rs:2622–2653). Fact record 72→~28 B. ~70 MB.
4. Dense-ize `cause_summaries: HashMap<CauseDraftId,_>` (receipts.rs:2703,
   minted densely at 5314/4188) and `merge_reads: HashMap<RuleMatchId,_>`
   (2698) into `Vec<Option<_>>`. ~25 MB, ~2% wall.
5. Still-live wall item: deferred merge-cause bracketing
   (`end_deferred_merge_cause` 20.1 + `ActiveCause::deferred` 10.5 ms/iter) —
   deletable once causes are batch-durable before heads (journal item 2/6).

---

## 4. Decision record (adopted)

Proceed end-to-end with the current recorder. The former 1.5×-native screen
is diagnostic only; sufficient headroom is recording ≤ 0.5× full proofs
(Math is 0.12× today), and the binding gate is total causal-proofs versus
full proofs per file. Freeze ALL recorder work, including §3.1, then: deletion
checkpoint → slicer → let-check / list-form run-rule → proof integration →
final per-file gate. §3.1/§5/§6 are contingent checkpoints triggered ONLY
by a final-gate loss attributable to recording cost. Rationale: the two
unknown-risk subsystems (slicer, grounded replay) are unbuilt; recording is a
known, twice-designed quantity; the end-to-end result decides which
contingency (if any) matters.

---

## 5. Contingency A: barrier-local append journal (recorder refactor)

The recorder team's design (kept verbatim in intent): per-wave/table dense
receipt transactions with range reservation; compact cause tokens (id + small
tag) instead of nested cause objects; raw merge-read/rekey/fact/equality
events appended to flat slabs, organized/deduplicated/validated ONCE at the
wave barrier; static origin/type validation moved to rule/table registration;
match metadata stored once per batch with premises as flat ranges; table-local
journals replacing global maps and per-event Arc/OnceLock publication.

### 5.1 Additions from this investigation
1. Fold §3.1 in explicitly (FactOrigin side table; rekey de-box + double-store
   deletion; reserve AND shrink; dense maps).
2. **Shadow-memory discipline** for hot writes (libdft, §8.8): metadata
   addressed by arithmetic from row/lane id, word-packed, single-assignment,
   branchless, no synchronization. The cause token must be writable this way.
3. **Tier-1-only compression** (WET warning, §8.7): premise columns may be
   delta/dictionary packed; never compressed so hard that slice-time traversal
   doubles (their tier-2 halved size but doubled extraction time).
4. Rationale correction: pre-#837 term/reason tables did NOT get canonicalized
   by rebuild — they were declared with rebuild disabled
   (egglog-bridge/src/lib.rs:354, :394 at upstream 6b04aeb). "Do not revive
   native proof tables" stands on simplicity grounds (extra tables/indexes/
   Value-space), not the rebuild-destruction argument.

### 5.2 Gate
One vertical slice (compact causes + barrier-local merge/rekey journals).
Verify snapshot/digest equivalence against the current recorder and all causal
canaries. One Math round; continue to three rounds only if plausibly <~1.65×.
Hard gate ≤1.5×; target ≈1.3×. Also record **instructions retired** (cleanest
metric; expect ~1.4× if wall ~1.3×). One further measured variable allowed on
a miss; then escalate to §6.

---

## 6. Contingency B: annotation-only contract (the Soufflé scheme)

If §5 misses, the exact full-history contract itself changes (consent
required). Both literature reviews converged independently on the same design,
with an in-domain existence proof.

**Design**: store per FACT a two-integer annotation `(rule#, first-wave)`
instead of per-firing `{rule, wave, ordered premise FactIds}`. Reconstruct a
fact's premises at slice time by bounded re-derivation: re-run that rule's
e-matching restricted to facts of strictly earlier wave (the wave gradient
prunes the search; egglog's wave-monotone order means the first label is final
— no annotation updates). Precedent: **Soufflé provenance at 1.27× (conf) /
1.31× (journal) runtime, 1.45×/1.76× memory**, exact, one recorded run, tens
of millions of tuples, proof heights >200 [Zhao19; Zhao20].

**Supporting techniques**:
- First-occurrence filtering: keep only the first-wave witness per fact; later
  re-derivations are provenance-redundant for backward slicing [Chothia16
  time-filter; Köhler12 measured the cost model — 64M firing records = 3.3×].
- Representative-edge sharing: one labeled (producer-site → consumer-site)
  edge with timestamp ranges; ~6% of edges stored, 7.46–93.4× graph shrink
  [ZhangGupta04].
- Enriched-pattern holes: one compressed record per uniformly-firing batch
  [Cheney14, order-of-magnitude trace/slice shrink].
- Memoized per-batch kill/write-set summaries; never recompute at slice time
  [Ricciotti17 — naïve bwd observed quadratic].
- Single-witness principle: exactness = one actual derivation = one monomial,
  not the full how-polynomial [Green07; Deutch15 top-k with k=1].

**Caveats (must be in the checkpoint spec)**:
- Reintroduces bounded slice-time search. The historical ban was against v0's
  unbounded eager selector search; this is annotation-guided and cone-scoped —
  but it is a contract amendment. Determinism canary: the `(rule#, wave)`
  tie-break must reconstruct the actual first firing.
- **Perera's law** [Perera12]: recovery-by-re-execution wins only while the
  retained cone ≪ the run; measured — delayed tracing ~eliminates trace cost,
  but when slice ≈ trace it is MORE expensive than lazy tracing. Verify the
  terminal-Math cone stays small before committing.
- **LP frame** [ZhangGupta03]: store-everything OOMs (their 5 GB graph; our
  3.39× RSS is the miniature); recover-everything is exact but minutes/slice;
  the winner is a compact exact traversal-optimized index + on-demand detail.
  Current recorder = mild FP; annotations = LP. Do not overshoot to NP.

---

## 7. Long-game shelf (triggers, not plans)

### 7.1 Eidetic split (record ~nothing; materialize offline)
Record in-band only what makes offline reconstruction deterministic and
seekable: program, dynamic wave schedule, per-fact annotations, digest. On a
slice/debug request, re-execute deterministically under the heavy recorder to
materialize the full dependence store; index it; serve slicing/debugging as
queries. Precedents: Arnold/Eidetic Systems — **<8% recording overhead**,
reconstructs any past state, ~1 TB/yr/workstation [Arnold14]; rr + Pernosco —
record cheap, build the omniscient all-writes database offline, debugging =
queries over time [rr; Pernosco]; TOD's indexed event database [TOD07].
Product direction: **omniscient e-graph debugger** ("why is this term in this
class", "what did rule X do at wave 7") — generalizes the sliced-artifact
goal. Trigger: slicing becomes a rare interactive operation rather than part
of every causal-proofs run. Cost: runs the workload twice when a slice IS
requested; two-phase architecture to maintain. Serial determinism is already
proven by the sink digest.

### 7.2 Off-heap mmap append-only arenas + columnar file format
ProvSQL stores its provenance circuit outside the DB in indexed, memory-mapped
append-only files (single writer; OS pages cold fragments out) [Sen25]. With
`frankmcsherry/columnar` (derive SoA for sum/product/list types; zero-copy
`&[u8]` round-trip) the on-disk format = in-memory format → **the trace
becomes a file format for free** (record once, slice many, cross-process)
[columnar]. Decision recorded earlier: hot slabs stay engine-native
(RowBuffer / Pooled<Vec<Value>> / FlatRange — allocator-pooled, profiled at
<1%); adopt columnar/mmap only when (a) trace persistence/offline slicing
enters scope, or (b) enum arenas show in a profile. `flatcontainer` is the
adjacent alternative. Related context: DD issue #742 (our thread: McSherry
reviving `explanation` atop DDIR; datatoad; DBSP discussion).

### 7.3 libdft-style metadata layout (last constant-factor layer)
Direct-mapped shadow: `taddr = vaddr + STAB[vaddr>>12]` — one addition;
byte-packed tags; branchless single-assignment propagation; whole-program
taint at 14%–6× [libdft12]. Control-dependence tracking as a separately
toggleable channel (it is the expensive part) [Dytan07]. Trigger: a
post-§5/§6 gate miss on pure constants (likely never).

---

## 8. Technique catalog with citations

Local PDFs: `P7 = /Users/saul/Downloads/Paperpile files 7/PhD/proofs/`.

### Datalog / e-graph provenance (in-domain)
1. **[Zhao19/Zhao20]** Zhao, Subotić, Scholz — *Provenance for Large-scale
   Datalog* (arXiv 1907.05045) / *Debugging Large-scale Datalog: A Scalable
   Provenance Evaluation Strategy* (TOPLAS 2020, doi 10.1145/3379446). P7.
   Two-integer per-tuple annotation (rule#, minimal proof height) via a
   provenance lattice; proof trees reconstructed lazily, 2 levels at a time,
   no re-evaluation for why-exists. **1.27×/1.31× runtime, 1.45×/1.76×
   memory.** The §6 template.
2. **[Köhler12]** Köhler, Ludäscher, Smaragdakis — *Declarative Datalog
   Debugging for Mere Mortals*. P7. Firing-reification rewriting stores full
   body bindings; **304k facts → 64M firings; 15.4s → 51.3s (3.3×)** — the
   measured cost model of "record every firing with bindings". Statelog round
   = our wave.
3. **[Chothia16]** Chothia, Liagouris, McSherry, Roscoe — *Explaining Outputs
   in Modern Data Analytics* (VLDB 2016). P7. Lazy per-operator reverse maps,
   explanations as joins; **1.3–1.4× overhead**; first-occurrence time
   filtering; join/distinct/top-k need no stored lineage; iterative backward
   re-execution for non-monotone ops (= our replay validation).
4. **[Ramusat21]** Ramusat, Maniu, Senellart — *A Practical Dynamic
   Programming Approach to Datalog Provenance*. P7. Best-weight single
   derivation per fact via Dijkstra/Knuth over the derivation hypergraph;
   ~4× on IRIS; warns annotation UPDATES are the cost — wave-monotone
   "first label is final" avoids it.
5. **[Deutch15]** Deutch, Gilad, Moskovitch — *Selective Provenance for
   Datalog using Top-k Queries* (VLDB 2015).
   https://amirgilad.github.io/publication/vldb15/VLDB15.pdf — generate only
   the top-k (k=1) witness, poly data complexity.
6. **[Zhang22]** Zhang, Wang, Willsey, Tatlock — *Relational E-matching*. P7.
   E-matching IS a conjunctive query; the join already produces substitution
   tuples — the premise bindings we record are engine-computed columns
   (F-Level capture is a memcpy).
7. **[VdC26]** Van der Cruysse et al. — *Parallel and Customizable Equality
   Saturation* (Foresight). P7. Deferred command batches with effective/no-op
   dedup; `onAddMany`/`onUnionMany` batch hooks — natural low-coupling recorder
   attach points; atomic-parent-array thread-safe UF.

### Database lineage capture engineering
8. **[Mohammed25]** Mohammed, Wu — *Lineage Capture Trade-offs: A Case Study
   in DuckDB*. P7. Query-level rewriting avg **1294%** (max 13424%); optimized
   157%; operator-level ≈1.2×; **function-level (log the index arrays
   vectorized operators already compute) <10%**. `LIST(rid)` per-group
   accumulation is the worst case (= our per-firing premise lists).
9. **[SmokedDuck23]** Mohammed et al. — *SmokedDuck Demonstration:
   SQLStepper*. P7. Lineage ≡ data movement; Slice/Scatter/Gather index
   arrays suffice; per-batch base offsets map batch-relative → global ids;
   capture format ≠ query format (index lazily).
10. **[NiuGlavic17]** Niu, Glavic et al. — *Optimizing Provenance
    Computations* (GProM). P7. Provenance-specific algebraic transforms +
    cost-based instrumentation choice: **>4 orders of magnitude**; `icols`
    pruning; cites reference-based storage + instrumented REPLAY as an
    established cheaper alternative to full propagation.
11. **[Sen25]** Sen et al. — *ProvSQL*. P7. UUIDv5 content-addressed circuit
    gates; append-only, **memory-mapped, out-of-DB storage**; late semiring
    specialization.
12. **[Pintor25]** Pintor et al. — *DBMS-independent provenance polynomials
    through query rewriting*. P7. Cautionary: eager string polynomials OOM /
    exceed 1 GB limits — never materialize how-provenance eagerly.

### Program-slicing cost engineering
13. **[AgrawalHorgan90]** — *Dynamic Program Slicing* (PLDI 1990,
    doi 10.1145/93542.93576). Reduced DDG: new node only when it yields a NEW
    dynamic slice — graph bounded by distinct slices, not run length.
14. **[ZhangGupta03]** Zhang, Gupta, Zhang — *Precise Dynamic Slicing
    Algorithms* (ICSE 2003).
    https://www.cs.purdue.edu/homes/xyzhang/Comp/icse03.pdf — FP/NP/LP axis;
    FP OOM at ~5 GB for a 100M-instruction trace; imprecise slices up to
    **5188×** larger; **LP (compact traversal index + demand-driven detail)
    wins**. The governing frame.
15. **[ZhangGupta04]** — *Cost Effective Dynamic Program Slicing* (PLDI 2004).
    https://www.cs.ucr.edu/~gupta/research/Publications/Comp/pldi04.pdf —
    edge sharing + timestamps: **~6% edges stored; 0.84–1.95 GB → 20–210 MB
    (7.46–93.4×)**; slices in seconds vs minutes for demand-driven.
16. **[WET04]** — *Whole Execution Traces* (MICRO 2004).
    https://microarch.org/micro37/papers/10_Zhang-WholeExecutionTraces.pdf —
    unified timestamp-labeled graph; two-tier compression **16–83×**
    (647M-statement trace → 331 MB); tier-2 halves size but DOUBLES extraction
    time — keep traversed data lightly compressed.
17. **[Perera12]** Perera, Acar, Cheney, Levy — *Functional Programs that
    Explain their Work* (ICFP 2012). https://www.mpi-sws.org/tr/2012-003.pdf —
    eager/lazy/**delayed** tracing; delay records (env, expr) and re-runs on
    demand; measured law: delay ≈ free at trace time but LOSES when slice ≈
    trace (repeated re-evaluation). The §6 cone-size guard.
18. **[Stolarek19]** Stolarek, Cheney — *Verified Self-Explaining Computation*
    (arXiv 1907.05818; local `/Users/saul/Downloads/1907.05818v1 (1).pdf`).
    Coq-verified Galois fwd/bwd for Imp; `writes(T)` + store erasure = our
    kill semantics; consistency (`fwd(bwd(o)) ⊒ o`) is the machine-checkable
    replay-validation law; minimality is the other adjoint (we forfeit it —
    NP-complete under congruence [Flatt22]).
19. **[Ricciotti17]** Ricciotti, Stolarek, Perera, Cheney — *Imperative
    Functional Programs that Explain their Work* (arXiv 1705.07678; local
    `/Users/saul/Downloads/1705.07678v1 (2).pdf`). Annotated holes `□^k_L`
    (write-set + outcome summaries for elided subtraces); naïve bwd observed
    QUADRATIC from recomputing write-sets — memoize kill-sets.
20. **[Weiser84]** — *Program Slicing* (TSE 1984, doi 10.1109/TSE.1984.5010248)
    — the projection-correctness origin.

### Replay / eidetic / omniscient
21. **[Arnold14]** Devecsery et al. — *Eidetic Systems* (OSDI 2014).
    https://www.usenix.org/conference/osdi14/technical-sessions/presentation/devecsery
    — record nondeterminism only, **<8% overhead**, ~1 TB/yr, any past state
    reconstructible by deterministic replay.
22. **[rr]** https://rr-project.org/ ; **[PinPlay]** Patil et al., CGO 2010 —
    record once cheaply, run many offline analyses on the recording.
23. **[TOD07]** Pothier, Tanter — *Scalable Omniscient Debugging*
    (OOPSLA 2007, doi 10.1145/1297027.1297067); **[Pernosco]**
    https://pernos.co/ — all state as an indexed database; debugging = queries.

### Shadow-memory / metadata layout
24. **[libdft12]** Kemerlis et al. — *libdft* (VEE 2012).
    https://nsl.cs.columbia.edu/papers/2012/libdft.vee12.pdf — direct-mapped
    tagmap, one-add STAB translation, byte tags, branchless propagation;
    **14%–6×** whole-program DFT.
25. **[Dytan07]** Clause, Li, Orso — *Dytan* (ISSTA 2007) — control-flow
    taint as a separate, optional (expensive) channel.

### Equality / proof forests
26. **[NO05]** Nieuwenhuis, Oliveras — *Proof-Producing Congruence Closure*
    (RTA 2005). P7. Reason-labeled union forest beside compressed UF;
    O(k log n) explain.
27. **[Flatt22]** Flatt et al. — *Small Proofs from Congruence Closure*
    (FMCAD 2022). P7. Minimum proofs NP-complete; O(n log n) greedy;
    keep-redundant-edges DAG for shorter proofs.
28. **[Andreotti24]** — *Shorter congruence closure proofs in cvc5*. P7.
    Greedy **1.18×** avg runtime; redundant edges **+8.7%** storage; proofs
    **14%** shorter when changed — the cone-size knob (§0.4).
29. **[Stevens25]** Stevens, Ghidini — *Simplified and Verified:
    proof-producing union-find*. P7. Union edges annotated by INDEX into the
    unions list (= our wave); explain = LCA + newest-on-path; two-UF split
    (compressed eval + uncompressed proof forest) is mandatory.

### Theory / semantics context
30. **[Green07]** Green, Karvounarakis, Tannen — *Provenance Semirings*
    (PODS 2007). P7. One monomial = one witness suffices for exactness.
31. **[Amsterdamer11]** — *Limitations of provenance for queries with
    difference*. P7. No uniform semiring captures deletion — validates
    explicit tombstones + replay for non-monotone, not algebra.
32. **[Cheney14]** Cheney et al. — *Database Queries that Explain their Work*.
    P7. Trace-replay + slicing formalized; **enriched patterns** (holes for
    uniform subsets) shrink traces/slices by an order of magnitude.
33. **[Bourgaux22]** — *Revisiting Semiring Provenance for Datalog*
    (arXiv 2202.10766). P7 companion.
34. **[columnar]** https://github.com/frankmcsherry/columnar ;
    **[DD#742]** https://github.com/TimelyDataflow/differential-dataflow/issues/742
    (our provenance thread: McSherry's `explanation` revival on DDIR;
    datatoad; DBSP discussion).

---

## 9. Empirical probe registry (semantic facts the recorder relies on)

Probes in `~/.claude/jobs/4f831045/tmp/probes/` (re-runnable against any
binary):

- **E2** match-time form vs final canonical form: slice seeded with the
  final-form term fails to re-fire the retained rule (necessity of
  match-time/occurrence identity).
- **E3** equality edges: omitting the union firing fails `(check (= …))`.
- **E4** rekey landmarks: consumer matching only-via-canonicalized row fails
  without the retained union.
- **E5/E5b** delete interference: omitted delete → `:merge max` silently
  diverges; `:no-merge` PANICS "Illegal merge attempted".
- **E6** check roots: wrong-cone slice fails.
- **E7** timeline positions: check emitted after a later retained delete
  fails (checks must replay at recorded positions).
- **E9** one `(run 1)` completes a two-level congruence cascade — intra-wave
  ordering requires the `as_of_edges` cutoff, waves are insufficient.
- Subsume: statically limited to constructors/relations ("Cannot subsume
  function with merge", incl. `:no-merge`); subsume-of-missing auto-creates
  (constructor AND relation, print-size=1); **checks see subsumed rows**
  (mark suppresses only rule matching) → no subsume receipts, ever;
  DefaultVal::Fail-via-subsume statically unreachable.
- Action reads: "Value lookup of non-constructor function in rule is
  disallowed" (typecheck) → rule dependencies = body premises + merge reads,
  complete; conditional under `:naive`/`:unsafe-seminaive` → causal mode
  enforces eligibility independently.
- Same-wave barrier ordering: deletes apply before writes regardless of
  textual action order (probe S4).
- Delete-of-missing is a no-op (probe S2).
- `run-rule` is NOT reachable through egglog-experimental's `run-schedule`
  (scheduling.rs shadows it) — replay must bypass or extend the experimental
  scheduler (stage-7/8 integration requirement).

## 10. Corrections registry

1. Pre-#837 backend proof tables were rebuild-DISABLED (lib.rs:354/:394 at
   6b04aeb), not canonicalized by rebuild. Keep "don't revive" on simplicity
   grounds.
2. "Supported user rules cannot observe subsumed rows" → true for matching
   only; checks DO see subsumed rows (probe-verified). No design change;
   rationale wording only.
3. "Dense producer index" and "serial-dispatch parity" optimization ideas:
   already implemented / structurally absent — do not revisit.
4. The waves-vs-graph question: waves are derivable from version chains +
   recorded readers (readers-of-v_n before creator-of-v_{n+1}); retained as a
   native-certified schedule annotation. Slicer correctness law = the
   soundness half of the Galois connection (fwd_T(bwd_T(o)) ⊒ o), minimality
   forfeited [Stolarek19; Flatt22].
