# Provenance, slicing, and proof production: a cross-field literature review

How four research traditions study the same problem under different names,
what this implementation took from each, and why the first architecture was
slow while the final one is fast. Companion to
`CONCEPT-SOURCES.md` (naming) and `RESEARCH-recorder-cost-2026-07-24.md`
(cost engineering). Local PDFs: `P7 = /Users/saul/Downloads/Paperpile files
7/PhD/proofs/`; Galois-slicing papers in `~/Downloads`.

---

## 1. The shared problem

Given a computation that produced an output, answer cheaply: *which parts of
the input and which steps of the computation were responsible?* — and
optionally re-establish the output from only those parts. At least four
traditions study this, largely without reading each other:

| Tradition | Community | Canonical question |
|---|---|---|
| **Database provenance** | DB theory + systems | why/how is this tuple in the result? |
| **Program slicing** | SE / PL | which statements affect this variable here? |
| **Proof production** | automated reasoning / SMT / e-graphs | produce a checkable certificate for this equality |
| **Datalog provenance & declarative debugging** | logic programming (the natural bridge) | why does this fact hold / why did this rule fire? |

Plus a fifth, engineering-first tradition that rediscovered the same
economics without the semantics: **record-replay and omniscient debugging**
(rr, Arnold/Eidetic, Pernosco, TOD) and **dynamic taint analysis** (libdft,
Dytan).

---

## 2. The four traditions in brief

### 2.1 Database provenance
Founded semantically by **Green–Karvounarakis–Tannen, *Provenance
Semirings* (PODS 2007)** [P7]: how-provenance is a polynomial (× within a
derivation, + across alternatives); every earlier notion (lineage,
why-provenance) is a coarser semiring. Surveyed in Cheney–Chiticariu–Tan,
*Provenance in Databases: Why, How, and Where* (FnT 2009) (web) and
questioned forward in **Buneman–Tan 2019** [P7]. Key structural result:
**provenance circuits** (Deutch et al., ICDT 2014, web) — the shared DAG is
exponentially smaller than its unfolded derivation trees. Key negative
result: **Amsterdamer et al. 2011** [P7] — no uniform semiring captures
relational difference; deletion provenance must be operational. Systems
engineering: **GProM** (Niu–Glavic 2017 [P7], instrumentation optimization,
>4 orders of magnitude), **ProvSQL** (Sen et al. 2025 [P7], append-only
mmap circuits, content-addressed gates), the cautionary **DataProv**
(Pintor et al. 2025 [P7], eager polynomials OOM), and the capture-cost
landmark **Mohammed–Wu 2025 / SmokedDuck** [P7]: query-level rewriting
averages 1294% overhead; operator-level ~20%; *function-level* — logging
the index arrays vectorized operators already compute — **<10%**. Lineage
is data movement; capture cost is materialization cost.

### 2.2 Program slicing
Founded by **Weiser (TSE 1984)** (web): the *slicing criterion* and
projection-correct static slices. Made dynamic by **Agrawal–Horgan
(PLDI 1990)** (web): the *dynamic dependence graph* (DDG), slice =
backward reachability; their Reduced DDG bounds graph size by distinct
slices, not run length. Cost-engineered definitively by **Zhang–Gupta–Zhang
(ICSE 2003)** (web): the **FP/NP/LP taxonomy** — full preprocessing OOMs
(5 GB graph), no-preprocessing is exact but minutes/slice, *limited
preprocessing* (compact exact traversal index + on-demand detail) wins —
plus **PLDI 2004** (edge sharing: ~6% of edges stored, 7.5–93× shrink) and
**WET (MICRO 2004)** (unified timestamped trace store, 16–83× compression,
and the warning that over-compressing traversed data doubles query time).
Made semantic by the **Galois-connection school**: Perera–Acar–Cheney–Levy
(ICFP 2012, web) — fwd/bwd slicing as adjoints, plus *delayed tracing*
(record (env, expr), re-run on demand — wins only while slice ≪ trace);
**Ricciotti et al. 2017** [~/Downloads/1705.07678] — references,
exceptions, kill semantics (`writes(T)`, annotated holes `□^k_L`),
correctness *and minimality* proofs; **Stolarek–Cheney 2019**
[~/Downloads/1907.05818] — Coq-verified, and the `(ℓ, k, D)` criterion:
a source label alone is ambiguous under repeated execution — dynamic
occurrence identity is part of the question.

### 2.3 Proof production (equality/e-graph line)
**Nieuwenhuis–Oliveras (RTA 2005)** [P7]: proof-producing congruence
closure — a reason-labeled union forest kept beside the path-compressed
union-find; `Explain` recovers the k relevant input equations in
O(k log n). **Flatt et al. (FMCAD 2022)** [P7]: egg's *explanations* —
minimum-size explanations are NP-complete; keep redundant edges as a DAG
and search greedily (no asymptotic overhead). **Andreotti et al. 2024**
[P7]: the same in cvc5 — greedy at 1.18× average, redundant edges cost
+8.7% storage, explanations shrink 14% when they change; per-edge levels +
a max-level cutoff prevent circular explanations. **Stevens–Ghidini 2025**
[P7]: verified union-find-explain — edges annotated by *index into the
unions list*; explain = LCA + newest-index-on-path; two-structure split
(compressed eval UF + uncompressed explain forest) is mandatory. The
tradition's defining trait: proofs are **reconstructed on demand from an
annotated structure**, never stored per-merge.

### 2.4 Datalog provenance and declarative debugging — the bridge field
**Köhler–Ludäscher–Smaragdakis 2012 (GPAD)** [P7]: reify rule firings via
rewriting; measured the cost model this project relived — 304k facts can
have 64M firings, and storing full firing bindings cost 3.3×. **Zhao–
Subotić–Scholz (TOPLAS 2020)** [P7 ×2]: the field's landmark — annotate
each tuple with two integers (rule, minimal derivation height), reconstruct
exact derivation trees lazily with no re-evaluation, at **1.27–1.31×
runtime / 1.45–1.76× memory** on tens of millions of tuples. **Ramusat et
al. 2021** [P7]: provenance as dynamic programming over the derivation
hypergraph; one best-weight witness per fact; warns that annotation
*updates* are the cost (moot under wave-monotone "first label is final").
**Chothia et al. 2016** [P7]: explanations in differential dataflow —
lazy per-operator reverse maps, explanation as a shadow join, replay for
non-monotone operators, 1.3–1.4× overhead. **Deutch et al. (VLDB 2015)**
(web): generate only the top-k (k=1) derivation — selective provenance.

### 2.5 The systems tradition (economics without semantics)
**Arnold/Eidetic Systems (OSDI 2014)** (web): record only nondeterminism,
<8% overhead, reconstruct any past state by deterministic replay.
**rr / Pernosco** (web): record cheap once; build the omniscient
all-writes database offline; debugging = queries over time. **TOD
(OOPSLA 2007)** (web): whole-execution event databases with indexing.
**libdft (VEE 2012)** (web): per-location metadata at scale — direct-mapped
shadow memory, one-addition address translation, branchless propagation.
These fix the *constants* the other fields' asymptotics hide.

---

## 3. Rosetta stone: same concept, four names

| Concept | DB provenance | Program slicing | Proof production | Datalog / this project |
|---|---|---|---|---|
| the recorded past | provenance / lineage | (execution) trace | proof object | trace (`provenance::Trace`) |
| the question | why-provenance query | slicing criterion (Weiser) | proof obligation | `Criterion` |
| the structure | provenance graph / circuit | dynamic dependence graph | proof forest | cause DAG + `ExplanationForest` |
| one derivation step | how-monomial factor | dependence edge | inference step | `Firing` (Köhler) |
| all vs one derivation | how-polynomial vs one monomial | all paths vs one slice | all proofs vs one certificate | one witness per fact (Green: a single monomial suffices) |
| shared vs unfolded | circuit vs polynomial (Deutch) | shared edges (Zhang–Gupta) vs per-instance DDG | proof DAG vs proof tree | trace vs proof-term unfolding |
| eager vs lazy | eager annotation vs query-time (GProM ICs) | FP vs NP vs LP | proof logging vs reconstruction-from-annotations | receipts (eager events) + lazy explanation/slicing |
| temporal stamp | — (mostly monotone) | timestamp (WET) | union index (Stevens–Ghidini) / edge level (Andreotti) | `Wave` (≡ Zhao's height, Köhler's round) + `EdgeHorizon` |
| dynamic identity | tuple instance | occurrence `(ℓ, k)` (Stolarek–Cheney) | proof-node occurrence | occurrence-scoped equality leaves |
| destruction | monus / difference (impossible uniformly — Amsterdamer) | kill / def-use (Ricciotti `writes(T)`) | — (monotone by nature) | `Tombstone` + `VersionChain` + interference |
| re-establishing the output | provenance replay (Subzero et al.) | `fwd_T` / validate-by-rerun | proof checking | grounded replay under unchanged proof mode |
| minimality | minimal why-provenance (NP-hard variants) | Galois lower adjoint (Ricciotti proves it) | minimum explanation NP-complete (Flatt) | deliberately forfeited — one *actual* derivation |

The convergence is striking and mostly unacknowledged: every field
independently discovered (a) the shared DAG beats unfolded trees, (b) lazy
reconstruction from small annotations beats eager materialization, (c) one
witness suffices for exactness, (d) minimality is intractable, (e) a
temporal stamp is needed the moment execution has phases or destruction.

---

## 4. What this implementation took from each field

| Component | Source field(s) | Specific inheritance |
|---|---|---|
| trace-as-object; correctness law `fwd(bwd(o)) ⊒ o`; occurrence identity; kill semantics | Galois slicing (Cheney school) | Provenance Traces 2008; Stolarek–Cheney; Ricciotti |
| capture economics: effective-only events, columnar per-batch, persist what the join computed | DB lineage engineering | Mohammed–Wu F-level; SmokedDuck; Zhang Relational E-matching (e-matching *is* the join) |
| the observation floor as an experiment (count sink, 0.97×) | systems (Arnold's "recording nondeterminism is cheap") | plus the digest as a semantic equivalence oracle |
| equality side: reason-labeled forest, lazy explain, horizon cutoffs | proof production | NO 2005; Stevens–Ghidini union index; Andreotti max-level; Flatt greedy (cone-size knob, filed) |
| firing vocabulary; wave-as-height; annotation contingency | Datalog provenance | Köhler; Zhao (1.3× existence proof, filed as contingency with corrections) |
| deletion: operational tombstones + interference-only retention | Amsterdamer impossibility + compiler anti-dependence | no algebra for difference; retain kills only when a retained observation crosses them |
| replay-as-validation for non-monotone effects | Cheney 2014; Chothia 2016 | re-execute the cone; the strict checker as independent oracle |
| storage discipline: LP point, light compression, dense sidecars | slicing cost engineering + taint | Zhang–Gupta ICSE'03/PLDI'04; WET tier-1-only; libdft layout (filed) |
| what proofs *are*: the unfolded presentation, produced only for the cone | synthesis of all four | circuits (shared vs unfolded) + Zhao (reconstruct on demand) + the checker's independence |

Project-native contributions with no direct antecedent found: occurrence-
scoped equality leaves for e-graphs (identical syntax across components
must not alias — forced by rebuild); interference-only *kill* retention
computed at slice time from recorded positive events; the count-and-digest
floor experiment as an architecture falsifier; grounded exact-one replay of
whole heads under unchanged proof instrumentation (no proof-side value
translation); byte-identical slice artifacts as a regression oracle.

---

## 5. Why v0 was slow and the final system is fast — as told by the literature

Every v0 pathology is a named anti-pattern in at least one field:

| v0 behavior | Measured cost | The literature's name for it |
|---|---|---|
| eagerly elaborate every match into full witnesses (944k for 1 retained on Math) | Math 15+ min pre-index; RSS 4.8 GB | FP extreme (Zhang–Gupta: OOM); eager how-provenance (Pintor: OOM); Köhler's 64M-firings 3.3× |
| conservative `Prefix` fallback when provenance was missing | Hardboiled slice 30,465 firings (87% conservative) | imprecise slicing — up to 5,188× larger than precise (Zhang–Gupta ICSE'03) |
| replay via thousands of generated selector queries | 5,119 plans; ~14s planning + ~11s joins → 47× | per-derivation queries against a batch-amortized engine — the anti-pattern shared-arrangements and semi-naive evaluation exist to prevent |
| serialize witness DAGs into source trees | 44.6s / 2.88 GB | unfolding the circuit (Deutch: exponential vs the DAG) |
| second frontend interpreting history (15.9k lines) | unmaintainable | reconstructing what the engine knew instead of recording it (the Subzero/GProM lesson: reference + replay beats re-derivation *only* if you kept the references) |

The intermediate exact-receipts system fixed precision but repeated the
eager mistake one level down (a shadow term e-graph: 48.5× → after removal
of a quadratic scan, 5×; instructions exactly 2.0× at the end — the
irreducible cost of constructing per-event records eagerly).

The final system sits at the literature's convergence point:

- **effective-only, columnar, batch capture** (F-level; count-sink floor
  0.97× proves observation is free);
- **one witness per fact** (Green's monomial), premises recorded as the
  join's own output (Relational E-matching);
- **lazy everything derivable**: explanations within horizons (NO/
  Stevens–Ghidini), term structure from creation rows, slices from
  criteria — the LP point;
- **operational non-monotonicity**: tombstones + version chains +
  interference (Amsterdamer + Ricciotti kills);
- **replay only the cone under the unchanged proof subsystem** (Cheney
  2014 validation-by-rerun; proofs = unfolded presentation, paid only
  where needed).

Result: suite 0.132–0.135× of full proof mode (Math 0.23×, Luminal
0.035×), all checks strict-verified, byte-stable artifacts, recording
1.35–1.39× suite-wide. The arc in one sentence: v0 paid *unfolding* costs
everywhere; the final system stores the *circuit* and unfolds only the
cone.

---

## 6. Do the fields talk to each other? Partially — through one group

**The bridge exists, and it is essentially Cheney's research program**:
- Cheney–Ahmed–Acar, *Provenance as Dependency Analysis* (DBPL 2007 /
  MSCS 2011) (web) — the explicit thesis that database provenance IS the
  dependency analysis underlying program slicing, with dependency-
  correctness defined à la noninterference.
- *Provenance Traces* (2008) [P7] — traces as the common substrate.
- Perera et al. (ICFP 2012) → Cheney et al., *Database Queries that
  Explain their Work* (2014) [P7] — Galois slicing exported INTO databases.
- Ricciotti/Stolarek — the imperative/verified closures of that program.
- Buneman–Tan 2019 [P7] closes asking for exactly these connections.

**What remains unbridged** (checked while surveying):
1. **Proof production ↔ provenance**: the e-graph/SMT explanation line
   (NO, Flatt, Andreotti, Stevens–Ghidini) and DB provenance do not
   cross-cite, despite proving parallel results — minimum explanations
   NP-complete (Flatt) vs minimal why-provenance hardness; explanation
   forests vs provenance circuits are the same shared-DAG idea. No paper
   found states the correspondence.
2. **Cost engineering ↔ semantics**: Zhang–Gupta's FP/NP/LP frontier,
   WET compression, and libdft-style layout are absent from the DB
   provenance and Galois-slicing literatures; conversely SmokedDuck's
   capture-level taxonomy has no analogue in slicing papers. The
   traditions optimize the same trade-off with disjoint vocabularies.
3. **E-graphs specifically**: egg's explanations cover only the equality
   dimension; Datalog provenance covers only the rule dimension; nothing
   published combines them with kills, rebuild/canonicalization
   provenance, and slice-replay — which is precisely what this
   implementation is.

**Is a synthesis paper interesting? Yes — two plausible shapes**:
- A *systematization*: the Rosetta stone (§3) as a survey bridging the
  four fields, with the FP/NP/LP frame as the unifying cost axis and
  measured datapoints from each tradition (Soufflé 1.3×, Chothia 1.3–1.4×,
  SmokedDuck <10%, this system 0.97× floor / 0.13× end-to-end).
- An *experience paper*: "causal slicing for equality saturation" — the
  first system providing exact, replayable, strictly-checked slices for an
  e-graph engine; the three eager→lazy inversions as the narrative; v0 vs
  final as a controlled architecture comparison with the 47×→0.13× arc.
  Natural venues: the egraphs community (EGRAPHS/PLDI workshops), TaPP
  (Theory and Practice of Provenance), or OOPSLA/ICFP experience tracks.
  Nearest neighbors to differentiate against: Zhao (Datalog, no
  equality/kills), egg explanations (equality only), Chothia (dataflow,
  no e-graphs), the DuckDB lineage line (no recursion/fixpoints).

---

## 7. Pointers

Full per-paper details: `RESEARCH-recorder-cost-2026-07-24.md` §8 (34
sources with numbers). Naming and rustdoc headers: `CONCEPT-SOURCES.md`.
Probe battery and verified semantic facts: research report §9–10.
Measured project history: `EXPERIMENTS.md` (both ledgers).
