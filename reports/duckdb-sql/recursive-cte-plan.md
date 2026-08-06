# Plan: Source-to-Source egglog → DuckDB SQL via Recursive CTEs

Written: 2026-08-05. Companion to the `duckdb-native-sql` effort
(`/Users/saul/p/wt/egglog-encoding/duckdb-native-sql`, branch `agent/duckdb-native-sql`,
HEAD `37fc161`) and its ledger `.codex/duckdb-native-sql/STATE.md`.

## Verdict

**No blocker was found. The recursive-CTE architecture is feasible**, with a
precisely bounded envelope and a working proof-of-concept. The load-bearing
question from the codex session — can the data-dependent schedule and
ordered-union/rebuild wave loop become a "recursive relational state machine"
with deterministic fresh-ID allocation and SQL-side failure assertions — is
answered **yes, demonstrated end-to-end**:

- A complete equality saturation (UF, congruence closure, hashcons, the four
  classic eqsat-basic rewrite rules, deterministic fresh e-class minting,
  canonicalization/rekeying, and an `error()`-backed final check) runs to
  fixpoint inside **one** `WITH RECURSIVE … USING KEY` statement on DuckDB
  1.5.5 in **0.19 s**, with zero host code between waves.
  Two runs produce **bit-identical state** (md5 `da868cbdb441a76ed5a54f7d4d3309e4`).
  Scaling probes: seed chains to depth 100 and diverging runs to 22k live
  enodes / 150 waves all stay under 2.6 s. Wave count for UF collapse grows
  ~logarithmically (min-propagation is pointer-jumping).
- Prototype preserved at
  `/Users/saul/p/wt/egglog-encoding-duckdb-recursive-cte-prototype/`
  (`eqsat_final.sql` is the complete artifact; `eqsat_fail.sql` demonstrates a
  failing `(check)` exiting nonzero with a message; `invariants.sql` shows 0
  violations of canonical-key/hashcons/edge/root-leader invariants at fixpoint).

The realistic product is **two artifact tiers**, both genuinely
source-to-source (all per-row and per-wave logic in SQL, statement text frozen
at compile time):

- **(a) Standalone `.sql`** — `duckdb < prog.compiled.sql` with no host process —
  for programs whose top-level schedule is statically bounded (`seq`/`run N`/
  `repeat N`, with `saturate` only over CTE-compilable regions, which includes
  all four generated maintenance rule families). eqsat-basic and
  math-microbenchmark (`run 11`) are in this class.
- **(b) `.sql` bundle + generic driver** — a program-independent loop that
  re-issues fixed statement text and reads back one boolean per schedule-node
  iteration — for everything else (unbounded top-level `saturate` over
  arbitrary rulesets). The driver interprets the schedule tree *as data*
  (a `egglog_schedule` bytecode table); it contains no rule, table, or count
  knowledge.

What can never be a standalone SQL file: programs using `unstable-fn`,
arbitrary stateful Rust callbacks/primitives without SQL lowerings, or
interactive Rust-API use. These fail closed with named reasons, same stance as
the current backend.

## Empirical foundation (all verified on this machine)

Probes run against DuckDB v1.5.5 CLI (`brew install duckdb`; pinned engine is
1.5.4 — re-pin in M0). Eight verification agents, all **confirmed**:

1. `error()` is lazily evaluated under CASE/EXISTS (no constant-folding trap)
   in projections, aggregates, FILTER, recursive CTEs, DML — fail-closed
   probes become in-SQL aborts with dynamic messages.
2. `error()` inside `BEGIN…COMMIT` aborts and poisons the transaction; all
   statements are rejected until ROLLBACK; COMMIT-after-abort silently rolls
   back. Atomicity contract preserved without host mediation. (Standalone
   scripts need CLI `-bail`; default CLI continues past errors.)
3. Every observation-derived literal (fresh-ID base, match count, watermark,
   generation) can be an **uncorrelated scalar subquery** in the same
   INSERT/UPDATE — reads the pre-statement snapshot, no Halloween effect,
   identical results to baked literals.
4. Fixed statement text self-enables/disables via a pc-guard scalar subquery
   (`WHERE (SELECT pc FROM egglog_ctl)=N`); disabled statements cost
   ~130–280 µs each.
5. `WITH RECURSIVE … USING KEY` + `recurring.<cte>` accumulated-state access
   works; path compression, keyed min-fixpoints, and congruence shapes run as
   single planned statements. **`UNION ALL` is mandatory** (recursive `UNION`
   deprecated for USING KEY in 1.5.0, semantics change next release).
6. Aggregates with GROUP BY (`arg_min`) and window functions work **inside the
   recursive term** (unlike Postgres) — one-candidate-per-key-per-wave folds
   and in-recursion ID minting are expressible.
7. **No mutually recursive named CTEs** (all side doors closed: views,
   RECURSIVE VIEW, macros). A multi-relation fixpoint region must flatten into
   ONE tagged state relation. This is the structural ceiling shaping the
   whole design.
8. `row_number()` over a total ORDER BY is bit-deterministic at threads=4/8,
   under spill and NULLs — `SET threads=1` can eventually be lifted without
   breaking fresh-ID/proof determinism.

Adversary findings that shape (not block) the design:

- Sequences (`nextval`) are non-transactional (don't roll back) and assign in
  physical scan order — **disqualified** for ID minting. Hash-based 64→32-bit
  IDs hit birthday collisions at ~77k ids — **dead on arrival**. Only
  counter-in-state + window arithmetic survives (and is what the prototype and
  the current backend both use).
- USING KEY does **not** suppress unchanged re-emission: re-emitting an
  identical (key, payload) row loops forever. Every branch needs an explicit
  change/no-op guard; a missed guard = non-termination. Compiler invariant +
  emitted-SQL lint required.
- Same-key multi-branch emission resolves **plan-order-dependent** ("unordered
  last"). Every keyed sink must be fed through an explicit deterministic
  pre-collapse (GROUP BY key + `min`/`arg_min` over phase-priority/ordinal).
  Never rely on last-row-wins.
- Keys can never be deleted from the recurring table — deletes/subsumes become
  payload tombstones; every consumer filters liveness; dead rows accumulate.
- DML is not allowed inside recursive terms; recursion is SELECT-only. Effects
  materialize *after* the fixpoint (`INSERT INTO … WITH RECURSIVE … SELECT`).

## Prototype techniques → plan requirements

From `eqsat_final.sql` (each is load-bearing):

1. **Chained plain CTEs inside the recursive arm** sequence a whole wave:
   canon view → congruence groups → rule matches → hashcons lookup → mint →
   assembly → edges → UF update. This is the structuring device that lets one
   recursive statement express egglog's multi-phase wave.
2. **Single tagged relation** keyed `(tag, op, a, b)` with payload
   `(x, live)`; sentinel `0` for absent children (keys cannot be NULL);
   leaf values folded into op tags. Real programs pad to max arity (≤27 in
   the delete-rule census) or serialize wide rows.
3. **UF as monotone min-propagation over persistent union-edge facts** — not
   destructive pointer union. `leader(x) := min(leader(leader(x)), leaders
   across incident edges)`, emitted only on strict decrease. Strict
   monotonicity is simultaneously the termination proof and the no-op guard.
   (Destructive one-hop union provably drops equivalences under stale
   leaders — identified and avoided.)
4. **Two-level hashcons lookup before minting**: exact key (live or dead —
   tombstones carry their eclass as a forwarding record), then canonical
   group. Mint = `(SELECT max(id) FROM uf) + dense_rank() OVER (ORDER BY key)`
   over DISTINCT unresolved keys.
5. **Same-key collision assembly**: group all live intents by key with
   `min(x)` + `bool_and(live)`; keys receiving distinct classes emit union
   edges. Tombstone-vs-upsert collisions resolved by anti-join (stale row
   survives one extra wave).
6. **Guard fact re-emission, not just payload updates** — identical edge rows
   suppressed via anti-join against `recurring`, else the delta never empties.
7. **Two-tier caps in a `ctl` state row**: per-ruleset wave budget implements
   `(run N)` — rules gate on `i < N` while congruence/UF/canonicalization run
   on to their own finite fixpoint (a complete rebuild after the last rule
   wave); a global safety cap backstops every branch. Checks must run against
   post-cap *rebuilt* state.
8. **`error()` in the final SELECT** gives `(check …)` semantics: message +
   nonzero exit.
9. Mid-run state may be non-canonical (one-hop leaders); every consumer
   self-corrects on later waves. Nothing may assume full canonicity mid-run.

Known wrong-answer hazard: correlated-EXISTS alias capture (unqualified outer
columns silently self-compare) produced a plausible-looking wrong fixpoint.
Mitigation: compiler emits aggregate-then-LEFT-JOIN-IS-NULL shapes, never
correlated EXISTS with bare columns; plus differential gates vs the reference
backend on every milestone.

## Architecture

Compile the resolved program (desugared + term-encoded + proof-instrumented —
`EGraph::resolve_program` output) to a bundle:

```
1. DDL prelude      — typed function tables (existing shapes)
2. State tables     — egglog_counters, egglog_watermarks(rule_id, watermark),
                      egglog_ctl(pc, halt, changed), egglog_frames(pc, remaining),
                      egglog_schedule(pc, opcode, ruleset, on_change_pc, on_quiet_pc)
3. Input section    — INSERT..SELECT FROM (VALUES …) literals (existing encoder)
4. step.sql         — fixed statement sequence, pc-gated blocks, effect phases,
                      recursive-CTE regions, schedule-advance epilogue in SQL
5. Epilogue         — error()-guarded checks, digest SELECT, COPY outputs
```

Region granularity (the critical sizing decision): **one recursive CTE per
fixpoint region, not one mega-CTE per program.** Regions: (i) the
parent/UF saturate, (ii) ordered-union queue drains (arg_min folds + wave
tags), (iii) rebuild/congruence + canonicalization, (iv) path compression, and
(v) any user ruleset under `saturate` that admits the monotone-keyed encoding.
`run N` unrolls; `seq` chains statements. Branch count stays bounded because
the generated-rule censuses collapse to a handful of schema-parametric
templates (3,892 rebuild rules → 6 classes; 2,169 delete rules → 1; 866
marker; 174 path-compress): emit one parameterized branch per family instance,
never per rule. Measured planning cost ~1 ms/branch (linear to 800 branches)
makes a whole-program mega-CTE at Luminal scale (~7–10k branches) a ~10 s
plan-time mistake — the per-region split avoids it.

Fallback rule (matches the ledger's stop discipline): if a region fails its
semantic gate twice, that region permanently stays a pc-gated statement loop
and the program downgrades from (a) to (b). (a) is a specialization, never a
correctness dependency.

## Milestones

| # | Checkpoint | Lands | Acceptance gate |
|---|---|---|---|
| M0 | **Probe freeze**: commit `probes/*.sql` (all 8 verified claims + prototype invariants, UNION ALL forms) with expected outputs, against pinned 1.5.4 dylib and 1.5.5 CLI | — | every probe's expected output committed; any failure re-routes dependents before code |
| M1 | **Self-parameterization** of existing executors: watermark/ctl/frames tables; scalar-subquery fresh/count/generation; boolean probes → CASE-guarded `error()`; changed-flag computed in SQL | (c)→(b) bridge | eqsat-basic + pointer digests byte-identical to HEAD `37fc161`; Rust readback reduced to {changed, halt}; grep-gate: zero run-derived literals in emitted SQL |
| M2 | **Schedule bytecode + generic driver**: pc-gated fixed `step.sql`; waves/saturates as pc self-loops; driver = schedule-tree interpreter over `egglog_schedule` rows, one changed-flag read per node iteration | **(b)** | eqsat-basic, math, pointer complete with no egglog process alive during execution; digests match M1; driver byte-identical across programs |
| M3 | **General rule compiler**: compositional body/action/merge codegen replaces the six recognizers (they become peepholes); `ReadMode::All`/`Subsumed` predicates; merge-IR semantic key (upstream SPI change) so custom merges (eggcc pair-min) compile to CASE expressions; full workload primitive table | (b) | Luminal/eggcc pass their current rebuild/merge frontiers; fail-closed reasons exhaustive and named |
| M4 | **Fusion + delta seminaive + threads**: fuse per-slot CTAS chains (61 stages/action today) into single pipelined INSERT..SELECT; per-table delta staging (Δ⋈full ∪ full⋈Δ); lift `threads=1` via total-ORDER-BY determinism | (b) | ≥5x statement-count reduction on eqsat-basic; math completes under 110 s; two runs bit-identical at threads=4 |
| M5 | **Recursive regions**: UF saturate, ordered-union drain, rebuild/congruence, path compression as USING KEY statements; counter/wave/pc rows in tagged state; post-CTE materialization; emitted-SQL lints (keyed-sink-behind-GROUP-BY, no-op guards, no bare correlated EXISTS) | (b), enables (a) | STATE.md semantic canaries (one-fold-per-key-per-pass, wave-w-before-w+1, Sym-before-Trans); digest parity with M2; driver iterations ≈ schedule length; 2× region failure ⇒ permanent pc-loop |
| M6 | **Standalone artifact class**: bounded-schedule admission check; `run N` unrolling with changed-gates; self-asserting checks; digest epilogue; `-bail` + per-region transactions | **(a)** | `duckdb < eqsat-basic.compiled.sql` exits 0, digest equals backend run; falsified check exits nonzero; `math.compiled.sql` same; artifact header names its admission proof + engine pin |
| M7 | **Containers, extraction, push/pop**: LIST/STRUCT codecs + container registry tables + relational container rebuild (unnest → canon-join → re-aggregate → re-intern); USING KEY min-cost extraction; schema-snapshot push/pop | (b), (a) where admitted | hardboiled + full eggcc complete; extract parity vs reference on math |

Demo ladder: eqsat-basic (frozen 5,795-statement transcript with
generation=8/fresh_id=318 as the differential oracle) → math-microbenchmark
(iteration-heavy; currently watchdog-censored — M4's proof point) →
pointer-analysis-small (scale + input ingestion; only completed baseline) →
luminal/eggcc/hardboiled as M3/M7 unlock them.

## Performance case and risks

Why this should win where the H-series host matcher lost: matching cost is
already gone (that was settled by the native-sql pivot — pointer completes now
where it never did before). The remaining 13x/9x gap on pointer is
architecture overhead the compiler removes: statement fusion (biggest constant
factor — ~170 µs per temp-table materialization × 61 per action), delta
seminaive (asymptotic on iteration-heavy loads), plan-once recursive regions
(amortizing the ~100 µs parse+plan floor per statement), and threads>1.
Honest bounds: main's free-join engine keeps winning small/latency-bound
workloads; the credible targets are large join-dominant runs — consistent with
the stated goal ("doesn't need to be faster on all, just on some").

Risks to carry in every gate: `recurring` is rescanned wholly each nonempty
wave and recursive-CTE column pruning is unimplemented (regions must stay
narrow); tombstone/edge accumulation is monotone (prototype: 1,154 edge rows
at depth-100 — bounded but real; RSS gates on every milestone); literal-text
SQL has no plan cache (mitigated by fewer/bigger statements — not by prepared
parameters, which defeat filter pushdown); BIGNUM/canonical-decimal readback
pins artifacts to the engine version (declare in header); exact
reference-proof parity stays relaxed to "deterministic, self-consistent,
checker-accepted, equal modulo sort-preserving fresh-ID bijection" — already
the accepted contract.

## Sources

- USING KEY announcement: https://duckdb.org/2025/05/23/using-key
- WITH clause docs (UNION ALL requirement, `recurring.`, connected components):
  https://duckdb.org/docs/current/sql/query_syntax/with.html
- SIGMOD 2025 companion paper "How DuckDB is USING KEY to Unlock Recursive
  Query Performance": https://dl.acm.org/doi/10.1145/3722212.3725107 /
  https://db.cs.uni-tuebingen.de/publications/2025/using-key/
- Lineage: Hirn & Grust, "A Fix for the Fixation on Fixpoints" (CIDR 2023) —
  USING KEY's origin; same group's "One WITH RECURSIVE is Worth Many GOTOs"
  (SIGMOD 2021) — compiling imperative control flow into recursive CTEs, the
  playbook for the schedule state machine.
- Utility functions (`error()`): https://duckdb.org/docs/current/sql/functions/utility

## Artifacts

- Prototype: `/Users/saul/p/wt/egglog-encoding-duckdb-recursive-cte-prototype/`
  (`eqsat_final.sql` re-verified 2026-08-05: `PROVED: (a*2)/2 == a in class 1`,
  10 waves, 78 live enodes, 17 canonical classes, 0.19 s).
- Full research corpus (5 evidence reports, architect + adversary designs,
  8 verification transcripts):
  `/private/tmp/claude-501/-Users-saul-p-egglog-encoding/26fdade1-3a24-4f0a-aa63-869ecfb79543/tasks/ws9u2warh.output`
  (JSON; volatile /tmp — extract anything worth keeping).
- Existing staged-architecture artifacts (comparison baseline):
  `/Users/saul/p/wt/egglog-encoding/duckdb-native-sql/.codex/duckdb-native-sql/artifacts/eqsat-basic.sql`
  (5,795-statement Rust-driven trace, 1.0 s standalone replay).
