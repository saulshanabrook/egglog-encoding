# Logical causal slicing experiment

## Steering frame

- Mission: make exact logical-support slicing plus unchanged proof replay faster
  than full proof mode on Math, Eggcc, Pointer, Hardboiled, and Luminal.
- Starting point: `0d7ffbb3846d95c2e1299c7fa9a8559f260d2f39`.
- Exactness: retain one actual native check-support derivation; physical-only
  rekeys, aliases, and rebuild versions are not provenance.
- Non-goals: Herbie, parallel capture, Prefix, projection fallback, selector
  search, partial bindings, proof translation, or a third replay architecture.
- First frontier: replace Math's shallow check, preserve the old/new proof
  baselines, then run the count-only observation-floor experiment.
- Hard stop: count-only Math above 1.50x native, digest drift, or two
  non-improving attempts in one domain.

## Roster

| Agent | Circle/domain | Aim | Authority | Status | Stop condition |
|---|---|---|---|---|---|
| `/root/logical_v1_owner` | terminal check, count-only sink, then accepted code path | Deliver one reviewed checkpoint at a time | Sole code/debug writer in this worktree and its experiment worktree | H0 accepted; H1 active on disposable branch | Checkpoint passes or its falsifier fires |
| semantic reviewer | receipt/replay correctness | Find concrete unsoundness against the logical-support contract | Read-only feedback | pending | One finite review per checkpoint |
| hot-path reviewer | allocation and event-path cost | Verify measured cost moved for the stated reason | Read-only feedback | pending | One finite review per performance checkpoint |
| benchmark reviewer | `./bench.py` cache/provenance and acceptance | Validate exact rows, hashes, ratios, and failures | Read-only; final-gate commands by assignment | pending | Report is reproducible or rejected |

## Active hypothesis H0: terminal observation

- Observation: the current Math check is true long before the declared final
  wave and therefore does not exercise a deep causal cone.
- Hypothesis: the source-rooted eleven-deep integration-by-parts check fails
  through wave 10 and succeeds at wave 11 in ordinary and strict proof modes.
- Confirming prediction: depth 10 succeeds at wave 10; depth 12 still fails at
  wave 11.
- Falsifier: the replacement succeeds early, fails at wave 11, or changes the
  two modes' truth result.
- Next probe: preserve the current fixture/full-proof baseline, apply only the
  check replacement, and run the three boundary cases.

## Active hypothesis H1: count-only observation floor

- Observation: full receipts take about 5x native time and 6x native RSS on
  terminal Math, but most of their work constructs provenance data rather than
  merely observing native decisions.
- Hypothesis: retaining the same serial native observation sites while updating
  only fixed counters and a deterministic noncommutative 128-bit digest costs
  at most about 1.30x native on Math and remains below the hard 1.50x screen on
  Math and Eggcc.
- Confirming prediction: normalized count-mode and full-receipt summaries agree
  on facts, applied native unions (`equality edges + native aliases`), redundant
  unions, successful checks, rebuild events, container events, and aggregate
  candidate/action batches for focused programs; the digest is stable across
  repeated serial executions. Candidate batches contribute active and
  successful lane counts and reserve one contiguous ordinal range per batch,
  but never allocate or retain a per-lane witness.
- Falsifier: any normalized sequence/count drift, nondeterministic digest,
  changed program outcome, three-round Math ratio at or above 1.50x, or a
  confirmed three-round Eggcc ratio at or above 1.50x.
- Experimental boundary: this branch temporarily routes CLI
  `--causal-receipts` to count mode so the existing benchmark treatment remains
  unchanged. Direct `enable_causal_receipts` APIs remain full fidelity for
  equivalence tests. Count activation must not construct frontend catalogs,
  terms, witnesses, facts, matches, causes, table sidecars, equality forests,
  or snapshots.
- Digest contract: mix normalized event tag, monotone event sequence, and fixed
  count fields only. Stable lexical site ordinals may be used only where the
  native path already has them; raw pointers, `RowId`, randomized hashes, and a
  new catalog are forbidden.

## Decisions

- Use the repository's normal append-only `.reports.jsonl` for all benchmarks.
- Compare arithmetic means and 95% intervals; do not substitute medians.
- The count-only sink is a disposable experiment commit and is never merged.
- Semantic creation rows use flat slabs plus ranges; per-fact boxes are banned.

## Results

### H1 checkpoint: fixed count-and-digest sink (2026-07-24)

**Status before timing:** semantic floor equivalence confirmed on the focused
canary and terminal Math. No benchmark timing has been collected yet.

- The first red test failed to compile because the separate observation type
  and APIs did not exist. The first executable comparison then found equal
  counters but a different digest: count mode numbered the first explicit run
  as wave 0 while durable receipts start at wave 1. This was a real normalized
  identity mismatch, not digest noise. Count mode now shares the durable wave
  numbering invariant.
- Count activation creates no `CausalState`, `ReceiptSnapshot`, replay catalog,
  terms, witnesses, fact/match/cause arenas, table receipt sidecars, or equality
  forest. Full receipts and count mode feed the same post-decision observer only
  so their normalized event streams can be compared.
- The fixed sink uses relaxed `u64` atomics, including two digest lanes read at
  a quiescent barrier. There is no per-event lock or allocation. Candidate
  observation is one aggregate update per native action batch: active lanes,
  successful lanes, and one contiguous ordinal-range reservation. Internal
  runtime action ids are deliberately excluded from the digest.
- Shared hooks in this checkpoint cover aggregate candidate batches, effective
  sorted-table facts, applied/redundant native UF unions, wave boundaries, and
  successful positive checks. Dedicated rebuild/container counters remain zero;
  effective rows and unions produced by Math rebuild are still observed through
  the table/UF decision hooks. Container and removal hooks were not added
  speculatively.

Focused full/count result (exactly equal): 15 events, 1 wave, 4 candidate
batches, 4 active/successful lanes, 7 facts, 1 applied union, 1 redundant union,
1 successful check, and identical digest.

Terminal Math full/count result (exactly equal):

```text
CausalObservationSummary {
  events: 2111697,
  waves: 11,
  candidate_batches: 7520,
  candidate_lanes: 943133,
  successful_lanes: 943133,
  reserved_native_ordinals: 943133,
  facts: 1731581,
  applied_native_unions: 350368,
  redundant_unions: 22216,
  successful_checks: 1,
  rebuild_events: 0,
  container_events: 0,
  digest: 78064506755757294491844443265500776026,
}
```

Validation commands:

```bash
cargo test -p egglog causal_observation_floor --lib -- --nocapture
cargo test -p egglog \
  tests::causal_observation_floor_matches_math_receipt_decisions \
  --lib -- --ignored --exact --nocapture
cargo test -p egglog causal_ --lib -- --nocapture
cargo test -p egglog --test causal_receipts_cli -- --nocapture
cargo test -p egglog-core-relations observations:: --lib -- --nocapture
cargo fmt --all -- --check
git diff --check
```

#### H1 Math count-floor gate (2026-07-24)

**Status:** passed the hard 1.5x recording screen. This is deliberately a
conservative count-plus-digest floor, not a storage-free lower bound: the sink
performs six relaxed atomic accesses in every digest mix in addition to its
event counter(s). For this Math execution, the 2,111,697 normalized events
therefore perform approximately 14.812 million relaxed atomic accesses
(14,811,982 before the quiescent summary loads). A serial logical recorder can
replace much of that fixed atomic/digest traffic with plain arena/map writes;
the result prices observation plus an order-sensitive validation digest rather
than claiming that all 0.967x point behavior is irreducible recording cost.

The normal append-only `.reports.jsonl` supplied the exact six selected rows.
They share clean target
`7701f92d686c3c4e10861a0c7615ec50bba5754e`, main backend, 120-second timeout,
empty fact-directory hash, binary SHA-256
`7dcae229c45dfa8923bac01e3f58ec3326b56503947f99a3025f6f25b4195214`,
and fixture SHA-256
`7303e72d4870a2855682d21a30fc3b0237dfe1c650def398b7da83472505ef1f`.
Every row has `status=success`, `target_is_dirty=false`, and null exit-code,
signal, and error-message fields.

| Treatment | JSONL line | Started at | Wall (s) | Peak RSS (bytes) |
|---|---:|---|---:|---:|
| off | 1 | 2026-07-24T06:01:15Z | 0.427372708014 | 271237120 |
| off | 3 | 2026-07-24T06:02:08Z | 0.417492666020 | 271761408 |
| off | 5 | 2026-07-24T06:02:09Z | 0.390859999985 | 270450688 |
| causal-receipts (count sink) | 2 | 2026-07-24T06:01:15Z | 0.408198249992 | 270827520 |
| causal-receipts (count sink) | 4 | 2026-07-24T06:02:08Z | 0.393671041995 | 270827520 |
| causal-receipts (count sink) | 6 | 2026-07-24T06:02:09Z | 0.393192584015 | 271368192 |

Arithmetic means and two-sided 95% Student-t intervals (`n=3`, `df=2`,
`t*=4.302652729749462`):

| Metric | Off mean (95% CI) | Count mean (95% CI) | Count/off Fieller ratio (95% CI) |
|---|---:|---:|---:|
| Wall | 0.411908458 s (0.364992967–0.458823949) | 0.398353959 s (0.377167339–0.419540578) | 0.967093x (0.856782–1.102826) |
| Peak RSS | 271149738.667 B (269510916.751–272788560.582) | 271007744 B (270232302.714–271783185.286) | 0.999476x (0.992829–1.006197) |

Mean phase totals:

| Treatment | Search | Apply | Merge | Rebuild | Execution overhead | Outside recorded rulesets |
|---|---:|---:|---:|---:|---:|---:|
| off | 92.139839 ms | 94.641997 ms | 44.820013 ms | 135.156389 ms | 0.732873 ms | 44.417347 ms |
| causal-receipts (count sink) | 87.504125 ms | 92.362780 ms | 46.366667 ms | 133.806223 ms | 0.640720 ms | 37.673444 ms |

Command (the first invocation collected one row per endpoint; the second
reused those exact rows and appended two more per endpoint):

```bash
./bench.py egglog/tests/math-microbenchmark.egg \
  --target . --treatment causal-receipts --compare-treatment off \
  --rounds 3 --timeout-sec 120 --detail phases --format markdown
```

The point estimate is slightly below native and its interval includes parity;
the only H1 decision is that the observation floor is decisively below the
1.5x screen. No Eggcc row was collected at this checkpoint.

### H0: terminal Math observation (2026-07-24)

**Status:** confirmed. The replacement check first succeeds after wave 11 and
strict proof testing validates the resulting eleven-step proof. No count-only
sink code was started in this checkpoint.

**Fixture boundary:**

- Old fixture SHA-256:
  `6017cf55fcc0bbc0dfb6c512b1a805709a33ac501b7f72796a74a788c804f77c`.
- New fixture SHA-256:
  `7303e72d4870a2855682d21a30fc3b0237dfe1c650def398b7da83472505ef1f`.
- The first focused canary executed one monotone ordinary e-graph and directly
  observed failure after waves 0 through 10 and success after wave 11.
- The committed canary derives the terminal check from the fixture, then uses
  fresh states for the strict 2x2 boundary in both ordinary and proof-testing
  modes: depth 10 passes and depth 11 fails at wave 10; depth 11 passes and
  depth 12 fails at wave 11.
- The ordinary file trial and `proofs/math_microbenchmark_proof_testing` both
  pass. The proof snapshot changed from one shallow rewrite to the expected
  eleven equality-producing integration-by-parts applications. It contains 21
  textual `Rule` forms because ten derived-premise proofs are also explicit;
  these are proof obligations, not extra saturation waves.

**Benchmark provenance:** all accepted rows are in the normal append-only
`.reports.jsonl`, use main backend, `-j 1`, three rounds, and a 120-second
per-process timeout. The first six rows collected from target `.` had
`target_is_dirty=true` due to untracked experiment state; they are retained as
exploratory cache history but are superseded below.

- Frozen old target: hash-pinned executable collected from the clean
  branch-attached worktree at target metadata
  `0d7ffbb3846d95c2e1299c7fa9a8559f260d2f39`, label `old-fixture`, binary
  SHA-256 `5fa57cb49134fb7329f74c2ad4e7db453f502a33c9ca2bed3b32182319ddd6ab`.
- Frozen new target: clean disposable commit
  `9f57e356bff2fd61a7cadaedc2fe2a6f726aedd7`, label `terminal-math`, binary
  SHA-256 `28e8321eacd7d9cd9c7ea1d759fc45960e5c8b5b0abce06253a7569f797642ed`.
  Its tree contains the terminal fixture, first boundary-canary version, and
  updated proof snapshot over parent `0d7ffbb`. The later test-only 2x2
  strengthening and evidence-only ledger addition do not change executable
  source or fixture bytes. The embedded Git version means the executable bytes
  themselves may still differ across commits with identical executable source.

H0 review correction: target `old-fixture` was built through the attached clean
branch worktree at
`/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1`; its exact identity
is the opaque binary SHA above. Its embedded `FULL_VERSION` is stale at
`1872563`, so that string is not provenance. The old fixture selector is the
absolute file
`/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1/egglog/tests/math-microbenchmark.egg`;
using the relative selector after H0 edits resolves the terminal fixture from
the invocation cwd instead. Detached benchmark worktree `terminal-math`
preserves `9f57e35`; the accepted H0 source is durable at `8c4e60d`.

Arithmetic means and two-sided 95% Student-t intervals (`n = 3`):

| Fixture | Treatment | Wall rounds (s) | Wall mean (95% CI) | RSS mean (95% CI) |
|---|---|---|---|---|
| old | off | 0.4324, 0.4612, 0.4168 | 0.4368 s (0.3808–0.4928) | 256.1 MiB (255.7–256.5) |
| old | proofs | 8.4413, 8.1917, 8.0713 | 8.2347 s (7.7660–8.7035) | 2940.3 MiB (2237.3–3643.2) |
| terminal, old binary | off | 0.4215, 0.4217, 0.4223 | 0.4218 s (0.4208–0.4229) | 258.6 MiB (256.9–260.3) |
| terminal, old binary | proofs | 8.1378, 7.7951, 7.8643 | 7.9324 s (7.4822–8.3826) | 3165.2 MiB (2869.2–3461.3) |
| terminal, old binary | causal-receipts | 2.1047, 2.1386, 2.1519 | 2.1318 s (2.0713–2.1922) | 1538.4 MiB (1484.3–1592.6) |
| terminal | off | 0.4288, 0.4183, 0.4189 | 0.4220 s (0.4074–0.4366) | 258.7 MiB (256.6–260.8) |
| terminal | proofs | 8.1522, 7.7331, 7.7024 | 7.8626 s (7.2383–8.4869) | 3218.9 MiB (2292.0–4145.8) |
| terminal | causal-receipts | 2.2209, 2.2044, 2.2661 | 2.2305 s (2.1511–2.3098) | 1561.7 MiB (1559.0–1564.4) |

The isolated same-binary comparison uses binary `5fa57c…`: native moved from
0.4368 s to 0.4218 s and full proofs from 8.2347 s to 7.9324 s, with overlapping
old/new intervals. The independent clean terminal target reproduced 0.4220 s
native, 7.8626 s full proofs, and 2.2305 s receipts. These are fixture-baseline
observations, not performance improvements. On the same old binary, terminal
receipts remain 5.05x native (95% Fieller CI 4.91–5.20x); on the independent
terminal target they are 5.29x (95% Fieller CI 5.03–5.55x). H1 therefore
retains the intended large recording-cost signal.

Terminal-target (`28e832…`, report rows 13–21) mean phase totals (95% CI), in
seconds. `Outside recorded rulesets` already subtracts `Execution overhead`;
the latter is shown separately so all recorded time remains auditable.

| Treatment | Search | Apply | Merge | Rebuild | Execution overhead | Outside recorded rulesets |
|---|---:|---:|---:|---:|---:|---:|
| off | 0.0920 (0.0876–0.0963) | 0.0975 (0.0956–0.0994) | 0.0478 (0.0450–0.0505) | 0.1432 (0.1412–0.1453) | 0.0008 (0.0006–0.0009) | 0.0408 (0.0369–0.0446) |
| proofs | 1.6750 (1.6008–1.7493) | 1.5179 (1.4983–1.5374) | 1.9343 (1.7520–2.1166) | 2.6289 (2.2943–2.9636) | 0.0050 (0.0047–0.0053) | 0.1014 (0.0728–0.1300) |
| causal-receipts | 0.1707 (0.1672–0.1742) | 0.8353 (0.8221–0.8484) | 0.6575 (0.5847–0.7302) | 0.3811 (0.3545–0.4077) | 0.0009 (0.0009–0.0010) | 0.1850 (0.1817–0.1883) |

**Commands:**

```bash
cargo test -p egglog --test math_terminal_check -- --nocapture
cargo test -p egglog --test files -- math_microbenchmark --exact
cargo test -p egglog --test files -- \
  'proofs/math_microbenchmark_proof_testing' --exact

./bench.py egglog/tests/math-microbenchmark.egg \
  --target old-fixture=@0d7ffbb3846d95c2e1299c7fa9a8559f260d2f39 \
  --treatment proofs --compare-treatment off --rounds 3 \
  --timeout-sec 120 --detail phases --format markdown --force-run

./bench.py egglog/tests/math-microbenchmark.egg \
  --target terminal-math=@9f57e356bff2fd61a7cadaedc2fe2a6f726aedd7 \
  --treatment proofs --compare-treatment off --rounds 3 \
  --timeout-sec 120 --detail phases --format markdown --force-run

./bench.py egglog/tests/math-microbenchmark.egg \
  --target terminal-math=@9f57e356bff2fd61a7cadaedc2fe2a6f726aedd7 \
  --treatment causal-receipts --compare-treatment off --rounds 3 \
  --timeout-sec 120 --detail phases --format markdown

# Same old binary with the terminal fixture resolved from this invocation cwd.
./bench.py egglog/tests/math-microbenchmark.egg \
  --target old-fixture=@0d7ffbb3846d95c2e1299c7fa9a8559f260d2f39 \
  --treatment proofs --compare-treatment off --rounds 3 \
  --timeout-sec 120 --detail phases --format markdown

./bench.py egglog/tests/math-microbenchmark.egg \
  --target old-fixture=@0d7ffbb3846d95c2e1299c7fa9a8559f260d2f39 \
  --treatment causal-receipts --compare-treatment off --rounds 3 \
  --timeout-sec 120 --detail phases --format markdown
```

For a fresh reproduction of the old-fixture rows, replace the first command's
relative file selector with:

```text
/Users/saul/p/wt/egglog-encoding/causal-slice-receipts-v1/egglog/tests/math-microbenchmark.egg
```

**Next probe:** H1 is the disposable count-and-digest-only sink. Its accepted
gate remains three Math rounds plus the Eggcc cross-workload screen; H0 adds no
evidence for or against that hypothesis.

### H1 accepted: conservative observation floor (2026-07-24)

**Status:** accepted. The terminal Math three-round gate above and the Eggcc
cross-workload screen both remain well below the hard 1.5x wall-time boundary.
Commits `661ef77855be5ef59dbbbb1e476890051514acb7` and
`58c18cf28d659896204eb81c7b2b850c3219c3c9` are disposable measurement
commits and **must not be merged**. Their only purpose is to falsify or accept
the logical-v1 observation floor before implementing the real recorder.

The Eggcc screen used the clean container checkpoint `58c18cf`, main backend,
one round, and a 120-second timeout. Normal append-only `.reports.jsonl` lines
7 and 8 share binary SHA-256
`d0126965036b2cf64791f6241eb4330409adcbf8d6f97f9fbb06fa864cbeee30`,
fixture SHA-256
`fcbaaa9d8910edb5b8f1e1304458288fa5c437e86c4c0da99faec20a0d333e9e`,
and an empty fact-directory hash. Both rows have `status=success`,
`target_is_dirty=false`, and null exit-code, signal, and error-message fields.

| Treatment | JSONL line | Started at | Wall (s) | Peak RSS (bytes) |
|---|---:|---|---:|---:|
| off | 7 | 2026-07-24T06:32:01Z | 1.161140874989 | 127696896 |
| causal-receipts (count sink) | 8 | 2026-07-24T06:32:02Z | 1.135058333020 | 127418368 |

With one observation per endpoint, intervals are undefined. The exact point
ratios are 0.977537x wall time and 0.997819x peak RSS (count/off).

One-round phase totals:

| Treatment | Search | Apply | Merge | Rebuild | Execution overhead | Outside recorded rulesets |
|---|---:|---:|---:|---:|---:|---:|
| off | 698.822811 ms | 15.883713 ms | 12.615425 ms | 253.880711 ms | 19.922574 ms | 160.015641 ms |
| causal-receipts (count sink) | 694.383762 ms | 15.482850 ms | 13.170166 ms | 254.277443 ms | 20.082998 ms | 137.661114 ms |

The ignored exact diagnostic ran the same Eggcc fixture once with full receipts
and once with count-only capture. Its summaries and order-sensitive digests
were identical:

```text
CausalObservationSummary {
  events: 234853,
  waves: 2677,
  candidate_batches: 9150,
  candidate_lanes: 312699,
  successful_lanes: 286490,
  reserved_native_ordinals: 312699,
  facts: 197300,
  applied_native_unions: 20801,
  redundant_unions: 4924,
  successful_checks: 1,
  rebuild_events: 0,
  container_events: 95,
  digest: 8539441538684068070460568722295956286,
}
```

All 95 container observations are applied registry-canonicalization native
unions; redundant container proposals contribute zero. The preceding full
receipt design also produced 30,915 rebuild causes, but logical-v1 deliberately
deletes rebuild versions and reconstructs congruence lazily, so H1 does not
price those obsolete records or call them missing coverage. The scheduled
Eggcc run reached no deletes, so this screen also requires no removal hook.

The accepted conclusion is bounded: native observation plus a conservative
order-sensitive digest is near parity on both tested shapes. H1 does not prove
that the future logical-support arena is free; it proves that the execution
hooks themselves do not impose the former multi-x recording cost.

### Checkpoint A: compact promoted-match bindings (2026-07-24)

**Status:** implementation green; performance deliberately unmeasured pending
independent review. The red mixed-layout canary initially preserved the public
three-term match but observed zero new logical/stored counters. After the
change, the same match exposes the identical source-order term vector while
retaining only its one `Current` handle in the provisional and durable arenas.

The rule catalog now shares one canonical binding recipe per causal rule.
`Current` entries have dense residual slots; `Premise` and `Constant` entries
are reconstructed lazily only when producing the public snapshot. Exact
RHS-produced terms remain residual handles rather than being replaced by a
global value lookup. Observed focused shapes:

| Canary | Logical handles | Stored handles |
|---|---:|---:|
| mixed premise/constant/current | 3 | 1 |
| premise plus primitive-only current | 2 | 1 |
| exact RHS-only current | 1 | 1 |
| four-premise decomposed join | 4 | 0 |

The old `term_handles` counter remains a compatibility alias for logical
handles. New counters report logical/stored handles and their `ReplayTermId`
payload bytes separately. This checkpoint does not alter facts, rekeys,
equality receipts, containers, removals, slicing, or replay.

**Commands:**

```bash
# Red: failed at logical_match_term_handles, observed 0 instead of 3.
cargo test -p egglog-core-relations \
  promoted_matches_store_only_current_terms_but_expand_the_public_snapshot \
  -- --nocapture

# Green validation.
cargo test -p egglog-core-relations
cargo test -p egglog-bridge --no-run
cargo test -p egglog-bridge causal_receipts
cargo fmt --all -- --check
git diff --check
cargo clippy -p egglog-core-relations --all-targets -- \
  -D warnings -A clippy::only-used-in-recursion
```

The core-relations run passed 147 unit tests and 2 doc tests. The bridge test
target compiled successfully and its serial-activation canary passed. Strict
Clippy is green for this checkpoint after allowing the unrelated, pre-existing
`prepare_dependencies` recursion-only parameter warning. No `./bench.py` run
belongs to this checkpoint; the next recording measurement requires explicit
continuation after review.

#### Checkpoint A review follow-up

Independent review found that the first green implementation compacted durable
storage but still walked every logical binding during promotion and copied the
lane's residual slice into `PreparedMatch`. The follow-up makes preparation
proportional to the actual dependency payload: it validates each resolved
premise `FactId` once, validates the already-dense residual slice for missing
handles, and retains only the premise array in `PreparedMatch`. Promotion now
copies residuals directly from the batch-owned lane slice into the provisional
arena. It does not inspect `Premise` or `Constant` recipe entries.

The unchanged core-relations suite again passed 147 unit tests and 2 doc tests,
including the mixed-layout, exact-RHS, primitive-only Current, decomposed, and
invalid-premise atomicity canaries. Scoped strict Clippy and formatting remain
green. No benchmark was run for this review fix.

### Checkpoint A measured gate: insufficient (2026-07-24)

**Status:** the compaction is coherent but fails the recording-cost gate. Move
directly to Checkpoint B; do not spend an A-only tuning cycle.

The normal append-only `.reports.jsonl` lines 31–32 measure clean commit
`84fb6f730a387036415112d6b725c0cd4b04a507`, main backend, terminal Math,
one round, and a 120-second timeout. Both rows have `status=success`, binary
SHA-256
`70bb5f6c5fc0f99f87996d51d242538b9cb20e8c47b6d26e0f8d7a8d03c5e696`,
fixture SHA-256
`7303e72d4870a2855682d21a30fc3b0237dfe1c650def398b7da83472505ef1f`,
and no fact directory.

| Treatment | Wall | Peak RSS | Search | Apply | Merge | Rebuild |
|---|---:|---:|---:|---:|---:|---:|
| off | 0.425444 s | 258.031 MiB | 0.095037 s | 0.098011 s | 0.047577 s | 0.137520 s |
| causal-receipts | 2.031365 s | 1488.750 MiB | 0.158733 s | 0.761436 s | 0.592153 s | 0.343844 s |

With one observation per endpoint, confidence intervals are undefined. The
point ratios are 4.77469x wall time and 5.76965x peak RSS. Relative to the
previous accepted full-receipt three-round mean of 2.2305 s (5.29x native),
the current one-round receipt time is descriptively 8.93% lower. This is a
modest improvement, not evidence that match-payload compaction is sufficient:
the result remains far above the 1.5x screen, and the current-versus-prior
comparison mixes a single observation with an earlier three-round mean.

A 10-second `./bench.py profile` sample on the current causal-receipts target
puts the remaining self CPU in the shadow structural recorder rather than
match expansion:

| Self sample | Share |
|---|---:|
| `ReplayTermStore::node` | 6.8% |
| `ReplayTermStore::install_value` | 5.2% |
| `ReplayTermStore::intern` | 3.8% |
| `ReplayTermStore::lookup` | 2.6% |
| `ReplayTermStore::intern_call` | 1.5% |
| `ReceiptBatch::record_fact_with_terms` | 2.5% |
| `CausalReceipts::constructor_row_terms` | 1.7% |
| `CausalReceipts::finalize_wave` | 3.7% |

These sampled self percentages are not additive wall-time accounting. They are
directional evidence for Checkpoint B's fact-graph-as-term-graph change: remove
the parallel `ReplayTermStore`/eager fact-term construction rather than tuning
the now-compact match payload. Checkpoint A remains landed because it removes
real per-match storage and preserves exact Current handles, but it is rejected
as the sufficient performance intervention.
