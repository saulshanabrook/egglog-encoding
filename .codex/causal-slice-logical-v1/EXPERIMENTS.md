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
| `/root/logical_v1_owner` | terminal check, count-only sink, then accepted code path | Deliver one reviewed checkpoint at a time | Sole code/debug writer in this worktree and its experiment worktree | H0 ready for review; H1 not started | Checkpoint passes or its falsifier fires |
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

## Decisions

- Use the repository's normal append-only `.reports.jsonl` for all benchmarks.
- Compare arithmetic means and 95% intervals; do not substitute medians.
- The count-only sink is a disposable experiment commit and is never merged.
- Semantic creation rows use flat slabs plus ranges; per-fact boxes are banned.

## Results

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

- Frozen old target: clean detached commit
  `0d7ffbb3846d95c2e1299c7fa9a8559f260d2f39`, label `old-fixture`, binary
  SHA-256 `5fa57cb49134fb7329f74c2ad4e7db453f502a33c9ca2bed3b32182319ddd6ab`.
- Frozen new target: clean disposable commit
  `9f57e356bff2fd61a7cadaedc2fe2a6f726aedd7`, label `terminal-math`, binary
  SHA-256 `28e8321eacd7d9cd9c7ea1d759fc45960e5c8b5b0abce06253a7569f797642ed`.
  Its tree contains the terminal fixture, first boundary-canary version, and
  updated proof snapshot over parent `0d7ffbb`. The later test-only 2x2
  strengthening and evidence-only ledger addition do not alter the benchmark
  executable or fixture.

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
receipts remain 4.91–5.20x native; on the independent terminal target they are
5.03–5.55x. H1 therefore retains the intended large recording-cost signal.

New-fixture mean phase totals (95% CI), in seconds:

| Treatment | Search | Apply | Merge | Rebuild | Outside recorded rulesets |
|---|---:|---:|---:|---:|---:|
| off | 0.0920 (0.0876–0.0963) | 0.0975 (0.0956–0.0994) | 0.0478 (0.0450–0.0505) | 0.1432 (0.1412–0.1453) | 0.0408 (0.0369–0.0446) |
| proofs | 1.6750 (1.6008–1.7493) | 1.5179 (1.4983–1.5374) | 1.9343 (1.7520–2.1166) | 2.6289 (2.2943–2.9636) | 0.1014 (0.0728–0.1300) |
| causal-receipts | 0.1707 (0.1672–0.1742) | 0.8353 (0.8221–0.8484) | 0.6575 (0.5847–0.7302) | 0.3811 (0.3545–0.4077) | 0.1850 (0.1817–0.1883) |

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

**Next probe:** H1 is the disposable count-and-digest-only sink. Its accepted
gate remains three Math rounds plus the Eggcc cross-workload screen; H0 adds no
evidence for or against that hypothesis.
