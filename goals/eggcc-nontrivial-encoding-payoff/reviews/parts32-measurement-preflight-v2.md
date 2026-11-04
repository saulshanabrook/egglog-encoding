# Parts32 measurement preflight audit: process policy v2

**Verdict: PASS to create a new preflight and collect the two frozen sessions under policy v2.** This is a protocol-readiness verdict, not performance evidence. At this independent audit, `timing-preflight.json`, the entire `timing/` directory, and all sample, warmup, process-check, and independent-verification outputs were absent. The sole rejected preflight remains intact. This audit ran syntax, static identity, and pure synthetic checks only; it did not run a preflight, host process inventory, compilation, native workload, or timing session. It changed only this review file.

## Current bindings

Paths below are relative to `benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration/`.

| Artifact | Current SHA-256 |
| --- | --- |
| `prospective-timing-design-frozen.json` | `c646d77e41334fd252a4e951245068f771afbbb41e44cd828e30edd58b0f6367` |
| `prepare-timing.py` | `57c3d7a9195e7d28e9563936effe26585dd1a9953cc59af31922ab7063861577` |
| `timing.py` | `bf71a082ce5afccc1a61f15f5c9162747808831c264133f62689dc43345ddb3f` |
| `verify-timing.py` | `2e01190ac2d09f8d9b368d049498e1c30f5c0041ad3f848f05860b6313e77749` |
| `check-process-policy.py` | `251394f693723bfd1aa156883fe3430db1922104219d421b5c4a443ad0789c3a` |
| `final-source-identities.json` | `932ca349f56070c4810edde24f1d23e97481322f1ddbf2af743f083b2cf2007b` |
| `artifact-identities.json` | `6d19abc65ef398d5bafa4f32d7a0649de45c42f2354a9d8056148713b8b8a57a` |
| `process-policy-static-validation.json` | `4739f75cb4bc1d713b5ee5930c6cc6bddca320b94af27e7237b0d65a68264754` |
| `final-source.tar` | `ba2f65df7091573a594b7c51ec68a8b3665b5c85f279fe4415ca0f6e08565873` |
| `bin-reviewed-final/eggcc` | `d712e8347bf6eea231de829174a9436f411a3cedfd210daf8e7c4614c2371d2f` |
| `final-reviewed/fixtures/source.bril` | `d1fe5b6ace306fff529d1ed7bac03609066624cf750fc0238cb71fcbee583ae0` |
| `timing-preflight-rejected-1792434879825091000.json` | `2f07377c98d30c53197682d0c1ef8feccefe4eaf117d936f6279f5461519841e` |

All 23 design bindings match both the frozen design and the static receipt: four artifacts for each of five arms, plus source input, compiler binary, and source archive. All 17 source-manifest file identities match; the 13 entries with archive paths also match their actual archive member bytes. All 11 entries in the earlier artifact manifest match their pre-existing hashes. The five separately hashed runtime binaries are:

| Arm | Current binary SHA-256 |
| --- | --- |
| `U0` | `0225044fd41b38a39e7281908ed6a90da5702da64736d34056c6d72ff0197bbb` |
| `B1` | `bcab16fe955e1ecbb1b62c5e040e662d5b65a266146da36a33d236c6e3c683aa` |
| `SeedOnly` | `0092b47bb94281266da5f7586569c2e396b0b38f3f9d88d401ede6ad4f78ef46` |
| `Manual` | `7cf36403f071dfd4cf734bd7353843042814d016de473766c485e385ea6ffb2c` |
| `Encoding` | `b4159d556b2f9bcb6407f0e24b7bd79296c9b1554073a173a5b5a2bb5ff372d2` |

`U0`, `B1`, and `SeedOnly` still share optimized Bril and both entry assemblies. `Manual` and `Encoding` likewise share those three code artifacts. These identities were checked from file contents, rather than inferred from labels or accepted from the receipt.

## Policy and retained rejection

The producer declares policy version 2 with a fixed `material_cpu_percent` of `75.0`. The verifier independently reconstructs the same complete dictionary without importing producer code. Known compiler/benchmark executable basenames and prefixes reject at every utilization, including zero. Every other process rejects at CPU **>=75%**. Only the collector PID and its inventory subprocess PID are exempt; GUI names have no special treatment.

The unchanged v1 rejection contains WindowServer at 16.7%, iTerm2 at 49.6%, and `protobuf-3080012d9de58429` at 98.4%. Replaying its retained process rows through the real v2 parser rejects protobuf alone. Removing that row admits the remaining inventory. The later documented GUI values, 28.6% and 48.2%, also pass synthetically. A GUI process at 75% still fails, as does an unknown executable at exactly 75%; 74.9% passes. The threshold therefore makes the documented prospective correction while continuing to catch the observed competing test.

The preparer imports the revised capture function, so a newly created preflight records v2, the complete process list, its hash, and the revised producer/verifier hashes. Sessions retain inventories at start, every 15-cycle boundary, and end. The verifier recomputes the competitor list and policy, then checks snapshot hashes, checkpoint contexts, owner identity, monotonic order, process-check file hashes, event hashes, completion, and summary bindings. It does not trust a producer's claimed passing result.

## Frozen measurement safeguards

The frozen design hash is identical to the prior audit. The three workloads, five arms, seven comparisons, two sessions, 90 cycles, 32 sequential invocations per observation, and three warmups per arm/workload remain fixed. Independent checks covered all 12 complete 15-cycle blocks: each arm occupies each position three times, every directed adjacent arm pair appears three times, and each workload occupies each position five times. Session 2 reverses every corresponding arm and workload row.

Current producer and verifier retain the cycle log-ratio estimator, `exp(median(log ratios))`, 10,000 bootstrap draws over six whole joint blocks, seed `20261019`, and per-workload/per-session acceptance. The upper 95% bound must be below `0.99` for `Encoding/U0`, `Manual/U0`, and `Encoding/B1` in both sessions. Any same-workload placebo point estimate below `0.99` in both sessions or above `1.01` in both sessions makes the final result inconclusive. Workloads and sessions are not pooled. A separate synthetic six-block input produced identical producer/verifier interval endpoints: `[0.8816999489622306, 0.8896999494211517]`.

A synthetic call-order check observed exactly 32 mocked `subprocess.run` calls between the two timer reads; every return-code, stderr, stdout, and output-hash inspection followed the second read. Nonzero exit, stderr, wrong stdout, and timeout each retained a failure event and aborted in separate synthetic checks. Real output checks, row hashes, exact order/count/uniqueness checks, recomputation of statistics and acceptance gates, and source/artifact/preflight bindings remain present in current source.

Preflight and independent-verification writes use exclusive creation. Sessions refuse an existing directory and create their directory freshly; summary writes are exclusive. Every persisted row/event and final artifact is flushed and fsynced. The common nonblocking measurement lock remains, as do failure retention and the verifier's requirement for complete, failure-free sessions. The unchanged preparer and current verifier reject optimized Python.

The v1 producer and verifier are retained only by their hashes in the prior audit; no old source copies or explicit patch were available for direct bytewise comparison. Consequently, this audit establishes that current code satisfies the frozen safeguards and prior audited requirements. It cannot independently prove that every changed source byte since v1 is a policy constant or comment. The unchanged design, unchanged preparer, and matching pre-existing artifact identities provide the cohort continuity evidence.

## Import incident and checks

Reading `inspect.py` confirms that its top-level work reads retained JSON/LLVM/assembly and writes 52 extracted function files, 12 diffs, and `inspection.json`: 65 derived files. It contains no compilation or native-execution calls. These paths lie outside the frozen `final-reviewed` arm files and do not occur in the artifact identity manifest. All 65 current hashes match the post-incident receipt. There are no pre-import hashes, so historical byte identity for those derived files remains unestablished; this audit does not turn that uncertainty into a claim of unchanged derived output. All artifacts with pre-existing frozen bindings still match.

The checker removes its directory from module search before importing `unittest.mock` and explicitly loads the producer and verifier by absolute path. Both `python3 -I -B check-process-policy.py` and ordinary `python3 -B check-process-policy.py` passed all 41 cases. Hashes and mtimes of the 65 derived files remained unchanged across the ordinary invocation. Additional independent synthetic checks rejected 14 corrupted or forbidden snapshots, rejected four malformed utilization/inventory inputs, checked the timer boundary and four failure paths, and confirmed bootstrap parity. Syntax parsing passed for all four scripts without writing bytecode.

The shared-host limitations documented by the amendment remain: multiple subthreshold processes, short-lived work between checkpoints, and other resource contention can evade admission. The 75% rule is not a calibrated noise bound. Collection still requires the owner to keep competing work out of the window, and the balanced/reversed schedules, two mandatory sessions, and identical-code placebo gates remain necessary. No accepted preflight or timing sample was generated by this review.
