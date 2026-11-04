# Parts32 measurement preflight audit: whole-session retry

**Verdict: PASS to issue a fresh exclusive preflight and, only if it admits the host, rerun all 90 cycles of session 1 from the beginning and then all 90 cycles of session 2.** This authorizes an environmental whole-session retry. It does not make the failed campaign performance evidence and does not authorize reusing, selecting, summarizing, or deleting any of its partial rows.

I did not read `elapsed_ns` or any other performance value from `samples.jsonl`, compute a ratio or estimate, run a preflight, launch a native benchmark, compile, or edit the design, producer, verifier, cohort, or evidence. I used byte hashes and line counts for `samples.jsonl` and `warmups.jsonl`; I decoded only the event and process-check records needed to audit the failure.

## Preserved failed campaign

The manifest itself has SHA-256 `47b4e0ca1a7d6faaec9bb686fb9baddb0dd115dc8b97e952f4e69aee950adc0b`. Every byte it claims to preserve recomputes to the recorded hash:

| Preserved artifact | Recomputed SHA-256 | Lines |
| --- | --- | ---: |
| accepted preflight, now `timing-preflight-aborted-process-admission-01.json` | `cd7691e1feec57a02093cab4b4bd9890c892f6c38073ea019c069d56846fc1a3` | — |
| screen transcript | `1aed44d9beb92efdf3785da0c96c46954ef12a70d8e9ff56100727ba47420ee7` | — |
| `session-01/events.jsonl` | `726b00f750531dd5e7b3e433ee7b1de543fec80220d372aa54b43386aace4b19` | 7 |
| `session-01/process-checks.jsonl` | `5948bf8a4dec18b6d85bdc7efee23c446ab9d6e0b04000b4d7fa922e495ec3c6` | 5 |
| `session-01/samples.jsonl` | `23672b788f404dfc927abf7ecd3d621155eb5db38750fc1823a00fa0a19420ca` | 900 |
| `session-01/warmups.jsonl` | `ee469ee5f4357da7f9bae5f414336c8762c45869436ddabf555b6d9eec023a08` | 45 |

The archived session contains exactly those four files. The counts agree with the frozen design and the event metadata: 3 workloads × 5 arms × 3 warmups = 45 warmups; 60 completed cycles × 3 workloads × 5 arms = 900 observations; and 45 warmup invocations + 900 observations × 32 processes = 28,845 completed invocations. Seven events are exactly one start, five process checks, and one failure. No summary exists.

I independently recomputed every canonical process-snapshot hash and every event-to-process-check hash. Checkpoints 0, 15, 30, and 45 passed with no competitor. Fixed checkpoint index 4 at the 60-cycle joint-block boundary failed with 900 rows and 28,845 invocations persisted. Its canonical snapshot SHA-256 is `24f769b08acd839ed40db22ad842e40ad85bae5944a94ccf68de00f268ac7b2f`. The only competitors are Cargo PID 35998 and its Rust compiler child PID 36260, each rejected for `known_compiler_or_benchmark`. Their parent chain is the separate `/Users/saul/p/egglog-experimental/.venv/bin/python` → `maturin` → Cargo → `rustc` chain; the measurement process is PID 6640 under its own `SCREEN`/`login` chain. The final event records only `process admission failed; retained inventory and competitors in process-checks.jsonl`, and the screen transcript records the same exception. Thus this was exactly the prospective environmental rejection, not a native invocation failure.

## No live or current campaign

The current `timing/` directory, `timing-preflight.json`, every `summary.json`, and `independent-verification.json` are absent. A live process-table inspection found no `timing.py`, Parts32 timing output, or Parts32 benchmark-program process; the stale launcher PID 6388 is absent. I also acquired and released the measurement lock without modifying it. These checks establish that no measurement process remains and that a new preflight can use exclusive paths.

## Frozen bindings

Current bytes match both the archived accepted preflight and the frozen design:

| Binding | SHA-256 |
| --- | --- |
| design | `c646d77e41334fd252a4e951245068f771afbbb41e44cd828e30edd58b0f6367` |
| producer | `ba93aedaf6d64115c6beaeb022de5367d6f3469e247444eff3f20679ab47364a` |
| verifier | `2e01190ac2d09f8d9b368d049498e1c30f5c0041ad3f848f05860b6313e77749` |
| preparer | `57c3d7a9195e7d28e9563936effe26585dd1a9953cc59af31922ab7063861577` |
| source input | `d1fe5b6ace306fff529d1ed7bac03609066624cf750fc0238cb71fcbee583ae0` |
| compiler | `d712e8347bf6eea231de829174a9436f411a3cedfd210daf8e7c4614c2371d2f` |
| compiler source archive | `ba2f65df7091573a594b7c51ec68a8b3665b5c85f279fe4415ca0f6e08565873` |
| source-identity manifest | `932ca349f56070c4810edde24f1d23e97481322f1ddbf2af743f083b2cf2007b` |

All 20 arm objects—binary, emitted Bril, main assembly, and Bril-main assembly for each of U0, B1, SeedOnly, Manual, and Encoding—match their design and preflight paths and hashes. Binary hashes remain U0 `0225044fd41b38a39e7281908ed6a90da5702da64736d34056c6d72ff0197bbb`, B1 `bcab16fe955e1ecbb1b62c5e040e662d5b65a266146da36a33d236c6e3c683aa`, SeedOnly `0092b47bb94281266da5f7586569c2e396b0b38f3f9d88d401ede6ad4f78ef46`, Manual `7cf36403f071dfd4cf734bd7353843042814d016de473766c485e385ea6ffb2c`, and Encoding `b4159d556b2f9bcb6407f0e24b7bd79296c9b1554073a173a5b5a2bb5ff372d2`. The baseline arms still share their three code-identity hashes, and Manual/Encoding still share theirs.

The source-identity manifest remains preflight-bound, its source-archive hash matches, and all 13 archived source members independently match their recorded hashes. The disposable `/private/tmp` source checkout paths have since been removed; therefore this audit can reconfirm the durable frozen archive, compiler, and cohort but cannot rehash those now-absent transient paths. That cleanup does not change any object the timing preparer or runner consumes.

The archived preflight's own process-snapshot digest independently recomputes to `91ba643e5c3676199ef10cba40e5e5478edd165570edc76b61ad281770cb6da3`; it passed with no competitor and binds the exact hashes above.

## Why the restart is admissible

The amendment has SHA-256 `075529cdd168e5646dddff22f17dd5553e42b4534aacff44984738aed6082001`. It was fixed after the environmental failure and before the archive manifest, explicitly before any elapsed-value inspection, estimate, or replacement observation. The manifest independently records `elapsed_sample_values_inspected_before_restart_decision: false` and `ratios_or_estimates_computed_before_restart_decision: false`. No summary or independent-verification artifact exists. I found no contrary artifact and did not inspect a performance value in this audit. This evidence can establish the recorded protocol history, although filesystem evidence cannot independently prove a person's unrecorded private observations.

The unchanged preparer refuses an existing current preflight, requires current timing outputs to be absent, acquires the lock, rehashes the full cohort, checks the process inventory, and creates `timing-preflight.json` exclusively. The unchanged producer refuses an existing session directory, initializes an empty in-memory row list, and iterates all 90 frozen cycle declarations. It never reads the archived directory. The verifier reads only the new `timing/session-01` and `timing/session-02` trees and requires complete summaries. Consequently a fresh admitted preflight followed by session 1 and session 2 is a whole-session retry and cannot mix the 900 archived rows into a result.

The failed campaign, its accepted preflight, transcript, and manifest must remain byte-for-byte preserved and excluded from every estimate, interval, gate, figure, and performance narrative. If the fresh preflight or another fixed checkpoint rejects the host, preserve that attempt as another failed campaign and repeat this audit boundary rather than weakening admission or selecting around the failure.
