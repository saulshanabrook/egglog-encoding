# Source-corrected specificity evidence review

Consent to the retained diagnostic result; no blocking evidence finding. The exact two-rule deletion changes the MAX case from the original wrong-answer/checker-rejection pattern to correct, accepted output in all four modes. This establishes specificity and localization for this witness. It does not establish general interval-analysis soundness, unique detection power over the manual oracle, upstream-current behavior, a performance benefit, final-gate success, or the final restored-source executable.

Read-only audit on 2026-10-17, cwd `/Users/saul/p/egglog-encoding`. I used standard-library Python to read/hash/compare retained files and independently assert command outcomes and stage boundaries; I imported no project code and executed no controller, compiler, test, build, or workload. Official gates were left to the compiler owner. `C/` below is `benchmarks/local/eggcc-encoding-impact/compiler/observations/corrected-control-1/`.

Both frozen source manifests have the same 788 paths and hashes except `dag_in_context/src/interval_analysis.egg`. I compared actual full source patches: removing the corrected patch's interval-file section leaves the original patch byte for byte. Applying that interval section in memory to the recovery original produces the independently predicted corrected bytes. The section has exactly the two reviewed deletion hunks, 22 removed lines/704 bytes, no added lines, and removes precisely the two captured blocks. Original/restored interval SHA is `ff363e2c10c57c2f3f79005d1f883f98091b3a32d023f43265b2ccbb89ce2647`; corrected interval SHA is `ef5ff6ca63884d2c2588babb624971b76f464c15e92849c0c6a95c3cfce33037`.

| Frozen endpoint identity | Original release | Corrected release |
| --- | --- | --- |
| Compiler SHA-256 | `5d980389feec6270146db9a2cfe4e1775974102ab6c50cdf7bad029471907af1` | `f44edb3cb9c4b9660524335a29bea536571fe2ddbd1bcc68ba589decbd9bcc15` |
| `manifest.json` SHA-256 | `b722688c93a27a8deb28f900efd9f1ad300887c1e7724a337774bb0f00fbed88` | `860add623480776002f680501c1077ea7c2cd8e268545ce4c028c0e90aab20e2` |
| `source.json` SHA-256 | `b37b2450fe8f131dcfdda620841fea5781f6cca09f80726dae8282871839ab18` | `8748805409bdc89ae7d529521140aacadb85483ffb421b957d82b3a8de0fbc22` |
| `source.patch` SHA-256 | `e3efea7f8d5a80bf085225a3ffd573c3643b7a071204fe4f10ad85a1cdb00439` | `9ea4a5a1fb8597ba498abb6ccbe80ce60944e20a31e15d8e36dbdd9aa518a61a` |

I hashed the actual compiler and sibling Tiger files, checked manifest/patch links, and verified actual CLI executable arguments select those frozen endpoints. Both Tiger files have SHA `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. Both build receipts record `cargo build --locked --release --bin eggcc`, Rust 1.91.0, jobs 4, the new compiler worktree target, exit 0/no timeout, and matching before/after source checks for their respective variants.

The original and corrected MAX drivers use identical live driver/helper/input bytes and the unchanged fixed `true\n` oracle. Bound SHAs are driver `e26e5682acf03af69b95e687d0c0d8d86a1fc098bfb9b383807d2fa1e4d4e6b8`, helper `0b3c77b5d8e1349cc849514da327be0b2164b69335d4000ced8649cd28b06afe`, input `f6624abf3e6018b7e6d2d5e410afff2f95822965515361b644cfc61ba8fd31eb`, and runner `9b4e1f0bd13b855a2f45393f8bed3523629ddc5ca305858f1496a4add3749aa8`. Actual driver receipts use the same Python/live-script prefix, environment, cwd and 540-second limit, with their own frozen binary/package arguments. The original driver's intentional exit 1 and exact four-mode red result finish before the controller's mutation timestamp; the corrected driver exits 0. Neither timed out.

I checked each raw CLI command, stdout/stderr, captured normal run data, graph count, and applicable evidence tree rather than accepting the summary booleans:

| Case/modes | Actual outcome |
| --- | --- |
| Original MAX Off/CommonSeed | Two exit-0 runs, non-null original `true\n` / optimized `false\n`; all three native passes finish. |
| Original MAX Manual/Injective | Two exit-101 runs, exact `(ObservationConflict 5 2 1 true false)`, named checker errors, pass 0 only, no serialization entry, Tiger graph, or reconstruction. |
| Corrected MAX Off/CommonSeed/Manual/Injective | Four exit-0 runs, non-null true/true, all three native passes; enabled audits accept with no conflicts. |
| Corrected x=1, x=0, x=-1, contradictory/dead arm, skipped unsupported, plus Off selected-unsupported | 21 exit-0 runs with expected original/result matches, all three native passes. |
| Corrected selected-unsupported CommonSeed/Manual/Injective | Three exit-101 runs, `before-seeding`, emitted seed count 0, domain-error evidence only, no initialization or native graph/reconstruction. |

The 24 nearby controls cover every pair of six cases and four modes exactly once. Expected output is false for x=1, empty for x=0/-1, and true for contradictory/dead, skipped-unsupported, and the Off selected-unsupported case. Captured input copies match the bound source input hashes. All successful CLI runs retain normal output; all Off receipts omit observer locators and evidence-root allocation. Thus Off and CommonSeed independently demonstrate the actual corrected result without relying on either rejecting checker.

Across these 32 CLI calls, all 27 native successes have passes exactly 0/1/2, three Tiger graph snapshots and at least three reconstruction schedule completions: 81 completed native passes in total. All 24 enabled evidence trees are PID/root/mode/locator bound to their own command/full-stderr receipts. Their 379 archival hash entries match both archived and persistent-child bytes. Audit schedules, accepted/rejected stages, pre-serialization markers and native-entry flags match the intended mode. All 24 nearby-control before/after full-source-check receipts also bind their own command hashes.

The original three enabled MAX modes retain the same concrete point-1 witness: selected true branch, region input `[StateV, 0, MAX, 2]`, type `[StateT, IntT, IntT, IntT]`, feasible multiplication-comparison seed 5=true and matching contextual literal seed 2=false. The manual error is its named conflict panic; the injective error names unequal primitive payload in `ObservedBool`. For each enabled mode, original/corrected pass-0 observation manifests and schedule bytes are identical; initialization bytes differ only by the exact two rule deletions. The immutable literal annotation remains mode-specific; `EvalBoolAt` and Expr remain unmarked. This directly controls the observation domain while changing the diagnosed rules.

The subsequently supplied existing-capture receipts agree with that independent byte comparison: `C/pass00-observation-comparison.json` SHA `88be035b99448b39010f4716b56dc0062589d158484e9a171821062b73d34a61`, and `C/pass00-initialization-deletion-check.json` SHA `80ca4b17dde64e933e2d9ffe434faf95ace9e6fdc448d150caa223f32af40ec6`. I checked every recorded original/corrected file hash against its actual bytes and independently confirmed each approved block occurs exactly once in each original initializer; removing them once gives the corrected initializer exactly. These receipts add attribution, not new compiler invocations.

Restoration has evidence beyond the controller rollup. The terminal `control-result.json` reports restored source after `finally`, and the separately launched `independent-restoration-command` subsequently executes the source-reviewed, hash-bound controller's `verify-only` phase. That process exits 0/no timeout with empty stderr and reports all 788 original source paths/hashes and original interval SHA. The checker also validates the runner, Python2 authority/live helpers, external E1 authority, five E1 source hashes, and recovery original. This is a separate post-controller invocation of the same audited verifier, not a claim of an independently implemented second algorithm. I did not rescan the live full source tree during official gates.

| Retained evidence | SHA-256 |
| --- | --- |
| `C/control-result.json` | `1fe893d4f9ef8cc202d26e11b79934cc704c8a133d88657b49957b3b810919d2` |
| `C/original-release-red/results.json` | `476d5939652cc041af7f29160c2cdbe7e0d7c59fad8cc638ccd8a26ad79bcfbd` |
| `C/corrected-release-green/results.json` | `a3d37046e6875842fdfdb822f11e11121bf6b15124f54d85fd3dfaac7e9759f2` |
| `C/corrected-controls/results.json` | `427968ca61444dc8fc18f9714ec62a26d9f432e557e451d19672dbe56fd70e1e` |
| `C/independent-restoration-command.json` | `b33e5dd1357a61630e01c565950025021952b1e5a2fa1cc64fa4f50073168c42` |
| `C/independent-restoration-command.stdout` | `61853efe86473bb74484f8a99ba145c5caadccd1ee883bde8f78a2247a38fad9` |

The main audit's 1,054-file read set matched its hashes again at completion; a supplemental overlapping 65-file check bound driver ordering, exact witness identity and all nearby-control source-check receipts. No raw evidence or source was modified. Final admission still requires official restored-source gates and a freshly bound final uncorrected executable: the mutable target may retain the corrected binary after byte restoration.
