# Original-one block-04: host-only admission review

**Host consent withheld on the existing evidence: retain block-04 as unresolved/invalid under the predeclared external-work rule unless independent attribution resolves the observed script.** This is not a finding that a build/test/collector definitely ran, or that the external work measurably slowed any arm. It is a concrete attribution gap during an actual measured invocation. No timing distribution, measured row, figure or postcapture output was parsed; technical verification/archival remains a separate decision. Only this note was written.

## Actual timeline

Collector receipt `234c1d158a539ad281329818cdd2d3cbf2c3b9e3c53d9c252ed909fe9937dc30` reports exit 0/no timeout, starting **00:16:19.801748 UTC** with 14.330410584 seconds wrapper elapsed; derived terminal time is **00:16:34.132159 UTC**, 2026-10-18. These are operational timeline values, not a per-arm cost analysis.

| Host receipt | Actual timestamp UTC | Relation to collector |
| --- | --- | --- |
| before | 00:16:18.677677 | 1.124s before start |
| during-01 | 00:16:25.547323 | 5.746s after start; inside run |
| during-02 | 00:16:56.352031 | **22.220s after terminal** |

The second filename supplies no additional in-run coverage. There is one actual mid-run process snapshot. It explicitly records an EggCC argv whose normal receipt path is `measurement-03-original-one-Off.json`, alongside the external Python process; overlap with a measured invocation is established without reading timing rows.

## Observed external work and limits

PID **58633**, PPID 6616, starts at local 17:16:25, elapsed `00:00`, with argv **`/Users/saul/p/wt/pfaf-data/modernize-uv-pfaf/.venv/bin/python -`**, 26.8% CPU and 0.3% process memory in the snapshot. Its CWD lookup is **exit 1 with empty stdout/stderr**, not a successfully identified CWD. The interpreter pathname identifies a different project's venv, but neither `python -` nor its shared Codex parent identifies the stdin body or workload category. It is absent in before/late-after records. That supports transient observed activity, not a proven harmless duration, cumulative CPU cost or allowed UI classification. The memory percentage is not this study's wait4 RSS measurement and does not resolve CPU/job materiality.

The same snapshot records transient Node PID 58631 at 18.9% with an unsuccessful CWD lookup, and Python PID 58636 at 1.9% whose CWD is the encoding root (consistent with monitoring/tool activity, without an independent owner attestation here). None should be mechanically classified from an empty build-name regex. `external_builds_or_tests=[]` establishes only that the detector matched no named job.

I do not infer a forbidden build/test/collector solely from the Python pathname. I also cannot certify its absence or classify this actual active script as normal UI from these bytes. The recorded CPU alone does not quantify interference with EggCC, and rounded zero elapsed/failed CWD is insufficient to bound duration or impact. Resolving attribution would require a contemporaneous command/source receipt or owner evidence describing that specific PID/script, not later absence or an assumption about the venv.

The approved policy `2df138b8…` waives memory blocking only and preserves build/test/collector exclusion. The unchanged screening supplement `c30342cc…` additionally says: **"On material interference or unresolved external work"**, retain the affected block as invalid/interrupted. This observed unowned active script during `measurement-03` remains unresolved under that predeclared rule. Admitting it merely because no familiar test/collector name appears would weaken the rule after collection. Existing data therefore do not support final host admission; absent specific attribution, exclude the **whole** block before statistics rather than trimming the overlapping Off call or reusing other rows.

## Allowed context and monitoring coverage

`duetexpertd` records 89.5% CPU at the mid snapshot; iTerm is 75.6/87.7/77.5%, WindowServer 46.2/46.5/45.9%, and WhisperNotes 12.4/11.5/12.8% in before/mid/late-after. AC power and 100% charged battery are recorded. System/UI activity is explicitly disclosed under the final descriptive policy; these values alone do not prove a forbidden job or independently mandate invalidation. They do preclude a globally idle or zero-background-overhead claim. No sustained duration or causal arm effect follows from one system-daemon sample.

The delayed second snapshot leaves the final ~8.6 seconds of this collector without another in-run observation. A future 5-second monitoring plan should be assessed from actual acquisition timestamps/delays, with ownership/category review of new processes; its name or target cadence cannot prove continuous job absence. Monitoring itself remains host activity. This limitation alone is not the concrete invalidation reason; unresolved observed external work is.

The prelaunch admission itself appropriately avoids claiming global idle, and the collector argv uses the authorized common unset-guard prefix. User memory override does not supply an active-job waiver. Root may seek concrete attribution for the already-observed script or retain the whole cohort as host-unresolved and declare another complete attempt. No protocol change, process interruption, workload, new host probe, project import, test or figure ran in this review. I quiesce now.

## Bound evidence

Study SHA256: `ef3139204c07f7882936e5ac254b262db82ee1035ada846a434ff4c5800c7112`.

| File | SHA-256 |
| --- | --- |
| `study.json` | `ef3139204c07f7882936e5ac254b262db82ee1035ada846a434ff4c5800c7112` |
| `collect-command.json` | `234c1d158a539ad281329818cdd2d3cbf2c3b9e3c53d9c252ed909fe9937dc30` |
| `host-before.json` | `93fa7b29c493dd5950b3ac8f90d72ccf210f236dcbe512fc1abbc70b8015c676` |
| `host-during-01.json` | `7f2137662d6436599ecba167a6cd5a1c50b7956ba5742318a28cc3be8416b599` |
| `host-during-02.json` | `3606de49c40b324654516b1dd3da5ae36259717f308e1981deb66d187f69df3f` |
| `host-admission.json` | `104cf4a08f4e8e00a32b376e6db3f4875dc35ea16cfd21236f5002030014676e` |
