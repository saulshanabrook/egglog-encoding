# Guard refusal and complete original-one block-03 replacement

**Original-one block-02 is a retained prelaunch resource-guard failure, not a compiler timing result.** Its collector receipt exits 1, without timeout, after 0.349608541 seconds of wrapper elapsed time. `results.json` has exactly **one failed correctness/Off checkpoint**, zero warmup rows and zero measured rows. Compiler receipt, receipt hash, wall time, RSS, exit code and signal fields are null; the compiler receipt directory is empty. The exact error is:

```text
resource guard refused to launch a workload: host memory pressure is not normal (kernel level 2)
```

The command receipt SHA256 is `8ec2fcded6f2fcaa9a46da41854fc9928fa666595be203643319da00d1860ee9`; failed results SHA256 is `892991315c0774416a1493d0889387b9bf771004e913451d302f30484f1ed56d`. Retained stdout is empty and stderr identifies the first correctness/Off attempt and the refusal. PID 53129 is the capturing runner's env/Python collector subprocess, not an attested EggCC PID.

The unchanged SHA-bound runner calls `MemoryGuard.from_environment()` at `processes.py:62` before the timing start and EggCC `Popen` at 72. `memory_guard.py:137` throws the exact retained prelaunch error. This source ordering plus the receipt places this attempt's refusal before EggCC launch; it does not imply that readiness-helper subprocesses or unrelated host work were absent. Wrapper elapsed time includes collector/setup/guard work and cannot substitute for null compiler timing. No source/compiler invariant failure or cause of kernel pressure is inferred. Root owns guard/host diagnosis and new admission.

| Next complete study | Exact SHA-256 |
| --- | --- |
| **New `original-one/block-03/study.json`** | `29ad750a902cda2aaba107970fc0ee49a688bd0e80529cd389b052ae6bdc3a7c` |
| Untouched `corrected-max/block-02/study.json` | `ee210e3e724a8d2405e51248901f6090602b69891803d7544e108c63b4b0e2cc` |

`replacement-original-one-block-03/declaration.json` SHA256 **`2064f47f4998067655cdcbcbb8fbe89571115cccf3a8a0ee261d9cb5fea34366`** binds the failure classification (`guard-failure.json`, SHA256 `e40e06723dd9cf7f52faeb4e7632443a52cdfcebdc58d721782a1e6723ec3233`), old/new study hashes and fresh output paths. This replaces **only original-one**. Corrected MAX block-02 remains unexecuted and contains only its study file.

Original-one's manifest changes exactly three values from block-02: study ID and the Manual/Injective mutable evidence roots. Reversing them reconstructs the entire old manifest. All 48 static provenance entries remain the same: three arm-binary entries, one archived input and 44 immutable artifacts, including the existing block-01 source-package authority. Endpoints, false reference, mode flags/defaults, environment, strict common outer guard, metric scope and arm order are unchanged. The full 42-call case must restart: three correctness, three warmups, 36 measured calls, one warmup/twelve observations per arm, 300-second timeout, complete balanced rotations. No failed checkpoint, correctness anchor, warmup or measured row is reused.

The new result/receipt/evidence/postcapture/figure paths are fresh and uncreated. `replacement-original-one-block-03/preservation.json` hash-binds 2534 prior files; all matched again after preparation. Old block-01/block-02/source-binding/replacement artifacts were not edited. I inspected only the explicitly permitted failed checkpoint fields, with no old timing-distribution analysis or figures.

No project/helper import, test, build, workload, collection, figure, source/collector edit or new host/guard probe ran. Only new raw preparation files and this note were written. The existing screening/stop protocol and guard remain unchanged; this declaration grants no timing window. Root must newly admit the host and strict guard before collection. Preparation is complete and I quiesce now.
