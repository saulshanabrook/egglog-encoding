# Python2 delta review: stale checkpoint

**No source consent: the nominated Python2 checkpoint was stale at the first live-source check.** Two of its four files had already changed. Per the coordinator's explicit stop rule, this review stops at the mismatch and does not transfer the frozen checkpoint's proposed repairs, reported 56 checks or pending diagnostics to the changed bytes. This is a provenance blocker to completing this review, not a new claim that the frozen helper or compiler behavior failed.

Nominated frozen authority: `compiler/observations/fresh-evidence-python-2/source.json`, SHA-256 `8514324dc8274b89a56f2161711035e16fc660a7e834eeac10f3ad3f226c815a`; full four-file patch `3230e2de0294346792f39e0ced8e37a5ea1d2cafacd090251fffe0a8d38e202f`; Python1→2 delta `6cecd0a667134bdefe2a1994155ae67e2592d8c83525768aa24ada1b221539fc`. Frozen `source/` copies still match those nominated hashes. The live worktree is `/Users/saul/p/wt/eggcc/encoding-impact`.

The live hashes below were identical at first check **2026-10-17T22:01:37.309733+00:00** and final check **2026-10-17T22:01:57.902762+00:00**. The first check deliberately raised an assertion on drift; that was a file-hash assertion, not a project test/import or compiler execution.

| File | Frozen Python2 SHA-256 | Live start/end SHA-256 |
| --- | --- | --- |
| `check_corrected_specificity.py` | `e26e5682acf03af69b95e687d0c0d8d86a1fc098bfb9b383807d2fa1e4d4e6b8` | Same |
| `observation_evidence.py` | `933a57a1c3ba69c3ee0dbf6678461b994df58d6c04cc6589b51a0e2902b7f1e4` | `0b3c77b5d8e1349cc849514da327be0b2164b69335d4000ced8649cd28b06afe` |
| `repeat_evidence.py` | `dfb0d3bd7192a30e34e50baaa3bc951a80041c3a73f3cc2bbfe7ec3f62cad20d` | Same |
| `verify_evidence_negatives.py` | `4da0166c2cdb8e56acf89ec0a3af18ed8ba4e9a75c2fbf45373a3a649def1074` | `8ad9196d0ed14d7b22d010ba39298dc810e89cd8434e65f012619712e069736c` |

Reads before stopping were the nominated manifest/file list, earlier [Python1 findings](observation-python-review.md), the first section of the immutable Python1→2 patch, line counts, and these standard-library hash checks. I did not read the changed live helper bodies to review them under the old checkpoint, import any project/helper module, run tests/builds/workloads, edit source, or inspect/upgrade the owner's running repeated/red/protocol-smoke outcomes into passes. Only this findings file was written.

Next review needs a newly frozen source manifest, full/delta patch, exact four-file snapshots and focused-check receipt for the actual repair bytes. Preserve Python2 and any failure-driven diagnostic evidence. The next review should resolve the five earlier findings and the actual phase-aware collector/source/reference association against that stable checkpoint; the pending repeated-ten/original-red-four/protocol-smoke-nine empirical outcomes remain separately classified. Existing Rust/source/collector consent and harness gates are untouched by this stopped review.
