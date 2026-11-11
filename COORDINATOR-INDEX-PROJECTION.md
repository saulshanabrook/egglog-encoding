# Coordinator index amplification correction

The source path that duplicates evidence is successful family preparation after an earlier failure: each selected case receives the full new `preparation` receipt and full `historical_outcome`. Current preparation failures likewise copy a whole family receipt to every case. This is linear fanout of large inventories, not demonstrated recursive stale-status wrapping. The stale-report branch marks a copied row pending and skips subsequent identity refreshes.

A size-only inventory of immutable live stage receipts found 401 receipts totaling 39,050,798 bytes; the latest MISAAL preparation receipt was 8,936,489 bytes and the two prior large preparation receipts were approximately 6.94 MB each. No production index/report JSON was loaded. Root independently retained the oversized publications and confirmed duplicated MISAAL rows through streaming inspection.

The synthetic 102-case fixture uses two small immutable preparation receipts. Old embedded representation: 14,904,642 bytes. Shallow reference representation: 124,230 bytes. Only two receipt hashes are computed, and projection is idempotent. The ordinary coordinator regression also exercises a failed preparation, successful retry, and three report rerenders over 102 cases while checking immutable stage bytes and empty corpus admission.

`compact_outcome(row, receipts=shared_dict)` replaces only preparation/history evidence with shallow summaries: status, reason, case, stage, attempt, identity digest, timestamps, and stage receipt path/hash. Existing receipt hashes are retained, including null for evidence missing when projected. No nested history, artifact inventory, or full identity is retained in those summaries. Current source capture and ordinary-validation outcomes keep their original verification structure. `write_index` projects and atomically replaces the index using streaming JSON serialization.

The public coordinator still initially reads its index normally. Root must first perform its authorized streaming compaction of the archived legacy index; do not use this patch as permission to load the oversized original. No production data mutations or native runs were performed for this correction.

Validation: 74 focused coordinator/corpus/stage tests passed; Ruff and mypy passed; live git apply --check passed. Independent read-only review by the runtime preparer agent found no concrete blocker. Only scripts/suite_reproduction.py and tests/test_suite_reproduction.py are in the patch.
