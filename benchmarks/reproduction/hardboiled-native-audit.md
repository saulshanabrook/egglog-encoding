# HardBoiled complete native canary audit

An independent read-only audit found no admission blocker for the current GPU `matmul` and AMX `matmul_vnni_1x1` canaries. Both completed the original source optimizer and then passed ordinary standalone replay. This does not establish target-device execution, strict proof validity, or an exact mapping of all AMX paper cells.

The GPU case has one invocation and 96 application roots. The AMX case has two fresh invocations, each with three roots. All raw inputs, actual sidecar output hashes, selected roots and checks are accounted for. The audit verified all 56 retained capture/validation artifacts against their receipts (24 GPU, 32 AMX), along with the genuine delegate binary identity. Native parent return codes are zero and the expected output files exist. The GPU LLVM contains the tensor-core instruction payload; the AMX output contains tile loads, dot products, zeroing and stores.

Replay construction is exactly modernization of the captured commands plus equality checks after their original extracts. No extracted target is inserted. All 55 sort/constructor/type/cost/unextractable declarations are preserved. The omitted custom `keep-best`/canonicalize behavior is unscheduled in these exact captured programs; it is not silently dropped active optimization.

All GPU displayed extracts match native outputs. In each AMX call, one displayed extract differs only by Add/Mul operand order; the other two roots match exactly. Both original and current extractors use additive node costs and summed vector costs, so these swaps preserve cost. Every equality check against the exact native selection passes. The contract claims native-result derivability with preserved extraction requests, not byte-identical AMX output or a separate optimality proof.

Current immutable attempt and validation paths are recorded under these case IDs in `benchmarks/local/reproduction/index.json`. If implementation or input identities change, those results remain historical until the coordinator validates the new identity. The [paper-cell mapping gap](hardboiled-amx-mapping.md) remains explicit.
