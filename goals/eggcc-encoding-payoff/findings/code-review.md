# Independent B1 code review

2026-10-18. **Disposition: no binding source defect found in this pass; proceed to the required full gates.** This is read-only source review, not a fresh validation run or whole-goal acceptance. I ran no build, test, compiler, native program, experiment, formatter or snapshot update, and changed no candidate source. The source owner retains the tree.

Reviewed B1 at `/Users/saul/p/wt/eggcc/encoding-payoff`, including the complete tracked diff, both lockfiles, all untracked observation/host-test files and all sixteen `tests/encoding_payoff` fixtures. Read the accepted goal/facts/plan and the add-sub, baseline and repair-review findings. No physical `AGENTS.md` was found in this worktree, its source subdirectories or its ancestor chain; the session's user instructions still govern this review.

## Correctness and the encoding contribution

- `dag_in_context/src/observations.rs:235-279,295-322,355-568` implements a bounded concrete checker, not general symbolic evaluation. It checks actual root types and trailing state, rejects extra functions/batches, unsupported reached grammar, invalid types and contexts, and transports the evaluated `If` input to only the selected region. Each region gets its own cache and point token; input alternatives and passes do not share tokens. Integer Add/Sub/Mul explicitly wrap. Pure Boolean expressions alone reach detached interpretation; Print is traversed structurally and any effect/region-dependent scalar operation is rejected. Skipped arms are recorded without evaluation. The source semantics and the stated restriction agree.
- `observations.rs:573-602,667-694` marks only `ObservedBool(bool)` injective. Neither `Expr` nor `EvalBoolAt(Expr,point)` is injective. All enabled modes seed the same contextual literals and reached observations; annotation and audit selection are the differences. An invalid same-point Expr equality transports through `EvalBoolAt`, equates contradictory ObservedBool outputs and makes injective cancellation fail on their primitive Bool arguments. The Manual control instead joins the same expression/point in `ObservationSeed` and rejects its committed conflict. CommonSeed has the same facts but no rejecting audit. No disequality query is needed or used for this candidate.
- `dag_in_context/src/lib.rs:1046-1072` places initialization, the actual source schedule, committed witness extraction and selected audit before serialization/native extraction. This is the real compiler consumer path. `observations.rs:769-811` preserves the witness before a rejecting cancellation can abort; source-schedule failures are separately recorded at `740-766`. This supports the encoding-led graph-detection claim, while independently executed U0 wrong-output evidence remains a distinct authority.
- The collector does not prove that a program is correct for all inputs, and a conflict-free audit is not such a proof. Zero observations remain visible as a count; unsupported inputs reject. The qualifying examples require their recorded reached predicate and conflict, not merely an accepted or empty audit.

## Arithmetic repair

`dag_in_context/src/interval_analysis.egg:119-150` replaces the four unguarded independent transfers with two complete-range rules. Both require all four numeric endpoints and nonempty operand intervals. The Add thresholds prove `MIN <= la+lb` and `ha+hb <= MAX`; the Sub thresholds prove `MIN <= la-hb` and `ha-lb <= MAX`. The min/max clamps keep threshold arithmetic defined even before any comparison filter is applied. Each matched witness therefore makes both action endpoints defined and sound. Both result bounds come from that same eligible tuple. No new Dead assertion or constructor law is introduced.

This agrees with the concrete semantic consent in `findings/repair-review.md:95-114`. It assumes sound input bounds and intentionally loses some one-sided and uniformly wrapping precision. Other pre-existing interval families, including the old Mul rules, are unchanged. This review does not infer whole-compiler soundness from the patch.

## Off behavior, API and evidence boundaries

- `dag_in_context/src/lib.rs:302-343,985-997,1057-1069` filters both None and Off out of observer preparation/allocation. Their original initialization-plus-schedule path remains together. Config forwarding preserves context, ablation and hacker-rule selection; the round-trip helper still uses context-enabled defaults. The intended arithmetic repair affects Off too; no other new Off semantic change was identified.
- `src/main.rs:181-185` and `src/util.rs:602-633` reject enabled observations outside optimize mode, with dummy contexts, with CLI ablation, or without an evidence root. Runtime inputs use the same parser and trailing-state convention as the existing DAG interpreter (`src/lib.rs:81-96,110-114`). None/Off adds no evidence locator to normal JSON (`src/util.rs:428-429`).
- `observations.rs:63-120` allocates invocation children with atomic directory creation, process ID and atomic counter; it never overwrites an existing invocation. `55-60,123-166` replace the index atomically and verify its identity. Current production calls update one invocation sequentially, so the read/modify/write index has no internal concurrent writers. Each pass directory is also created exclusively (`636-643`). Failures leave incomplete/rejected/error status rather than marking successful native completion. The index is a locator/progress record; external manifests must still bind its artifacts and source identities.
- Domain rejection and several receipt-I/O failures intentionally use panics (`619-621,636-661`); this is consistent with this experiment's retained exit-101 diagnostics and cannot be counted as successful output validation. The API does not promise recovery from arbitrary I/O failures. No result-forging or failed-run-as-success shortcut was found.
- Both manifests contain an absolute local E1 path (`Cargo.toml:12`, `dag_in_context/Cargo.toml:9`). This is acceptable for the expressly isolated experiment, with U0 retained separately; it is not a portable upstream patch. Reproduction must reconstruct that pinned E1 source at the documented path or deliberately retarget both manifests and regenerate their identities. The lock retarget changes the engine closure, so B1 alone cannot establish that a bug predates integration; the independent U0 evidence is required.

## Tests, scope and remaining checks

The test modules are actually registered: `dag_in_context/src/observations.rs:826-827` and `src/lib.rs:22-23`. The eleven observer tests include wrapping endpoints with externally supplied expected values, selected/unselected paths, wrong types/contexts, unsupported arithmetic, same-expression/different-input transport and synthetic Manual/Injective controls. The five host tests exercise actual optimizer/native-extractor calls, compare both interpreted outputs explicitly, and check three completed pass receipts. The two new transfer tests in `interval_analysis.rs:4-58` retain eight safe ranges and reject missing endpoints, all four unsafe arithmetic directions and an empty range. These are meaningful tests rather than implementation-mirroring accessors. Nonzero discovery and successful execution are reported by the existing findings; I did not independently rerun them.

One **nonbinding test gap** remains relative to the repair note's suggested boundary list: the new transfer tests do not explicitly supply a `Dead` or symbolic bound (`interval_analysis.rs:37-56`). The four `IntB` patterns make their nonmatching behavior clear in source, so this does not undermine the two concrete bug/repair claims. Retain the finite scope; do not describe these tests as exhaustive Dead/alternative-row validation. A targeted test would be useful if that broader guarantee is claimed later.

The diff is confined to dependency admission, observer plumbing, meaningful collector/audit/evidence logic, the Add/Sub repair and focused tests/fixtures. I found no trivial forwarding/accessor helper that needs removal, unrelated production cleanup, global Expr annotation, unsafe allocation/Concat law, or mutation of earlier study source. Full Make gates, baseline attribution of any failures and final evidence/claim review are still required; this source review is not a waiver.

## Exact reviewed identities

Candidate paths below are relative to B1. These hashes bind the final source read; the final status has the same changed-path set as the initial status. No untracked candidate file was omitted from review.

| File | SHA-256 |
| --- | --- |
| `Cargo.toml` | `d0a5348590fff1a985cd36f2fe3d381adbf3944c0fe7ef12a1f4afcffe8bf370` |
| `Cargo.lock` | `760bc3a0003dd467de29c3f664af1df58485c801abd8aee1a5bcd67987cab630` |
| `dag_in_context/Cargo.toml` | `b89f4ab74f8a98f905fe461a6810d099815dfc6ff83dccbf6cf95b0657340a57` |
| `dag_in_context/Cargo.lock` | `6ab079882f74ae94c96f92d9c1f24bb25eb9a5d4e483c6f401522a4f26d07e2e` |
| `dag_in_context/src/observations.rs` | `4d6d27afdef7ba46de435710effc47d19cffb9ef61141a52ab5eb663c7656376` |
| `dag_in_context/src/observations/tests.rs` | `befa63730b3d4a59f12fdfe46a3515fa0c95f405b28130a902ba0e0dbcd819fe` |
| `dag_in_context/src/interval_analysis.egg` | `ba4180adf9c460c061d4207124ed808810f4dcb91cc0dcccd021c46d2ab1c3a7` |
| `dag_in_context/src/interval_analysis.rs` | `868d8e108db7a632705ed3b81f3f6242754080da3e4226a8b495e0d400cda07a` |
| `dag_in_context/src/lib.rs` | `af235c323cd9f4d7d760efc33b5bfb01f6857d0a6845a7b6baba1c565e6be5db` |
| `src/lib.rs` | `64f601b5dcefabab9ffe19e02147a4691514efcea4049340ab090cfbae4bf686` |
| `src/main.rs` | `37fc0bae0ada65a47a1307974460cb27e479c62d2ecbdd351d130b41c44f4578` |
| `src/util.rs` | `af5a9655e6f2668cab4790be81ad3d0f162e8e98f0df3438f397ad24281a1721` |
| `src/observation_tests.rs` | `bb74b736a9741e2da7fda1357c9e845ce8294d2d06d2f76b3a2caf0f42752c16` |

Reviewed twelve arithmetic fixtures and four known canaries. Endpoint fixture hashes are `fd66c539d29bdf03a388994ca4a53c9f0c15ac3dc579a69741a700f2a5ff8a6c` (Add/MAX) and `ea45c09d586d036b12ceaa8284d0ad183e2bab0b634d9c6bf166ed6762275310` (Sub/MIN). The independent oracle and corrected checkpoint remain the complete fixture/evidence authorities; this review creates no replacement evidence manifest.

Goal-document SHAs: `goal.md` `20084eb0eab534b65c7b50316ca9c9144f5cf30fb8c12819bd7fea4fa7b557ec`; `facts.md` `cabf4e7ec192658a1d7932c901cb380aab1af3a9f9ea8ebc98a14f95d3257092`; `plan.md` `2b407991c3f70ed9d8e278c681ab6a8e4d80ae5c55c966ce8e5bd1ea4c91592d`; `findings/add-sub.md` `f0b3ce6b8c5fd985fc4ab28835dad029128e66991dc7c2f439f59ab31f4faf8c`; `findings/baseline.md` `f0b74a3b79c74ddfbfaa33ff8429d31c810c62ccc7a732b13db3d2e99c9d6268`; `findings/repair-review.md` `80834273160ade644e20faa6d2081bb1806472214c8134ab896d8a831af68d2b`.
