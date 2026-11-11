# DialEgg polynomial extraction-output contract

Read-only diagnosis, 2026-09-24. Native commands in this report were executed by root and read here; this agent performed no native runs. A narrowly scoped adapter/validator patch and synthetic tests were subsequently implemented in the isolated mirror, as recorded in DIALEGG-TIE-HANDOFF.md.

## Finding

**The observed polynomial output difference is exclusively an equal-cost commutative extraction tie.** The two printed terms become identical by swapping the two arithmetic operands at three nodes; no reassociation, distributive change, type change, attribute change, or different polynomial is needed. Both trees have exact cost **354** under the original and current static tree-additive models. This is strong source/output evidence for a harmless choice among representatives, rather than changed cost semantics. Root subsequently confirmed exact native-result membership, both backend numeric costs, unchanged constructor counts around the positive query, and a failing fabricated Value999 negative control.

The complete native parent succeeded in 0.702 seconds, reconstructed `optimized.mlir`, and passed the native MLIR verifier in 0.070 seconds. Optimized MLIR hash is `5a1dfc2a53e8008071408545737b6f6012f518f7c49a3dbb8363f3bd4734650b`. Of its four captured independent calls, invocations 0, 1, and 2 have byte-identical native/current stdout. Only invocation 3 differs. The parent receipt correctly records `source_complete=true` and `ordinary_compatible=false` under the current exact-output comparator. [Parent receipt][parent].

The source request is exactly **one best extraction**, `(extract op14)`, modernized to `(extract $op14)`. There is no positive variants argument, custom extractor, dynamic-cost assignment, or subsumption in this invocation. The presence of `unstable-cost` elsewhere in DialEgg must not be attributed to this polynomial case.

## Exact term comparison

Let `ai = (Value i (F64))`, `x = a4`, and retain the identical `NamedAttr "fastmath" (arith_fastmath (none))` / `F64` metadata at every arithmetic operation. The outputs are:

```text
native:  a3 + ((a2 + ((a1 + (x*a0))*x))*x)
current: a3 + (x*((x*(a1 + (x*a0))) + a2))
```

Three swaps suffice: the outer multiplication, the middle addition, and the middle multiplication. An offline parser compared the full expression trees, sorting only the first two operands of `arith_addf` and `arith_mulf` and leaving every other argument unchanged. The resulting trees are identical. This comparison does not flatten addition/multiplication or interpret the coefficient values.

The original source contains active commutativity rewrites for both operators and runs its ruleset to saturation. It already authorizes these exact swaps; the importer need not introduce new algebraic rules. Whether those original rewrites are valid for all IEEE floating-point inputs with `fastmath=none` is a separate author-source semantic issue. This diagnosis concerns faithfully reproducing the declared Egglog workload and does not claim hardware floating-point equivalence.

| Evidence | SHA-256 |
|---|---|
| [Raw invocation][raw] | `9e4cae0931a7370ead256efa3bcfc0566e3b89cbd94fe74c53c1faee8523f996` |
| [Standalone invocation][standalone] | `cb11523b6ba89b9f677b52ed6b51aa9f6524d61acfedc2c1cab75ccc8127461c` |
| [Native output][native-out] | `86afa0a69bcdc4229b2267374e584e9af9672c303d7fa88caea9226014514bf4` |
| [Current output][current-out] | `0054c9eb37f76f43042a80040e4366b6e419d2da6b31d29c97761abff52154a9` |
| Historical backend binary, from [invocation receipt][native-receipt] | `af1f78ef1ec7d3733dee50a11cf3dea8d8e9ff62a87f720eedf0330d0777a82a` |

## Cost and modernization audit

The original polynomial declarations set `arith_mulf :cost 100`, `math_powf :cost 100000`, and leave other constructors at their default cost 1. The standalone file preserves both explicit costs. It expands the same base prelude, converts constructor-like `function` declarations to `constructor`, adds the already-required `:merge old` to unused `type-of` and `dims` helper functions, and prefixes globals. The active initial terms, eight rules, saturation schedule, and extraction remain unchanged. No shape diagnostic query is present. [Modernizer][modernizer], [materialization helpers][materializer].

The historical backend is revision `b6e1c96ed7335366e90056ea0a24ef425dfbb8fb`, built from the recorded source archive. Its extractor uses a node-specific dynamic cost if one exists, otherwise the declaration cost, otherwise 1; then it adds each child's cost with saturation. Its integer and string primitive values each cost 1. This invocation has no dynamic-cost updates. [Backend preparation][backend], [old extractor lines149–164][old-extract], [old integer cost][old-int], [old string cost][old-string].

The current ordinary extractor likewise adds declaration/default head cost to child costs; primitive values cost 1. It counts repeated subexpressions each time, rather than using DAG-sharing cost. All costs here are small positive integers, so the old `usize` versus current `u64` and overflow behavior do not affect the result. [Current cost model][current-extract], [default head cost][current-head], [tree-cost documentation][extract-doc].

An independent recursive count of **each printed tree**, including primitive leaves, gives:

| Head / leaf | Occurrences | Unit cost | Contribution |
|---|---:|---:|---:|
| `arith_mulf` | 3 | 100 | 300 |
| `arith_addf` | 3 | 1 | 3 |
| `Value` | 7 | 1 | 7 |
| `F64` | 13 | 1 | 13 |
| `NamedAttr` | 6 | 1 | 6 |
| `arith_fastmath` | 6 | 1 | 6 |
| `none` | 6 | 1 | 6 |
| Primitive integer/string literals | 13 | 1 | 13 |
| **Total** | **57 tree nodes/leaves** | | **354** |

Both algorithms permit distinct equal-cost answers. The old implementation changes its saved representative only when a candidate has a **strictly smaller** cost. The current implementation computes best costs and then saves the first eligible equal-cost parent edge encountered during reconstruction, subject to acyclicity. No shared textual tie-break specification is present. Thus backend traversal/order changes can select the two observed representatives while respecting the same minimum-cost objective. [Old tie selection, lines188–200][old-extract], [current reconstruction, lines405–440][current-parent]. The investigation did not prove equivalence of the entire saturated egraphs; that stronger claim is unnecessary to explain these outputs and should not be inferred.

## Guarded probe design (now executed by root)

Run one process at a time under the existing stage lock and `run_bounded_command` with `require_guard=True`, `disk_reserve_bytes=10*1024**3`, `allow_warning_pressure=True`, and a 30-second timeout. Use fresh diagnostic copies and retain command, binary/input hashes, stdout/stderr, and process receipts. Do not change the archived captures.

1. **Exact native term is present at the original boundary.** Read the single expression from `invocation-3.egg.stdout`. In a copy of `invocation-3.standalone.egg`, insert only `(check (= $op14 <that exact expression>))` immediately before its original `(extract $op14)`, after the existing saturation. Preserve the original extraction. Execute the current engine with `RUST_LOG=egglog::extract=debug`. Expected: check succeeds, one output remains, and `Best cost for the extract root: 354` appears. A failed check or different best cost falsifies the proposed admission gate and needs investigation; do not seed the target with `let`, a constructor action, or `union`.

2. **Confirm the historical cost directly.** Execute the untouched raw invocation using the recorded historical binary and its original frontend working directory (which contains `src/base.egg`), with `RUST_LOG=info`. Historical `src/actions.rs:378` logs `extracted with cost 354: ...`. A different printed representative is allowed in this diagnostic if it still has the same verified static cost; retain it as a new observation, not a replacement for the original native response. [Old numeric-cost logging][old-actions].

3. **Negative control for a fabricated target.** In a separate copy, change only the target query's outer `(Value 3 (F64))` to `(Value 999 (F64))`; do not add that value to initialization. Use `(fail (check ...))` or require an explicit check failure. Original extracts and their cardinality remain unchanged. Expected: the equality is absent. Also compare application-constructor table sizes around the positive query if the framework's admission tests require a runtime mutation check.

The current `check_facts` implementation compiles an empty-head rule body in a read context and reports a match through a side channel. It does not evaluate the target as an action that inserts constructors. This is the appropriate query mechanism, and the negative control subsequently failed specifically at the equality check. [Current check implementation][check]. The current CLI reads `RUST_LOG`; the proposed debug filter is supported. [CLI logger][logger].

## Contract recommendation after the probes pass

For this **static-cost, single-best-extraction** case, preserve the original extraction request and its output cardinality, retain the exact native term and native compiler output as evidence, check that native term against the already-existing replay graph at the same boundary, and require the current best cost to equal the native term's verified cost. Record byte-level output disagreement as a permitted equal-cost representative choice. Equality alone establishes membership, not minimum cost; the cost comparison is essential.

Do not silently apply this reasoning to positive extraction variants, negative/dynamic/custom costs, changed constructor costs, different attributes/types, incomplete saturation, or a native term transformed after extraction. In particular, DialEgg's matrix examples use node-specific costs; their native-selected node costs need their own verified accounting. Do not remove original extraction requests merely because a membership check passes, and do not treat a generic commutative pretty-printer as proof that the native tree existed in the graph.

The probes now pass their intended positive/negative outcomes. The old failed ordinary-admission receipt remains accurate under its original byte-equality policy; fresh complete captures are required to validate the newly implemented contract. Native completion and valid reconstructed MLIR are already established and should remain separate from that replay-admission result. No strict proof validation was performed by this investigation.

## Observed probe outcomes and implemented gate

The [correct-working-directory receipt](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/dialegg-polynomial-tie-cwd/receipt.json) retains the original source/native run (0.138 seconds), with `extracted with cost 354`, and the current membership run (0.067 seconds), with `Best cost for the extract root: 354`. Constructor table sizes printed immediately before and after the native-result query are identical. The earlier wrong-working-directory failure is retained separately and does not establish a source/compiler failure. The [negative-control receipt](/Users/saul/p/egglog-encoding/benchmarks/local/reproduction/dialegg-polynomial-negative/receipt.json) records exit 1, specifically `Check failed` for the otherwise identical target after `Value 3` becomes `Value 999`; this is neither a parser error nor a resource stop.

The new `ordinary-best-static-native` contract inserts only an equality query immediately before each unchanged original best extraction, using the shared `native_check_contract` to bind order and prior commands. It requires the native printed term's typed additive tree cost to agree with its historical logged extraction cost, preserves the same full supported constructor signatures/costs across modernization, and requires both the current printed tree and its numeric best-cost log to equal that native minimum. A moved check, missing/multiple cost log, changed cost, type mismatch, unsupported container/dynamic/scoped cost model, or nonzero variants cannot receive this tie exemption. Unsupported static-model sessions keep the existing exact-output contract; helpers remain zero-output helpers.

The raw native stdout, stderr and command/environment receipt remain retained. Native logs are enabled with `RUST_LOG=info`, and each logged term is matched in order against actual native stdout before its cost is accepted. Current cost logging uses `RUST_LOG=egglog::extract=debug`. `output_matches_native` continues to mean exact output agreement; `output_contract_passed` separately reports contract admission. Thus a valid tie is visible rather than silently relabeled as identical output. No original extract is removed, no rule/schedule/constructor action is added, and no native compiler output is replaced.

Focused Python tests passed (104); six-file Ruff and Mypy passed. Offline use of the new functions on the retained real invocation confirmed cost 354 on both trees and that all original source commands survive in order. These validations exercise implementation and retained evidence; four fresh complete polynomial parents and strict proof testing remain pending. See [handoff](DIALEGG-TIE-HANDOFF.md) for the exact command and file list.

[parent]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-runtime-polynomial-eqsat/complete/f50f7cb1a340e52638ec1d2d798f44555c3d15870d82adbd78f26349ae2db441/attempt-0001/capture/dialegg/dialegg-runtime-polynomial-eqsat/manifest.json
[raw]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-runtime-polynomial-eqsat/complete/f50f7cb1a340e52638ec1d2d798f44555c3d15870d82adbd78f26349ae2db441/attempt-0001/capture/dialegg/dialegg-runtime-polynomial-eqsat/calls/invocation-3.egg
[standalone]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-runtime-polynomial-eqsat/complete/f50f7cb1a340e52638ec1d2d798f44555c3d15870d82adbd78f26349ae2db441/attempt-0001/capture/dialegg/dialegg-runtime-polynomial-eqsat/calls/invocation-3.standalone.egg
[native-out]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-runtime-polynomial-eqsat/complete/f50f7cb1a340e52638ec1d2d798f44555c3d15870d82adbd78f26349ae2db441/attempt-0001/capture/dialegg/dialegg-runtime-polynomial-eqsat/calls/invocation-3.egg.stdout
[current-out]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-runtime-polynomial-eqsat/complete/f50f7cb1a340e52638ec1d2d798f44555c3d15870d82adbd78f26349ae2db441/attempt-0001/capture/dialegg/dialegg-runtime-polynomial-eqsat/calls/invocation-3.replay.stdout.log
[native-receipt]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-runtime-polynomial-eqsat/complete/f50f7cb1a340e52638ec1d2d798f44555c3d15870d82adbd78f26349ae2db441/attempt-0001/capture/dialegg/dialegg-runtime-polynomial-eqsat/calls/invocation-3.json
[modernizer]: /Users/saul/p/egglog-encoding/scripts/suite_capture_dialegg_speq.py:175
[materializer]: /Users/saul/p/egglog-encoding/scripts/paper_benchmarks/materialize.py:101
[backend]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-backend/prepare/bf1e171cd34d58bd91b9274798682f21728873d126181d90c9973e64676dda86/attempt-0001/preparation.json
[old-extract]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-backend/prepare/bf1e171cd34d58bd91b9274798682f21728873d126181d90c9973e64676dda86/attempt-0001/source/src/extract.rs:149
[old-int]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-backend/prepare/bf1e171cd34d58bd91b9274798682f21728873d126181d90c9973e64676dda86/attempt-0001/source/src/sort/i64.rs:77
[old-string]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-backend/prepare/bf1e171cd34d58bd91b9274798682f21728873d126181d90c9973e64676dda86/attempt-0001/source/src/sort/string.rs:27
[old-actions]: /Users/saul/p/egglog-encoding/benchmarks/local/reproduction/stages/dialegg-backend/prepare/bf1e171cd34d58bd91b9274798682f21728873d126181d90c9973e64676dda86/attempt-0001/source/src/actions.rs:372
[current-extract]: /Users/saul/p/egglog-encoding/egglog/src/extract.rs:41
[current-head]: /Users/saul/p/egglog-encoding/egglog/src/extract.rs:721
[current-parent]: /Users/saul/p/egglog-encoding/egglog/src/extract.rs:405
[extract-doc]: /Users/saul/p/egglog-encoding/egglog/src/ast/mod.rs:1013
[check]: /Users/saul/p/egglog-encoding/egglog/src/lib.rs:2014
[logger]: /Users/saul/p/egglog-encoding/egglog/src/cli.rs:95
