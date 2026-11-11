# DialEgg static extraction tie handoff

The six-file patch below is implemented only in `/Users/saul/p/wt/egglog-encoding/reproduction-dialegg-speq`. Fresh integrated root snapshots are retained under `.baseline/dialegg-tie-contract/`. No native builds, generators, Docker jobs, or benchmarks were run here. Root has supplied and this agent has inspected the real positive cost/membership and negative `Value 999` probes.

## Changes

* Native delegates retain `RUST_LOG=info`, bind each observed cost to its exact ordered stdout term, and record the environment and cost evidence. Missing/misbound logs cannot enable a tie exemption.
* Eligible sessions retain every original extraction, including an explicit zero variants argument. Only exact native-result equality queries are inserted immediately before those extraction commands; shared `native_check_contract` binds their command positions and preceding source.
* Static cost accounting validates the output's constructor argument/result sorts, primitive types, explicit/default costs, tree multiplicity, and bounded integer totals. The **entire supported constructor table**, including unselected competitors, is compared between original and modernized source. The known merged lookup-table declarations may be excluded from the original constructor comparison only after proving no application of any such table appears anywhere in the raw session. The actual polynomial has 53 constructor signatures and only unused `dims`/`type-of` excluded.
* Admission requires the native logged minimum, native printed tree cost, current logged minimum, and current printed tree cost all to agree. Checks provide graph membership, not an invented witness or a syntactic commutativity shortcut. Dynamic/scoped/unextractable/unknown-container cases receive no exemption and retain exact-output comparison. Positive variants remain unsupported and are never reduced to one output.
* Revalidation recognizes the same new contract and rechecks its boundary/model metadata before launching the replay. `output_matches_native` remains textual/token agreement; `output_contract_passed` separately admits an equal-cost alternative, with explicit numeric evidence.
* Public capture CLI forwards repeated `--speq-frontend-flag=...` only in complete mode. No optimizer pipeline default or SpEQ success count changed.

## Validation

104 focused Python tests passed; six-file Ruff and Mypy passed. Tests include missing/extra/wrong cost logs, different constructor costs including an unselected competitor, ill-typed terms, containers, dynamic costs, negative costs, scope and variants exclusion, moved query boundaries, ordered duplicate roots, exact native-log term binding, full parent/mock replay routing, and a fabricated `Value 999` query failing without workload promotion. These are bounded synthetic tests, not native reproduction evidence.

Offline application of the final functions to the retained actual polynomial and original/current backend logs yields `native_costs=[354]`, `replay_costs=[354]`, `exact_terms=false`; all original commands remain unchanged and ordered. The native evidence itself was produced by root. See [cost report](DIALEGG-OUTPUT-CONTRACT.md) and [SpEQ recovery report](SPEQ-RECOVERY.md).

## Integration and fresh four-parent canary

Only copy the following six owned files or apply [patch](DIALEGG-TIE-CONTRACT.patch). The copied unmodified coordinator support modules in this mirror are test dependencies, **not** integration files.

| File | SHA-256 |
|---|---|
| `scripts/dialegg_speq_complete.py` | `7fe08ddb736d3f9ef72d036a0348681f40d0e4aff9d2224cb0cce74cd2e10e9f` |
| `scripts/suite_capture_dialegg_speq.py` | `0d5aa2eabbab5e8ef6a248347ad0fa93a8b2f1a4ad5cc26aea05961e04c94f97` |
| `scripts/reproduction_validation.py` | `8b6285165ce72734277dad2c5c7e661fe125eb033300c924164c2183d548bed3` |
| `tests/test_dialegg_speq_complete.py` | `33eb1222299afa8a8cad818db6b1473c4f53aa5ee6905778215dbddcdb6a97b2` |
| `tests/test_suite_capture_dialegg_speq.py` | `89f1ab056d806537093015fe617d8c4e2a753032aa4de94c193b348769140c05` |
| `tests/test_reproduction_validation.py` | `0ee4ca536c503202c2dda02604fdd58ea05759768865900bb8fe0824b1a2fa6b` |

Run from the live root, through the coordinator's existing exclusive heavy-stage lock. **Proposed command; not executed here.** The ordinary native resource guard, 10 GiB disk reserve, and configured per-stage deadlines still apply. Existing settings already identify LLVM18, the real historical DialEgg backend, source checkout, and ordinary replay engine.

```bash
EGGLOG_BENCH_MEMORY_GUARD=1 .venv/bin/python -m scripts.suite_reproduction \
  --family dialegg --stage all \
  --settings benchmarks/local/reproduction/settings.json \
  --case dialegg-runtime-polynomial-eqsat \
  --case dialegg-runtime-polynomial-canonicalize-eqsat \
  --case dialegg-runtime-polynomial-eqsat-canonicalize \
  --case dialegg-timer-polynomial
```

Changed implementation hashes create new immutable attempts; `--retry` is needed only if explicitly rerunning an already-identical attempt. Gate each parent on successful source/native MLIR reconstruction + verifier, all calls materialized, actual native costs bound to responses, successful exact-native membership checks and cost agreement for every eligible extraction, then independent standalone revalidation. Retain textual disagreements explicitly. Strict proof validation is a later separate gate and has not been performed by this patch.

The original failed byte-equality captures and source-prefix diagnostics remain historical evidence; do not retroactively overwrite their results. SpEQ no-GVN diagnostics have exposed further FIR correctness limitations and do not add a successful application source.
