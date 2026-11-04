# T1: fixed-split tuple cancellation has no surviving trigger in this screen

Close T1 for the six-fixture portfolio below. A fresh current-main run found no same-result, same-split `Concat` pair from which guarded cancellation could derive a new child equality. No encoding or compiler change was made. This is a bounded negative result, not a claim that tuple cancellation can never help EggCC.

## What was tested

For total finite tuples in the same semantic scope, the relevant law is

\[
\operatorname{Concat}(a,b)=\operatorname{Concat}(c,d)
\land |a|=|c|
\implies a=c\land b=d.
\]

The split condition is essential: `[x] ++ [y,z] = [x,y] ++ [z]` has different children. EggCC already equates associative and empty-tuple forms in [`canonicalize.egg`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/utility/canonicalize.egg:41). Marking its general binary `Concat` constructor injective would therefore be unsound.

The census uses U0 commit `a0bbec127f83249074a46af3fd6f6126c90fe0fb`, which the parent admission verified against current remote main. It runs the admitted release `eggcc` binary, SHA-256 `d86869982413d4561cf713cc769c96eb1c9bfefe46fa459a2692c53a7aa93cf0`, with its admitted `tiger`, the normal optimization schedule, `--with-context`, and `--egraph-out-dir`. Each of six invocations has a 180-second timeout. All six exited successfully and each exported three graphs; no build or full test suite was run for this diagnostic.

The CLI exports **after a complete pass schedule, before extraction** ([source](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/lib.rs:973)). It cannot capture helpers before their consumers without a source change. Thus this screen does not measure transient demand or prove that a different schedule could never avoid work.

## Fresh results

Counts below sum the three pass graphs for each fixture. The 18 graph contents have distinct SHA-256 values, but nodes and semantic facts may recur between passes. These are diagnostic counts, not performance measurements.

| Existing fixture | Nodes | Concat rows | Same-output, different-child pairs | Unequal split from `tuple-length` facts | Missing length facts | Same known split |
|---|---:|---:|---:|---:|---:|---:|
| `if_invariant_do_pull_out.rs` | 11,197 | 158 | 26 | 24 | 2 | 0 |
| `ivt.rs` | 7,088 | 164 | 57 | 46 | 11 | 0 |
| `loop_hoist.bril` | 8,168 | 150 | 46 | 46 | 0 | 0 |
| `loop_pass_through.bril` | 2,583 | 30 | 0 | 0 | 0 | 0 |
| `loop_with_mul_by_inv.bril` | 6,952 | 156 | 43 | 43 | 0 | 0 |
| `lowbit_naive_extra.rs` | 9,917 | 222 | 78 | 65 | 13 | 0 |
| **Total** | **45,905** | **880** | **250** | **224** | **26** | **0** |

Rows are compared using canonical child eclasses, not whichever serialized node happens to represent a child. All 880 `Concat` rows were active, and all 250 nonidentical alternative pairs differed in both children. The export contains 1,208 `tuple-length` rows and 1,610 `Get` rows; all exported integer length results and `Get` indices could be decoded.

The 26 missing-length pairs are retained as missing evidence. Separately, each has an `Empty`, `Single`, or constant-length `SubTuple` representation giving **different advertised prefix lengths**. The length pairs are `0/1` (8 pairs), `1/2` (6), `0/2` (4), `1/3` (3), `0/3` (2), `2/3` (2), and `3/1` (1). These shape observations are not relabeled as engine `tuple-length` facts or totality proofs. For example, `ivt` pass 2 has an alternative split at prefix lengths 1 and 2, represented by `Single`/`SubTuple` helpers whose length facts are absent. None of the missing-fact pairs supplies a same-split producer.

## Why the current consumers do not rescue this lead

EggCC already creates every in-range `Get` for leading loop, branch, and argument tuples, then pushes those projections through `Concat` using `Add-Gets` and `Add-All-Gets` ([`util.egg`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/utility/util.egg:58)). Its `SubTuple` reconstruction adds canonical tuple forms for the region values ([`canonicalize.egg`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/utility/canonicalize.egg:71)).

The existing loop and branch passthrough rules consume equalities between individual `Get` results ([`passthrough.egg`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/passthrough.egg:4)). IVT likewise matches shared projected values and recursively decomposes `Concat(Single(Get(...)), rest)` ([`ivt.egg`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/ivt.egg:42)). A useful new whole-child equality would need an eligible producer and an actual changed match in one of these consumers. This census found no eligible producer, so there is no sound new child equality to test at a consumer. It does not establish blanket projection redundancy for all possible future tuple graphs.

The retained pair inventory includes each child's canonical type/context facts, purity flag, and demanded `Get` indices and results. These are evidence, not admission guards: totality was not certified. In particular, `ExprIsPure` includes `Div` and can propagate through `DoWhile` ([`purity_analysis.egg`](/private/tmp/eggcc-nontrivial-encoding-payoff-u0/dag_in_context/src/optimizations/purity_analysis.egg:10)), so it does not establish finite total tuple semantics by itself. There is no reason to implement a new totality analysis here when the necessary same-split trigger already fails.

## Receipts and reproduction

All scripts and evidence are in [the tuple-census directory](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/tuple-census). The [capture index](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/tuple-census/capture-index.json) records each exact argv, cwd, complete supplied environment, input and binary hashes, timeout, exit status, and output hashes. The [census](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/tuple-census/census.json) retains every graph hash and every pair, including missing lengths and separate advertised-shape evidence. The source/code identities and verification results are recorded in `source-review.json` in that directory.

Recompute the analysis without rerunning the compiler:

```sh
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/tuple-census/census.py --self-test
python3 benchmarks/local/eggcc-nontrivial-encoding-payoff/tuple-census/census.py
```

The self-test exercises a positive same-split pair, an unequal-split rejection, missing lengths remaining unknown, and shape evidence remaining separate from engine facts. `capture.py` preserves existing captures and refuses to overwrite their receipts; a future fresh compiler run should use a new study directory and retain its own identities.

**Disposition:** `T1-fixed-split` is closed without implementation for this bounded portfolio. Reopen only on a new source-backed same-result/same-split pair with justified semantic guards and a blocked consumer, or a concrete avoided-work hypothesis with an appropriate schedule/manual comparison. No bug or speedup was established.
