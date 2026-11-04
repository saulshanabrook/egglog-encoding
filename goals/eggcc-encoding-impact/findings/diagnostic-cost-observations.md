# Excluded-cohort diagnostic observations

**Diagnostic only: invalid for paper performance use, causal arm comparisons, or speedup/overhead inference.** These are descriptive numbers from original-one/block-04 and corrected-max/block-02 only. Neither cohort is admitted as an accepted cost result. No earlier block is pooled, no row is salvaged or trimmed, and no figure is generated.

Before reading distributions, I read the retained `observations-cost/invalid-retry-cohorts.json` (SHA `540e1bae5834db20dd09c1053c1264443bc6243bb83844294caf1d5b50e81c21`). It excludes both complete cohorts before distribution inspection. Original-one has unresolved transient external Python/Node work with failed cwd attribution; this does not establish a particular forbidden job or a slowdown. Corrected-max overlaps actual unrelated asset tar/gzip packaging. The memory-policy override does not remove those recorded CPU/I/O exclusions. This derivation does not reinterpret the host decision.

Each table row uses exactly twelve `phase=measurement` observations, repetitions 0–11. Three correctness and three warmup timings per case are excluded. Wall columns are milliseconds; SD is sample SD with denominator n−1. RSS columns are MiB (bytes divided by 2²⁰).

| Case / excluded block | Arm | n | Wall median | Wall min–max | Wall sample SD | wait4 RSS median | RSS min–max |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| original-one / block-04 | Off | 12 | 153.848 | 152.139–197.927 | 14.168 | 42.516 | 42.359–42.625 |
| original-one / block-04 | Manual | 12 | 293.848 | 291.938–315.960 | 6.794 | 43.367 | 43.000–43.547 |
| original-one / block-04 | Injective | 12 | 288.757 | 281.992–338.202 | 15.299 | 43.375 | 42.984–44.250 |
| corrected-max / block-02 | Off | 12 | 155.462 | 153.891–170.134 | 4.798 | 42.539 | 42.453–42.828 |
| corrected-max / block-02 | Manual | 12 | 289.876 | 284.140–298.233 | 4.263 | 43.461 | 43.094–43.906 |
| corrected-max / block-02 | Injective | 12 | 294.317 | 287.241–312.933 | 7.114 | 43.438 | 43.000–43.766 |

Wall time is the recorded compiler-process boundary including CLI JSON receipt, excluding interpretation; it is not generated-program execution time. RSS is platform-normalized `wait4` child `ru_maxrss`, not simultaneous process-group peak or per-pair storage. The rows describe the excluded runs without attributing their differences to an encoding or checker.

The standalone [derivation script](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/observations-cost/diagnostic-excluded-01/summarize.py) imports standard-library modules only. It requires the exclusion-bound input hashes, completed schema/row status, all three arms and twelve unique measurements each; computes wall median/min/max/sample SD and RSS median/range; and cross-checks SD with the explicit n−1 formula. It reuses the existing zero-exit verify/postcapture receipts and complete 42-row postcapture records. Embedded correctness rows independently match false/false for original x=1 and true/true for corrected MAX. It does not rerun project verification or re-audit all compiler receipts.

The [machine-readable summary](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/observations-cost/diagnostic-excluded-01/summary.json) retains all twelve raw wall and RSS values per arm, repetition order, original row indices, full-precision statistics, exclusion reasons and input hashes: 72 wall observations and 72 corresponding RSS observations. It expressly marks paper-performance/causal-comparison use false. No cross-case aggregate or ratio is produced.

| Bound artifact | SHA-256 |
| --- | --- |
| Original-one block-04 `results.json` | `568accf5df72b44f1176760480b76be038e9a04df92943f4ced051ff4ef8141c` |
| Corrected-max block-02 `results.json` | `8faa4ae097fc3b9075e638566e542fa01f927c57adc3bea137dc86deb04554e9` |
| Derivation script | `cd3057c532d34460e8208a0bcaa0c8a5fa1dbeea68d73e3a44e4360cd4261af2` |
| Machine-readable summary | `507fcff21ab28898c5b101ccac54ae9380eb3c93278d53fbc97d868bdbd754db` |

Executed from `/Users/saul/p/egglog-encoding`:

```sh
python3 benchmarks/local/eggcc-encoding-impact/observations-cost/diagnostic-excluded-01/summarize.py --output benchmarks/local/eggcc-encoding-impact/observations-cost/diagnostic-excluded-01/summary.json
```

The script refuses to overwrite a prior derived output. Input hashes matched again after derivation and a final read-only check. No project/peer classifier was imported; no workload, build, test, source edit, host-policy change, or figure command ran. This small-case diagnostic request is fulfilled; accepted cost results and final completion remain pending. All computation from this task is terminal.
