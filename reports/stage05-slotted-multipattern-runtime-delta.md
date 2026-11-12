# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage04 | 83dac3f0a4ac | slotted |
| Candidate | stage05 | 2d2a3dac4b44 | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage05 slotted vs stage04 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.887–1.01x | CI includes 1 |
| Wall time | Lowest-ratio file | batax_1st-44rules.egg | 0.868–1.01x | CI includes 1 |
| Wall time | Highest-ratio file | mttkrp_1st-44rules.egg | 0.912–1.05x | CI includes 1 |
| Peak RSS | Lowest-ratio file | batax_1st-44rules.egg | 0.999–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.00–1.00x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 83.7–89.8 s | 75.9–87.3 s | 0.868–1.01x | CI includes 1 |
| mmm_1st-44rules.egg | 436–440 ms | 415–433 ms | 0.947–0.990x | faster |
| mmm_2nd-44rules.egg | 5.68–5.86 s | 5.39–5.78 s | 0.931–1.01x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 184–190 ms | 173–187 ms | 0.924–1.00x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 853–907 ms | 795–905 ms | 0.897–1.04x | CI includes 1 |
| mttkrp_1st-44rules.egg | 1.05–1.10 s | 0.985–1.12 s | 0.912–1.05x | CI includes 1 |
| ttm_1st-44rules.egg | 565–579 ms | 524–578 ms | 0.915–1.01x | CI includes 1 |
| ttm_2nd-44rules.egg | 10.6–11.0 s | 10.2–10.9 s | 0.937–1.01x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.7–1.8 GiB | 1.7–1.8 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 105.7–105.7 MiB | 105.9–105.9 MiB | 1.00–1.00x | higher RSS |
| mmm_2nd-44rules.egg | 310.3–310.7 MiB | 310.5–310.7 MiB | 1.000–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 105.7–105.7 MiB | 105.9–105.9 MiB | 1.00–1.00x | higher RSS |
| mmm_sum_2nd-44rules.egg | 105.7–105.7 MiB | 105.9–105.9 MiB | 1.00–1.00x | higher RSS |
| mttkrp_1st-44rules.egg | 105.7–105.7 MiB | 105.9–105.9 MiB | 1.00–1.00x | higher RSS |
| ttm_1st-44rules.egg | 105.7–105.7 MiB | 105.9–105.9 MiB | 1.00–1.00x | higher RSS |
| ttm_2nd-44rules.egg | 531.9–532.1 MiB | 531.5–533.2 MiB | 0.999–1.00x | CI includes 1 |
