# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage01 | acbe3a91b4d3 | slotted |
| Candidate | stage02 | e9a2c07334e1 | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage02 slotted vs stage01 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.813–1.18x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_sum_2nd-44rules.egg | 0.589–0.691x | faster |
| Wall time | Highest-ratio file | batax_1st-44rules.egg | 0.843–1.33x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_2nd-44rules.egg | 0.957–0.964x | lower RSS |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.02–1.02x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 85.1–95.1 s | 76.4–119 s | 0.843–1.33x | CI includes 1 |
| mmm_1st-44rules.egg | 631–645 ms | 416–478 ms | 0.652–0.750x | faster |
| mmm_2nd-44rules.egg | 7.76–8.00 s | 5.86–6.23 s | 0.741–0.793x | faster |
| mmm_sum_1st-44rules.egg | 230–255 ms | 179–195 ms | 0.722–0.825x | faster |
| mmm_sum_2nd-44rules.egg | 1.37–1.50 s | 856–975 ms | 0.589–0.691x | faster |
| mttkrp_1st-44rules.egg | 1.60–1.66 s | 1.09–1.19 s | 0.666–0.730x | faster |
| ttm_1st-44rules.egg | 878–913 ms | 577–622 ms | 0.642–0.698x | faster |
| ttm_2nd-44rules.egg | 16.4–16.8 s | 9.57–14.3 s | 0.576–0.861x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.8–1.8 GiB | 1.8–1.8 GiB | 1.000–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 102.4–102.4 MiB | 104.8–104.8 MiB | 1.02–1.02x | higher RSS |
| mmm_2nd-44rules.egg | 325.0–326.8 MiB | 312.4–313.6 MiB | 0.957–0.964x | lower RSS |
| mmm_sum_1st-44rules.egg | 102.4–102.4 MiB | 104.8–104.8 MiB | 1.02–1.02x | higher RSS |
| mmm_sum_2nd-44rules.egg | 102.4–102.4 MiB | 104.8–104.8 MiB | 1.02–1.02x | higher RSS |
| mttkrp_1st-44rules.egg | 102.4–102.4 MiB | 104.8–104.8 MiB | 1.02–1.02x | higher RSS |
| ttm_1st-44rules.egg | 102.4–102.4 MiB | 104.8–104.8 MiB | 1.02–1.02x | higher RSS |
| ttm_2nd-44rules.egg | 556.0–556.4 MiB | 535.0–535.3 MiB | 0.962–0.963x | lower RSS |
