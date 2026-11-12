# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage02 | e9a2c07334e1 | slotted |
| Candidate | stage03 | cfc7c8a0982b | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage03 slotted vs stage02 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.885–1.42x | CI includes 1 |
| Wall time | Lowest-ratio file | ttm_2nd-44rules.egg | 0.744–1.46x | CI includes 1 |
| Wall time | Highest-ratio file | mmm_1st-44rules.egg | 0.848–1.54x | CI includes 1 |
| Peak RSS | Lowest-ratio file | batax_1st-44rules.egg | 0.999–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.00–1.00x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 76.4–119 s | 90.1–129 s | 0.849–1.50x | CI includes 1 |
| mmm_1st-44rules.egg | 416–478 ms | 382–683 ms | 0.848–1.54x | CI includes 1 |
| mmm_2nd-44rules.egg | 5.86–6.23 s | 5.14–8.80 s | 0.849–1.46x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 179–195 ms | 158–256 ms | 0.844–1.37x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 856–975 ms | 0.693–1.30 s | 0.753–1.44x | CI includes 1 |
| mttkrp_1st-44rules.egg | 1.09–1.19 s | 0.901–1.65 s | 0.790–1.46x | CI includes 1 |
| ttm_1st-44rules.egg | 577–622 ms | 437–912 ms | 0.728–1.52x | CI includes 1 |
| ttm_2nd-44rules.egg | 9.57–14.3 s | 9.32–15.9 s | 0.744–1.46x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.8–1.8 GiB | 1.8–1.8 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 104.8–104.8 MiB | 105.0–105.0 MiB | 1.00–1.00x | higher RSS |
| mmm_2nd-44rules.egg | 312.4–313.6 MiB | 312.2–314.4 MiB | 0.997–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 104.8–104.8 MiB | 105.0–105.0 MiB | 1.00–1.00x | higher RSS |
| mmm_sum_2nd-44rules.egg | 104.8–104.8 MiB | 105.0–105.0 MiB | 1.00–1.00x | higher RSS |
| mttkrp_1st-44rules.egg | 104.8–104.8 MiB | 105.0–105.0 MiB | 1.00–1.00x | higher RSS |
| ttm_1st-44rules.egg | 104.8–104.8 MiB | 105.0–105.0 MiB | 1.00–1.00x | higher RSS |
| ttm_2nd-44rules.egg | 535.0–535.3 MiB | 535.1–535.3 MiB | 1.000–1.00x | CI includes 1 |
