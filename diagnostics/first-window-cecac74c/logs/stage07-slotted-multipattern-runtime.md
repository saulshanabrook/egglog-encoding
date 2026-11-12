# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | main | 37b148e74175 | slotted |
| Candidate | stage07 | b5a6dcde4721 | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage07 slotted vs main slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.940–1.05x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_sum_1st-44rules.egg | 0.931–0.993x | faster |
| Wall time | Highest-ratio file | mmm_sum_2nd-44rules.egg | 0.982–1.02x | CI includes 1 |
| Peak RSS | Lowest-ratio file | ttm_2nd-44rules.egg | 0.998–1.000x | lower RSS |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.00–1.00x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 77.4–80.9 s | 74.3–83.6 s | 0.935–1.06x | CI includes 1 |
| mmm_1st-44rules.egg | 405–419 ms | 399–407 ms | 0.961–0.999x | faster |
| mmm_2nd-44rules.egg | 5.42–5.54 s | 5.26–5.58 s | 0.958–1.02x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 173–184 ms | 170–174 ms | 0.931–0.993x | faster |
| mmm_sum_2nd-44rules.egg | 809–827 ms | 806–828 ms | 0.982–1.02x | CI includes 1 |
| mttkrp_1st-44rules.egg | 0.996–1.04 s | 0.994–1.01 s | 0.958–1.01x | CI includes 1 |
| ttm_1st-44rules.egg | 527–543 ms | 521–529 ms | 0.965–0.997x | faster |
| ttm_2nd-44rules.egg | 8.80–12.4 s | 10.1–10.3 s | 0.822–1.16x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.7–1.8 GiB | 1.7–1.7 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 103.4–103.4 MiB | 103.7–103.7 MiB | 1.00–1.00x | higher RSS |
| mmm_2nd-44rules.egg | 309.8–310.8 MiB | 310.3–310.8 MiB | 0.999–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 103.4–103.4 MiB | 103.7–103.7 MiB | 1.00–1.00x | higher RSS |
| mmm_sum_2nd-44rules.egg | 103.4–103.4 MiB | 103.7–103.7 MiB | 1.00–1.00x | higher RSS |
| mttkrp_1st-44rules.egg | 103.4–103.4 MiB | 103.7–103.7 MiB | 1.00–1.00x | higher RSS |
| ttm_1st-44rules.egg | 103.4–103.4 MiB | 103.7–103.7 MiB | 1.00–1.00x | higher RSS |
| ttm_2nd-44rules.egg | 531.6–532.0 MiB | 530.9–531.7 MiB | 0.998–1.000x | lower RSS |
