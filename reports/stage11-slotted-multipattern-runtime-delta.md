# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage10 | 33c4a35dfbe0 | slotted |
| Candidate | stage11 | ff3ff0721ffb | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage11 slotted vs stage10 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.956–1.07x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_sum_1st-44rules.egg | 0.985–1.03x | CI includes 1 |
| Wall time | Highest-ratio file | ttm_1st-44rules.egg | 0.972–1.09x | CI includes 1 |
| Peak RSS | Lowest-ratio file | ttm_2nd-44rules.egg | 0.997–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.01–1.01x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 76.6–86.9 s | 79.9–85.6 s | 0.943–1.09x | CI includes 1 |
| mmm_1st-44rules.egg | 381–397 ms | 391–393 ms | 0.988–1.03x | CI includes 1 |
| mmm_2nd-44rules.egg | 5.46–5.76 s | 5.51–5.96 s | 0.974–1.07x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 167–170 ms | 166–173 ms | 0.985–1.03x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 810–830 ms | 823–836 ms | 0.997–1.03x | CI includes 1 |
| mttkrp_1st-44rules.egg | 1.03–1.05 s | 0.991–1.10 s | 0.954–1.06x | CI includes 1 |
| ttm_1st-44rules.egg | 531–535 ms | 518–580 ms | 0.972–1.09x | CI includes 1 |
| ttm_2nd-44rules.egg | 10.1–10.5 s | 10.3–10.5 s | 0.987–1.04x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.7–1.7 GiB | 1.7–1.7 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 106.8–106.8 MiB | 107.4–107.4 MiB | 1.01–1.01x | higher RSS |
| mmm_2nd-44rules.egg | 310.7–312.2 MiB | 310.9–311.8 MiB | 0.997–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 106.8–106.8 MiB | 107.4–107.4 MiB | 1.01–1.01x | higher RSS |
| mmm_sum_2nd-44rules.egg | 106.8–106.8 MiB | 107.4–107.4 MiB | 1.01–1.01x | higher RSS |
| mttkrp_1st-44rules.egg | 106.8–106.8 MiB | 107.4–107.4 MiB | 1.01–1.01x | higher RSS |
| ttm_1st-44rules.egg | 106.8–106.8 MiB | 107.4–107.4 MiB | 1.01–1.01x | higher RSS |
| ttm_2nd-44rules.egg | 529.0–531.8 MiB | 529.9–530.2 MiB | 0.997–1.00x | CI includes 1 |
