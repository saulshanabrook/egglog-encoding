# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage09 | bf13e3ac9d6c | slotted |
| Candidate | stage10 | 33c4a35dfbe0 | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage10 slotted vs stage09 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.978–1.09x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_2nd-44rules.egg | 0.972–1.05x | CI includes 1 |
| Wall time | Highest-ratio file | batax_1st-44rules.egg | 0.968–1.10x | CI includes 1 |
| Peak RSS | Lowest-ratio file | batax_1st-44rules.egg | 0.999–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.01–1.01x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 78.0–80.0 s | 76.6–86.9 s | 0.968–1.10x | CI includes 1 |
| mmm_1st-44rules.egg | 380–388 ms | 381–397 ms | 0.989–1.04x | CI includes 1 |
| mmm_2nd-44rules.egg | 5.39–5.71 s | 5.46–5.76 s | 0.972–1.05x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 164–166 ms | 167–170 ms | 1.01–1.03x | slower |
| mmm_sum_2nd-44rules.egg | 806–812 ms | 810–830 ms | 1.00–1.03x | slower |
| mttkrp_1st-44rules.egg | 1.01–1.02 s | 1.03–1.05 s | 1.01–1.03x | slower |
| ttm_1st-44rules.egg | 512–538 ms | 531–535 ms | 0.990–1.04x | CI includes 1 |
| ttm_2nd-44rules.egg | 9.99–10.1 s | 10.1–10.5 s | 1.00–1.05x | slower |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.7–1.7 GiB | 1.7–1.7 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 105.7–105.7 MiB | 106.8–106.8 MiB | 1.01–1.01x | higher RSS |
| mmm_2nd-44rules.egg | 310.7–311.6 MiB | 310.7–312.2 MiB | 0.998–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 105.7–105.7 MiB | 106.8–106.8 MiB | 1.01–1.01x | higher RSS |
| mmm_sum_2nd-44rules.egg | 105.7–105.7 MiB | 106.8–106.8 MiB | 1.01–1.01x | higher RSS |
| mttkrp_1st-44rules.egg | 105.7–105.7 MiB | 106.8–106.8 MiB | 1.01–1.01x | higher RSS |
| ttm_1st-44rules.egg | 105.7–105.7 MiB | 106.8–106.8 MiB | 1.01–1.01x | higher RSS |
| ttm_2nd-44rules.egg | 528.8–530.9 MiB | 529.0–531.8 MiB | 0.998–1.00x | CI includes 1 |
