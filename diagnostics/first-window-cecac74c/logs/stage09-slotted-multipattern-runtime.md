# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage08 | bfa0d2f76d70 | slotted |
| Candidate | stage09 | bf13e3ac9d6c | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage09 slotted vs stage08 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 1.01–1.04x | slower |
| Wall time | Lowest-ratio file | mmm_sum_1st-44rules.egg | 0.952–0.974x | faster |
| Wall time | Highest-ratio file | batax_1st-44rules.egg | 1.01–1.04x | slower |
| Peak RSS | Lowest-ratio file | mmm_2nd-44rules.egg | 0.998–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.02–1.02x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 76.3–77.4 s | 78.0–80.0 s | 1.01–1.04x | slower |
| mmm_1st-44rules.egg | 380–399 ms | 380–388 ms | 0.961–1.01x | CI includes 1 |
| mmm_2nd-44rules.egg | 5.29–5.67 s | 5.39–5.71 s | 0.967–1.06x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 170–173 ms | 164–166 ms | 0.952–0.974x | faster |
| mmm_sum_2nd-44rules.egg | 802–830 ms | 806–812 ms | 0.975–1.01x | CI includes 1 |
| mttkrp_1st-44rules.egg | 0.979–1.04 s | 1.01–1.02 s | 0.978–1.04x | CI includes 1 |
| ttm_1st-44rules.egg | 528–534 ms | 512–538 ms | 0.964–1.01x | CI includes 1 |
| ttm_2nd-44rules.egg | 9.63–10.3 s | 9.99–10.1 s | 0.970–1.04x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.7–1.7 GiB | 1.7–1.7 GiB | 1.000–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 103.9–103.9 MiB | 105.7–105.7 MiB | 1.02–1.02x | higher RSS |
| mmm_2nd-44rules.egg | 310.9–311.6 MiB | 310.7–311.6 MiB | 0.998–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 103.9–103.9 MiB | 105.7–105.7 MiB | 1.02–1.02x | higher RSS |
| mmm_sum_2nd-44rules.egg | 103.9–103.9 MiB | 105.7–105.7 MiB | 1.02–1.02x | higher RSS |
| mttkrp_1st-44rules.egg | 103.9–103.9 MiB | 105.7–105.7 MiB | 1.02–1.02x | higher RSS |
| ttm_1st-44rules.egg | 103.9–103.9 MiB | 105.7–105.7 MiB | 1.02–1.02x | higher RSS |
| ttm_2nd-44rules.egg | 528.4–530.8 MiB | 528.8–530.9 MiB | 0.997–1.00x | CI includes 1 |
