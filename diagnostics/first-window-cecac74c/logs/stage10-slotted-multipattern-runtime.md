# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage09 | bf13e3ac9d6c | slotted |
| Candidate | stage10 | fb04877229a0 | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage10 slotted vs stage09 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 1.78–1.82x | slower |
| Wall time | Lowest-ratio file | mmm_sum_1st-44rules.egg | 0.931–0.966x | faster |
| Wall time | Highest-ratio file | ttm_2nd-44rules.egg | 5.78–5.86x | slower |
| Peak RSS | Lowest-ratio file | ttm_2nd-44rules.egg | 0.995–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | batax_1st-44rules.egg | 0.999–1.00x | CI includes 1 |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 78.0–80.0 s | 93.1–95.2 s | 1.17–1.21x | slower |
| mmm_1st-44rules.egg | 380–388 ms | 415–429 ms | 1.08–1.12x | slower |
| mmm_2nd-44rules.egg | 5.39–5.71 s | 17.7–19.5 s | 3.17–3.54x | slower |
| mmm_sum_1st-44rules.egg | 164–166 ms | 154–159 ms | 0.931–0.966x | faster |
| mmm_sum_2nd-44rules.egg | 806–812 ms | 1.92–1.97 s | 2.37–2.44x | slower |
| mttkrp_1st-44rules.egg | 1.01–1.02 s | 1.12–1.24 s | 1.10–1.22x | slower |
| ttm_1st-44rules.egg | 512–538 ms | 629–654 ms | 1.18–1.26x | slower |
| ttm_2nd-44rules.egg | 9.99–10.1 s | 58.0–58.6 s | 5.78–5.86x | slower |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.7–1.7 GiB | 1.7–1.7 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 105.7–105.7 MiB | 105.5–105.5 MiB | 0.999–0.999x | lower RSS |
| mmm_2nd-44rules.egg | 310.7–311.6 MiB | 310.3–311.6 MiB | 0.997–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 105.7–105.7 MiB | 105.5–105.5 MiB | 0.999–0.999x | lower RSS |
| mmm_sum_2nd-44rules.egg | 105.7–105.7 MiB | 105.5–105.5 MiB | 0.999–0.999x | lower RSS |
| mttkrp_1st-44rules.egg | 105.7–105.7 MiB | 105.5–105.5 MiB | 0.999–0.999x | lower RSS |
| ttm_1st-44rules.egg | 105.7–105.7 MiB | 105.5–105.5 MiB | 0.999–0.999x | lower RSS |
| ttm_2nd-44rules.egg | 528.8–530.9 MiB | 527.5–530.2 MiB | 0.995–1.00x | CI includes 1 |
