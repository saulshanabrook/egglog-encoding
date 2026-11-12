# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage10 | fb04877229a0 | slotted |
| Candidate | stage11 | cecac74c2a2a | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage11 slotted vs stage10 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.980–1.07x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_1st-44rules.egg | 0.968–1.00x | CI includes 1 |
| Wall time | Highest-ratio file | mmm_2nd-44rules.egg | 0.963–1.15x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_2nd-44rules.egg | 0.996–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.00–1.00x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 93.1–95.2 s | 91.5–101 s | 0.970–1.08x | CI includes 1 |
| mmm_1st-44rules.egg | 415–429 ms | 415–417 ms | 0.968–1.00x | CI includes 1 |
| mmm_2nd-44rules.egg | 17.7–19.5 s | 18.1–21.1 s | 0.963–1.15x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 154–159 ms | 153–156 ms | 0.971–1.01x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 1.92–1.97 s | 1.90–2.04 s | 0.974–1.05x | CI includes 1 |
| mttkrp_1st-44rules.egg | 1.12–1.24 s | 1.17–1.24 s | 0.965–1.08x | CI includes 1 |
| ttm_1st-44rules.egg | 629–654 ms | 628–670 ms | 0.974–1.05x | CI includes 1 |
| ttm_2nd-44rules.egg | 58.0–58.6 s | 53.5–65.5 s | 0.917–1.12x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.7–1.7 GiB | 1.7–1.7 GiB | 1.000–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 105.5–105.5 MiB | 105.8–105.8 MiB | 1.00–1.00x | higher RSS |
| mmm_2nd-44rules.egg | 310.3–311.6 MiB | 310.2–310.6 MiB | 0.996–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 105.5–105.5 MiB | 105.8–105.8 MiB | 1.00–1.00x | higher RSS |
| mmm_sum_2nd-44rules.egg | 105.5–105.5 MiB | 105.8–105.8 MiB | 1.00–1.00x | higher RSS |
| mttkrp_1st-44rules.egg | 105.5–105.5 MiB | 105.8–105.8 MiB | 1.00–1.00x | higher RSS |
| ttm_1st-44rules.egg | 105.5–105.5 MiB | 105.8–105.8 MiB | 1.00–1.00x | higher RSS |
| ttm_2nd-44rules.egg | 527.5–530.2 MiB | 528.5–528.8 MiB | 0.997–1.00x | CI includes 1 |
