# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage02 | e9a2c07334e1 | slotted-no-aliasing |
| Candidate | stage03 | cfc7c8a0982b | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage03 slotted-no-aliasing vs stage02 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.852–1.13x | CI includes 1 |
| Wall time | Lowest-ratio file | ttm_1st-44rules.egg | 0.789–1.05x | CI includes 1 |
| Wall time | Highest-ratio file | ttm_2nd-44rules.egg | 0.863–1.17x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_2nd-44rules.egg | 0.991–1.01x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.01–1.01x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 82.2–115 s | 89.1–103 s | 0.819–1.18x | CI includes 1 |
| batax_2nd-44rules.egg | 42.3–77.1 s | 54.1–63.1 s | 0.751–1.39x | CI includes 1 |
| mmm_1st-44rules.egg | 284–533 ms | 342–444 ms | 0.713–1.41x | CI includes 1 |
| mmm_2nd-44rules.egg | 1.86–3.23 s | 2.21–2.65 s | 0.739–1.32x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 146–227 ms | 161–198 ms | 0.769–1.26x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 467–902 ms | 567–720 ms | 0.693–1.40x | CI includes 1 |
| mttkrp_1st-44rules.egg | 560–969 ms | 667–794 ms | 0.741–1.32x | CI includes 1 |
| mttkrp_2nd-44rules.egg | 9.03–14.7 s | 10.5–12.2 s | 0.759–1.27x | CI includes 1 |
| ttm_1st-44rules.egg | 448–559 ms | 417–496 ms | 0.789–1.05x | CI includes 1 |
| ttm_2nd-44rules.egg | 4.41–5.14 s | 4.19–5.48 s | 0.863–1.17x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 0.999–1.00x | CI includes 1 |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 1.000–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 103.8–103.8 MiB | 104.7–104.7 MiB | 1.01–1.01x | higher RSS |
| mmm_2nd-44rules.egg | 122.9–124.8 MiB | 123.4–123.9 MiB | 0.991–1.01x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 103.8–103.8 MiB | 104.7–104.7 MiB | 1.01–1.01x | higher RSS |
| mmm_sum_2nd-44rules.egg | 103.8–103.8 MiB | 104.7–104.7 MiB | 1.01–1.01x | higher RSS |
| mttkrp_1st-44rules.egg | 103.8–103.8 MiB | 104.7–104.7 MiB | 1.01–1.01x | higher RSS |
| mttkrp_2nd-44rules.egg | 478.3–479.0 MiB | 477.9–479.2 MiB | 0.998–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 103.8–103.8 MiB | 104.7–104.7 MiB | 1.01–1.01x | higher RSS |
| ttm_2nd-44rules.egg | 211.8–213.0 MiB | 212.3–212.7 MiB | 0.998–1.00x | CI includes 1 |
