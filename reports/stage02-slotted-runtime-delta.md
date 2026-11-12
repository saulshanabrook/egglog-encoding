# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage01 | acbe3a91b4d3 | slotted-no-aliasing |
| Candidate | stage02 | e9a2c07334e1 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage02 slotted-no-aliasing vs stage01 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.870–1.16x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_sum_2nd-44rules.egg | 0.403–1.09x | CI includes 1 |
| Wall time | Highest-ratio file | batax_2nd-44rules.egg | 0.758–1.38x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_2nd-44rules.egg | 0.938–0.964x | lower RSS |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.01–1.01x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 88.6–100 s | 82.2–115 s | 0.863–1.24x | CI includes 1 |
| batax_2nd-44rules.egg | 54.1–57.4 s | 42.3–77.1 s | 0.758–1.38x | CI includes 1 |
| mmm_1st-44rules.egg | 446–691 ms | 284–533 ms | 0.477–1.03x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.33–4.39 s | 1.86–3.23 s | 0.502–1.17x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 169–323 ms | 146–227 ms | 0.524–1.16x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 0.682–1.41 s | 467–902 ms | 0.403–1.09x | CI includes 1 |
| mttkrp_1st-44rules.egg | 0.633–1.22 s | 560–969 ms | 0.546–1.29x | CI includes 1 |
| mttkrp_2nd-44rules.egg | 10.1–19.7 s | 9.03–14.7 s | 0.538–1.24x | CI includes 1 |
| ttm_1st-44rules.egg | 477–831 ms | 448–559 ms | 0.590–1.07x | CI includes 1 |
| ttm_2nd-44rules.egg | 5.37–7.09 s | 4.41–5.14 s | 0.658–0.905x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 1.00–1.00x | higher RSS |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 1.00–1.00x | higher RSS |
| mmm_1st-44rules.egg | 102.4–102.4 MiB | 103.8–103.8 MiB | 1.01–1.01x | higher RSS |
| mmm_2nd-44rules.egg | 128.8–131.7 MiB | 122.9–124.8 MiB | 0.938–0.964x | lower RSS |
| mmm_sum_1st-44rules.egg | 102.4–102.4 MiB | 103.8–103.8 MiB | 1.01–1.01x | higher RSS |
| mmm_sum_2nd-44rules.egg | 102.4–102.4 MiB | 103.8–103.8 MiB | 1.01–1.01x | higher RSS |
| mttkrp_1st-44rules.egg | 102.4–102.4 MiB | 103.8–103.8 MiB | 1.01–1.01x | higher RSS |
| mttkrp_2nd-44rules.egg | 492.1–493.4 MiB | 478.3–479.0 MiB | 0.970–0.973x | lower RSS |
| ttm_1st-44rules.egg | 102.4–102.4 MiB | 103.8–103.8 MiB | 1.01–1.01x | higher RSS |
| ttm_2nd-44rules.egg | 220.7–221.4 MiB | 211.8–213.0 MiB | 0.958–0.964x | lower RSS |
