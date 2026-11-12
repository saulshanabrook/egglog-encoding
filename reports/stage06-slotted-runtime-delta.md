# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage05 | 2d2a3dac4b44 | slotted-no-aliasing |
| Candidate | stage06 | 06f9387ec51e | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage06 slotted-no-aliasing vs stage05 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.948–1.17x | CI includes 1 |
| Wall time | Lowest-ratio file | mttkrp_1st-44rules.egg | 0.861–0.922x | faster |
| Wall time | Highest-ratio file | batax_2nd-44rules.egg | 1.05–1.19x | slower |
| Peak RSS | Lowest-ratio file | mttkrp_2nd-44rules.egg | 0.995–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.01–1.01x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 70.4–99.5 s | 81.6–92.1 s | 0.862–1.24x | CI includes 1 |
| batax_2nd-44rules.egg | 45.0–48.5 s | 49.7–55.1 s | 1.05–1.19x | slower |
| mmm_1st-44rules.egg | 321–362 ms | 323–336 ms | 0.907–1.03x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.17–2.18 s | 2.13–2.17 s | 0.980–0.997x | faster |
| mmm_sum_1st-44rules.egg | 169–173 ms | 166–175 ms | 0.970–1.03x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 566–584 ms | 564–580 ms | 0.973–1.01x | CI includes 1 |
| mttkrp_1st-44rules.egg | 641–676 ms | 574–599 ms | 0.861–0.922x | faster |
| mttkrp_2nd-44rules.egg | 10.2–10.4 s | 9.94–10.3 s | 0.964–1.01x | CI includes 1 |
| ttm_1st-44rules.egg | 442–455 ms | 421–429 ms | 0.932–0.965x | faster |
| ttm_2nd-44rules.egg | 4.24–4.49 s | 4.16–4.54 s | 0.946–1.05x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 0.998–0.999x | lower RSS |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 0.999–0.999x | lower RSS |
| mmm_1st-44rules.egg | 104.7–104.7 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| mmm_2nd-44rules.egg | 122.9–124.0 MiB | 122.7–124.5 MiB | 0.993–1.01x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 104.7–104.7 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| mmm_sum_2nd-44rules.egg | 104.7–104.7 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| mttkrp_1st-44rules.egg | 104.7–104.7 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| mttkrp_2nd-44rules.egg | 477.7–478.8 MiB | 475.9–478.7 MiB | 0.995–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 104.7–104.7 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| ttm_2nd-44rules.egg | 212.0–213.2 MiB | 211.5–214.3 MiB | 0.994–1.01x | CI includes 1 |
