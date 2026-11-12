# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage04 | 83dac3f0a4ac | slotted-no-aliasing |
| Candidate | stage05 | 2d2a3dac4b44 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage05 slotted-no-aliasing vs stage04 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.770–1.02x | CI includes 1 |
| Wall time | Lowest-ratio file | batax_2nd-44rules.egg | 0.842–0.910x | faster |
| Wall time | Highest-ratio file | mmm_1st-44rules.egg | 0.864–1.07x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.998–0.998x | lower RSS |
| Peak RSS | Highest-ratio file | mmm_2nd-44rules.egg | 0.994–1.01x | CI includes 1 |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 79.3–113 s | 70.4–99.5 s | 0.688–1.13x | CI includes 1 |
| batax_2nd-44rules.egg | 52.9–54.0 s | 45.0–48.5 s | 0.842–0.910x | faster |
| mmm_1st-44rules.egg | 325–387 ms | 321–362 ms | 0.864–1.07x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.14–2.54 s | 2.17–2.18 s | 0.857–1.02x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 165–195 ms | 169–173 ms | 0.877–1.04x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 551–664 ms | 566–584 ms | 0.865–1.05x | CI includes 1 |
| mttkrp_1st-44rules.egg | 648–751 ms | 641–676 ms | 0.872–1.02x | CI includes 1 |
| mttkrp_2nd-44rules.egg | 9.68–12.6 s | 10.2–10.4 s | 0.819–1.06x | CI includes 1 |
| ttm_1st-44rules.egg | 424–525 ms | 442–455 ms | 0.853–1.06x | CI includes 1 |
| ttm_2nd-44rules.egg | 4.18–5.18 s | 4.24–4.49 s | 0.838–1.05x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 0.999–1.00x | CI includes 1 |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 1.00–1.00x | higher RSS |
| mmm_1st-44rules.egg | 104.9–104.9 MiB | 104.7–104.7 MiB | 0.998–0.998x | lower RSS |
| mmm_2nd-44rules.egg | 122.5–124.0 MiB | 122.9–124.0 MiB | 0.994–1.01x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 104.9–104.9 MiB | 104.7–104.7 MiB | 0.998–0.998x | lower RSS |
| mmm_sum_2nd-44rules.egg | 104.9–104.9 MiB | 104.7–104.7 MiB | 0.998–0.998x | lower RSS |
| mttkrp_1st-44rules.egg | 104.9–104.9 MiB | 104.7–104.7 MiB | 0.998–0.998x | lower RSS |
| mttkrp_2nd-44rules.egg | 477.3–478.2 MiB | 477.7–478.8 MiB | 1.000–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 104.9–104.9 MiB | 104.7–104.7 MiB | 0.998–0.998x | lower RSS |
| ttm_2nd-44rules.egg | 211.8–213.3 MiB | 212.0–213.2 MiB | 0.996–1.01x | CI includes 1 |
