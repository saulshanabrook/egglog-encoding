# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage03 | cfc7c8a0982b | slotted |
| Candidate | stage04 | 83dac3f0a4ac | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage04 slotted vs stage03 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.697–0.945x | faster |
| Wall time | Lowest-ratio file | batax_1st-44rules.egg | 0.671–0.966x | faster |
| Wall time | Highest-ratio file | mmm_sum_1st-44rules.egg | 0.731–1.18x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_2nd-44rules.egg | 0.988–0.995x | lower RSS |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.01–1.01x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 90.1–129 s | 83.7–89.8 s | 0.671–0.966x | faster |
| mmm_1st-44rules.egg | 382–683 ms | 436–440 ms | 0.641–1.15x | CI includes 1 |
| mmm_2nd-44rules.egg | 5.14–8.80 s | 5.68–5.86 s | 0.655–1.12x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 158–256 ms | 184–190 ms | 0.731–1.18x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 0.693–1.30 s | 853–907 ms | 0.675–1.27x | CI includes 1 |
| mttkrp_1st-44rules.egg | 0.901–1.65 s | 1.05–1.10 s | 0.651–1.19x | CI includes 1 |
| ttm_1st-44rules.egg | 437–912 ms | 565–579 ms | 0.628–1.31x | CI includes 1 |
| ttm_2nd-44rules.egg | 9.32–15.9 s | 10.6–11.0 s | 0.678–1.16x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.8–1.8 GiB | 1.7–1.8 GiB | 0.995–0.995x | lower RSS |
| mmm_1st-44rules.egg | 105.0–105.0 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| mmm_2nd-44rules.egg | 312.2–314.4 MiB | 310.3–310.7 MiB | 0.988–0.995x | lower RSS |
| mmm_sum_1st-44rules.egg | 105.0–105.0 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| mmm_sum_2nd-44rules.egg | 105.0–105.0 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| mttkrp_1st-44rules.egg | 105.0–105.0 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| ttm_1st-44rules.egg | 105.0–105.0 MiB | 105.7–105.7 MiB | 1.01–1.01x | higher RSS |
| ttm_2nd-44rules.egg | 535.1–535.3 MiB | 531.9–532.1 MiB | 0.994–0.994x | lower RSS |
