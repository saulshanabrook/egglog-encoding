# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage07 | b5a6dcde4721 | slotted-no-aliasing |
| Candidate | stage08 | bfa0d2f76d70 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage08 slotted-no-aliasing vs stage07 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.964–1.05x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_1st-44rules.egg | 0.943–1.01x | CI includes 1 |
| Wall time | Highest-ratio file | batax_2nd-44rules.egg | 0.946–1.17x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_2nd-44rules.egg | 0.971–0.983x | lower RSS |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.02–1.02x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 80.2–86.0 s | 79.5–83.3 s | 0.939–1.02x | CI includes 1 |
| batax_2nd-44rules.egg | 44.0–48.2 s | 44.0–53.2 s | 0.946–1.17x | CI includes 1 |
| mmm_1st-44rules.egg | 308–327 ms | 305–313 ms | 0.943–1.01x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.10–2.13 s | 2.12–2.18 s | 0.998–1.03x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 161–164 ms | 158–160 ms | 0.969–0.992x | faster |
| mmm_sum_2nd-44rules.egg | 555–564 ms | 554–563 ms | 0.987–1.01x | CI includes 1 |
| mttkrp_1st-44rules.egg | 568–576 ms | 574–603 ms | 1.00–1.05x | slower |
| mttkrp_2nd-44rules.egg | 9.91–10.2 s | 9.73–10.1 s | 0.964–1.01x | CI includes 1 |
| ttm_1st-44rules.egg | 406–413 ms | 407–418 ms | 0.992–1.02x | CI includes 1 |
| ttm_2nd-44rules.egg | 4.13–4.30 s | 4.14–4.38 s | 0.975–1.05x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 0.996–0.998x | lower RSS |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 1.00–1.00x | higher RSS |
| mmm_1st-44rules.egg | 102.7–102.7 MiB | 104.6–104.6 MiB | 1.02–1.02x | higher RSS |
| mmm_2nd-44rules.egg | 122.6–124.1 MiB | 120.4–120.6 MiB | 0.971–0.983x | lower RSS |
| mmm_sum_1st-44rules.egg | 102.7–102.7 MiB | 104.6–104.6 MiB | 1.02–1.02x | higher RSS |
| mmm_sum_2nd-44rules.egg | 102.7–102.7 MiB | 104.6–104.6 MiB | 1.02–1.02x | higher RSS |
| mttkrp_1st-44rules.egg | 102.7–102.7 MiB | 104.6–104.6 MiB | 1.02–1.02x | higher RSS |
| mttkrp_2nd-44rules.egg | 478.1–478.7 MiB | 478.8–479.4 MiB | 1.00–1.00x | higher RSS |
| ttm_1st-44rules.egg | 102.7–102.7 MiB | 104.6–104.6 MiB | 1.02–1.02x | higher RSS |
| ttm_2nd-44rules.egg | 212.1–212.5 MiB | 210.6–211.5 MiB | 0.992–0.997x | lower RSS |
