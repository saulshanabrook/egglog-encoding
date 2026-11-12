# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage08 | bfa0d2f76d70 | slotted-no-aliasing |
| Candidate | stage09 | bf13e3ac9d6c | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage09 slotted-no-aliasing vs stage08 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.961–1.07x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_sum_1st-44rules.egg | 0.932–0.982x | faster |
| Wall time | Highest-ratio file | batax_2nd-44rules.egg | 0.881–1.17x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.991–0.991x | lower RSS |
| Peak RSS | Highest-ratio file | ttm_2nd-44rules.egg | 0.995–1.01x | CI includes 1 |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 79.5–83.3 s | 79.1–85.6 s | 0.967–1.06x | CI includes 1 |
| batax_2nd-44rules.egg | 44.0–53.2 s | 44.2–54.5 s | 0.881–1.17x | CI includes 1 |
| mmm_1st-44rules.egg | 305–313 ms | 298–310 ms | 0.963–1.01x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.12–2.18 s | 2.13–2.20 s | 0.987–1.03x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 158–160 ms | 148–156 ms | 0.932–0.982x | faster |
| mmm_sum_2nd-44rules.egg | 554–563 ms | 548–574 ms | 0.980–1.03x | CI includes 1 |
| mttkrp_1st-44rules.egg | 574–603 ms | 566–600 ms | 0.954–1.03x | CI includes 1 |
| mttkrp_2nd-44rules.egg | 9.73–10.1 s | 9.83–10.3 s | 0.986–1.04x | CI includes 1 |
| ttm_1st-44rules.egg | 407–418 ms | 394–417 ms | 0.953–1.01x | CI includes 1 |
| ttm_2nd-44rules.egg | 4.14–4.38 s | 4.13–4.50 s | 0.963–1.07x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 0.999–1.00x | CI includes 1 |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 104.6–104.6 MiB | 103.6–103.6 MiB | 0.991–0.991x | lower RSS |
| mmm_2nd-44rules.egg | 120.4–120.6 MiB | 120.1–120.8 MiB | 0.997–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 104.6–104.6 MiB | 103.6–103.6 MiB | 0.991–0.991x | lower RSS |
| mmm_sum_2nd-44rules.egg | 104.6–104.6 MiB | 103.6–103.6 MiB | 0.991–0.991x | lower RSS |
| mttkrp_1st-44rules.egg | 104.6–104.6 MiB | 103.6–103.6 MiB | 0.991–0.991x | lower RSS |
| mttkrp_2nd-44rules.egg | 478.8–479.4 MiB | 477.7–480.1 MiB | 0.997–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 104.6–104.6 MiB | 103.6–103.6 MiB | 0.991–0.991x | lower RSS |
| ttm_2nd-44rules.egg | 210.6–211.5 MiB | 210.1–213.1 MiB | 0.995–1.01x | CI includes 1 |
