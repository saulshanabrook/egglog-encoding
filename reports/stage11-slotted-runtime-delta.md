# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage10 | 33c4a35dfbe0 | slotted-no-aliasing |
| Candidate | stage11 | ff3ff0721ffb | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage11 slotted-no-aliasing vs stage10 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.961–1.07x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_sum_2nd-44rules.egg | 0.950–1.00x | CI includes 1 |
| Wall time | Highest-ratio file | batax_1st-44rules.egg | 0.949–1.12x | CI includes 1 |
| Peak RSS | Lowest-ratio file | ttm_2nd-44rules.egg | 0.991–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.01–1.01x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 81.7–87.4 s | 80.8–94.0 s | 0.949–1.12x | CI includes 1 |
| batax_2nd-44rules.egg | 49.3–50.5 s | 45.6–52.7 s | 0.914–1.06x | CI includes 1 |
| mmm_1st-44rules.egg | 275–296 ms | 281–293 ms | 0.963–1.05x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.11–2.19 s | 2.09–2.23 s | 0.966–1.04x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 146–151 ms | 144–146 ms | 0.957–0.999x | faster |
| mmm_sum_2nd-44rules.egg | 541–563 ms | 528–549 ms | 0.950–1.00x | CI includes 1 |
| mttkrp_1st-44rules.egg | 521–575 ms | 513–559 ms | 0.916–1.04x | CI includes 1 |
| mttkrp_2nd-44rules.egg | 10.2–10.5 s | 10.3–10.5 s | 0.985–1.02x | CI includes 1 |
| ttm_1st-44rules.egg | 374–389 ms | 380–387 ms | 0.983–1.03x | CI includes 1 |
| ttm_2nd-44rules.egg | 4.29–4.55 s | 4.35–4.45 s | 0.965–1.03x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 1.000–1.00x | CI includes 1 |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 105.7–105.7 MiB | 106.4–106.4 MiB | 1.01–1.01x | higher RSS |
| mmm_2nd-44rules.egg | 120.7–120.7 MiB | 120.8–121.6 MiB | 1.00–1.01x | higher RSS |
| mmm_sum_1st-44rules.egg | 105.7–105.7 MiB | 106.4–106.4 MiB | 1.01–1.01x | higher RSS |
| mmm_sum_2nd-44rules.egg | 105.7–105.7 MiB | 106.4–106.4 MiB | 1.01–1.01x | higher RSS |
| mttkrp_1st-44rules.egg | 105.7–105.7 MiB | 106.4–106.4 MiB | 1.01–1.01x | higher RSS |
| mttkrp_2nd-44rules.egg | 476.7–478.3 MiB | 476.3–478.0 MiB | 0.997–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 105.7–105.7 MiB | 106.4–106.4 MiB | 1.01–1.01x | higher RSS |
| ttm_2nd-44rules.egg | 211.1–213.8 MiB | 211.8–212.2 MiB | 0.991–1.00x | CI includes 1 |
