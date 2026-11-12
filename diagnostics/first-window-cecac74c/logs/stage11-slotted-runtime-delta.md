# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage10 | fb04877229a0 | slotted-no-aliasing |
| Candidate | stage11 | cecac74c2a2a | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage11 slotted-no-aliasing vs stage10 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.909–1.15x | CI includes 1 |
| Wall time | Lowest-ratio file | batax_2nd-44rules.egg | 0.869–1.09x | CI includes 1 |
| Wall time | Highest-ratio file | batax_1st-44rules.egg | 0.862–1.29x | CI includes 1 |
| Peak RSS | Lowest-ratio file | ttm_2nd-44rules.egg | 0.992–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.00–1.00x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 81.3–83.3 s | 71.0–106 s | 0.862–1.29x | CI includes 1 |
| batax_2nd-44rules.egg | 43.4–54.2 s | 46.7–47.6 s | 0.869–1.09x | CI includes 1 |
| mmm_1st-44rules.egg | 275–281 ms | 276–281 ms | 0.988–1.01x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.05–2.12 s | 2.06–2.13 s | 0.983–1.03x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 142–145 ms | 143–143 ms | 0.981–1.00x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 521–548 ms | 524–531 ms | 0.961–1.01x | CI includes 1 |
| mttkrp_1st-44rules.egg | 530–534 ms | 518–521 ms | 0.970–0.981x | faster |
| mttkrp_2nd-44rules.egg | 9.60–10.6 s | 10.1–10.4 s | 0.966–1.07x | CI includes 1 |
| ttm_1st-44rules.egg | 367–381 ms | 371–374 ms | 0.978–1.02x | CI includes 1 |
| ttm_2nd-44rules.egg | 4.16–4.34 s | 4.23–4.38 s | 0.986–1.04x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 0.999–1.00x | CI includes 1 |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 105.5–105.5 MiB | 105.6–105.6 MiB | 1.00–1.00x | higher RSS |
| mmm_2nd-44rules.egg | 119.9–122.3 MiB | 120.3–122.1 MiB | 0.988–1.01x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 105.5–105.5 MiB | 105.6–105.6 MiB | 1.00–1.00x | higher RSS |
| mmm_sum_2nd-44rules.egg | 105.5–105.5 MiB | 105.6–105.6 MiB | 1.00–1.00x | higher RSS |
| mttkrp_1st-44rules.egg | 105.5–105.5 MiB | 105.6–105.6 MiB | 1.00–1.00x | higher RSS |
| mttkrp_2nd-44rules.egg | 476.3–478.5 MiB | 477.5–477.9 MiB | 0.998–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 105.5–105.5 MiB | 105.6–105.6 MiB | 1.00–1.00x | higher RSS |
| ttm_2nd-44rules.egg | 211.1–213.6 MiB | 211.5–212.1 MiB | 0.992–1.00x | CI includes 1 |
