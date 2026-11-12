# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | main | 37b148e74175 | slotted-no-aliasing |
| Candidate | stage07 | b5a6dcde4721 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage07 slotted-no-aliasing vs main slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.980–1.06x | CI includes 1 |
| Wall time | Lowest-ratio file | mttkrp_1st-44rules.egg | 0.867–0.917x | faster |
| Wall time | Highest-ratio file | batax_1st-44rules.egg | 0.961–1.09x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.890–0.890x | lower RSS |
| Peak RSS | Highest-ratio file | mmm_2nd-44rules.egg | 0.995–1.01x | CI includes 1 |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 76.8–85.5 s | 80.2–86.0 s | 0.961–1.09x | CI includes 1 |
| batax_2nd-44rules.egg | 44.6–45.8 s | 44.0–48.2 s | 0.971–1.07x | CI includes 1 |
| mmm_1st-44rules.egg | 321–329 ms | 308–327 ms | 0.944–1.01x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.08–2.16 s | 2.10–2.13 s | 0.980–1.02x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 167–168 ms | 161–164 ms | 0.960–0.981x | faster |
| mmm_sum_2nd-44rules.egg | 555–570 ms | 555–564 ms | 0.979–1.01x | CI includes 1 |
| mttkrp_1st-44rules.egg | 624–659 ms | 568–576 ms | 0.867–0.917x | faster |
| mttkrp_2nd-44rules.egg | 9.98–10.1 s | 9.91–10.2 s | 0.985–1.02x | CI includes 1 |
| ttm_1st-44rules.egg | 427–446 ms | 406–413 ms | 0.916–0.961x | faster |
| ttm_2nd-44rules.egg | 4.18–4.30 s | 4.13–4.30 s | 0.970–1.02x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 1.00–1.00x | higher RSS |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 0.998–1.000x | lower RSS |
| mmm_1st-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| mmm_2nd-44rules.egg | 123.2–123.3 MiB | 122.6–124.1 MiB | 0.995–1.01x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| mmm_sum_2nd-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| mttkrp_1st-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| mttkrp_2nd-44rules.egg | 476.7–479.8 MiB | 478.1–478.7 MiB | 0.997–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| ttm_2nd-44rules.egg | 210.9–214.3 MiB | 212.1–212.5 MiB | 0.991–1.01x | CI includes 1 |
