# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | native | 155b6812c334 | slotted-ref-nested |
| Candidate | main | 37b148e74175 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

*This comparison changes both target and treatment. Its ratios describe the joint endpoint change and do not isolate one cause.*

## Summary — main slotted-no-aliasing vs native slotted-ref-nested

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.763–0.812x | faster |
| Wall time | Lowest-ratio file | mttkrp_2nd-44rules.egg | 0.350–0.358x | faster |
| Wall time | Highest-ratio file | mmm_sum_1st-44rules.egg | 15.9–16.0x | slower |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 1.00–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | batax_2nd-44rules.egg | 6.69–6.75x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 54.8–55.2 s | 76.8–85.5 s | 1.40–1.55x | slower |
| batax_2nd-44rules.egg | 85.5–87.0 s | 44.6–45.8 s | 0.515–0.533x | faster |
| mmm_1st-44rules.egg | 75.6–77.5 ms | 321–329 ms | 4.18–4.32x | slower |
| mmm_2nd-44rules.egg | 3.22–3.26 s | 2.08–2.16 s | 0.641–0.667x | faster |
| mmm_sum_1st-44rules.egg | 10.5–10.5 ms | 167–168 ms | 15.9–16.0x | slower |
| mmm_sum_2nd-44rules.egg | 322–330 ms | 555–570 ms | 1.70–1.76x | slower |
| mttkrp_1st-44rules.egg | 279–281 ms | 624–659 ms | 2.23–2.36x | slower |
| mttkrp_2nd-44rules.egg | 28.1–28.6 s | 9.98–10.1 s | 0.350–0.358x | faster |
| ttm_1st-44rules.egg | 173–180 ms | 427–446 ms | 2.40–2.54x | slower |
| ttm_2nd-44rules.egg | 10.1–10.2 s | 4.18–4.30 s | 0.410–0.422x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 272.0–272.1 MiB | 1.4–1.4 GiB | 5.13–5.13x | higher RSS |
| batax_2nd-44rules.egg | 336.6–339.7 MiB | 2.2–2.2 GiB | 6.69–6.75x | higher RSS |
| mmm_1st-44rules.egg | 115.4–115.4 MiB | 115.4–115.4 MiB | 1.00–1.00x | CI includes 1 |
| mmm_2nd-44rules.egg | 115.4–115.4 MiB | 123.2–123.3 MiB | 1.07–1.07x | higher RSS |
| mmm_sum_1st-44rules.egg | 115.4–115.4 MiB | 115.4–115.4 MiB | 1.00–1.00x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 115.4–115.4 MiB | 115.4–115.4 MiB | 1.00–1.00x | CI includes 1 |
| mttkrp_1st-44rules.egg | 115.4–115.4 MiB | 115.4–115.4 MiB | 1.00–1.00x | CI includes 1 |
| mttkrp_2nd-44rules.egg | 115.4–115.4 MiB | 476.7–479.8 MiB | 4.13–4.16x | higher RSS |
| ttm_1st-44rules.egg | 115.4–115.4 MiB | 115.4–115.4 MiB | 1.00–1.00x | CI includes 1 |
| ttm_2nd-44rules.egg | 115.4–115.4 MiB | 210.9–214.3 MiB | 1.83–1.86x | higher RSS |
