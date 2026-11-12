# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | native | 155b6812c334 | slotted-ref-nested |
| Candidate | stage08 | bfa0d2f76d70 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

*This comparison changes both target and treatment. Its ratios describe the joint endpoint change and do not isolate one cause.*

## Summary — stage08 slotted-no-aliasing vs native slotted-ref-nested

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.779–0.833x | faster |
| Wall time | Lowest-ratio file | mttkrp_2nd-44rules.egg | 0.342–0.356x | faster |
| Wall time | Highest-ratio file | mmm_sum_1st-44rules.egg | 15.1–15.3x | slower |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.906–0.906x | lower RSS |
| Peak RSS | Highest-ratio file | batax_2nd-44rules.egg | 6.71–6.78x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 54.8–55.2 s | 79.5–83.3 s | 1.44–1.51x | slower |
| batax_2nd-44rules.egg | 85.5–87.0 s | 44.0–53.2 s | 0.510–0.616x | faster |
| mmm_1st-44rules.egg | 75.6–77.5 ms | 305–313 ms | 3.96–4.10x | slower |
| mmm_2nd-44rules.egg | 3.22–3.26 s | 2.12–2.18 s | 0.652–0.672x | faster |
| mmm_sum_1st-44rules.egg | 10.5–10.5 ms | 158–160 ms | 15.1–15.3x | slower |
| mmm_sum_2nd-44rules.egg | 322–330 ms | 554–563 ms | 1.69–1.74x | slower |
| mttkrp_1st-44rules.egg | 279–281 ms | 574–603 ms | 2.05–2.16x | slower |
| mttkrp_2nd-44rules.egg | 28.1–28.6 s | 9.73–10.1 s | 0.342–0.356x | faster |
| ttm_1st-44rules.egg | 173–180 ms | 407–418 ms | 2.28–2.39x | slower |
| ttm_2nd-44rules.egg | 10.1–10.2 s | 4.14–4.38 s | 0.406–0.430x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 272.0–272.1 MiB | 1.4–1.4 GiB | 5.12–5.13x | higher RSS |
| batax_2nd-44rules.egg | 336.6–339.7 MiB | 2.2–2.2 GiB | 6.71–6.78x | higher RSS |
| mmm_1st-44rules.egg | 115.4–115.4 MiB | 104.6–104.6 MiB | 0.906–0.906x | lower RSS |
| mmm_2nd-44rules.egg | 115.4–115.4 MiB | 120.4–120.6 MiB | 1.04–1.04x | higher RSS |
| mmm_sum_1st-44rules.egg | 115.4–115.4 MiB | 104.6–104.6 MiB | 0.906–0.906x | lower RSS |
| mmm_sum_2nd-44rules.egg | 115.4–115.4 MiB | 104.6–104.6 MiB | 0.906–0.906x | lower RSS |
| mttkrp_1st-44rules.egg | 115.4–115.4 MiB | 104.6–104.6 MiB | 0.906–0.906x | lower RSS |
| mttkrp_2nd-44rules.egg | 115.4–115.4 MiB | 478.8–479.4 MiB | 4.15–4.15x | higher RSS |
| ttm_1st-44rules.egg | 115.4–115.4 MiB | 104.6–104.6 MiB | 0.906–0.906x | lower RSS |
| ttm_2nd-44rules.egg | 115.4–115.4 MiB | 210.6–211.5 MiB | 1.83–1.83x | higher RSS |
