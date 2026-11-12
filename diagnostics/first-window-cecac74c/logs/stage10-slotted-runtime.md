# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | native | 155b6812c334 | slotted-ref-nested |
| Candidate | stage10 | fb04877229a0 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

*This comparison changes both target and treatment. Its ratios describe the joint endpoint change and do not isolate one cause.*

## Summary — stage10 slotted-no-aliasing vs native slotted-ref-nested

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.782–0.843x | faster |
| Wall time | Lowest-ratio file | mttkrp_2nd-44rules.egg | 0.338–0.375x | faster |
| Wall time | Highest-ratio file | mmm_sum_1st-44rules.egg | 13.6–13.9x | slower |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.914–0.914x | lower RSS |
| Peak RSS | Highest-ratio file | batax_2nd-44rules.egg | 6.72–6.78x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 54.8–55.2 s | 81.3–83.3 s | 1.48–1.52x | slower |
| batax_2nd-44rules.egg | 85.5–87.0 s | 43.4–54.2 s | 0.503–0.629x | faster |
| mmm_1st-44rules.egg | 75.6–77.5 ms | 275–281 ms | 3.58–3.69x | slower |
| mmm_2nd-44rules.egg | 3.22–3.26 s | 2.05–2.12 s | 0.630–0.653x | faster |
| mmm_sum_1st-44rules.egg | 10.5–10.5 ms | 142–145 ms | 13.6–13.9x | slower |
| mmm_sum_2nd-44rules.egg | 322–330 ms | 521–548 ms | 1.60–1.69x | slower |
| mttkrp_1st-44rules.egg | 279–281 ms | 530–534 ms | 1.89–1.91x | slower |
| mttkrp_2nd-44rules.egg | 28.1–28.6 s | 9.60–10.6 s | 0.338–0.375x | faster |
| ttm_1st-44rules.egg | 173–180 ms | 367–381 ms | 2.07–2.18x | slower |
| ttm_2nd-44rules.egg | 10.1–10.2 s | 4.16–4.34 s | 0.409–0.426x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 272.0–272.1 MiB | 1.4–1.4 GiB | 5.12–5.13x | higher RSS |
| batax_2nd-44rules.egg | 336.6–339.7 MiB | 2.2–2.2 GiB | 6.72–6.78x | higher RSS |
| mmm_1st-44rules.egg | 115.4–115.4 MiB | 105.5–105.5 MiB | 0.914–0.914x | lower RSS |
| mmm_2nd-44rules.egg | 115.4–115.4 MiB | 119.9–122.3 MiB | 1.04–1.06x | higher RSS |
| mmm_sum_1st-44rules.egg | 115.4–115.4 MiB | 105.5–105.5 MiB | 0.914–0.914x | lower RSS |
| mmm_sum_2nd-44rules.egg | 115.4–115.4 MiB | 105.5–105.5 MiB | 0.914–0.914x | lower RSS |
| mttkrp_1st-44rules.egg | 115.4–115.4 MiB | 105.5–105.5 MiB | 0.914–0.914x | lower RSS |
| mttkrp_2nd-44rules.egg | 115.4–115.4 MiB | 476.3–478.5 MiB | 4.13–4.15x | higher RSS |
| ttm_1st-44rules.egg | 115.4–115.4 MiB | 105.5–105.5 MiB | 0.914–0.914x | lower RSS |
| ttm_2nd-44rules.egg | 115.4–115.4 MiB | 211.1–213.6 MiB | 1.83–1.85x | higher RSS |
