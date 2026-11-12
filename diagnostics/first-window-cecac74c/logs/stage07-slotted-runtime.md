# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | native | 155b6812c334 | slotted-ref-nested |
| Candidate | stage07 | b5a6dcde4721 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

*This comparison changes both target and treatment. Its ratios describe the joint endpoint change and do not isolate one cause.*

## Summary — stage07 slotted-no-aliasing vs native slotted-ref-nested

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.783–0.822x | faster |
| Wall time | Lowest-ratio file | mttkrp_2nd-44rules.egg | 0.348–0.360x | faster |
| Wall time | Highest-ratio file | mmm_sum_1st-44rules.egg | 15.3–15.6x | slower |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.890–0.890x | lower RSS |
| Peak RSS | Highest-ratio file | batax_2nd-44rules.egg | 6.69–6.75x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 54.8–55.2 s | 80.2–86.0 s | 1.46–1.56x | slower |
| batax_2nd-44rules.egg | 85.5–87.0 s | 44.0–48.2 s | 0.510–0.559x | faster |
| mmm_1st-44rules.egg | 75.6–77.5 ms | 308–327 ms | 4.01–4.27x | slower |
| mmm_2nd-44rules.egg | 3.22–3.26 s | 2.10–2.13 s | 0.647–0.659x | faster |
| mmm_sum_1st-44rules.egg | 10.5–10.5 ms | 161–164 ms | 15.3–15.6x | slower |
| mmm_sum_2nd-44rules.egg | 322–330 ms | 555–564 ms | 1.69–1.74x | slower |
| mttkrp_1st-44rules.egg | 279–281 ms | 568–576 ms | 2.03–2.06x | slower |
| mttkrp_2nd-44rules.egg | 28.1–28.6 s | 9.91–10.2 s | 0.348–0.360x | faster |
| ttm_1st-44rules.egg | 173–180 ms | 406–413 ms | 2.27–2.36x | slower |
| ttm_2nd-44rules.egg | 10.1–10.2 s | 4.13–4.30 s | 0.405–0.422x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 272.0–272.1 MiB | 1.4–1.4 GiB | 5.14–5.14x | higher RSS |
| batax_2nd-44rules.egg | 336.6–339.7 MiB | 2.2–2.2 GiB | 6.69–6.75x | higher RSS |
| mmm_1st-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| mmm_2nd-44rules.egg | 115.4–115.4 MiB | 122.6–124.1 MiB | 1.06–1.08x | higher RSS |
| mmm_sum_1st-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| mmm_sum_2nd-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| mttkrp_1st-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| mttkrp_2nd-44rules.egg | 115.4–115.4 MiB | 478.1–478.7 MiB | 4.14–4.15x | higher RSS |
| ttm_1st-44rules.egg | 115.4–115.4 MiB | 102.7–102.7 MiB | 0.890–0.890x | lower RSS |
| ttm_2nd-44rules.egg | 115.4–115.4 MiB | 212.1–212.5 MiB | 1.84–1.84x | higher RSS |
