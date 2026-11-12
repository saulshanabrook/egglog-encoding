# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | native | 155b6812c334 | slotted-ref-nested |
| Candidate | stage11 | cecac74c2a2a | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

*This comparison changes both target and treatment. Its ratios describe the joint endpoint change and do not isolate one cause.*

## Summary — stage11 slotted-no-aliasing vs native slotted-ref-nested

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.743–0.932x | faster |
| Wall time | Lowest-ratio file | mttkrp_2nd-44rules.egg | 0.356–0.368x | faster |
| Wall time | Highest-ratio file | mmm_sum_1st-44rules.egg | 13.6–13.6x | slower |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.916–0.916x | lower RSS |
| Peak RSS | Highest-ratio file | batax_2nd-44rules.egg | 6.72–6.78x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 54.8–55.2 s | 71.0–106 s | 1.29–1.92x | slower |
| batax_2nd-44rules.egg | 85.5–87.0 s | 46.7–47.6 s | 0.540–0.553x | faster |
| mmm_1st-44rules.egg | 75.6–77.5 ms | 276–281 ms | 3.58–3.69x | slower |
| mmm_2nd-44rules.egg | 3.22–3.26 s | 2.06–2.13 s | 0.635–0.657x | faster |
| mmm_sum_1st-44rules.egg | 10.5–10.5 ms | 143–143 ms | 13.6–13.6x | slower |
| mmm_sum_2nd-44rules.egg | 322–330 ms | 524–531 ms | 1.60–1.64x | slower |
| mttkrp_1st-44rules.egg | 279–281 ms | 518–521 ms | 1.85–1.87x | slower |
| mttkrp_2nd-44rules.egg | 28.1–28.6 s | 10.1–10.4 s | 0.356–0.368x | faster |
| ttm_1st-44rules.egg | 173–180 ms | 371–374 ms | 2.07–2.15x | slower |
| ttm_2nd-44rules.egg | 10.1–10.2 s | 4.23–4.38 s | 0.415–0.430x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 272.0–272.1 MiB | 1.4–1.4 GiB | 5.12–5.13x | higher RSS |
| batax_2nd-44rules.egg | 336.6–339.7 MiB | 2.2–2.2 GiB | 6.72–6.78x | higher RSS |
| mmm_1st-44rules.egg | 115.4–115.4 MiB | 105.6–105.6 MiB | 0.916–0.916x | lower RSS |
| mmm_2nd-44rules.egg | 115.4–115.4 MiB | 120.3–122.1 MiB | 1.04–1.06x | higher RSS |
| mmm_sum_1st-44rules.egg | 115.4–115.4 MiB | 105.6–105.6 MiB | 0.916–0.916x | lower RSS |
| mmm_sum_2nd-44rules.egg | 115.4–115.4 MiB | 105.6–105.6 MiB | 0.916–0.916x | lower RSS |
| mttkrp_1st-44rules.egg | 115.4–115.4 MiB | 105.6–105.6 MiB | 0.916–0.916x | lower RSS |
| mttkrp_2nd-44rules.egg | 115.4–115.4 MiB | 477.5–477.9 MiB | 4.14–4.14x | higher RSS |
| ttm_1st-44rules.egg | 115.4–115.4 MiB | 105.6–105.6 MiB | 0.916–0.916x | lower RSS |
| ttm_2nd-44rules.egg | 115.4–115.4 MiB | 211.5–212.1 MiB | 1.83–1.84x | higher RSS |
