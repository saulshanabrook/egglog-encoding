# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | native | 155b6812c334 | slotted-ref-nested |
| Candidate | stage09 | bf13e3ac9d6c | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

*This comparison changes both target and treatment. Its ratios describe the joint endpoint change and do not isolate one cause.*

## Summary — stage09 slotted-no-aliasing vs native slotted-ref-nested

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.783–0.850x | faster |
| Wall time | Lowest-ratio file | mttkrp_2nd-44rules.egg | 0.346–0.363x | faster |
| Wall time | Highest-ratio file | mmm_sum_1st-44rules.egg | 14.1–14.9x | slower |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.898–0.898x | lower RSS |
| Peak RSS | Highest-ratio file | batax_2nd-44rules.egg | 6.71–6.77x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 54.8–55.2 s | 79.1–85.6 s | 1.44–1.56x | slower |
| batax_2nd-44rules.egg | 85.5–87.0 s | 44.2–54.5 s | 0.512–0.632x | faster |
| mmm_1st-44rules.egg | 75.6–77.5 ms | 298–310 ms | 3.88–4.07x | slower |
| mmm_2nd-44rules.egg | 3.22–3.26 s | 2.13–2.20 s | 0.656–0.678x | faster |
| mmm_sum_1st-44rules.egg | 10.5–10.5 ms | 148–156 ms | 14.1–14.9x | slower |
| mmm_sum_2nd-44rules.egg | 322–330 ms | 548–574 ms | 1.68–1.77x | slower |
| mttkrp_1st-44rules.egg | 279–281 ms | 566–600 ms | 2.02–2.15x | slower |
| mttkrp_2nd-44rules.egg | 28.1–28.6 s | 9.83–10.3 s | 0.346–0.363x | faster |
| ttm_1st-44rules.egg | 173–180 ms | 394–417 ms | 2.22–2.37x | slower |
| ttm_2nd-44rules.egg | 10.1–10.2 s | 4.13–4.50 s | 0.405–0.442x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 272.0–272.1 MiB | 1.4–1.4 GiB | 5.12–5.13x | higher RSS |
| batax_2nd-44rules.egg | 336.6–339.7 MiB | 2.2–2.2 GiB | 6.71–6.77x | higher RSS |
| mmm_1st-44rules.egg | 115.4–115.4 MiB | 103.6–103.6 MiB | 0.898–0.898x | lower RSS |
| mmm_2nd-44rules.egg | 115.4–115.4 MiB | 120.1–120.8 MiB | 1.04–1.05x | higher RSS |
| mmm_sum_1st-44rules.egg | 115.4–115.4 MiB | 103.6–103.6 MiB | 0.898–0.898x | lower RSS |
| mmm_sum_2nd-44rules.egg | 115.4–115.4 MiB | 103.6–103.6 MiB | 0.898–0.898x | lower RSS |
| mttkrp_1st-44rules.egg | 115.4–115.4 MiB | 103.6–103.6 MiB | 0.898–0.898x | lower RSS |
| mttkrp_2nd-44rules.egg | 115.4–115.4 MiB | 477.7–480.1 MiB | 4.14–4.16x | higher RSS |
| ttm_1st-44rules.egg | 115.4–115.4 MiB | 103.6–103.6 MiB | 0.898–0.898x | lower RSS |
| ttm_2nd-44rules.egg | 115.4–115.4 MiB | 210.1–213.1 MiB | 1.82–1.85x | higher RSS |
