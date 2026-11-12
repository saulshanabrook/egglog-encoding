# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | main | 37b148e74175 | slotted-no-aliasing |
| Candidate | main | 37b148e74175 | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — main slotted vs main slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 1.04–1.16x | slower |
| Wall time | Lowest-ratio file | batax_1st-44rules.egg | 0.922–1.04x | CI includes 1 |
| Wall time | Highest-ratio file | mmm_2nd-44rules.egg | 2.53–2.64x | slower |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.896–0.896x | lower RSS |
| Peak RSS | Highest-ratio file | mmm_2nd-44rules.egg | 2.51–2.52x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 76.8–85.5 s | 77.4–80.9 s | 0.922–1.04x | CI includes 1 |
| mmm_1st-44rules.egg | 321–329 ms | 405–419 ms | 1.24–1.29x | slower |
| mmm_2nd-44rules.egg | 2.08–2.16 s | 5.42–5.54 s | 2.53–2.64x | slower |
| mmm_sum_1st-44rules.egg | 167–168 ms | 173–184 ms | 1.04–1.10x | slower |
| mmm_sum_2nd-44rules.egg | 555–570 ms | 809–827 ms | 1.43–1.48x | slower |
| mttkrp_1st-44rules.egg | 624–659 ms | 0.996–1.04 s | 1.53–1.65x | slower |
| ttm_1st-44rules.egg | 427–446 ms | 527–543 ms | 1.19–1.26x | slower |
| ttm_2nd-44rules.egg | 4.18–4.30 s | 8.80–12.4 s | 2.08–2.92x | slower |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.7–1.8 GiB | 1.28–1.28x | higher RSS |
| mmm_1st-44rules.egg | 115.4–115.4 MiB | 103.4–103.4 MiB | 0.896–0.896x | lower RSS |
| mmm_2nd-44rules.egg | 123.2–123.3 MiB | 309.8–310.8 MiB | 2.51–2.52x | higher RSS |
| mmm_sum_1st-44rules.egg | 115.4–115.4 MiB | 103.4–103.4 MiB | 0.896–0.896x | lower RSS |
| mmm_sum_2nd-44rules.egg | 115.4–115.4 MiB | 103.4–103.4 MiB | 0.896–0.896x | lower RSS |
| mttkrp_1st-44rules.egg | 115.4–115.4 MiB | 103.4–103.4 MiB | 0.896–0.896x | lower RSS |
| ttm_1st-44rules.egg | 115.4–115.4 MiB | 103.4–103.4 MiB | 0.896–0.896x | lower RSS |
| ttm_2nd-44rules.egg | 210.9–214.3 MiB | 531.6–532.0 MiB | 2.48–2.52x | higher RSS |
