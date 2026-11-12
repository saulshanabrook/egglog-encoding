# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | main | 155b6812c334 | slotted-no-aliasing |
| Candidate | stage01 | acbe3a91b4d3 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage01 slotted-no-aliasing vs main slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.878–0.963x | faster |
| Wall time | Lowest-ratio file | batax_1st-44rules.egg | 0.780–0.888x | faster |
| Wall time | Highest-ratio file | mttkrp_2nd-44rules.egg | 0.721–1.43x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.885–0.885x | lower RSS |
| Peak RSS | Highest-ratio file | batax_1st-44rules.egg | 0.999–1.00x | CI includes 1 |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 111–115 s | 88.6–100 s | 0.780–0.888x | faster |
| batax_2nd-44rules.egg | 52.6–55.2 s | 54.1–57.4 s | 0.997–1.08x | CI includes 1 |
| mmm_1st-44rules.egg | 506–632 ms | 446–691 ms | 0.767–1.26x | CI includes 1 |
| mmm_2nd-44rules.egg | 3.02–3.30 s | 2.33–4.39 s | 0.737–1.40x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 227–249 ms | 169–323 ms | 0.707–1.36x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 0.914–1.06 s | 0.682–1.41 s | 0.687–1.44x | CI includes 1 |
| mttkrp_1st-44rules.egg | 0.800–1.03 s | 0.633–1.22 s | 0.680–1.37x | CI includes 1 |
| mttkrp_2nd-44rules.egg | 13.0–14.8 s | 10.1–19.7 s | 0.721–1.43x | CI includes 1 |
| ttm_1st-44rules.egg | 621–643 ms | 477–831 ms | 0.755–1.32x | CI includes 1 |
| ttm_2nd-44rules.egg | 5.83–6.29 s | 5.37–7.09 s | 0.881–1.18x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 0.999–1.00x | CI includes 1 |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 115.7–115.7 MiB | 102.4–102.4 MiB | 0.885–0.885x | lower RSS |
| mmm_2nd-44rules.egg | 129.7–132.1 MiB | 128.8–131.7 MiB | 0.980–1.01x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 115.7–115.7 MiB | 102.4–102.4 MiB | 0.885–0.885x | lower RSS |
| mmm_sum_2nd-44rules.egg | 115.7–115.7 MiB | 102.4–102.4 MiB | 0.885–0.885x | lower RSS |
| mttkrp_1st-44rules.egg | 115.7–115.7 MiB | 102.4–102.4 MiB | 0.885–0.885x | lower RSS |
| mttkrp_2nd-44rules.egg | 492.6–493.0 MiB | 492.1–493.4 MiB | 0.998–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 115.7–115.7 MiB | 102.4–102.4 MiB | 0.885–0.885x | lower RSS |
| ttm_2nd-44rules.egg | 220.4–222.7 MiB | 220.7–221.4 MiB | 0.992–1.00x | CI includes 1 |
