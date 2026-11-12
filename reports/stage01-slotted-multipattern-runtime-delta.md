# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | main | 155b6812c334 | slotted |
| Candidate | stage01 | acbe3a91b4d3 | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage01 slotted vs main slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.690–0.971x | faster |
| Wall time | Lowest-ratio file | batax_1st-44rules.egg | 0.628–0.966x | faster |
| Wall time | Highest-ratio file | mmm_2nd-44rules.egg | 0.984–1.02x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_1st-44rules.egg | 0.991–0.991x | lower RSS |
| Peak RSS | Highest-ratio file | ttm_2nd-44rules.egg | 0.999–1.00x | CI includes 1 |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 93.8–142 s | 85.1–95.1 s | 0.628–0.966x | faster |
| mmm_1st-44rules.egg | 629–646 ms | 631–645 ms | 0.984–1.02x | CI includes 1 |
| mmm_2nd-44rules.egg | 7.79–7.94 s | 7.76–8.00 s | 0.984–1.02x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 234–254 ms | 230–255 ms | 0.929–1.06x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 1.35–1.51 s | 1.37–1.50 s | 0.930–1.08x | CI includes 1 |
| mttkrp_1st-44rules.egg | 1.55–1.72 s | 1.60–1.66 s | 0.947–1.05x | CI includes 1 |
| ttm_1st-44rules.egg | 882–937 ms | 878–913 ms | 0.950–1.02x | CI includes 1 |
| ttm_2nd-44rules.egg | 16.8–17.2 s | 16.4–16.8 s | 0.964–0.996x | faster |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.8–1.8 GiB | 1.8–1.8 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 103.3–103.3 MiB | 102.4–102.4 MiB | 0.991–0.991x | lower RSS |
| mmm_2nd-44rules.egg | 325.0–326.9 MiB | 325.0–326.8 MiB | 0.996–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 103.3–103.3 MiB | 102.4–102.4 MiB | 0.991–0.991x | lower RSS |
| mmm_sum_2nd-44rules.egg | 103.3–103.3 MiB | 102.4–102.4 MiB | 0.991–0.991x | lower RSS |
| mttkrp_1st-44rules.egg | 103.3–103.3 MiB | 102.4–102.4 MiB | 0.991–0.991x | lower RSS |
| ttm_1st-44rules.egg | 103.3–103.3 MiB | 102.4–102.4 MiB | 0.991–0.991x | lower RSS |
| ttm_2nd-44rules.egg | 555.9–556.9 MiB | 556.0–556.4 MiB | 0.999–1.00x | CI includes 1 |
