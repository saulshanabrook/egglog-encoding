# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage07 | b5a6dcde4721 | slotted |
| Candidate | stage08 | bfa0d2f76d70 | slotted |

*8 file(s): batax_1st-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage08 slotted vs stage07 slotted

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 8 files | 0.932–1.03x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_1st-44rules.egg | 0.940–0.992x | faster |
| Wall time | Highest-ratio file | ttm_1st-44rules.egg | 1.00–1.02x | slower |
| Peak RSS | Lowest-ratio file | ttm_2nd-44rules.egg | 0.994–0.999x | lower RSS |
| Peak RSS | Highest-ratio file | mmm_2nd-44rules.egg | 1.00–1.00x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 74.3–83.6 s | 76.3–77.4 s | 0.919–1.03x | CI includes 1 |
| mmm_1st-44rules.egg | 399–407 ms | 380–399 ms | 0.940–0.992x | faster |
| mmm_2nd-44rules.egg | 5.26–5.58 s | 5.29–5.67 s | 0.966–1.06x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 170–174 ms | 170–173 ms | 0.983–1.01x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 806–828 ms | 802–830 ms | 0.977–1.02x | CI includes 1 |
| mttkrp_1st-44rules.egg | 0.994–1.01 s | 0.979–1.04 s | 0.976–1.04x | CI includes 1 |
| ttm_1st-44rules.egg | 521–529 ms | 528–534 ms | 1.00–1.02x | slower |
| ttm_2nd-44rules.egg | 10.1–10.3 s | 9.63–10.3 s | 0.945–1.02x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.7–1.7 GiB | 1.7–1.7 GiB | 0.998–0.998x | lower RSS |
| mmm_1st-44rules.egg | 103.7–103.7 MiB | 103.9–103.9 MiB | 1.00–1.00x | higher RSS |
| mmm_2nd-44rules.egg | 310.3–310.8 MiB | 310.9–311.6 MiB | 1.00–1.00x | higher RSS |
| mmm_sum_1st-44rules.egg | 103.7–103.7 MiB | 103.9–103.9 MiB | 1.00–1.00x | higher RSS |
| mmm_sum_2nd-44rules.egg | 103.7–103.7 MiB | 103.9–103.9 MiB | 1.00–1.00x | higher RSS |
| mttkrp_1st-44rules.egg | 103.7–103.7 MiB | 103.9–103.9 MiB | 1.00–1.00x | higher RSS |
| ttm_1st-44rules.egg | 103.7–103.7 MiB | 103.9–103.9 MiB | 1.00–1.00x | higher RSS |
| ttm_2nd-44rules.egg | 530.9–531.7 MiB | 528.4–530.8 MiB | 0.994–0.999x | lower RSS |
