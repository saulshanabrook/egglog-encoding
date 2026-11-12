# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage09 | bf13e3ac9d6c | slotted-no-aliasing |
| Candidate | stage10 | fb04877229a0 | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-mmm-implementation/pr-stack/report.jsonl*

## Summary — stage10 slotted-no-aliasing vs stage09 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.942–1.05x | CI includes 1 |
| Wall time | Lowest-ratio file | mttkrp_1st-44rules.egg | 0.886–0.941x | faster |
| Wall time | Highest-ratio file | mttkrp_2nd-44rules.egg | 0.951–1.06x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mttkrp_2nd-44rules.egg | 0.993–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.02–1.02x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 79.1–85.6 s | 81.3–83.3 s | 0.960–1.04x | CI includes 1 |
| batax_2nd-44rules.egg | 44.2–54.5 s | 43.4–54.2 s | 0.848–1.15x | CI includes 1 |
| mmm_1st-44rules.egg | 298–310 ms | 275–281 ms | 0.894–0.935x | faster |
| mmm_2nd-44rules.egg | 2.13–2.20 s | 2.05–2.12 s | 0.940–0.984x | faster |
| mmm_sum_1st-44rules.egg | 148–156 ms | 142–145 ms | 0.920–0.972x | faster |
| mmm_sum_2nd-44rules.egg | 548–574 ms | 521–548 ms | 0.921–0.986x | faster |
| mttkrp_1st-44rules.egg | 566–600 ms | 530–534 ms | 0.886–0.941x | faster |
| mttkrp_2nd-44rules.egg | 9.83–10.3 s | 9.60–10.6 s | 0.951–1.06x | CI includes 1 |
| ttm_1st-44rules.egg | 394–417 ms | 367–381 ms | 0.894–0.955x | faster |
| ttm_2nd-44rules.egg | 4.13–4.50 s | 4.16–4.34 s | 0.940–1.03x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 1.000–1.00x | CI includes 1 |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 1.000–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 103.6–103.6 MiB | 105.5–105.5 MiB | 1.02–1.02x | higher RSS |
| mmm_2nd-44rules.egg | 120.1–120.8 MiB | 119.9–122.3 MiB | 0.995–1.02x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 103.6–103.6 MiB | 105.5–105.5 MiB | 1.02–1.02x | higher RSS |
| mmm_sum_2nd-44rules.egg | 103.6–103.6 MiB | 105.5–105.5 MiB | 1.02–1.02x | higher RSS |
| mttkrp_1st-44rules.egg | 103.6–103.6 MiB | 105.5–105.5 MiB | 1.02–1.02x | higher RSS |
| mttkrp_2nd-44rules.egg | 477.7–480.1 MiB | 476.3–478.5 MiB | 0.993–1.00x | CI includes 1 |
| ttm_1st-44rules.egg | 103.6–103.6 MiB | 105.5–105.5 MiB | 1.02–1.02x | higher RSS |
| ttm_2nd-44rules.egg | 210.1–213.1 MiB | 211.1–213.6 MiB | 0.994–1.01x | CI includes 1 |
