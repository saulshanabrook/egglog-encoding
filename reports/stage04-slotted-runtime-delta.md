# Benchmark Report

## Comparison

| Role | Target | Git | Treatment |
| --- | --- | --- | --- |
| Baseline | stage03 | cfc7c8a0982b | slotted-no-aliasing |
| Candidate | stage04 | 83dac3f0a4ac | slotted-no-aliasing |

*10 file(s): batax_1st-44rules.egg, batax_2nd-44rules.egg, mmm_1st-44rules.egg, mmm_2nd-44rules.egg, mmm_sum_1st-44rules.egg, mmm_sum_2nd-44rules.egg, mttkrp_1st-44rules.egg, mttkrp_2nd-44rules.egg, ttm_1st-44rules.egg, ttm_2nd-44rules.egg · 3 round(s) per endpoint/file · 500 s timeout per run · Allocator: 16 GiB cap · Report: /tmp/slotted-perf-pr203/pr-stack/report.jsonl*

## Summary — stage04 slotted-no-aliasing vs stage03 slotted-no-aliasing

| Metric | Scope | File(s) | Ratio (95% CI) | Result |
| --- | --- | --- | ---: | --- |
| Wall time | Suite total | 10 files | 0.865–1.08x | CI includes 1 |
| Wall time | Lowest-ratio file | mmm_1st-44rules.egg | 0.778–1.06x | CI includes 1 |
| Wall time | Highest-ratio file | ttm_1st-44rules.egg | 0.904–1.19x | CI includes 1 |
| Peak RSS | Lowest-ratio file | mmm_2nd-44rules.egg | 0.990–1.00x | CI includes 1 |
| Peak RSS | Highest-ratio file | ttm_1st-44rules.egg | 1.00–1.00x | higher RSS |

*Ratios are candidate / baseline; below 1 is lower and above 1 is higher.*

## Per-file results

### Wall time

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 89.1–103 s | 79.3–113 s | 0.818–1.20x | CI includes 1 |
| batax_2nd-44rules.egg | 54.1–63.1 s | 52.9–54.0 s | 0.846–0.988x | faster |
| mmm_1st-44rules.egg | 342–444 ms | 325–387 ms | 0.778–1.06x | CI includes 1 |
| mmm_2nd-44rules.egg | 2.21–2.65 s | 2.14–2.54 s | 0.850–1.09x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 161–198 ms | 165–195 ms | 0.878–1.15x | CI includes 1 |
| mmm_sum_2nd-44rules.egg | 567–720 ms | 551–664 ms | 0.813–1.10x | CI includes 1 |
| mttkrp_1st-44rules.egg | 667–794 ms | 648–751 ms | 0.855–1.08x | CI includes 1 |
| mttkrp_2nd-44rules.egg | 10.5–12.2 s | 9.68–12.6 s | 0.840–1.14x | CI includes 1 |
| ttm_1st-44rules.egg | 417–496 ms | 424–525 ms | 0.904–1.19x | CI includes 1 |
| ttm_2nd-44rules.egg | 4.19–5.48 s | 4.18–5.18 s | 0.818–1.15x | CI includes 1 |

### Peak RSS

| File | Baseline (95% CI) | Candidate (95% CI) | Ratio (95% CI) | Result |
| --- | ---: | ---: | ---: | --- |
| batax_1st-44rules.egg | 1.4–1.4 GiB | 1.4–1.4 GiB | 0.997–0.998x | lower RSS |
| batax_2nd-44rules.egg | 2.2–2.2 GiB | 2.2–2.2 GiB | 0.999–1.00x | CI includes 1 |
| mmm_1st-44rules.egg | 104.7–104.7 MiB | 104.9–104.9 MiB | 1.00–1.00x | higher RSS |
| mmm_2nd-44rules.egg | 123.4–123.9 MiB | 122.5–124.0 MiB | 0.990–1.00x | CI includes 1 |
| mmm_sum_1st-44rules.egg | 104.7–104.7 MiB | 104.9–104.9 MiB | 1.00–1.00x | higher RSS |
| mmm_sum_2nd-44rules.egg | 104.7–104.7 MiB | 104.9–104.9 MiB | 1.00–1.00x | higher RSS |
| mttkrp_1st-44rules.egg | 104.7–104.7 MiB | 104.9–104.9 MiB | 1.00–1.00x | higher RSS |
| mttkrp_2nd-44rules.egg | 477.9–479.2 MiB | 477.3–478.2 MiB | 0.997–1.000x | lower RSS |
| ttm_1st-44rules.egg | 104.7–104.7 MiB | 104.9–104.9 MiB | 1.00–1.00x | higher RSS |
| ttm_2nd-44rules.egg | 212.3–212.7 MiB | 211.8–213.3 MiB | 0.996–1.00x | CI includes 1 |
