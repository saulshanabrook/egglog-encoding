"""Descriptive numbers from two excluded cohorts; no workloads or performance admission."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import statistics


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
if args.output.exists():
    raise ValueError('choose a new derived-output file; preserve earlier evidence')
base = Path(__file__).resolve().parents[1]
invalid_path = base / 'invalid-retry-cohorts.json'
invalid_bytes = invalid_path.read_bytes()
invalid_sha = hashlib.sha256(invalid_bytes).hexdigest()
if invalid_sha != '540e1bae5834db20dd09c1053c1264443bc6243bb83844294caf1d5b50e81c21':
    raise ValueError('invalidation authority changed')
invalid = json.loads(invalid_bytes)
if invalid['distribution_inspected_before_decision'] is not False:
    raise ValueError('required pre-inspection exclusion not established')
inputs = {str(invalid_path): invalid_sha}
cases = []
for name, block, reference in [('original-one', 'block-04', 'false\n'),
                               ('corrected-max', 'block-02', 'true\n')]:
    decision = next(d for d in invalid['decisions'] if (d['case'], d['block']) == (name, block))
    if decision['decision'] != 'invalid_for_performance_use_before_distribution_inspection':
        raise ValueError('cohort is not the expressly excluded diagnostic input')
    directory = base / name / block
    result_path = directory / 'results.json'
    contents = result_path.read_bytes()
    digest = hashlib.sha256(contents).hexdigest()
    if digest != decision['results_sha256']:
        raise ValueError('results differ from excluded bytes')
    inputs[str(result_path)] = digest
    data = json.loads(contents)
    rows = data['rows']
    if data['schema_version'] != 1 or data['status'] != 'complete' or len(rows) != 42:
        raise ValueError('unexpected completed cohort schema/count')
    if Counter(r['phase'] for r in rows) != {'correctness': 3, 'warmup': 3, 'measurement': 36}:
        raise ValueError('unexpected phase counts')
    if any(r['case'] != name or r['arm'] not in ('Off', 'Manual', 'Injective') for r in rows):
        raise ValueError('foreign case/arm')
    if any(r['status'] != 'success' or r['exit_code'] != 0 or r['signal'] is not None or r['error'] is not None for r in rows):
        raise ValueError('unsuccessful row')
    correct = [r for r in rows if r['phase'] == 'correctness']
    if {r['arm'] for r in correct} != {'Off', 'Manual', 'Injective'} or any(
            r['receipt']['original_interpreted'] != reference or r['receipt']['result_interpreted'] != reference for r in correct):
        raise ValueError('correctness reference mismatch')
    for relative in ['verify-command.json', 'postcapture-command.json', 'postcapture/results.json']:
        path = directory / relative
        blob = path.read_bytes()
        inputs[str(path)] = hashlib.sha256(blob).hexdigest()
        receipt = json.loads(blob)
        if relative.endswith('command.json'):
            if receipt['returncode'] != 0 or receipt['timed_out']:
                raise ValueError('verification/postcapture did not pass')
        elif receipt['status'] != 'complete' or len(receipt['rows']) != 42:
            raise ValueError('incomplete postcapture')
    groups = []
    for arm in ['Off', 'Manual', 'Injective']:
        selected = sorted([(i, r) for i, r in enumerate(rows)
                           if r['phase'] == 'measurement' and r['arm'] == arm], key=lambda pair: pair[1]['repetition'])
        if len(selected) != 12 or [r['repetition'] for _, r in selected] != list(range(12)):
            raise ValueError('requires all twelve distinct measurements per arm')
        wall = [r['wall_sec'] for _, r in selected]
        rss = [r['max_rss_bytes'] for _, r in selected]
        if any(type(v) not in (int, float) or not math.isfinite(v) or v <= 0 for v in wall):
            raise ValueError('invalid wall observation')
        if any(type(v) is not int or v <= 0 for v in rss):
            raise ValueError('invalid wait4 RSS observation')
        deviation = statistics.stdev(wall)
        mean = math.fsum(wall) / len(wall)
        independent_sd = math.sqrt(math.fsum((v - mean) ** 2 for v in wall) / (len(wall) - 1))
        if not math.isclose(deviation, independent_sd, rel_tol=1e-12, abs_tol=1e-15):
            raise ValueError('sample SD calculation disagrees')
        group = {'arm': arm, 'n': 12, 'repetitions': list(range(12)), 'source_row_indices': [i for i, _ in selected],
                 'wall_seconds': {'raw_values': wall, 'median': statistics.median(wall),
                                  'min': min(wall), 'max': max(wall), 'sample_sd': deviation},
                 'wait4_rss_bytes': {'raw_values': rss, 'median': statistics.median(rss), 'min': min(rss), 'max': max(rss)}}
        groups.append(group)
        print(f"{name} | {arm} | {group['wall_seconds']['median'] * 1000:.3f} | "
              f"{min(wall) * 1000:.3f}–{max(wall) * 1000:.3f} | {deviation * 1000:.3f} | "
              f"{statistics.median(rss) / 2**20:.3f} | {min(rss) / 2**20:.3f}–{max(rss) / 2**20:.3f}")
    cases.append({'case': name, 'block': block, 'results_path': str(result_path), 'results_sha256': digest,
                  'exclusion_reason': decision['reason'], 'reference': reference,
                  'timing_scope': data['timing_scope'], 'rss_scope': data['rss_scope'],
                  'ignored_timing_rows': {'correctness': 3, 'warmup': 3}, 'arms': groups})
for path, digest in inputs.items():
    if hashlib.sha256(Path(path).read_bytes()).hexdigest() != digest:
        raise ValueError('input changed during derivation: ' + path)
summary = {'status': 'diagnostic_only_excluded_cohorts', 'accepted_for_paper_performance': False,
           'valid_for_causal_arm_comparisons': False, 'speedup_inference': False, 'pooled_blocks': False,
           'created_utc': datetime.now(timezone.utc).isoformat(),
           'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'source_files_sha256': inputs, 'cases': cases,
           'method': 'Only phase=measurement; all 12 repetitions per arm; median/min/max and sample SD (n-1); no trimming/retries/pooling. RSS remains bytes; display MiB divides by 2**20.'}
args.output.parent.mkdir(parents=True, exist_ok=True)
with args.output.open('x') as handle:
    handle.write(json.dumps(summary, indent=2, allow_nan=False) + '\n')
print('summary_sha256', hashlib.sha256(args.output.read_bytes()).hexdigest())
