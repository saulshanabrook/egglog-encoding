#!/usr/bin/env python3
"""Package final evidence and prepare PR descriptions; no JSONL or remote writes."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/oflatt/work/egglog-encoding3')
FORMATS = ('png', 'svg', 'pdf', 'bound.vl.json', 'results.json')
SUITES = (('slotted-runtime', 'Nested (10 workloads)'),
          ('slotted-multipattern-runtime', 'Encoded multipattern (8 workloads)'))
spec = importlib.util.spec_from_file_location('stack_figures', HERE / 'stack-figures.py')
figures = importlib.util.module_from_spec(spec)
spec.loader.exec_module(figures)


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return 'sha256:' + hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()


def suite_estimate(result, name):
    suite = next(s for s in result['suites'] if s['name'] == name)
    return next(s['estimate'] for s in suite['child_parent']['summary']
                if s['metric'] == 'wall_sec' and s['kind'] == 'suite')


def display(estimate):
    low, high = estimate['ci_low'], estimate['ci_high']
    interval = 'unbounded' if low is None or high is None else f'{low:.3f}–{high:.3f}'
    if high is not None and high < 1:
        conclusion = f"{100 * (1 - estimate['point']):.1f}% lower measured suite time"
    elif low is not None and low > 1:
        conclusion = f"{100 * (estimate['point'] - 1):.1f}% higher measured suite time"
    else:
        conclusion = 'direction inconclusive in this pilot'
    return f"{estimate['point']:.3f}× | {interval} | {conclusion}"


def checked_inputs():
    manifest = read(HERE / 'manifest.json')
    plan = read(HERE / 'pr-plan.json')
    validation = read(HERE / 'publication-validation.json')
    tip = manifest['stages'][-1]['git_sha']
    sources = {stage['label']: stage['git_sha'] for stage in manifest['stages']}
    if (not validation['required_checks_complete'] or validation['source_sha'] != tip
            or validation['source_commits'] != sources):
        raise ValueError('Required validation is incomplete or identifies different source revisions')
    run = read(HERE.parent / 'validation.json')
    if run['source_sha'] != tip:
        raise ValueError('The Makefile validation run used a different tip')
    checks = {check['name']: check for check in run['checks']}
    for name in ('make-check', 'mttkrp2-scoped'):
        check = checks[name]
        if check['exit_code'] != 0 or check['source_sha'] != tip:
            raise ValueError(f'Required scoped validation did not pass at the final tip: {name}')
    if not validation['evidence']:
        raise ValueError('Validation evidence has not been recorded')
    for evidence in validation['evidence']:
        path = Path(evidence['path'])
        if path.suffix == '.jsonl' or digest(path) != evidence['sha256']:
            raise ValueError(f'Unexpected validation evidence: {path}')
    grouped_hash = digest(HERE / 'report-grouped.json')
    manifest_hash = digest(HERE / 'manifest.json')
    renderer_hash = digest(HERE / 'stack-figures.py')
    if (plan['base_commit'] != manifest['stages'][0]['git_sha']
            or plan['native_commit'] != manifest['native']['git_sha']
            or len(plan['pull_requests']) != 5):
        raise ValueError('The five-layer source plan does not match the manifest')
    results = {}
    parent_sha = plan['base_commit']
    for pr, stage in zip(plan['pull_requests'], manifest['stages'][1:], strict=True):
        if (pr['sha'] != stage['git_sha'] or pr['stage'] != stage['label']
                or git('rev-parse', pr['head']) != pr['sha']
                or git('rev-parse', pr['sha'] + '^') != parent_sha):
            raise ValueError(f'Unexpected branch or ancestry: {pr["head"]}')
        result = read(HERE / 'artifacts' / f"{pr['stage']}-slotted-comparison.results.json")
        if (result['stage']['git_sha'] != pr['sha'] or result['parent']['git_sha'] != parent_sha
                or result['native']['git_sha'] != plan['native_commit']):
            raise ValueError('Artifact source/parent/reference commit mismatch')
        if result['scope']['native_multipattern_comparison']:
            raise ValueError('Native multipattern is outside publication scope')
        if (result['source_grouped']['sha256'] != grouped_hash
                or result['manifest_sha256'] != manifest_hash
                or result['renderer']['script_sha256'] != renderer_hash
                or result['renderer']['git_sha'] != manifest['renderer_git_sha']):
            raise ValueError('Artifact snapshot or generator provenance mismatch')
        for suite in result['suites']:
            for condition in suite['conditions']:
                observations = condition['observations']
                if len(observations) != manifest['protocol']['rounds'] or any(
                        row['status'] != 'success' or row['target_is_dirty'] for row in observations):
                    raise ValueError('Incomplete or unsuccessful selected condition')
        results[pr['stage']] = result
        parent_sha = pr['sha']
    cumulative = read(HERE / 'cumulative-results.json')
    if (cumulative['source_grouped']['sha256'] != grouped_hash
            or cumulative['manifest_sha256'] != manifest_hash
            or cumulative['analysis']['script_sha256'] != renderer_hash
            or cumulative['baseline']['git_sha'] != plan['base_commit']
            or cumulative['candidate']['git_sha'] != tip):
        raise ValueError('Cumulative comparison does not match final inputs')
    audit = read(HERE / 'final-artifact-validation.json')
    if (audit['grouped_sha256'] != grouped_hash or audit['manifest_sha256'] != manifest_hash
            or audit['script_sha256'] != renderer_hash or audit['selected_conditions'] != 118
            or audit['selected_observations'] != 354 or audit['selected_status'] != 'all success'
            or not audit['all_plots_visually_inspected']
            or {s['label'] for s in audit['stages']} != set(results)
            or not all(s['pdf_fonts_embedded'] and s['visually_inspected_at_approximately_800px']
                       for s in audit['stages'])):
        raise ValueError('Final plot audit does not match publication inputs')
    for stage in audit['stages']:
        for suffix in FORMATS:
            path = HERE / 'artifacts' / f"{stage['label']}-slotted-comparison.{suffix}"
            if not path.stat().st_size or digest(path) != stage['files'][suffix]['sha256']:
                raise ValueError(f'Artifact changed after inspection: {path}')
    if audit['cumulative_results']['sha256'] != digest(HERE / 'cumulative-results.json'):
        raise ValueError('Cumulative results changed after the audit')
    focus = read(HERE / 'mmm-focus-results.json')
    if (focus != figures.mmm_focus_summary(cumulative)
            or audit['mmm_focus_results']['sha256'] != digest(HERE / 'mmm-focus-results.json')):
        raise ValueError('ΣMMM/MMM focus summary differs from final cumulative evidence')
    return plan, validation, results


def source_files(plan, validation):
    files = {}
    for pr in plan['pull_requests']:
        for suffix in FORMATS:
            name = f"{pr['stage']}-slotted-comparison.{suffix}"
            files[f'plots/{name}'] = HERE / 'artifacts' / name
    for name in ('report-grouped.json', 'cumulative-results.json', 'mmm-focus-results.json'):
        files[f'data/{name}'] = HERE / name
    for name in ('manifest.json', 'protocol.txt', 'collect.py', 'stack-figures.py',
                 'pr-plan.json', 'collection-plan.json', 'toolchain.json',
                 'prepare-publication.py', 'commit-artifacts.py',
                 'audit-artifacts.py', 'resize-previews.py'):
        files[f'reproduction/{name}'] = HERE / name
    for name in ('prebuild.py', 'validate.py'):
        files[f'reproduction/{name}'] = HERE.parent / name
    for name in ('publication-validation.json', 'final-artifact-validation.json'):
        files[f'validation/{name}'] = HERE / name
    files['validation/campaign-validation.json'] = HERE.parent / 'validation.json'
    for evidence in validation['evidence']:
        path = Path(evidence['path'])
        name = 'validation/' + evidence.get('name', path.name)
        if name in files and files[name] != path:
            raise ValueError(f'Duplicate evidence destination: {name}')
        files[name] = path
    for path in (HERE / 'builds').glob('*.ready.json'):
        files[f'builds/{path.name}'] = path
    for path in (HERE / 'final-fonts').glob('*.txt'):
        files[f'validation/final-fonts/{path.name}'] = path
    for path in (HERE / 'logs').glob('*-delta.md'):
        files[f'reports/{path.name}'] = path
    for path in (HERE / 'logs').glob('collection-*.json'):
        files[f'reproduction/{path.name}'] = path
    return files


def package(destination):
    plan, validation, results = checked_inputs()
    destination.mkdir(parents=True, exist_ok=False)
    for name, source in source_files(plan, validation).items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, path)
    rows = [f"| {pr['title']} | {label} | {display(suite_estimate(results[pr['stage']], name))} |"
            for pr in plan['pull_requests'] for name, label in SUITES]
    manifest = read(HERE / 'manifest.json')
    protocol = manifest['protocol']
    readme = f"""# Slotted startup optimization stack: benchmark evidence

Five cumulative commits start at main `{plan['base_commit']}`. Each plot
compares its commit with its immediate parent, plus parent/child comparisons
against native nested Slotted from fixed commit `{plan['native_commit']}`.

These are PR comparison pilots: {protocol['rounds']} observations per condition,
CPU {protocol['cpu']}, {protocol['timeout_sec']}-second watchdog, 16 GiB allocator cap.
All task builds/tests finished before timing. Concurrent builds, tests, rendering,
and other heavy task work were excluded; lightweight progress monitoring was allowed.
The host is shared. Native multipattern is omitted at the user's request;
encoded multipattern remains. No benchmark exclusion policy changed.

Ratios below 1 mean less runtime. Suite time is the sum of workload means;
large workloads dominate it. Intervals are independent Fieller 95% intervals.
Small or inconclusive changes should not be treated as established gains.

| Layer | Suite | Child / parent | 95% interval | Interpretation |
|---|---|---:|---|---|
{chr(10).join(rows)}

Validation: {validation['pr_validation_text']}

`plots/` contains five PNG/SVG/PDF bundles, bound Vega-Lite specifications,
and results with selected observations and source/binary/input hashes.
All five plots were inspected near 800 pixels wide; PDF fonts are embedded.
`data/` includes the complete public grouped export, a cumulative baseline
comparison, and the four-row nested ΣMMM/MMM focus summary with selected
observations. Raw tool-owned JSONL is not included. Public CLI tables are in
`reports/`; full protocol and source revisions are in `reproduction/`.

For reproduction, recreate the recorded worktrees, update absolute paths in a
copy of the manifest, and select a fresh report path. `collect.py` without
`--run` prints commands. The wrapper requires matching prepared-build markers;
original markers identify the measured binaries and must be regenerated for a
new build. The scripts record the exact runner source and renderer versions.
Rendered plots and bound specs require no measurement cache to view or share.
"""
    (destination / 'README.md').write_text(readme)
    hashes = {str(path.relative_to(destination)): digest(path)
              for path in sorted(destination.rglob('*')) if path.is_file()}
    (destination / 'sha256.json').write_text(json.dumps(hashes, indent=2) + '\n')
    print(f'Packaged {len(hashes)} files in {destination}')


def performance_details(result):
    notes = []
    for suite_name, label in SUITES:
        suite = next(s for s in result['suites'] if s['name'] == suite_name)
        regressions = [r for r in suite['child_parent']['files'] if r['metric'] == 'wall_sec'
                       and r['ci_low'] is not None and r['ci_low'] > 1]
        if regressions:
            names = ', '.join(f"{Path(r['file_path']).stem.removesuffix('-44rules')}: {r['ratio']:.3f}×"
                              for r in regressions)
            notes.append(f'{label}: workload regressions whose 95% intervals exceed 1: {names}.')
    return '\n\n'.join(notes)


def mmm_focus_table(result):
    nested = next(suite for suite in result['suites'] if suite['name'] == 'slotted-runtime')
    rows = []
    for row in figures.mmm_focus_rows(nested['child_parent']):
        ratio = row['ratio']
        lo, hi = ratio['ci_low'], ratio['ci_high']
        interval = 'unbounded' if lo is None or hi is None else f'{lo:.3f}–{hi:.3f}'
        issue = f"; {row['issue']}" if row['issue'] else ''
        rows.append(f"| {row['workload']} | {row['baseline_mean_ms']:.1f} → {row['candidate_mean_ms']:.1f} | "
                    f"{ratio['point']:.3f}× ({interval}{issue}) |")
    return ('Nested ΣMMM/MMM focus (whole-process arithmetic means):\n\n'
            '| Workload | Parent → PR (ms) | PR / parent (95% interval) |\n'
            '|---|---:|---:|\n' + '\n'.join(rows))


def bodies(artifact_commit):
    plan, validation, results = checked_inputs()
    if len(artifact_commit) != 40 or any(c not in '0123456789abcdef' for c in artifact_commit):
        raise ValueError('Use an immutable full artifact commit SHA')
    recorded = read(HERE / 'artifact-commit.json')
    if (recorded['commit'] != artifact_commit or recorded['branch'] != plan['artifact_branch']
            or git('rev-parse', f'{artifact_commit}^{{tree}}') != recorded['tree']):
        raise ValueError('Artifact commit does not match prepared publication')

    def committed(name):
        return subprocess.check_output(['git', '-C', str(ROOT), 'show', f'{artifact_commit}:{name}'])

    checksums = json.loads(committed('sha256.json'))
    names = set(git('ls-tree', '-r', '--name-only', artifact_commit).splitlines())
    if set(checksums) != names - {'sha256.json'}:
        raise ValueError('Committed checksum manifest differs from artifact tree')
    for name, expected in checksums.items():
        if 'sha256:' + hashlib.sha256(committed(name)).hexdigest() != expected:
            raise ValueError(f'Committed checksum mismatch: {name}')
    for name, source in source_files(plan, validation).items():
        if checksums.get(name) != digest(source):
            raise ValueError(f'Committed artifact differs from final evidence: {name}')
    repository = plan['repository']
    blob = f'https://github.com/{repository}/blob/{artifact_commit}'
    raw = f'https://raw.githubusercontent.com/{repository}/{artifact_commit}'
    directory = HERE / 'pr-bodies'
    directory.mkdir(exist_ok=True)
    output = []
    protocol = read(HERE / 'manifest.json')['protocol']
    for index, pr in enumerate(plan['pull_requests'], 1):
        prefix = f"plots/{pr['stage']}-slotted-comparison"
        result = results[pr['stage']]
        rows = '\n'.join(f'| {label} | {display(suite_estimate(result, name))} |' for name, label in SUITES)
        body = f"""{pr['description']}

Layer {index} of 5, based on `{pr['base']}`. The graph shows this commit and
its parent against native nested Slotted, then workload changes from the parent
in both encoded modes.

![Runtime comparison for layer {index}]({raw}/{prefix}.png)

| Suite | This PR / parent | 95% interval | Interpretation |
|---|---:|---|---|
{rows}

{mmm_focus_table(result)}

{performance_details(result)}

{pr.get('performance_note', '')}

Suite time is the sum of workload means, so larger cases dominate. Ratios below
1 mean less runtime. This pilot uses {protocol['rounds']} observations per condition,
CPU {protocol['cpu']}, a {protocol['timeout_sec']}-second watchdog, a 16 GiB allocator
cap, and independent Fieller 95% intervals. Task builds and tests completed
before collection. Concurrent builds, tests, rendering, and other heavy task
work were excluded; lightweight progress monitoring was allowed. The host
remains shared. Intervals crossing 1 do not establish
a directional gain. Native multipattern was omitted at the user's request.

[PDF]({blob}/{prefix}.pdf) · [SVG]({blob}/{prefix}.svg) ·
[Selected results and hashes]({blob}/{prefix}.results.json) ·
[Protocol and reproduction]({blob}/reproduction/protocol.txt)

Validation: {validation['pr_validation_text']}
[Validation evidence]({blob}/validation/publication-validation.json).

<!-- STACK_NAVIGATION -->
"""
        path = directory / f"{pr['stage']}.md"
        path.write_text(body)
        output.append({**pr, 'body_path': str(path), 'artifact_commit': artifact_commit})
    (HERE / 'publication-requests.json').write_text(json.dumps(output, indent=2) + '\n')
    print(f'Prepared {len(output)} PR descriptions in {directory}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    pack = commands.add_parser('package')
    pack.add_argument('destination', type=Path)
    desc = commands.add_parser('bodies')
    desc.add_argument('artifact_commit')
    args = parser.parse_args()
    package(args.destination) if args.command == 'package' else bodies(args.artifact_commit)


if __name__ == '__main__':
    main()
