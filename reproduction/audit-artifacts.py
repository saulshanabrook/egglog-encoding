#!/usr/bin/env python3
"""Audit final grouped selections and scientific plots; never read raw JSONL."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('stack_figures', HERE / 'stack-figures.py')
figures = importlib.util.module_from_spec(spec)
spec.loader.exec_module(figures)
FORMATS = ('png', 'svg', 'pdf', 'bound.vl.json', 'results.json')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=HERE / 'manifest.json')
    parser.add_argument('--prepare-previews', action='store_true')
    parser.add_argument('--inspected', action='append', default=[],
                        help='Record a stage only after actually viewing its current 800px preview')
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    figures.validate_manifest(manifest, require_bound=True)
    sys.path.insert(0, manifest['renderer_root'])
    from benchmarking.reports.store import parse_grouped_report
    _, resolved = figures.config_and_figures(manifest)
    grouped_path = Path(manifest['grouped_path'])
    grouped_bytes = grouped_path.read_bytes()
    grouped_hash = 'sha256:' + hashlib.sha256(grouped_bytes).hexdigest()
    grouped = parse_grouped_report(grouped_bytes, str(grouped_path))
    manifest_hash = figures.digest(args.manifest)
    script_hash = figures.digest(HERE / 'stack-figures.py')
    selections = {}
    for figure in resolved:
        treatment = 'slotted-no-aliasing' if figure.figure.name == 'slotted-runtime' else 'slotted'
        sources = [(stage, treatment) for stage in manifest['stages']]
        if figure.figure.name == 'slotted-runtime':
            sources.append((manifest['native'], 'slotted-ref-nested'))
        for source, selected_treatment in sources:
            endpoint = figures.endpoint(grouped, source, selected_treatment, manifest['protocol'])
            marker_path = HERE / 'builds' / f"{source['label']}.ready.json"
            marker = json.loads(marker_path.read_text())
            binary = 'slotted-reference' if source is manifest['native'] else 'egglog-experimental'
            if marker['git_sha'] != source['git_sha'] or marker['path'] != source['source']:
                raise ValueError(f'Wrong prepared source: {source["label"]}')
            if endpoint.binary_sha256 != 'sha256:' + marker['binaries'][binary]:
                raise ValueError(f'Wrong measured executable: {source["label"]}')
            for file in figure.files:
                condition = figures.selected_condition(grouped, endpoint, file, manifest)
                selections[(source['label'], selected_treatment, file.sha256)] = condition
    selected_rows = {index for item in selections.values() for index in item['selected_row_indices']}
    if len(selections) != 118 or len(selected_rows) != 354:
        raise ValueError(f'Unexpected selected coverage: {len(selections)} conditions / {len(selected_rows)} rows')
    rows = {sample['row_index']: sample for group in grouped.data['groups'] for sample in group['samples']}
    if any(rows[index]['status'] != 'success' for index in selected_rows):
        raise ValueError('The selected observations contain a failure')
    windows = manifest['protocol']['collection_windows']
    first, second = windows
    original_path = Path(first['diagnostic_directory']) / 'report-grouped.json'
    original_bytes = original_path.read_bytes()
    if 'sha256:' + hashlib.sha256(original_bytes).hexdigest() != first['grouped_sha256']:
        raise ValueError('The original grouped snapshot changed')
    original = parse_grouped_report(original_bytes, str(original_path))
    original_rows = {sample['row_index']: sample for group in original.data['groups']
                     for sample in group['samples']}
    if any(rows.get(index) != sample for index, sample in original_rows.items()):
        raise ValueError('Original observations are missing or changed in the final grouped export')
    reused = selected_rows.intersection(original_rows)
    fresh = selected_rows.difference(original_rows)
    fresh_labels = set(second['new_stage_labels'])
    for (label, _, _), condition in selections.items():
        indices = set(condition['selected_row_indices'])
        if not indices <= (fresh if label in fresh_labels else reused):
            raise ValueError(f'Unexpected measurement window for selected condition: {label}')
    if (len(reused) != second['expected_reused_selected_observations']
            or len(fresh) != second['expected_fresh_observations']
            or len(rows) != second['expected_retained_observations']):
        raise ValueError('Actual collection-window counts differ from the declared protocol')
    collection_windows = {
        'original_grouped_sha256': first['grouped_sha256'],
        'original_observations_preserved': len(original_rows),
        'reused_selected_observations': len(reused),
        'fresh_selected_observations': len(fresh),
        'reused_selected_row_indices': sorted(reused),
        'fresh_selected_row_indices': sorted(fresh),
        'historical_unselected_row_indices': sorted(set(original_rows) - selected_rows),
    }
    resize = None
    if args.prepare_previews:
        output = subprocess.check_output([
            'taskset', '-c', str(manifest['renderer_cpu']), 'uv', 'run', '--with', 'pillow==11.3.0',
            '--no-project', 'python', str(HERE / 'resize-previews.py'), str(args.manifest)], text=True)
        resize = json.loads(output)
    inspected = set(args.inspected)
    labels = {stage['label'] for stage in manifest['stages'][1:]}
    if inspected - labels:
        raise ValueError(f'Unknown inspected stages: {inspected - labels}')
    font_dir = HERE / 'final-fonts'
    font_dir.mkdir(exist_ok=True)
    stages = []
    for parent, stage in zip(manifest['stages'], manifest['stages'][1:]):
        stem = Path(manifest['output_dir']) / f"{stage['label']}-slotted-comparison"
        paths = {suffix: Path(str(stem) + '.' + suffix) for suffix in FORMATS}
        result = json.loads(paths['results.json'].read_text())
        if (result['source_grouped']['sha256'] != grouped_hash or result['manifest_sha256'] != manifest_hash
                or result['renderer']['script_sha256'] != script_hash or result['stage'] != stage
                or result['parent'] != parent or result['native'] != manifest['native']):
            raise ValueError(f'Bundle provenance mismatch: {stage["label"]}')
        suites = []
        for suite in result['suites']:
            for condition in suite['conditions']:
                endpoint = condition['endpoint']
                key = (endpoint['target']['label'], endpoint['treatment'], condition['logical_id'])
                if condition != selections[key]:
                    raise ValueError(f'Artifact selection differs from final shared selection: {key}')
            comparison = suite['child_parent']
            estimate = next(row['estimate'] for row in comparison['summary']
                            if row['metric'] == 'wall_sec' and row['kind'] == 'suite')
            directional = [{key: row[key] for key in ('file_path', 'ratio', 'ci_low', 'ci_high', 'result_class')}
                           for row in comparison['files'] if row['metric'] == 'wall_sec'
                           and row['result_class'] in ('lower', 'higher')]
            suites.append({'name': suite['name'], 'runtime_ratio': estimate, 'directional_files': directional})
        font_text = subprocess.check_output(['pdffonts', str(paths['pdf'])], text=True)
        fonts = [line.split() for line in font_text.splitlines()[2:] if line.strip()]
        embedded = bool(fonts) and all(len(fields) >= 6 and fields[-5] == 'yes' for fields in fonts)
        if not embedded:
            raise ValueError(f'PDF fonts are not all embedded: {stage["label"]}')
        font_path = font_dir / f"{stage['label']}.txt"
        font_path.write_text(font_text)
        preview = HERE / 'previews' / f"{stage['label']}-800.png"
        files = {suffix: {'path': str(path), 'sha256': figures.digest(path)} for suffix, path in paths.items()}
        stages.append({'label': stage['label'], 'files': files, 'pdf_fonts_embedded': embedded,
                       'font_count': len(fonts), 'font_report_sha256': figures.digest(font_path),
                       'preview': str(preview), 'preview_sha256': figures.digest(preview),
                       'visually_inspected_at_approximately_800px': stage['label'] in inspected,
                       'suites': suites})
    cumulative_path = HERE / 'cumulative-results.json'
    cumulative = json.loads(cumulative_path.read_text())
    if (cumulative['source_grouped']['sha256'] != grouped_hash or cumulative['manifest_sha256'] != manifest_hash
            or cumulative['analysis']['script_sha256'] != script_hash
            or cumulative['baseline'] != manifest['stages'][0]
            or cumulative['candidate'] != manifest['stages'][-1]):
        raise ValueError('Cumulative result provenance mismatch')
    focus_path = HERE / 'mmm-focus-results.json'
    if json.loads(focus_path.read_text()) != figures.mmm_focus_summary(cumulative):
        raise ValueError('ΣMMM/MMM summary differs from the cumulative selected results')
    result = {'validated_at': datetime.now(timezone.utc).isoformat(),
              'grouped_sha256': grouped_hash, 'manifest_sha256': manifest_hash, 'script_sha256': script_hash,
              'selected_conditions': len(selections), 'selected_observations': len(selected_rows),
              'selected_status': 'all success', 'retained_observations': len(rows),
              'retained_status_counts': dict(Counter(row['status'] for row in rows.values())),
              'collection_windows': collection_windows,
              'stages': stages, 'cumulative_results': {'path': str(cumulative_path), 'sha256': figures.digest(cumulative_path)},
              'mmm_focus_results': {'path': str(focus_path), 'sha256': figures.digest(focus_path)},
              'all_plots_visually_inspected': inspected == labels,
              'preview_renderer': resize or {'pillow': '11.3.0', 'preview_width': 800}}
    destination = HERE / ('final-artifact-validation.json' if inspected == labels else 'artifact-audit.pending.json')
    figures.write_json(destination, result)
    print(str(destination))


if __name__ == '__main__':
    main()
