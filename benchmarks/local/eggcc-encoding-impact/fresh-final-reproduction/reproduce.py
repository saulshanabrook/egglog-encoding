"""Two independent correctness reproductions; no builds, imports from peers, or timings study."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time


RAW = Path(__file__).resolve().parents[1]
CONTROL = RAW / 'compiler/observations/corrected-control-1'
TIGER_SHA = 'bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a'
CASES = [
    ('original-one', 'final-release', 1,
     '5d980389feec6270146db9a2cfe4e1775974102ab6c50cdf7bad029471907af1',
     'ff017790bf298fd56213f56759b8372cd6d74bb12457a747f088c03670f9fef2',
     'tests/encoding_impact/arithmetic/mul-minimal-one.bril',
     'b8bc31ef18ebefd6f25057439e277569a931b2ec769295cbf590aef14550bf9c'),
    ('corrected-max', 'corrected-release', (1 << 63) - 1,
     'f44edb3cb9c4b9660524335a29bea536571fe2ddbd1bcc68ba589decbd9bcc15',
     '860add623480776002f680501c1077ea7c2cd8e268545ce4c028c0e90aab20e2',
     'tests/encoding_impact/arithmetic/mul-minimal-max.bril',
     'f6624abf3e6018b7e6d2d5e410afff2f95822965515361b644cfc61ba8fd31eb'),
]


def validate_run(directory, pid, expected, x):
    """Independently bind actual CLI outputs, feasible witness, and three native completions."""
    command = json.loads((directory / 'command.json').read_text())
    assert command['returncode'] == 0 and not command['timed_out']
    stdout = (directory / 'command.stdout').read_bytes()
    assert stdout == (expected + '\n').encode()  # CLI prints its own separator newline.
    data = json.loads((directory / 'run-data.json').read_text())
    assert data['original_interpreted'] == data['result_interpreted'] == expected
    stderr = (directory / 'command.stderr').read_text()
    assert list(map(int, re.findall(r'Running pass (\d+)\.\.\.', stderr))) == [0, 1, 2]
    assert stderr.count('Ran schedule (repeat 1 (run reconstruction))') >= 3
    graphs = sorted((directory / 'egraphs').glob('tiger_egraph_*.json'))
    assert len(graphs) == 3 and all(json.loads(p.read_text()) for p in graphs)
    locators = [json.loads(s.removeprefix('observation-evidence: '))
                for s in stderr.splitlines() if s.startswith('observation-evidence: ')]
    assert len(locators) == 1 and locators[0] == data['observation_evidence']
    locator = locators[0]
    child, index_path = Path(locator['directory']), Path(locator['index'])
    assert child.is_absolute() and child.resolve() == child
    assert child.parent == directory / 'evidence-root' and index_path == child / 'index.json'
    assert not any(p.is_symlink() for p in [child, *child.rglob('*')])
    index = json.loads(index_path.read_text())
    assert index['pid'] == pid and child.name.startswith(f'invocation-{pid}-')
    assert index['directory'] == str(child) and index['index'] == str(index_path)
    assert index['root'] == str(child.parent) and index['mode'] == 'Injective'
    assert index['stage'] == 'optimizer-complete' and index['status'] == 'complete'
    assert set(index['passes']) == {'00', '01', '02'}
    assert {p.name for p in child.iterdir()} == {'index.json', 'pass-00', 'pass-01', 'pass-02'}
    observations = []
    for key, record in sorted(index['passes'].items()):
        path = child / f'pass-{key}'
        assert record['stage'] == 'native-round-trip-complete' and record['directory'] == str(path)
        assert set(record['evidence']) == {str(p) for p in path.iterdir()}
        assert {p.name for p in path.iterdir()} == {
            'observations.json', 'initialization.egg', 'source-schedule.egg',
            'committed-before-audit.json', 'audit.json', 'serialization-entry.json'}
        obs = json.loads((path / 'observations.json').read_text())
        audit = json.loads((path / 'audit.json').read_text())
        committed = json.loads((path / 'committed-before-audit.json').read_text())
        assert obs['pass'] == int(key) and obs['mode'] == 'Injective'
        assert obs['literal_injective'] is True and obs['eval_bool_at_injective'] is False
        assert obs['expr_annotations'] is False and obs['supported_bool_observations'] > 0
        assert len(obs['seeds']) > 0
        initialization = (path / 'initialization.egg').read_text()
        for seed in obs['seeds']:
            row = f"(ObservationSeed {seed['id']} {seed['expr']} {seed['point']} {str(seed['value']).lower()})"
            assert initialization.count(row) == 1
        assert audit == {'stage': 'pre-serialization-observation-audit', 'accepted': True,
                         'mode': 'Injective', 'error': None, 'native_extraction_entered': False}
        assert committed['stage'] == 'source-schedule-committed-before-serialization'
        assert committed['conflicts'] == [] and committed['native_extraction_entered'] is False
        assert committed['audit'] == '(run-schedule (saturate injectivity))'
        assert json.loads((path / 'serialization-entry.json').read_text()) == {
            'stage': 'observer-accepted-entering-serialization'}
        if key == '00':
            selected = [s for s in obs['seeds'] if s['origin'] == 'feasible-pure-expression'
                        and s['term'].startswith('(Bop (LessThan) (Bop (Mul)')]
            assert len(selected) == 1 and selected[0]['value'] == (expected == 'true\n')
            point = next(p for p in obs['points'] if p['token'] == selected[0]['point'])
            assert point['branch'] is True
            assert point['region_input'] == f'Tuple([StateV, Const(Int(0)), Const(Int({x})), Const(Int(2))])'
        observations.append({'pass': int(key), 'supported_bool_observations': obs['supported_bool_observations'],
                             'seed_count': len(obs['seeds']), 'audit_accepted': True})
    archive = directory / 'evidence-archive'
    shutil.copytree(child, archive)
    inventory = {str(p.relative_to(child)): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in sorted(child.rglob('*')) if p.is_file()}
    assert inventory == {str(p.relative_to(archive)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in sorted(archive.rglob('*')) if p.is_file()}
    shutil.copy2(directory / 'run-data.json', directory / 'captured-run-data.json')
    assert (directory / 'run-data.json').read_bytes() == (directory / 'captured-run-data.json').read_bytes()
    return {'status': 'pass', 'reference': expected, 'source_output': data['original_interpreted'],
            'result_output': data['result_interpreted'], 'passes': observations,
            'native_graphs_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in graphs},
            'locator': locator, 'archive': str(archive), 'files_sha256': inventory}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False)
    script = Path(__file__).resolve()
    script_hash = hashlib.sha256(script.read_bytes()).hexdigest()
    prepared = []
    for name, endpoint, x, binary_sha, manifest_sha, relative, input_sha in CASES:
        directory = output / name
        directory.mkdir()
        manifest_path = CONTROL / endpoint / 'manifest.json'
        assert hashlib.sha256(manifest_path.read_bytes()).hexdigest() == manifest_sha
        package = json.loads(manifest_path.read_text())
        source_path = Path(package['source_manifest'])
        source = json.loads(source_path.read_text())
        source_root = Path(source['source_root'])
        fixture = source_root / relative
        bindings = {manifest_path: manifest_sha, source_path: package['source_manifest_sha256'],
                    Path(source['patch']): package['source_patch_sha256'],
                    Path(package['binary']): binary_sha, Path(package['tiger']): TIGER_SHA,
                    fixture: input_sha, script: script_hash}
        assert package['binary_sha256'] == binary_sha and package['tiger_sha256'] == TIGER_SHA
        assert Path(package['binary']).parent == Path(package['tiger']).parent
        assert source['source_sha256'][relative] == input_sha
        assert re.search(r'^# ARGS: (\d+)\s*$', fixture.read_text(), re.M)[1] == str(x)
        assert all(hashlib.sha256(p.read_bytes()).hexdigest() == digest for p, digest in bindings.items())
        copied = directory / 'input.bril'
        copied.write_bytes(fixture.read_bytes())
        bindings[copied] = input_sha
        wrapped = ((x * 2 + (1 << 63)) % (1 << 64)) - (1 << 63)
        expected = ('true' if wrapped < 0 else 'false') + '\n'
        before = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in bindings}
        (directory / 'before.json').write_text(json.dumps({'files_sha256': before, 'x': x,
            'wrapping_i64_product': wrapped, 'expected': expected, 'package': package}, indent=2) + '\n')
        prepared.append((directory, package, source_root, copied, x, expected, bindings, before))
    rows = []
    for directory, package, source_root, copied, x, expected, bindings, before in prepared:
        argv = [package['binary'], '--with-context', '--run-mode', 'optimize', '--interp',
                '--run-data-out', str(directory / 'run-data.json'), '--egraph-out-dir', str(directory / 'egraphs'),
                '--observations', 'injective', '--observation-evidence-dir', str(directory / 'evidence-root'), str(copied)]
        env = {**os.environ, 'RUST_LOG': 'info', 'RAYON_NUM_THREADS': '1'}
        command = {'argv': argv, 'cwd': str(source_root), 'timeout_seconds': 120,
                   'started_at': datetime.now(timezone.utc).isoformat(),
                   'env': {k: env.get(k) for k in ['PATH', 'RUST_LOG', 'RAYON_NUM_THREADS', 'LLVM_SYS_180_PREFIX',
                       'LIBRARY_PATH', 'CARGO_TARGET_DIR', 'RUSTUP_TOOLCHAIN', 'CARGO_BUILD_JOBS']}}
        started = time.monotonic()
        with (directory / 'command.stdout').open('wb') as stdout, (directory / 'command.stderr').open('wb') as stderr:
            child = subprocess.Popen(argv, cwd=source_root, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
            command['pid'] = child.pid
            (directory / 'command.running.json').write_text(json.dumps(command, indent=2) + '\n')
            try:
                command['returncode'] = child.wait(timeout=120)
                command['timed_out'] = False
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                command['returncode'] = child.wait()
                command['timed_out'] = True
        command['wall_seconds_diagnostic_only'] = time.monotonic() - started
        (directory / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
        (directory / 'command.running.json').unlink()
        try:
            row = validate_run(directory, child.pid, expected, x)
        except Exception as error:
            row = {'status': 'failed', 'error': repr(error), 'reference': expected}
        after = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in bindings}
        row.update(case=directory.name, receipt=str(directory / 'command.json'), pid=child.pid,
                   returncode=command['returncode'], child_reaped=child.poll() is not None,
                   before_after_equal=before == after)
        if before != after:
            row.update(status='failed', error='bound input/source/endpoint bytes changed')
        (directory / 'after.json').write_text(json.dumps({'files_sha256': after, 'equal': before == after}, indent=2) + '\n')
        (directory / 'review.json').write_text(json.dumps(row, indent=2) + '\n')
        rows.append(row)
        print(json.dumps({k: row[k] for k in ['case', 'status', 'reference', 'pid', 'returncode', 'before_after_equal']}), flush=True)
    summary = {'invocations': len(rows), 'status': 'pass' if len(rows) == 2 and all(r['status'] == 'pass' for r in rows) else 'failed',
               'script_sha256': script_hash, 'performance_evidence': False,
               'owned_live_children': [r['pid'] for r in rows if not r['child_reaped']], 'rows': rows}
    (output / 'results.json').write_text(json.dumps(summary, indent=2) + '\n')
    return 0 if summary['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
