#!/usr/bin/env python3
"""Reconstruct QR7 sources from hash-verified retained archives; never builds."""
import hashlib
import io
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent / 'parts32-integration'
HOST = Path('/private/tmp/eggcc-qr7-candidate')
ENGINE = Path('/private/tmp/encoding-qr7-candidate')
U0 = Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
U0_REV = 'a0bbec127f83249074a46af3fd6f6126c90fe0fb'


def main():
    if (ROOT / 'source-admission.json').exists() or HOST.exists() or ENGINE.exists():
        raise RuntimeError('QR7 admission already exists; preserve it and choose fresh roots')
    admitted = json.loads((ROOT.parent / 'admission/manifest.json').read_text())
    revision = admitted['remote_eggcc_main']
    if revision != U0_REV:
        raise RuntimeError(f'pinned U0 admission changed: {revision}')
    source_manifest = ROOT.parent / 'admission/source-files.json'
    source_files = json.loads(source_manifest.read_text())
    for relative, expected in source_files.items():
        if hashlib.sha256((U0 / relative).read_bytes()).hexdigest() != expected:
            raise RuntimeError(f'admitted U0 source changed: {relative}')
    prior = json.loads((PRIOR / 'source-admission.json').read_text())
    identities = json.loads((PRIOR / 'final-source-identities.json').read_text())
    if hashlib.sha256((PRIOR / 'final-source.tar').read_bytes()).hexdigest() != identities['source_archive_sha256']:
        raise RuntimeError('retained final-source archive hash changed')
    base_rows = []
    archives = []
    for old, dest in [('eggcc-parts32-candidate', HOST), ('encoding-parts32-candidate', ENGINE)]:
        archive = PRIOR / (old + '.tar')
        blob = archive.read_bytes()
        sha = hashlib.sha256(blob).hexdigest()
        expected = next(row for row in prior['roots'] if Path(row['path']).name == old)
        if sha != expected['archive_sha256']:
            raise RuntimeError(f'base archive hash changed: {archive}')
        archives.append((blob, dest))
        base_rows.append(dict(path=str(dest), archive=str(archive), archive_sha256=sha,
                              revision=expected['revision']))
    retained = {}
    with tarfile.open(PRIOR / 'final-source.tar') as archive:
        for row in identities['files']:
            name = row.get('archive_path')
            if not name:
                continue
            blob = archive.extractfile(name).read()
            if hashlib.sha256(blob).hexdigest() != row['sha256']:
                raise RuntimeError(f'retained source hash changed: {name}')
            retained[name] = blob
    # Validate all archives and members before creating either destination.
    for blob, dest in archives:
        dest.mkdir()
        with tarfile.open(fileobj=io.BytesIO(blob)) as archive:
            archive.extractall(dest, filter='data')
    overlay = []
    for name, blob in retained.items():
        role, relative = name.split('/', 1)
        if role == 'eggcc' and relative not in {
            'Cargo.toml', 'Cargo.lock', 'dag_in_context/Cargo.toml',
            'dag_in_context/Cargo.lock', 'runtime/rt.bc', 'runtime/rt.o',
        }:
            continue
        target = (HOST if role == 'eggcc' else ENGINE) / relative
        if relative.endswith('Cargo.toml'):
            blob = blob.replace(b'/private/tmp/encoding-parts32-candidate', str(ENGINE).encode())
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(blob)
        overlay.append(dict(path=str(target), retained_member=name,
                            sha256=hashlib.sha256(blob).hexdigest()))
    fixtures = ROOT / 'fixtures'
    fixtures.mkdir()
    fixture_rows = []
    for name in ['source', 'omit-quotient-v2', 'omit-remainder-v2', 'different-divisor']:
        source = ROOT.parent / 'qr7-screen' / (name + '.bril')
        blob = source.read_bytes()
        target = fixtures / source.name
        target.write_bytes(blob)
        fixture_rows.append(dict(path=str(target), source=str(source),
                                 sha256=hashlib.sha256(blob).hexdigest()))
    report = dict(status='sources-reconstructed-not-built', roots=base_rows,
                  u0_revision=revision, overlays=overlay, fixtures=fixture_rows,
                  u0_source_files_verified=len(source_files),
                  source_manifest_sha256=hashlib.sha256(source_manifest.read_bytes()).hexdigest(),
                  setup_failures=['Initial git rev-parse rejected the extracted U0 archive because it has no .git. Admission now checks every file against the retained pinned source manifest. No destination was created by that failed attempt.'],
                  no_compiler_or_engine_executed=True, timing_taken=False)
    (ROOT / 'source-admission.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'roots': [str(HOST), str(ENGINE)]}))


if __name__ == '__main__':
    main()
