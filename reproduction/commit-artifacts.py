#!/usr/bin/env python3
"""Create an isolated artifact commit; never push or change the main index."""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/oflatt/work/egglog-encoding3')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    directory = args.directory.resolve(strict=True)
    spec = importlib.util.spec_from_file_location('prepare_publication', HERE / 'prepare-publication.py')
    publication = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(publication)
    checked_plan, validation, _ = publication.checked_inputs()
    plan = json.loads((HERE / 'pr-plan.json').read_text())
    if plan != checked_plan:
        raise ValueError('Publication plan changed during validation')
    for name, source in publication.source_files(plan, validation).items():
        if publication.digest(directory / name) != publication.digest(source):
            raise ValueError(f'Packaged evidence differs from the final source: {name}')
    branch = plan['artifact_branch']
    ref = f'refs/heads/{branch}'
    existing = subprocess.run(['git', '-C', str(ROOT), 'show-ref', '--verify', '--quiet', ref])
    if existing.returncode != 1:
        raise ValueError(f'Artifact ref already exists or cannot be checked: {ref}')
    files = [path for path in directory.rglob('*') if path.is_file()]
    if any(path.is_symlink() or path.suffix == '.jsonl' or 'layout-test' in path.name for path in files):
        raise ValueError('Artifact tree contains an unapproved file')
    if not (directory / 'sha256.json').is_file():
        raise ValueError('Run prepare-publication.py package first')
    with tempfile.TemporaryDirectory(prefix='slotted-artifact-index-') as temporary:
        environment = dict(os.environ, GIT_INDEX_FILE=str(Path(temporary) / 'index'))
        prefix = ['git', '-C', str(ROOT), f'--work-tree={directory}']

        def git(*arguments, input=None):
            return subprocess.check_output(prefix + list(arguments), env=environment, text=True, input=input).strip()

        git('read-tree', '--empty')
        git('add', '--force', '--all')
        tracked = git('ls-files', '-z').split('\0')
        if tracked[-1] == '':
            tracked.pop()
        if len(tracked) != len(files):
            raise ValueError('Git artifact tree does not match the prepared directory')
        def staged(name):
            return subprocess.check_output(prefix + ['show', f':{name}'], env=environment)

        checksums = json.loads(staged('sha256.json'))
        if set(checksums) != set(tracked) - {'sha256.json'}:
            raise ValueError('Checksum manifest does not name the exact staged file set')
        for name, expected in checksums.items():
            actual = 'sha256:' + hashlib.sha256(staged(name)).hexdigest()
            if actual != expected:
                raise ValueError(f'Staged artifact checksum mismatch: {name}')
        tree = git('write-tree')
        commit = git('commit-tree', tree, input='Record five slotted startup optimization benchmark pilots\n')
        git('update-ref', ref, commit, '0' * 40)
    result = {'branch': branch, 'commit': commit, 'tree': tree, 'directory': str(directory), 'files': len(files)}
    (HERE / 'artifact-commit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
