import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

out = Path('/tmp/slotted-perf-pr203/pr-stack/builds')
out.mkdir(parents=True, exist_ok=True)
seed = Path('/home/oflatt/work/egglog-encoding3/target/release')
env = dict(os.environ, CARGO_BUILD_JOBS='2', CARGO_INCREMENTAL='0', OPENBLAS_NUM_THREADS='1')
env.pop('CARGO_TARGET_DIR', None)
for index in range(7):
    label = 'main' if index == 0 else f'stage{index:02}'
    work = Path('/tmp/slotted-stack-bench-' + ('00-main' if index == 0 else f'{index:02}'))
    target = work / 'target'
    target.mkdir(exist_ok=True)
    if not (target / 'release').exists():
        subprocess.run(['cp', '-a', '--reflink=auto', str(seed), str(target / 'release')], check=True)
    start = time.time()
    with (out / f'{label}.log').open('w') as log:
        cmd = ['cargo', 'build', '--locked', '-p', 'egglog-experimental', '--no-default-features', '--features', 'bin', '--bin', 'egglog-experimental', '--release']
        subprocess.run(cmd, cwd=work, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        if index == 0:
            subprocess.run(['cargo', 'build', '--locked', '-p', 'slotted-reference', '--no-default-features', '--bin', 'slotted-reference', '--release'], cwd=work, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    files = ['egglog-experimental'] + (['slotted-reference'] if index == 0 else [])
    result = {
        'label': label,
        'path': str(work),
        'git_sha': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=work, text=True).strip(),
        'elapsed_sec': time.time() - start,
        'binaries': {name: hashlib.file_digest((target / 'release' / name).open('rb'), 'sha256').hexdigest() for name in files},
    }
    (out / f'{label}.ready.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)
(out / 'complete').write_text('All seven release builds succeeded.\n')
