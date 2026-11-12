import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path('/home/oflatt/work/egglog-encoding3')
OUT = Path('/tmp/slotted-mmm-implementation/pr-stack')
SEED = Path('/tmp/slotted-stack-bench-05/target')
OUT.joinpath('builds').mkdir(parents=True, exist_ok=True)
state = json.loads(Path('/tmp/slotted-mmm-implementation/task-state.json').read_text())
stages = [(None, state['base'])] + [(int(row['branch'].split('-')[1]), row['branch']) for row in state['integrated_layers']]
if len(sys.argv) > 1:
    selected = set(sys.argv[1:])
    stages = [(number, branch) for number, branch in stages if ('main' if number is None else str(number)) in selected]
env = dict(os.environ, CARGO_BUILD_JOBS='2', CARGO_INCREMENTAL='0')
env.pop('CARGO_TARGET_DIR',None)
for number,branch in stages:
    label='main' if number is None else f'stage{number:02}'
    source=Path('/tmp/slotted-mmm-bench-main' if number is None else f'/tmp/slotted-mmm-bench-{number:02}')
    sha=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',branch],text=True).strip()
    if not source.exists():
        subprocess.run(['git','-C',str(ROOT),'worktree','add','--quiet','--detach',str(source),sha],check=True)
        source.joinpath('target').mkdir()
        subprocess.run(['cp','-a','--reflink=auto',str(SEED/'release'),str(source/'target/release')],check=True)
        if (SEED/'.rustc_info.json').exists():
            subprocess.run(['cp','-a',str(SEED/'.rustc_info.json'),str(source/'target/.rustc_info.json')],check=True)
    assert not subprocess.check_output(['git','-C',str(source),'status','--porcelain'],text=True).strip()
    actual_sha=subprocess.check_output(['git','-C',str(source),'rev-parse','HEAD'],text=True).strip()
    if actual_sha!=sha:
        # These detached worktrees are owned by this script and have no edits.
        subprocess.run(['git','-C',str(source),'switch','--detach',sha],check=True)
    marker=OUT/'builds'/f'{label}.ready.json'
    if marker.exists():
        ready=json.loads(marker.read_text())
        binary=source/'target/release/egglog-experimental'
        if ready['git_sha']==sha and binary.exists() and hashlib.sha256(binary.read_bytes()).hexdigest()==ready['binaries']['egglog-experimental']:
            print('Already ready',label,sha,flush=True)
            continue
        marker.unlink()
    start=time.monotonic()
    command=['taskset','-c','30,31','cargo','build','--release','--locked','-p','egglog-experimental','--no-default-features','--features','bin','--bin','egglog-experimental']
    print('Building',label,sha,flush=True)
    with (OUT/'builds'/f'{label}.log').open('w') as log:
        subprocess.run(command,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
    binary=source/'target/release/egglog-experimental'
    ready=dict(label=label,path=str(source),git_sha=sha,command=command,
        elapsed_sec=time.monotonic()-start,
        binaries={'egglog-experimental':hashlib.sha256(binary.read_bytes()).hexdigest()})
    (OUT/'builds'/f'{label}.ready.json').write_text(json.dumps(ready,indent=2)+'\n')
    print('Ready',label,ready['elapsed_sec'],flush=True)
