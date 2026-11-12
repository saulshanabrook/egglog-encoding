"""Run the root Makefile and the exact scoped paper child; no corpus generation."""
import json
import os
from pathlib import Path
import subprocess
import time
import sys

ROOT = Path('/home/oflatt/work/egglog-encoding3')
OUT = Path('/tmp/slotted-mmm-implementation/validation-nested')
OUT.mkdir(parents=True,exist_ok=True)
SOURCE = 'benchmarks/slotted/inputs/sdql/mttkrp_2nd-44rules.egg'
env = dict(os.environ,CARGO_BUILD_JOBS='2',CARGO_INCREMENTAL='0',
    CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_TEST_DEBUG='0',RUST_TEST_THREADS='2')
env.pop('CARGO_TARGET_DIR',None)
env['RUST_TEST_ARGS'] = '--skip paper/' + SOURCE
records=[]
sha=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
assert len(sys.argv)==2 and sha==sys.argv[1], 'Pass the exact final expected source SHA'
assert sha!='cecac74c2a2a4fcdc9400b3e6fadf560b51aed89', 'Do not rerun the obsolete full-query variant'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip()

def run(name,command,environment,timeout=None):
    start=time.monotonic()
    print('Starting',name,flush=True)
    with (OUT/f'{name}.log').open('w') as log:
        result=subprocess.run(command,cwd=ROOT,env=environment,stdout=log,
            stderr=subprocess.STDOUT,timeout=timeout)
    records.append(dict(name=name,source_sha=sha,command=command,
        exit_code=result.returncode,elapsed_sec=time.monotonic()-start,
        log=str(OUT/f'{name}.log')))
    (OUT/'validation.json').write_text(json.dumps(dict(
        source_sha=sha,excluded_configuration='native multipattern MTTKRP second phase, per user',
        make_filter=env['RUST_TEST_ARGS'],checks=records),indent=2)+'\n')
    print(name,'exit',result.returncode,flush=True)
    result.check_returncode()

run('make-check',['taskset','-c','16-19','make','check'],env)
# Ask Cargo for the exact just-built paper executable rather than guessing a
# dependency hash or accidentally selecting an older validation artifact.
with (OUT/'paper-binary.log').open('w') as log:
    built=subprocess.run(['taskset','-c','16-19','cargo','test','--locked','-p',
        'paper-tests','--test','paper','--no-run','--message-format=json'],
        cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=log,text=True,check=True)
artifacts=[json.loads(line) for line in built.stdout.splitlines() if line.startswith('{')]
executables=[r['executable'] for r in artifacts if r.get('reason')=='compiler-artifact'
    and r.get('target',{}).get('name')=='paper' and r.get('executable')]
assert len(executables)==1,executables
child_env=dict(env,MIMALLOC_ARENA_RESERVE='0',MIMALLOC_DISALLOW_ARENA_ALLOC='1',
    MIMALLOC_RESERVE_OS_MEMORY='0',MIMALLOC_RESERVE_HUGE_OS_PAGES='0')
run('mttkrp2-scoped',['taskset','-c','16-19',executables[0],
    '--memory-limit-bytes=17179869184','--paper-child',str(ROOT/SOURCE),
    'slotted,slotted-no-aliasing,slotted-ref-nested,slotted-ref-nested-snapshot'],child_env,6000)
