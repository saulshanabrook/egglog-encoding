#!/usr/bin/env python3
"""Execute the already-frozen four-arm generated-program confirmation."""
from pathlib import Path
import datetime
import hashlib
import importlib.util
import json
import os
import platform
import random
import statistics
import subprocess
import time

ROOT=Path(__file__).resolve().parent
design_path=ROOT/'confirmation-design.json'
design=json.loads(design_path.read_text())
OUTPUT=ROOT/'confirmation'
OUTPUT.mkdir(exist_ok=False)
env=dict(os.environ)
for key in ['EGGLOG_BENCH_MEMORY_GUARD','EGGCC_SCOPED_MODE','EGGCC_SCOPED_EVIDENCE']:
    env.pop(key,None)
env['RAYON_NUM_THREADS']='1'

def measure(phase,cycle,arm,args,expected):
    binary=Path(design['arms'][arm]['binary'])
    out=OUTPUT/f'{phase}-{cycle:02d}-{arm}';out.mkdir()
    start=time.perf_counter_ns()
    try:
        process=subprocess.run([str(binary),*map(str,args)],cwd=ROOT,env=env,capture_output=True,timeout=30)
        stop=time.perf_counter_ns()
        stdout,stderr=process.stdout,process.stderr
        exit_code=process.returncode;timed_out=False
    except subprocess.TimeoutExpired as error:
        stop=time.perf_counter_ns()
        stdout,stderr=error.stdout or b'',error.stderr or b''
        exit_code=None;timed_out=True
    row={'phase':phase,'cycle':cycle,'arm':arm,'argv':[str(binary),*map(str,args)],
         'cwd':str(ROOT),'timeout_s':30,'elapsed_ns':stop-start,'exit_code':exit_code,
         'timed_out':timed_out,'stdout':stdout.decode(),'expected_stdout':expected,
         'stdout_sha256':hashlib.sha256(stdout).hexdigest(),'stderr_sha256':hashlib.sha256(stderr).hexdigest(),
         'correct':exit_code==0 and stdout.decode()==expected,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (out/'stdout').write_bytes(stdout);(out/'stderr').write_bytes(stderr)
    (out/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
    with (ROOT/'confirmation-samples.jsonl').open('a') as stream:stream.write(json.dumps(row)+'\n')
    assert row['correct'],row
    return row

for arm,identity in design['arms'].items():
    assert hashlib.sha256(Path(identity['binary']).read_bytes()).hexdigest()==identity['binary_sha256']
spec=importlib.util.spec_from_file_location('hot',ROOT.parent/'scoped-screen/hot-same-mask/run.py')
hot=importlib.util.module_from_spec(spec);spec.loader.exec_module(hot)
assert hot.pilot_expected(*design['args'])==design['expected_stdout']
metadata={'design_sha256':hashlib.sha256(design_path.read_bytes()).hexdigest(),
          'load_before':os.getloadavg(),'platform':platform.platform(),
          'utc_before':datetime.datetime.now(datetime.timezone.utc).isoformat()}
for cycle in range(design['warmups_per_arm']):
    for arm in design['order_rows'][cycle%4]:
        measure('warmup',cycle,arm,design['warmup_args'],hot.pilot_expected(*design['warmup_args']))
cycles=[]
for cycle in range(design['cycles']):
    order=design['order_rows'][cycle%4]
    row={'cycle':cycle,'order':order,'load_before':os.getloadavg(),'observations':{}}
    for arm in order:row['observations'][arm]=measure('measure',cycle,arm,design['args'],design['expected_stdout'])
    cycles.append(row)
    print('cycle',cycle,{arm:round(value['elapsed_ns']/1e6,3) for arm,value in row['observations'].items()},flush=True)
metadata.update(load_after=os.getloadavg(),utc_after=datetime.datetime.now(datetime.timezone.utc).isoformat())
(ROOT/'confirmation-cycles.json').write_text(json.dumps({'metadata':metadata,'cycles':cycles},indent=2)+'\n')
summary={'observations_per_arm':len(cycles),'arms':{},'paired_ratios':{}}
for arm in design['arms']:
    values=[row['observations'][arm]['elapsed_ns']/1e9 for row in cycles];ordered=sorted(values)
    summary['arms'][arm]={'samples_s':values,'median_s':statistics.median(values),'mean_s':statistics.mean(values),
        'stdev_s':statistics.stdev(values),'min_s':min(values),'max_s':max(values),
        'q1_s':statistics.median(ordered[:16]),'q3_s':statistics.median(ordered[16:])}
for arm in ['B1','Manual','Encoding']:
    values=[row['observations'][arm]['elapsed_ns']/row['observations']['U0']['elapsed_ns'] for row in cycles]
    rng=random.Random(20261019);bootstrap=[]
    for _ in range(10000):bootstrap.append(statistics.median(rng.choices(values,k=len(values))))
    bootstrap.sort()
    summary['paired_ratios'][arm+'/U0']={'cycles':values,'median':statistics.median(values),
        'bootstrap95':[bootstrap[249],bootstrap[9749]],
        'by_order_row_median':[statistics.median(values[i] for i in range(len(values)) if i%4==row) for row in range(4)]}
summary['prospective_runtime_gate_passed']=summary['paired_ratios']['Encoding/U0']['bootstrap95'][1]<0.99
summary['gate']='frozen upper95% paired median Encoding/U0 ratio<0.99;code parity established separately;all outputs exact'
for arm,identity in design['arms'].items():
    assert hashlib.sha256(Path(identity['binary']).read_bytes()).hexdigest()==identity['binary_sha256']
(ROOT/'confirmation-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'gate_passed':summary['prospective_runtime_gate_passed'],'paired_ratios':summary['paired_ratios']},indent=2),flush=True)
