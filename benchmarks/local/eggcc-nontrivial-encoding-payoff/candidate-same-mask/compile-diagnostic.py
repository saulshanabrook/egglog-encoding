#!/usr/bin/env python3
"""Five-arm compiler-wall-time diagnostic. Does not run generated programs."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,os,platform,random,statistics,subprocess,time
ROOT=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('candidate',ROOT/'run.py');c=importlib.util.module_from_spec(s);s.loader.exec_module(c)
SOURCE=ROOT/'fixtures/hot.bril'
ARMS={
 'U0':{'binary':ROOT.parent/'admission/bin/eggcc','cwd':Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0'),'mode':'off','reference':ROOT/'matrix-supplement/hot-u0/off/optimized.bril'},
 'B1':{'binary':ROOT/'bin-invariants/eggcc','cwd':Path('/private/tmp/eggcc-same-mask-candidate'),'mode':'off','reference':ROOT/'matrix-invariants/hot/off/optimized.bril'},
 'SeedOnly':{'binary':ROOT/'bin-invariants/eggcc','cwd':Path('/private/tmp/eggcc-same-mask-candidate'),'mode':'seed-only','reference':ROOT/'matrix-invariants/hot/seed-only/optimized.bril'},
 'Manual':{'binary':ROOT/'bin-invariants/eggcc','cwd':Path('/private/tmp/eggcc-same-mask-candidate'),'mode':'manual','reference':ROOT/'matrix-invariants/hot/manual/optimized.bril'},
 'Encoding':{'binary':ROOT/'bin-invariants/eggcc','cwd':Path('/private/tmp/eggcc-same-mask-candidate'),'mode':'encoding','reference':ROOT/'matrix-invariants/hot/encoding/optimized.bril'},
}
NAMES=list(ARMS)
base=[0,1,4,2,3]
orders=[[NAMES[(i+offset)%5] for i in base] for offset in range(5)]
orders+=list(map(lambda r:list(reversed(r)),orders))
OUTPUT=ROOT/'compile-diagnostic';OUTPUT.mkdir(exist_ok=False)
identities={name:{k:str(v) for k,v in a.items()}|{'binary_sha256':hashlib.sha256(a['binary'].read_bytes()).hexdigest(),'emission_sha256':hashlib.sha256(a['reference'].read_bytes()).hexdigest()} for name,a in ARMS.items()}
design={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'purpose':'diagnostic total EggCC optimize wall time, no speedup threshold','source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'cycles':10,'observations_per_arm':10,'warmups_per_arm':1,'order_rows':orders,'timer':'perf_counter_ns immediately around subprocess.run; compiler --run-data-out inside interval; capture persistence outside','includes':'all compiler startup, parsing, contextualization, private graph construction, translation, schedule, extraction and emitted Bril; per-query evidence-file output disabled equally','excludes':'Rust build, generated native lowering and execution','timeout_s':180,'identities':identities,'memory_guard_enabled':False,'cpu_isolation':False}
(ROOT/'compile-diagnostic-design.json').write_text(json.dumps(design,indent=2)+'\n')
env=dict(c.capture.ENV)
for key in list(env):
 if key.startswith('EGGCC_CONTROL_') or key=='EGGCC_SCOPED_EVIDENCE':env.pop(key,None)
env['RUST_LOG']='info'
rows=[]
def run(phase,cycle,arm):
 a=ARMS[arm];out=OUTPUT/f'{phase}-{cycle:02d}-{arm}';out.mkdir()
 e=env|{'EGGCC_ROOT':str(a['cwd']),'EGGCC_SCOPED_MODE':a['mode']}
 argv=[str(a['binary']),'--with-context','--run-mode','optimize','--run-data-out',str(out/'run-data.json'),str(SOURCE)]
 start=time.perf_counter_ns()
 try:
  p=subprocess.run(argv,cwd=a['cwd'],env=e,capture_output=True,timeout=180);stop=time.perf_counter_ns();stdout,stderr=p.stdout,p.stderr;code=p.returncode;timeout=False
 except subprocess.TimeoutExpired as exc:
  stop=time.perf_counter_ns();stdout,stderr=exc.stdout or b'',exc.stderr or b'';code=None;timeout=True
 row={'phase':phase,'cycle':cycle,'arm':arm,'argv':argv,'cwd':str(a['cwd']),'scoped_mode':a['mode'],'elapsed_ns':stop-start,'exit_code':code,'timed_out':timeout,'stdout_sha256':hashlib.sha256(stdout).hexdigest(),'stderr_sha256':hashlib.sha256(stderr).hexdigest(),'expected_stdout_sha256':identities[arm]['emission_sha256'],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 row['emission_exact']=row['stdout_sha256']==row['expected_stdout_sha256']
 (out/'optimized.bril').write_bytes(stdout);(out/'stderr').write_bytes(stderr);(out/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
 with (ROOT/'compile-diagnostic-samples.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 assert code==0 and row['emission_exact'],row
 data=json.loads((out/'run-data.json').read_text());assert 'result_interpreted' in data
 rows.append(row)
 return row
metadata={'platform':platform.platform(),'load_before':os.getloadavg(),'utc_before':datetime.datetime.now(datetime.timezone.utc).isoformat()}
for arm in NAMES:run('warmup',0,arm)
cycles=[]
for cycle,order in enumerate(orders):
 obs={arm:run('measure',cycle,arm) for arm in order};cycles.append(obs)
 print('compile cycle',cycle,{arm:round(v['elapsed_ns']/1e6,2) for arm,v in obs.items()},flush=True)
metadata.update(load_after=os.getloadavg(),utc_after=datetime.datetime.now(datetime.timezone.utc).isoformat())
summary={'diagnostic_only':True,'no_speedup_threshold':True,'metadata':metadata,'observations_per_arm':10,'arms':{},'paired_ratios':{}}
for arm in NAMES:
 values=[obs[arm]['elapsed_ns']/1e9 for obs in cycles]
 summary['arms'][arm]={'seconds':values,'median_s':statistics.median(values),'mean_s':statistics.mean(values),'min_s':min(values),'max_s':max(values),'stdev_s':statistics.stdev(values)}
for arm in NAMES[1:]:
 values=[obs[arm]['elapsed_ns']/obs['U0']['elapsed_ns'] for obs in cycles];rng=random.Random(20261019);b=sorted(statistics.median(rng.choices(values,k=10)) for _ in range(10000))
 summary['paired_ratios'][arm+'/U0']={'cycles':values,'median':statistics.median(values),'bootstrap95':[b[249],b[9749]]}
for arm,a in ARMS.items():assert hashlib.sha256(a['binary'].read_bytes()).hexdigest()==identities[arm]['binary_sha256']
(ROOT/'compile-diagnostic-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2),flush=True)
