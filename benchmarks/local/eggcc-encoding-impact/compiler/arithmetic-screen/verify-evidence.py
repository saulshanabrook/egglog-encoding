"""Verify the retained bug evidence, not that the compiler is correct."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
valid=json.loads((root/'valid-args/results.json').read_text());assert valid['status']=='completed'
assert len(valid['rows'])==32
assert sum(r['classification']=='compiler failure' for r in valid['rows'])==6
assert sum(r['classification']=='source/result mismatch' for r in valid['rows'])==3
assert sum(r['run_mode']=='parse' and r['non_null_equal_expected'] for r in valid['rows'])==8
for r in valid['rows']:
    assert not r['timed_out']
    assert hashlib.sha256(Path(r['input']).read_bytes()).hexdigest()==r['input_sha256']
    for key in ['binary','tiger']:assert hashlib.sha256(Path(r[key]).read_bytes()).hexdigest()==r[key+'_sha256']
    for path,sha in r['files_sha256'].items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==sha
    if r['run_mode']=='optimize' and r['returncode']==0:assert r['passes_started']==[0,1,2]
local=json.loads((root/'localization/results.json').read_text());assert len(local['rows'])==23
for arm in ['A','B','P-off']:
    bug=next(r for r in local['rows'] if r['case']=='mul-minimal-max' and r['arm']==arm and r['mode']=='optimize' and not r['diagnostic_ablation'])
    assert bug['returncode']==0 and not bug['timed_out'] and bug['passes_started']==[0,1,2]
    assert bug['original_interpreted']=='true\n' and bug['result_interpreted']=='false\n'
    control=next(r for r in local['rows'] if r['case']=='mul-minimal-one' and r['arm']==arm and r['mode']=='optimize')
    assert control['non_null_equal_expected'] and control['passes_started']==[0,1,2]
    for key in ['binary','tiger']:assert hashlib.sha256(Path(bug[key]).read_bytes()).hexdigest()==bug[key+'_sha256']
    assert hashlib.sha256(Path(bug['input']).read_bytes()).hexdigest()==bug['input_sha256']
    emitted=root/'localization/runs/mul-minimal-max'/(arm+'-emit')/'optimized.bril'
    text=emitted.read_text();assert '= const false;' in text and ' = mul ' not in text
for r in local['rows']:
    for path,sha in r['files_sha256'].items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==sha
replay=json.loads((root/'pass0-replay/results.json').read_text());assert len(replay['rows'])==9
by_stem={r['stem']:r for r in replay['rows']}
assert by_stem['mul-minimal-max/original']['returncode']==0
assert by_stem['mul-minimal-max/filtered']['returncode']==1
for name in ['max-ge-max','min-le-min']:
    assert by_stem[name+'/original']['returncode']==1 and by_stem[name+'/filtered']['returncode']==0
filtered=json.loads((root/'pass0-replay/mul-minimal-max/filtered-two-sign-rules/receipt.json').read_text())
assert filtered['returncode']==0 and not filtered['timed_out']
assert hashlib.sha256(Path(filtered['input']).read_bytes()).hexdigest()==filtered['input_sha256']
assert hashlib.sha256(Path(filtered['engine']['path']).read_bytes()).hexdigest()==filtered['engine']['sha256']
# Integer reference is defined modulo 2^64, then interpreted signed.
max_i64=(1<<63)-1
wrapped=((max_i64*2+(1<<63))%(1<<64))-(1<<63)
assert wrapped==-2 and wrapped<0
result={'status':'evidence verified; baseline remains buggy','valid_first_screen_runs':32,'localization_compiler_runs':23,'exported_pass_replay_runs':10,'retained_fixture_setup_failures':1,'reference_wrapped_product':wrapped,'silent_mismatch_arms':['A','B','P-off'],'active_processes':[],'performance_claim':None,'encoding_incremental_value_established':False}
(root/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
