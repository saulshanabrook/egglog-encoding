#!/usr/bin/env python3
"""Controlled theory knockout/rescue and existing-consumer evidence."""
from pathlib import Path
import importlib.util
import hashlib
import json
import os

ROOT=Path(__file__).resolve().parent
os.environ.update(CANDIDATE_MATRIX_TAG='causal',CANDIDATE_BINARY=str(ROOT/'bin-causal-control/eggcc'))
spec=importlib.util.spec_from_file_location('matrix',ROOT/'matrix.py')
matrix=importlib.util.module_from_spec(spec);spec.loader.exec_module(matrix)
capture=matrix.capture
capture.U0=Path('/private/tmp/eggcc-same-mask-causal-control')
capture.ENV['EGGCC_ROOT']=str(capture.U0)
cases=[('normal','encoding',{}),
       ('reverse-off','encoding',{'EGGCC_CONTROL_REVERSE_OFF':'1'}),
       ('reverse-rescue','encoding',{'EGGCC_CONTROL_REVERSE_OFF':'1','EGGCC_CONTROL_RESCUE':'child'}),
       ('annotation-off','annotation-off',{}),
       ('annotation-rescue','annotation-off',{'EGGCC_CONTROL_RESCUE':'target'}),
       ('primitive-null','primitive-null',{}),
       ('consumer-off','encoding',{'EGGCC_CONTROL_CONSUMER_OFF':'1'})]
results=[]
for family,args,expected in [('cold',(0,1,1),'7\n'),('hot',(8,0,1,6),'48\n')]:
    for label,mode,flags in cases:
        for name in ['EGGCC_CONTROL_REVERSE_OFF','EGGCC_CONTROL_RESCUE','EGGCC_CONTROL_CONSUMER_OFF']:
            capture.ENV.pop(name,None)
        capture.ENV.update(flags)
        folder=matrix.compile_case(family+'-'+label,mode,ROOT/'fixtures'/(family+'.bril'))
        data=json.loads((folder/'interp.json').read_text())
        assert data['original_interpreted']==data['result_interpreted']==expected,(family,label,data)
        queries=[json.loads(p.read_text()) for p in sorted((folder/'emit-evidence').glob('query-*.json'))]
        first=queries[0]
        want_export=label in ['normal','reverse-rescue','annotation-rescue','consumer-off']
        assert first['export']==want_export,(label,first)
        if label=='reverse-off':
            assert first['parent_known'] and not first['child_known'] and not first['target_known'],first
        elif label=='reverse-rescue':
            assert first['parent_known'] and first['child_known'] and first['target_known'] and first['control_rescue_fact'],first
        elif label=='annotation-rescue':
            assert first['child_known'] and first['target_known'] and first['control_rescue_fact'],first
        elif label=='primitive-null':
            assert first['word_constructor_primitive_fields']==0 and not first['target_known'],first
        binary=matrix.native(folder,family+'-'+label)
        actual=capture.run('causal-'+family+'-'+label+'-native',[binary,*map(str,args)],30).decode()
        assert actual==expected
        asm=(folder/'native/main.asm').read_bytes()
        reference=('encoding' if want_export else 'off')
        reference_asm=(ROOT/'matrix-invariants'/family/reference/'native/main.asm').read_bytes()
        if label!='consumer-off':assert asm==reference_asm,(family,label,'native control mismatch')
        results.append({'family':family,'label':label,'mode':mode,'flags':flags,
                        'queries':queries,'native_sha256':hashlib.sha256(asm).hexdigest(),
                        'native_matches_reference':asm==reference_asm,'reference':reference,'stdout':actual})
        if label=='consumer-off':
            capture.ENV.update(EGGCC_SCOPED_MODE=mode,EGGCC_SCOPED_EVIDENCE=str(folder/'dag-evidence'))
            capture.run('causal-'+family+'-consumer-off-dag',[matrix.BIN,'--with-context','--run-mode','dag-optimize',
                '--run-data-out',folder/'dag.json',ROOT/'fixtures'/(family+'.bril')],180)
    normal=next(x for x in results if x['family']==family and x['label']=='normal')['queries'][0]
    removed=next(x for x in results if x['family']==family and x['label']=='reverse-off')['queries'][0]
    assert normal['program']==removed['program'],'reverse knockout changed terms or parent seed'
(ROOT/'causal-results.json').write_text(json.dumps(results,indent=2)+'\n')
