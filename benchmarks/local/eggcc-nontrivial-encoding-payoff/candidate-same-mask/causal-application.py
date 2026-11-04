#!/usr/bin/env python3
"""Exact queried-fact application knockout; no runtime timing."""
from pathlib import Path
import importlib.util,hashlib,json,os
ROOT=Path(__file__).resolve().parent
os.environ.update(CANDIDATE_MATRIX_TAG='causal-application',CANDIDATE_BINARY=str(ROOT/'bin-causal-application/eggcc'))
s=importlib.util.spec_from_file_location('matrix',ROOT/'matrix.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
c=m.capture;c.U0=Path('/private/tmp/eggcc-same-mask-causal-control');c.ENV['EGGCC_ROOT']=str(c.U0)
rows=[]
for family,args,expected in [('cold',(0,1,1),'7\n'),('hot',(8,0,1,6),'48\n')]:
 for label,applied in [('normal',True),('application-off',False)]:
  for flag in ['EGGCC_CONTROL_REVERSE_OFF','EGGCC_CONTROL_RESCUE','EGGCC_CONTROL_CONSUMER_OFF','EGGCC_CONTROL_APPLY_OFF']:c.ENV.pop(flag,None)
  if not applied:c.ENV['EGGCC_CONTROL_APPLY_OFF']='1'
  folder=m.compile_case(family+'-'+label,'encoding',ROOT/'fixtures'/(family+'.bril'))
  data=json.loads((folder/'interp.json').read_text());assert data['original_interpreted']==data['result_interpreted']==expected
  queries=[json.loads(p.read_text()) for p in sorted((folder/'emit-evidence').glob('query-*.json'))]
  q=queries[0];assert all(q[k] for k in ['parent_known','child_known','target_known','export'])
  applications=[json.loads(p.read_text()) for p in sorted((folder/'emit-evidence').glob('application-*.json'))]
  assert applications and all(a['main_graph_union_applied']==applied and a['queried_target_returned'] and a['false_constant_materialized'] for a in applications)
  binary=m.native(folder,family+'-'+label);actual=c.run('causal-application-'+family+'-'+label+'-native',[binary,*map(str,args)],30).decode();assert actual==expected
  ref='encoding' if applied else 'off';asm=(folder/'native/main.asm').read_bytes();assert asm==(ROOT/'matrix-invariants'/family/ref/'native/main.asm').read_bytes()
  rows.append({'family':family,'label':label,'main_graph_union_applied':applied,'queries':queries,'applications':applications,'stdout':actual,'reference':ref,'native_matches_reference':True,'native_entry_sha256':hashlib.sha256(asm).hexdigest()})
 normal=next(x for x in rows if x['family']==family and x['label']=='normal')['queries'][0]
 off=next(x for x in rows if x['family']==family and x['label']=='application-off')['queries'][0]
 assert normal['program']==off['program']
(ROOT/'causal-application-results.json').write_text(json.dumps(rows,indent=2)+'\n')
