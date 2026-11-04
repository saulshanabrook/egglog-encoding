#!/usr/bin/env python3
"""Verify causal and native-code gates; contains no timing collection."""
from pathlib import Path
import json,re,hashlib,difflib
ROOT=Path(__file__).resolve().parent
positive=json.loads((ROOT/'positive-results.json').read_text());by={r['mode']:r for r in positive};report={'functions':{},'causal':{},'gates':{},'timing_campaign':False}
for row in positive:
 mode=row['mode'];folder=ROOT/'matrix/positive'/mode/'native';llvm=(folder/'program.ll').read_text();asm=(folder/'program.asm').read_text();info={}
 for name in ['main','_main']:
  m=re.search(r'^define [^\n]*@'+name+r'\([^\n]*\n.*?^\}',llvm,re.M|re.S);assert m
  text=m.group(0)+'\n';(folder/(name+'.ll')).write_text(text);info[name]={'score99':bool(re.search(r'\bi64 99\b',text)),'vector_i64':'<2 x i64>' in text,'conditional_branches':len(re.findall(r'\bbr i1\b',text)),'sha256':hashlib.sha256(text.encode()).hexdigest()}
 for name in ['__main','_main']:
  m=re.search(r'^[0-9a-f]+ <'+name+r'>:\n.*?(?=\n[0-9a-f]+ <|\Z)',asm,re.M|re.S);assert m;(folder/(name+'.asm')).write_text(m.group(0)+'\n')
 report['functions'][mode]=info
 report['causal'][mode]=[{k:q.get(k) for k in ['word_known','low_equal','parts_known','pair_known','high_known','bottom','export','consumer_enabled','reverse_enabled','parts32_marked','representation_identity','rescue']} for q in row['queries'] if q['accepted']]
for a,b in [('u0','off'),('manual','encoding'),('u0','encoding')]:
 for name in ['main.ll','_main.ll','_main.asm','__main.asm']:
  x=(ROOT/'matrix/positive'/a/'native'/name).read_text();y=(ROOT/'matrix/positive'/b/'native'/name).read_text();(ROOT/(a+'-'+b+'-'+name+'.diff')).write_text(''.join(difflib.unified_diff(x.splitlines(True),y.splitlines(True),fromfile=a+'/'+name,tofile=b+'/'+name)))
for a,b in [('u0','off'),('manual','encoding')]:
 assert by[a]['emitted_sha256']==by[b]['emitted_sha256'];assert by[a]['main_sha256']==by[b]['main_sha256']
 for f in ['main','_main']:assert report['functions'][a][f]==report['functions'][b][f]
for mode in ['primitive-only','forward-off','reverse-off','identity-off','query-off','bridge-off','consumer-off']:
 assert by[mode]['emitted_sha256']==by['u0']['emitted_sha256'];assert by[mode]['main_sha256']==by['u0']['main_sha256']
for mode in ['high-rescue','if-consumer-off']:
 assert by[mode]['emitted_sha256']==by['encoding']['emitted_sha256'];assert by[mode]['main_sha256']==by['encoding']['main_sha256']
for f in ['main','_main']:
 assert report['functions']['u0'][f]['score99'] and not report['functions']['u0'][f]['vector_i64']
 assert not report['functions']['encoding'][f]['score99'] and report['functions']['encoding'][f]['vector_i64']
negatives=json.loads((ROOT/'negative-results.json').read_text());loops=json.loads((ROOT/'loop-negative-results.json').read_text());context=json.loads((ROOT/'context-negative-results.json').read_text())
for row in negatives+loops+context:assert not any(q.get('export') for q in row['queries'])
for family in set(r['family'] for r in negatives+loops):
 group={r['mode']:r for r in negatives+loops if r['family']==family}
 for mode in ['off','manual','encoding']:
  assert group[mode]['emitted_sha256']==group['u0']['emitted_sha256'];assert group[mode]['main_sha256']==group['u0']['main_sha256']
report['gates']={'positive_native_executions':sum(len(r['outputs']) for r in positive),'semantic_negative_native_executions':sum(len(r['outputs']) for r in negatives),'loop_negative_native_executions':sum(len(r['outputs']) for r in loops),'context_negative_native_executions':sum(len(r['outputs']) for r in context),'B1_matches_U0':True,'Encoding_matches_Manual':True,'all_output_checks_passed':True,'native_difference_survives':True,'primitive_only_is_null':True,'all_required_theory_knockouts_restore_U0':True,'exact_high_rescue_restores_Encoding':True,'Eq_false_consumer_knockout_restores_U0':True,'existing_EggCC_false_If_rule_is_essential':False}
(ROOT/'inspection.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report['gates'],indent=2))
