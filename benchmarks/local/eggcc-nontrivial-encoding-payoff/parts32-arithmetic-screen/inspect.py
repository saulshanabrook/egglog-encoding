#!/usr/bin/env python3
"""Extract native endpoint differences without turning diagnostic times into results."""
import collections
import difflib
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parent
report={'llvm':{},'graphs':[]}
for role in ('source','optimized','manual'):
    folder=ROOT/(role+'-native')
    llvm=(folder/'program.ll').read_text();assembly=(folder/'disassembly.txt').read_text()
    result={}
    for name in ('_main','main'):
        match=re.search(r'^define [^\n]*@'+name+r'\([^\n]*\n.*?^\}',llvm,re.M|re.S)
        assert match
        text=match.group(0)+'\n';(folder/(name+'.ll')).write_text(text)
        result[name]=dict(start_line=llvm[:match.start()].count('\n')+1,
            score99=bool(re.search(r'\bi64 99\b',text)),
            vector_i64='<2 x i64>' in text,conditional_branches=len(re.findall(r'\bbr i1\b',text)),
            sha256=hashlib.sha256(text.encode()).hexdigest())
    for name in ('__main','_main'):
        match=re.search(r'^[0-9a-f]+ <'+name+r'>:\n.*?(?=\n[0-9a-f]+ <|\Z)',assembly,re.M|re.S)
        assert match;(folder/(name+'.asm')).write_text(match.group(0)+'\n')
    report['llvm'][role]=result
for suffix in ('_main.ll','main.ll','__main.asm','_main.asm'):
    a=(ROOT/'optimized-native'/suffix).read_text();b=(ROOT/'manual-native'/suffix).read_text()
    (ROOT/(suffix+'.diff')).write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),
        fromfile='optimized-native/'+suffix,tofile='manual-native/'+suffix)))
for path in sorted((ROOT/'egraphs').glob('*.json')):
    nodes=json.loads(path.read_text())['nodes']
    high_classes=set()
    for node in nodes.values():
        if node['op']=='Bop' and nodes[node['children'][0]]['op']=='Div':high_classes.add(node['eclass'])
    candidates=[]
    for key,node in nodes.items():
        if node['op']!='Bop' or nodes[node['children'][0]]['op']!='Eq':continue
        a,b=(nodes[k]['eclass'] for k in node['children'][1:])
        if a in high_classes and b in high_classes:candidates.append(dict(id=key,**node,left_class=a,right_class=b))
    counts=collections.Counter(n['op'] for n in nodes.values())
    report['graphs'].append(dict(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        nodes=len(nodes),InIf=counts['InIf'],InLoop=counts['InLoop'],
        division_classes=sorted(high_classes),high_equalities=candidates))
receipts=[json.loads(p.read_text()) for p in (ROOT/'commands').glob('*/receipt.json')]
report['commands']=dict(count=len(receipts),successes=sum(r['exit_code']==0 for r in receipts),
    timeouts=sum(r['timed_out'] for r in receipts),elapsed_times_are_performance_evidence=False)
assert report['commands']['count']==report['commands']['successes']==78
assert report['commands']['timeouts']==0
for name in ('_main','main'):
    assert report['llvm']['source'][name]['score99']
    assert report['llvm']['optimized'][name]['score99']
    assert not report['llvm']['manual'][name]['score99']
    assert not report['llvm']['optimized'][name]['vector_i64']
    assert report['llvm']['manual'][name]['vector_i64']
(ROOT/'inspection.json').write_text(json.dumps(report,indent=2)+'\n')
(ROOT/'disposition.json').write_text(json.dumps(dict(status='retain as prospective encoding integration',
    native_target_survives=True,manual_fold_vectorizes=True,encoding_executed=False,
    timing_campaign=False,compiler_or_engine_changed=False),indent=2)+'\n')
print(json.dumps({'llvm':report['llvm'],'commands':report['commands'],
    'graphs':[(g['nodes'],len(g['high_equalities'])) for g in report['graphs']]},indent=2))
