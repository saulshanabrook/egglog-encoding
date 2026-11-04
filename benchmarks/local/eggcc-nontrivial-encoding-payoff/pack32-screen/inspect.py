#!/usr/bin/env python3
"""Derive compact function/code differences and source-pattern graph receipts."""
import collections
import difflib
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parent
report={'llvm':{},'graphs':[]}
for role in ('source','optimized','manual'):
    out=ROOT/(role+'-native')
    llvm=(out/'program.ll').read_text()
    assembly=(out/'disassembly.txt').read_text()
    result={}
    for name in ('_main','main'):
        match=re.search(r'^define [^\n]*@'+name+r'\([^\n]*\n.*?^\}',llvm,re.M|re.S)
        assert match
        text=match.group(0)+'\n';(out/(name+'.ll')).write_text(text)
        result[name]=dict(start_line=llvm[:match.start()].count('\n')+1,
            compare_eq_i64=len(re.findall(r'\bicmp eq i64\b',text)),
            score99=bool(re.search(r'\bi64 99\b',text)),
            conditional_branches=len(re.findall(r'\bbr i1\b',text)),
            sha256=hashlib.sha256(text.encode()).hexdigest())
    for name in ('__main','_main'):
        match=re.search(r'^[0-9a-f]+ <'+name+r'>:\n.*?(?=\n[0-9a-f]+ <|\Z)',assembly,re.M|re.S)
        assert match
        (out/(name+'.asm')).write_text(match.group(0)+'\n')
    report['llvm'][role]=result
for suffix in ('_main.ll','main.ll','__main.asm','_main.asm'):
    baseline=(ROOT/'optimized-native'/suffix).read_text()
    manual=(ROOT/'manual-native'/suffix).read_text()
    (ROOT/(suffix+'.diff')).write_text(''.join(difflib.unified_diff(
        baseline.splitlines(True),manual.splitlines(True),
        fromfile='optimized-native/'+suffix,tofile='manual-native/'+suffix)))
for path in sorted((ROOT/'egraphs').glob('*.json')):
    nodes=json.loads(path.read_text())['nodes']
    classes=collections.defaultdict(list)
    for key,node in nodes.items():
        classes[node['eclass']].append(key)
    constants=collections.defaultdict(set)
    for key,node in nodes.items():
        if node['op']!='Const':continue
        for value in classes[nodes[node['children'][0]]['eclass']]:
            int_node=nodes[value]
            if int_node['op']=='Int':
                for literal in classes[nodes[int_node['children'][0]]['eclass']]:
                    if literal.startswith('primitive-i64-'):
                        constants[node['eclass']].add(int(nodes[literal]['op']))
    translated=collections.defaultdict(set)
    multiplies=collections.defaultdict(set)
    for key,node in nodes.items():
        if node['op']!='Bop':continue
        tag=nodes[node['children'][0]]['op']
        a,b=(nodes[x]['eclass'] for x in node['children'][1:])
        if tag=='Add':
            if 7 in constants[a]:translated[node['eclass']].add(b)
            if 7 in constants[b]:translated[node['eclass']].add(a)
        if tag=='Mul':
            if 1<<32 in constants[a]:multiplies[node['eclass']].add(b)
            if 1<<32 in constants[b]:multiplies[node['eclass']].add(a)
    packed=[];targets=[]
    for key,node in nodes.items():
        if node['op']!='Bop':continue
        tag=nodes[node['children'][0]]['op']
        a,b=(nodes[x]['eclass'] for x in node['children'][1:])
        if tag=='Add':
            for high,low in ((a,b),(b,a)):
                for field in multiplies[high]:
                    packed.append(dict(row=key,packed_class=node['eclass'],high=field,low=low))
        if tag=='Eq' and translated[a] and translated[b]:
            targets.append(dict(row=key,predicate_class=node['eclass'],
                left_children=sorted(translated[a]),right_children=sorted(translated[b]),
                equivalent_eq_rows=[dict(id=k,**nodes[k]) for k in classes[node['eclass']]
                    if nodes[k]['op']=='Bop' and nodes[nodes[k]['children'][0]]['op']=='Eq']))
    report['graphs'].append(dict(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        nodes=len(nodes),packed_patterns=packed,translated_target_equalities=targets))
receipts=[json.loads(p.read_text()) for p in (ROOT/'commands').glob('*/receipt.json')]
report['commands']=dict(count=len(receipts),successes=sum(r['exit_code']==0 for r in receipts),
    timeouts=sum(r['timed_out'] for r in receipts),elapsed_times_are_performance_evidence=False)
assert report['commands']['count']==report['commands']['successes']==64
assert report['commands']['timeouts']==0
assert report['llvm']['source']['_main']['score99']
assert report['llvm']['optimized']['_main']['score99']
assert not report['llvm']['manual']['_main']['score99']
assert any(g['translated_target_equalities'] for g in report['graphs'])
(ROOT/'inspection.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'llvm':report['llvm'],'commands':report['commands'],
    'graph_summary':[(g['nodes'],len(g['packed_patterns']),len(g['translated_target_equalities']))
        for g in report['graphs']]},indent=2))
