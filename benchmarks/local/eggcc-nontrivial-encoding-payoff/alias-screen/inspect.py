#!/usr/bin/env python3
"""Derive compact artifacts from the retained LLVM, native and graph captures."""
import collections
import difflib
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
report = {'llvm': {}, 'graphs': [], 'commands': {}}
for role in ('source','optimized','manual'):
    out = ROOT/(role+'-native')
    llvm = (out/'program.ll').read_text()
    assembly = (out/'disassembly.txt').read_text()
    functions = {}
    for name in ('_main','main'):
        match = re.search(r'^define [^\n]*@'+name+r'\([^\n]*\n.*?^\}',
                          llvm,re.M|re.S)
        assert match is not None
        text = match.group(0)+'\n'
        (out/(name+'.ll')).write_text(text)
        functions[name] = dict(start_line=llvm[:match.start()].count('\n')+1,
            load_i64=len(re.findall(r'\bload i64\b',text)),
            store_i64=len(re.findall(r'\bstore i64\b',text)),
            vector_adds=len(re.findall(r'\badd <2 x i64>',text)),
            sha256=hashlib.sha256(text.encode()).hexdigest())
    for name in ('__main','_main'):
        match = re.search(r'^[0-9a-f]+ <'+name+r'>:\n.*?(?=\n[0-9a-f]+ <|\Z)',
                          assembly,re.M|re.S)
        assert match is not None
        (out/(name+'.asm')).write_text(match.group(0)+'\n')
    report['llvm'][role] = functions

for suffix in ('_main.ll','main.ll','__main.asm','_main.asm'):
    baseline = (ROOT/'optimized-native'/suffix).read_text()
    manual = (ROOT/'manual-native'/suffix).read_text()
    (ROOT/(suffix+'.diff')).write_text(''.join(difflib.unified_diff(
        baseline.splitlines(True),manual.splitlines(True),
        fromfile='optimized-native/'+suffix,tofile='manual-native/'+suffix)))

for path in sorted((ROOT/'egraphs').glob('*.json')):
    nodes = json.loads(path.read_text())['nodes']
    classes = collections.defaultdict(list)
    for key,node in nodes.items():
        classes[node['eclass']].append(key)
    counts = collections.Counter(n['op'] for n in nodes.values())
    hot = []
    for key,node in nodes.items():
        if node['op'] != 'Bop':
            continue
        children = node['children']
        if not any(nodes[tag]['op']=='Load' for tag in classes[nodes[children[0]]['eclass']]):
            continue
        load = {'id':key, **node, 'state_alternatives':[], 'address_arg_paths':[]}
        for state_id in classes[nodes[children[2]]['eclass']]:
            state = nodes[state_id]
            if state['op']=='Top':
                load['state_alternatives'].append({'id':state_id, **state})
        # Preserve shortest finite graph paths to scope-bearing Arg rows. This is
        # context evidence, not a proof that loop-passthrough transport is valid.
        queue = collections.deque([(nodes[children[1]]['eclass'],[])])
        visited = set()
        found_depth = None
        while queue:
            eclass,steps = queue.popleft()
            if eclass in visited or len(steps)>8:
                continue
            visited.add(eclass)
            if found_depth is not None and len(steps)>found_depth:
                break
            for row_id in classes[eclass]:
                row = nodes[row_id]
                step = {'id':row_id, **row}
                if row['op']=='Arg':
                    found_depth=len(steps)
                    load['address_arg_paths'].append(steps+[step,{
                        'id':row['children'][1],**nodes[row['children'][1]]}])
                else:
                    for child in row['children']:
                        queue.append((nodes[child]['eclass'],steps+[step]))
        hot.append(load)
    false_eq_contexts = []
    for key,node in nodes.items():
        if node['op']!='InIf' or nodes[node['children'][0]]['op']!='false':
            continue
        pred=nodes[node['children'][1]]
        if pred['op']=='Bop' and nodes[pred['children'][0]]['op']=='Eq':
            false_eq_contexts.append({'id':key,**node,'predicate':pred,
                'left':nodes[pred['children'][1]],'right':nodes[pred['children'][2]]})
    report['graphs'].append(dict(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        nodes=len(nodes),NoAlias=counts['NoAlias'],DidMemOptimization=counts['DidMemOptimization'],
        InLoop=counts['InLoop'],InIf=counts['InIf'],loads=hot,false_eq_contexts=false_eq_contexts))

receipts = [json.loads(p.read_text()) for p in (ROOT/'commands').glob('*/receipt.json')]
report['commands'] = dict(count=len(receipts),passed=sum(
    x['exit_code']==0 and not x['timed_out'] for x in receipts),
    timeouts=sum(x['timed_out'] for x in receipts),
    elapsed_times_are_performance_evidence=False)
assert report['commands']==dict(count=43,passed=43,timeouts=0,
    elapsed_times_are_performance_evidence=False)
assert report['llvm']['source']['_main']['load_i64']==1
assert report['llvm']['optimized']['_main']['load_i64']==1
assert report['llvm']['manual']['_main']['load_i64']==0
assert report['llvm']['manual']['_main']['store_i64']==0
assert all(g['NoAlias']==0 and g['DidMemOptimization']==0 for g in report['graphs'])
(ROOT/'inspection.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='graphs'},indent=2))
print('graphs:', [(g['nodes'],g['NoAlias'],len(g['loads'])) for g in report['graphs']])
