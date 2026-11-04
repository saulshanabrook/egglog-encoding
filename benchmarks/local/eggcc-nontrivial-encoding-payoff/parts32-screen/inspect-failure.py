#!/usr/bin/env python3
"""Preserve the failed extraction graph and inspect the missing typing premise."""
import collections
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
U0=Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
crash=Path('/var/folders/x4/rfvvhxcd53lft2b9844dw1lr0000gn/T/tiger-crash-7PJvpD.json')
raw=crash.read_bytes()
(ROOT/'tiger-crash.json').write_bytes(raw)
graph=json.loads(raw)
nodes=graph['nodes']
classes=collections.defaultdict(list)
for key,node in nodes.items():classes[node['eclass']].append(key)
typed={nodes[n['children'][0]]['eclass'] for n in nodes.values() if n['op']=='HasType'}
shifts=[]
for key,node in nodes.items():
    if node['op']=='Bop' and nodes[node['children'][0]]['op']=='Shr':
        shifts.append(dict(id=key,**node,has_type=node['eclass'] in typed,
            operand_types=[nodes[c]['eclass'] in typed for c in node['children'][1:]]))
source=U0/'dag_in_context/src/type_analysis.egg'
text=source.read_text()
assert '(bop-of-type (Shr)' not in text and '(bop-of-type (Shl)' not in text
assert shifts and all(not row['has_type'] for row in shifts)
assert 'Expr-720' not in typed
oracle=json.loads((ROOT/'oracle.json').read_text())
before=(ROOT/'source.bril').read_text()
for row in oracle['negative_rows']:
    kind=row['kind'];out=ROOT/kind;out.mkdir(exist_ok=False)
    fixture=before.replace('# ARGS: 0 4294967296 8','# ARGS: '+' '.join(map(str,row['args'])))
    if kind=='missing-word-disequality':
        fixture=fixture.replace('  br same_word .same_word .different_word;','  jmp .different_word;')
    elif kind=='wrong-width':
        fixture=fixture.replace('  shift: int = const 32;','  shift: int = const 33;')
    elif kind=='unequal-widths':
        fixture=fixture.replace('  hy: int = shr y shift;',
            '  other_shift: int = const 16;\n  hy: int = shr y other_shift;')
    else:fixture=fixture.replace('  br same_low .same_low .different_low;','  jmp .same_low;')
    (out/'source.bril').write_text(fixture)
    (out/'status.json').write_text(json.dumps(dict(status='oracle only; not compiler executed',**row),indent=2)+'\n')
paths=[source,U0/'src/rvsdg/to_dag.rs',U0/'src/rvsdg/from_dag.rs',
    U0/'dag_in_context/src/interpreter.rs',U0/'dag_in_context/src/schema.egg']
result=dict(disposition='closed at direct-Shr IR gate; no emitted/native comparison',
    original_crash_path=str(crash),crash_sha256=hashlib.sha256(raw).hexdigest(),
    graph_nodes=len(nodes),shift_rows=shifts,affected_function_body='Expr-720',
    affected_body_has_type=False,
    shift_bop_type_fact_in_source=False,
    sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
    commands=dict(count=3,successes=2,failed_optimizer=1,native=0,timeouts=0),
    negative_fixtures='retained, oracle validated, not compiler executed')
(ROOT/'failure-inspection.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'disposition.json').write_text(json.dumps(dict(status='closed',
    reason='U0 direct Shr expression has no HasType and cannot be extracted',
    compiler_or_engine_changed=False,timing_campaign=False,native_runs=0,
    encoding_payoff=False),indent=2)+'\n')
print(json.dumps(result,indent=2))
