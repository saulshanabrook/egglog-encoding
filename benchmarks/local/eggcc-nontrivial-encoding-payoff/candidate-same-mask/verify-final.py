#!/usr/bin/env python3
"""Audit retained evidence only; no compiler/native/timing executions."""
from pathlib import Path
import hashlib,json,tarfile
ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(ROOT/'bin-invariants/eggcc')=='5343e3352f74e4e7ec80082a1e47912019d2f37bc641f2ed62891267e465fb87'
assert sha(ROOT/'fixtures/hot.bril')=='f4448682f67a73ab98677b1c997f419175999f4c221e297f1a443e6c95f856dd'
with tarfile.open(ROOT/'invariants-source.tar') as archive:
 for name in archive.getnames():
  data=archive.extractfile(name).read();assert (ROOT/'source/eggcc'/name).read_bytes()==data
  assert (Path('/private/tmp/eggcc-same-mask-candidate')/name).read_bytes()==data
for row in json.loads((ROOT/'source-admission.json').read_text())['retained_e1_delta']:
 assert sha(ROOT/'source/engine'/row['path'])==row['copy_sha256']
 assert sha(Path('/private/tmp/encoding-same-mask-candidate')/row['path'])==row['copy_sha256']
for family in ['cold','hot']:
 base=ROOT/'matrix-invariants'/family
 assert (base/'encoding/optimized.bril').read_bytes()==(base/'manual/optimized.bril').read_bytes()
 assert (base/'encoding/native/main.asm').read_bytes()==(base/'manual/native/main.asm').read_bytes()
 assert (base/'off/optimized.bril').read_bytes()==(ROOT/'matrix-supplement'/(family+'-u0')/'off/optimized.bril').read_bytes()
 assert (base/'off/native/main.asm').read_bytes()==(ROOT/'matrix-supplement'/(family+'-u0')/'off/native/main.asm').read_bytes()
 for mode in ['seed-only','annotation-off','query-off','bridge-off']:
  assert (base/mode/'native/main.asm').read_bytes()==(base/'off/native/main.asm').read_bytes()
controls=json.loads((ROOT/'causal-results.json').read_text())
apps=json.loads((ROOT/'causal-application-results.json').read_text())
for family in ['cold','hot']:
 group={r['label']:r for r in controls if r['family']==family}
 assert all(r['native_matches_reference'] for k,r in group.items() if k!='consumer-off')
 assert group['normal']['queries'][0]['program']==group['reverse-off']['queries'][0]['program']
 q=group['reverse-off']['queries'][0];assert q['parent_known'] and not q['child_known'] and not q['target_known'] and not q['export']
 q=group['reverse-rescue']['queries'][0];assert q['parent_known'] and q['child_known'] and q['target_known'] and q['export'] and q['control_rescue_fact']
 q=group['annotation-off']['queries'][0];assert q['child_known'] and not q['target_known'] and not q['export']
 q=group['annotation-rescue']['queries'][0];assert q['child_known'] and q['target_known'] and q['export'] and q['control_rescue_fact']
 q=group['primitive-null']['queries'][0];assert q['word_constructor_primitive_fields']==0 and not q['target_known'] and not q['export']
 agroup={r['label']:r for r in apps if r['family']==family};assert agroup['normal']['queries'][0]['program']==agroup['application-off']['queries'][0]['program']
 for label,row in agroup.items():
  q=row['queries'][0];assert all(q[k] for k in ['parent_known','child_known','target_known','export'])
  assert row['native_matches_reference'] and row['main_graph_union_applied']==(label=='normal')
  assert all(a['queried_target_returned'] and a['false_constant_materialized'] and a['main_graph_union_applied']==(label=='normal') for a in row['applications'])
confirm=json.loads((ROOT/'confirmation-summary.json').read_text());assert confirm['prospective_runtime_gate_passed']
cycles=json.loads((ROOT/'confirmation-cycles.json').read_text())['cycles'];assert len(cycles)==32
for row in cycles:
 assert set(row['observations'])=={'U0','B1','Manual','Encoding'}
 assert all(r['correct'] and r['exit_code']==0 and not r['timed_out'] and r['stdout']=='1200000000\n' for r in row['observations'].values())
comp=[json.loads(line) for line in (ROOT/'compile-diagnostic-samples.jsonl').read_text().splitlines()]
assert len(comp)==55
for arm in ['U0','B1','SeedOnly','Manual','Encoding']:
 rows=[r for r in comp if r['arm']==arm and r['phase']=='measure'];assert len(rows)==10
 assert all(r['exit_code']==0 and not r['timed_out'] and r['emission_exact'] for r in rows)
validation=json.loads((ROOT/'full-validation-results.json').read_text());assert not validation['all_required_gates_green'] and validation['engine_make_check_green'] and validation['pending_snapshots']==13 and not validation['snapshots_accepted']
assert json.loads((ROOT/'snapshot-attribution-current.json').read_text())['all_match_dependency_only_historical_control']
result={'evidence_audit_passed':True,'new_compiler_or_native_executions':0,'selected_sources_and_binary_unchanged':True,'causal_controls_verified':True,'confirmation_complete_cycles':32,'compile_diagnostic_measurements_per_arm':10,'runtime_microbenchmark_gate_passed':True,'full_eggcc_integration_gates_green':False,'qualification_and_goal_completion':'parent-owned; no new bug and no suite-wide claim'}
(ROOT/'final-evidence-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
