#!/usr/bin/env python3
"""Read-only acceptance audit of the frozen Route integration artifacts."""
from pathlib import Path
import hashlib,json,re,tarfile
BASE=Path(__file__).resolve().parent

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def read(name):return json.loads((BASE/name).read_text())
def main():
 identities=read('identities.json')
 for row in identities['files']:
  path=Path(row['path']);assert path.is_file(),path
  assert digest(path)==row['sha256'],path
 for label,root in identities['source_roots'].items():
  for name,expected in identities['source_files'][label].items():
   assert digest(Path(root)/name)==expected,(label,name)
 for label in ['candidate','engine']:
  with tarfile.open(BASE/(label+'-source.tar')) as archive:
   archived={member.name.removeprefix(label+'/'):hashlib.sha256(archive.extractfile(member).read()).hexdigest() for member in archive if member.isfile() or member.islnk()}
  assert archived==identities['source_files'][label],label
 positive={row['mode']:row for row in read('positive-results.json')}
 baseline=positive['u0'];optimized=positive['encoding']
 null=['off','seed-only','primitive-only','cancellation-off','identity-off','reverse-off','forward-off','query-off','bridge-off','application-off']
 for mode in null:
  assert positive[mode]['emitted_sha256']==baseline['emitted_sha256'],mode
  assert positive[mode]['main_sha256']==baseline['main_sha256'],mode
 for mode in ['manual','equality-rescue','disequality-rescue']:
  assert positive[mode]['emitted_sha256']==optimized['emitted_sha256'],mode
  assert positive[mode]['main_sha256']==optimized['main_sha256'],mode
 assert optimized['emitted_sha256']!=baseline['emitted_sha256']
 assert optimized['main_sha256']!=baseline['main_sha256']
 accepted={mode:[q for q in row['queries'] if q.get('accepted')] for mode,row in positive.items() if mode!='u0'}
 for mode in ['encoding','manual','equality-rescue','disequality-rescue','application-off']:
  assert accepted[mode] and any(q['target_known_disequal'] and q['export'] for q in accepted[mode]),mode
 for mode in ['encoding','manual']:
  q=accepted[mode][0];assert q['a_equal_c'] and q['z_known_disequal_w'] and not q['bottom'],mode
 q=accepted['cancellation-off'][0];assert not q['a_equal_c'] and not q['z_known_disequal_w']
 q=accepted['identity-off'][0];assert q['pair_equal'] and not q['key_equal'] and not q['a_equal_c']
 q=accepted['reverse-off'][0];assert q['a_equal_c'] and not q['z_known_disequal_w']
 q=accepted['forward-off'][0];assert q['z_known_disequal_w'] and not q['target_known_disequal']
 q=accepted['equality-rescue'][0];assert not q['route_marked'] and q['intermediate_equality_rescue'] and q['a_equal_c'] and not q['b_equal_d'] and q['z_known_disequal_w']
 q=accepted['disequality-rescue'][0];assert not q['route_marked'] and not q['reverse_enabled'] and q['intermediate_disequality_rescue'] and not q['a_equal_c'] and q['z_known_disequal_w']
 q=accepted['query-off'][0];assert q['z_known_disequal_w'] and q['target_known_disequal'] is None and not q['export']
 q=accepted['bridge-off'][0];assert q['target_known_disequal'] and not q['export']
 q=accepted['application-off'][0];assert q['target_known_disequal'] and q['export'] and not q['application_enabled']
 primitive=accepted['primitive-only'][0];seed=accepted['seed-only'][0];encoding=accepted['encoding'][0]
 assert primitive['program']==seed['program']==encoding['program'].removesuffix('(run-schedule (saturate injectivity))\n')
 assert primitive['primitive_only_same_rows_seeds_identities'] and not primitive['primitive_only_equality_sort_reasoning']
 assert not primitive['engine_witness_queries_run'] and not primitive['export']
 assert primitive['fixed_primitive_column_comparisons']==dict(compared=8,equal=8,unequal=0,column='OddMul.coefficient',values=[3,3])
 native_summary=read('native-summary.json')
 for mode,row in native_summary.items():
  body=(BASE/'matrix/positive'/mode/'native/_main.ll').read_text()
  assert row['eq_i64']==body.count('icmp eq i64')
  assert row['conditional_branches']==len(re.findall(r'^\s+br i1',body,re.M))
  assert row['target99']==('i64 99' in body)
 assert native_summary['u0']['eq_i64']==4 and native_summary['encoding']['eq_i64']==3
 assert native_summary['u0']['target99'] and not native_summary['encoding']['target99']
 assert native_summary['u0']['native99'] and not native_summary['encoding']['native99']
 negative=read('negative-results.json')
 for family in {row['family'] for row in negative}:
  rows={row['mode']:row for row in negative if row['family']==family}
  for mode,row in rows.items():
   assert row['emitted_sha256']==rows['u0']['emitted_sha256'],(family,mode)
   assert row['main_sha256']==rows['u0']['main_sha256'],(family,mode)
   assert not any(q.get('export') for q in row['queries']),(family,mode)
 for row in read('context-negative-results.json'):
  assert not any(q.get('export') for q in row['queries'])
 for row in [*positive.values(),*negative,*read('context-negative-results.json'),*read('source-native-results.json')]:
  for output in row['outputs']:assert output['stdout']==output['expected']
 commands=[]
 for path in sorted((BASE/'commands').glob('*/receipt.json')):
  row=json.loads(path.read_text())
  for suffix in ['stdout','stderr']:assert digest(path.parent/suffix)==row[suffix+'_sha256'],path
  for file in row['files']:assert digest(Path(file['path']))==file['sha256'] or path.parent.name in identities['historical_mutable_command_inputs'],(path,file)
  commands.append(row)
 result=dict(status='audit_passed',positive_modes=len(positive),positive_native_outputs=sum(len(r['outputs']) for r in positive.values()),negative_native_outputs=sum(len(r['outputs']) for r in negative),context_negative_outputs=sum(len(r['outputs']) for r in read('context-negative-results.json')),source_native_outputs=sum(len(r['outputs']) for r in read('source-native-results.json')),interpretations=read('verification.json')['count'],command_receipts=len(commands),validation=read('validation.json')['status'],measured_speedup=False,preexisting_bug=False)
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
