#!/usr/bin/env python3
"""Freeze source/binary identities and a complete command-output evidence manifest."""
from pathlib import Path
import difflib,hashlib,json,tarfile,platform
BASE=Path(__file__).resolve().parent
HOST=Path('/private/tmp/eggcc-sort-candidate')
ENGINE=Path('/private/tmp/encoding-sort-candidate')
U0=Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
REFERENCE=Path('/private/tmp/encoding-parts32-candidate')
def sources(root):
 return {str(p.relative_to(root)):hashlib.sha256((p).read_bytes()).hexdigest() for p in sorted(root.rglob('*')) if p.is_file() and not ({'target','.git','.venv','.uv-cache','__pycache__'} & set(p.parts)) and not p.name.endswith('.snap.new')}
def main():
 admission=json.loads((BASE.parent/'admission/source-files.json').read_text())
 assert all(hashlib.sha256((U0/n).read_bytes()).hexdigest()==v for n,v in admission.items())
 manifests={'host':sources(HOST),'engine':sources(ENGINE)}
 assert all((REFERENCE/n).is_file() and hashlib.sha256((REFERENCE/n).read_bytes()).hexdigest()==v for n,v in manifests['engine'].items())
 frozen=json.loads((BASE.parent/'parts32-integration/final-source-identities.json').read_text())
 assert hashlib.sha256((Path(frozen['source_archive'])).read_bytes()).hexdigest()==frozen['source_archive_sha256']
 for row in frozen['files']:
  if row.get('archive_path','').startswith('encoding/'):
   assert hashlib.sha256((ENGINE/row['archive_path'].removeprefix('encoding/')).read_bytes()).hexdigest()==row['sha256']
 sourcefile=BASE/'source-files.json'
 if sourcefile.exists():assert json.loads(sourcefile.read_text())==manifests,'frozen source changed'
 else:sourcefile.write_text(json.dumps(manifests,indent=2)+'\n')
 for name,root in [('host',HOST),('engine',ENGINE)]:
  archive=BASE/f'{name}-source.tar'
  if not archive.exists():
   with tarfile.open(archive,'w') as output:
    for n in manifests[name]:output.add(root/n,arcname=f'{name}/{n}',recursive=False)
  with tarfile.open(archive) as contents:
   actual={m.name.removeprefix(name+'/'):hashlib.sha256(contents.extractfile(m).read()).hexdigest() for m in contents if m.isfile()}
  assert actual==manifests[name]
 upstream=sources(U0)
 changed=[n for n in sorted(set(upstream)|set(manifests['host'])) if upstream.get(n)!=manifests['host'].get(n)]
 assert changed==['Cargo.lock','Cargo.toml','dag_in_context/Cargo.lock','dag_in_context/Cargo.toml','dag_in_context/src/lib.rs','dag_in_context/src/scoped_reasoning.rs'],changed
 patch=''
 for name in changed:
  old=(U0/name).read_text().splitlines(True) if (U0/name).exists() else []
  new=(HOST/name).read_text().splitlines(True)
  patch+=''.join(difflib.unified_diff(old,new,fromfile='a/'+name,tofile='b/'+name))
 (BASE/'candidate.patch').write_text(patch)
 files={str(p.relative_to(BASE)):hashlib.sha256((p).read_bytes()).hexdigest() for p in sorted(BASE.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.name not in {'identities.json','inspection.json'}}
 commands=[]
 for p in sorted((BASE/'commands').glob('*/receipt.json')):
  row=json.loads(p.read_text());out=p.parent
  assert hashlib.sha256((out/'stdout').read_bytes()).hexdigest()==row['stdout_sha256']
  assert hashlib.sha256((out/'stderr').read_bytes()).hexdigest()==row['stderr_sha256']
  commands.append({'label':out.name,'receipt_sha256':hashlib.sha256((p).read_bytes()).hexdigest(),'argv_sha256':hashlib.sha256(json.dumps(row['argv'],separators=(',',':')).encode()).hexdigest(),'environment_sha256':hashlib.sha256(json.dumps({'environment':row['environment'],'scoped_mode':row.get('scoped_mode'),'scoped_evidence':row.get('scoped_evidence')},sort_keys=True,separators=(',',':')).encode()).hexdigest(),'exit_code':row['exit_code'],'timed_out':row['timed_out']})
 receipt=BASE.parent/'parts32-integration/commands/engine-make-check-process-access/receipt.json'
 r=json.loads(receipt.read_text());assert r['exit_code']==0 and not r['timed_out']
 result={'u0_revision':'a0bbec127f83249074a46af3fd6f6126c90fe0fb','engine_e1_base':'392b6d6b48b5bc307a5b9c981c957fc0a09e23e5','admitted_u0_files_verified':len(admission),'host_source_files':len(manifests['host']),'host_changed_files':changed,'semantic_changes':changed[-2:],'engine_files_byte_equal_parts32':len(manifests['engine']),'engine_frozen_changed_files_verified':5,'engine_full_check_reused':{'path':str(receipt),'sha256':hashlib.sha256((receipt).read_bytes()).hexdigest()},'source_manifests_sha256':hashlib.sha256((sourcefile).read_bytes()).hexdigest(),'host_binary_sha256':hashlib.sha256((BASE/'bin/eggcc').read_bytes()).hexdigest(),'u0_binary_sha256':hashlib.sha256((BASE.parent/'admission/bin/eggcc').read_bytes()).hexdigest(),'machine':platform.platform(),'files':files,'commands':commands,'semantic_revisions':0,'environmental_retries':1,'timing_campaign':False}
 (BASE/'identities.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['host_source_files','engine_files_byte_equal_parts32','host_binary_sha256','semantic_revisions','timing_campaign']}))
if __name__=='__main__':main()
