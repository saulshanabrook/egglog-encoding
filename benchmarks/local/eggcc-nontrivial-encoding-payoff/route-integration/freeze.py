#!/usr/bin/env python3
"""Freeze exact final source, binary, command, fixture and report identities."""
from pathlib import Path
import difflib,hashlib,json,platform,tarfile
BASE=Path(__file__).resolve().parent
ROOTS={'u0':Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0'),'candidate':Path('/private/tmp/eggcc-route-candidate'),'engine':Path('/private/tmp/encoding-route-candidate')}
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def source(root):return {str(p.relative_to(root)):digest(p) for p in root.rglob('*') if p.is_file() and 'target' not in p.parts and '.git' not in p.parts and not p.name.endswith('.snap.new')}
def main():
 sources={name:source(root) for name,root in ROOTS.items()}
 admitted=json.loads((BASE.parent/'admission/source-files.json').read_text())
 assert all(sources['u0'][name]==value for name,value in admitted.items())
 engine=json.loads((BASE/'engine-reuse.json').read_text())
 assert sources['engine']==engine['source_files']
 for name in ['candidate','engine']:
  path=BASE/(name+'-source.tar')
  with tarfile.open(path,'w') as archive:
   for relative in sorted(sources[name]):archive.add(ROOTS[name]/relative,arcname=name+'/'+relative,recursive=False)
 changed=[name for name in sorted(sources['u0'].keys()|sources['candidate'].keys()) if sources['u0'].get(name)!=sources['candidate'].get(name)]
 assert changed==['Cargo.lock','Cargo.toml','dag_in_context/Cargo.lock','dag_in_context/Cargo.toml','dag_in_context/src/lib.rs','dag_in_context/src/scoped_reasoning.rs'],changed
 patch=''
 for relative in changed:
  old=ROOTS['u0']/relative;new=ROOTS['candidate']/relative
  patch+=''.join(difflib.unified_diff(old.read_text().splitlines(True) if old.exists() else [],new.read_text().splitlines(True),fromfile='a/'+relative if old.exists() else '/dev/null',tofile='b/'+relative))
 (BASE/'candidate.patch').write_text(patch)
 tracked=[p for p in BASE.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name not in ['identities.json','inspection.json']]
 tracked += [BASE.parent/'admission/bin/eggcc',BASE.parent/'admission/bin/tiger',Path(engine['previous_check']),BASE.parent/'parts32-integration/final-source-identities.json',BASE.parent/'parts32-integration/final-source.tar',BASE.parent/'parts32-integration/encoding-parts32-candidate.tar',BASE.parent/'parts32-integration/source-admission.json']
 result=dict(u0_revision='a0bbec127f83249074a46af3fd6f6126c90fe0fb',source_roots={name:str(path) for name,path in ROOTS.items()},source_files=sources,candidate_changed_files=changed,admitted_u0_files_checked=len(admitted),engine_files_byte_identical_to_prior_check=len(sources['engine']),machine=platform.platform(),timing_campaign=False,historical_mutable_command_inputs=[],files=[dict(path=str(path.resolve()),sha256=digest(path)) for path in sorted(set(tracked))])
 (BASE/'identities.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ['source_files','files']},indent=2))
if __name__=='__main__':main()
