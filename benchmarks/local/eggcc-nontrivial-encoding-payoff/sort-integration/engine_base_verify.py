#!/usr/bin/env python3
"""Verify selected engine code equals its immutable Git base plus five frozen changes."""
from pathlib import Path
import hashlib,json,subprocess
BASE=Path(__file__).resolve().parent
ENGINE=Path('/private/tmp/encoding-sort-candidate')
REPOSITORY=Path('/Users/saul/p/egglog-encoding')
REVISION='392b6d6b48b5bc307a5b9c981c957fc0a09e23e5'
def main():
    argv=['git','-C',str(REPOSITORY),'ls-tree','-r','-z',REVISION]
    raw=subprocess.check_output(argv);tree={}
    for entry in raw.split(b'\0'):
        if entry:
            meta,name=entry.split(b'\t');tree[name.decode()]=meta.split()[2].decode()
    changed=[];not_in_base=[];checked=0
    for path in sorted(ENGINE.rglob('*')):
        if not path.is_file() or 'target' in path.parts or '.git' in path.parts:continue
        name=str(path.relative_to(ENGINE));data=path.read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if name not in tree:not_in_base.append(name)
        elif tree[name]!=actual:changed.append(name)
        checked+=1
    logs=[name for name in not_in_base if name.startswith('egglog/output.') and name.endswith('.log')]
    new_source=[name for name in not_in_base if name not in logs]
    frozen=json.loads((BASE.parent/'parts32-integration/final-source-identities.json').read_text())
    expected={row['archive_path'].removeprefix('encoding/'):row['sha256'] for row in frozen['files'] if row.get('archive_path','').startswith('encoding/')}
    assert set(changed+new_source)==set(expected)
    assert all(hashlib.sha256((ENGINE/name).read_bytes()).hexdigest()==expected[name] for name in expected)
    result={'status':'passed','base':REVISION,'argv':argv,'git_tree_stdout_sha256':hashlib.sha256(raw).hexdigest(),'retained_files_checked':checked,'generated_logs_not_in_base':logs,'new_source_not_in_base':new_source,'source_differences_from_base':changed,'changed_and_new_source_hashes_equal_frozen_parts32':expected,'unchanged_code_and_manifest_files_at_base':checked-len(logs)-len(expected),'scope':'selected Rust dependency source and manifests; unchanged root Python code is outside the copied dependency closure'}
    (BASE/'engine-base-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','retained_files':checked,'base_files':result['unchanged_code_and_manifest_files_at_base'],'frozen_changes':len(expected),'generated_logs':len(logs)}))
if __name__=='__main__':main()
