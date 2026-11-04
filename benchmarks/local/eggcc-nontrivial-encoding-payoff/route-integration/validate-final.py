#!/usr/bin/env python3
from pathlib import Path
import importlib.util,json,re,hashlib
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('capture',BASE/'run.py');capture=importlib.util.module_from_spec(spec);spec.loader.exec_module(capture)
CANDIDATE=Path('/private/tmp/eggcc-route-candidate')
checks=[('format-final',['cargo','fmt','--all','--','--check']),('dag-format-final',['cargo','fmt','--manifest-path',str(CANDIDATE/'dag_in_context/Cargo.toml'),'--','--check']),('dag-clippy-audit-final',['cargo','clippy','--offline','--locked','--manifest-path',str(CANDIDATE/'dag_in_context/Cargo.toml'),'--tests','--','-D','warnings']),('host-clippy-final',['cargo','clippy','--offline','--locked','--tests','--','-D','warnings']),('host-make-test-final',['make','test']),('dag-library-final',['cargo','test','--offline','--locked','--manifest-path',str(CANDIDATE/'dag_in_context/Cargo.toml'),'--lib','--','--nocapture'])]
for name,argv in checks:
 if not (BASE/'commands'/name/'receipt.json').exists():capture.run(name,argv,1800,check=False)
rows={}
for name in ['focused-primitive-final','engine-focused','u0-root-clippy','host-make-test','host-make-test-disk-retry','dag-release-required',*[x[0] for x in checks]]:
 path=BASE/'commands'/name
 receipt=json.loads((path/'receipt.json').read_text());stdout=(path/'stdout').read_text();stderr=(path/'stderr').read_text()
 row=dict(disk_error_occurrences=len(re.findall('No space left on device|ENOSPC',stdout+stderr)),receipt=str((path/'receipt.json').relative_to(BASE)),argv=receipt['argv'],exit_code=receipt['exit_code'],timed_out=receipt['timed_out'],test_results=re.findall(r'test result:.*',stdout),diagnostics=[dict(message=m[0],location=m[1]) for m in re.findall(r'error: ([^\n]+)\n\s+--> ([^\n]+)',stderr)])
 rows[name]=row
snapshots=[]
for path in sorted(CANDIDATE.rglob('*.snap.new')):
 snapshots.append(dict(path=str(path.relative_to(CANDIDATE)),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
prior=json.loads((BASE.parent/'parts32-integration/eggcc-snapshot-comparison.json').read_text())
snapshot_match={Path(row['path']).name:row['sha256'] for row in snapshots}=={row['name']:row['sha256'] for row in prior}
previous=(BASE.parent/'affine-integration/commands/validation-dag-clippy-final/stderr').read_text()
previous_diags=set(re.findall(r'error: ([^\n]+)\n\s+--> ([^\n]+)',previous))
u0_clippy=(BASE/'commands/u0-root-clippy/stderr').read_text()
previous_diags.update(re.findall(r'error: ([^\n]+)\n\s+--> ([^\n]+)',u0_clippy))
for name in ['dag-clippy-audit-final','host-clippy-final']:
 for diag in rows[name]['diagnostics']:
  assert (diag['message'],diag['location']) in previous_diags,(name,diag)
 assert all('scoped_reasoning.rs' not in d['location'] for d in rows[name]['diagnostics'])
assert rows['format-final']['exit_code']==rows['dag-format-final']['exit_code']==0
assert rows['focused-primitive-final']['exit_code']==rows['engine-focused']['exit_code']==rows['dag-library-final']['exit_code']==rows['dag-release-required']['exit_code']==0
assert any('2 passed' in line for line in rows['focused-primitive-final']['test_results'])
assert any('18 passed' in line for line in rows['engine-focused']['test_results'])
assert any('66 passed' in line for line in rows['dag-library-final']['test_results'])
assert any('66 passed' in line for line in rows['dag-release-required']['test_results'])
result=dict(status='supporting_only_host_validation_failed' if rows['host-make-test-disk-retry']['exit_code'] else 'host_test_passed',required_host_make_test='host-make-test-disk-retry',resource_contaminated_runs=[name for name,row in rows.items() if row['disk_error_occurrences']],checks=rows,new_lint_diagnostics=0,snapshots_accepted=False,pending_snapshots=snapshots,pending_snapshots_match_frozen_parts32=snapshot_match,engine_full_check_reused= json.loads((BASE/'engine-reuse.json').read_text())['previous_check'],timing_campaign=False,qualification='Supporting mechanism/native evidence only; no compiler bug or measured speedup claimed.')
(BASE/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['checks','pending_snapshots']},indent=2))
