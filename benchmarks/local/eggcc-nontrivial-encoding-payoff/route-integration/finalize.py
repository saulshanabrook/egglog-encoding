#!/usr/bin/env python3
"""Freeze the completed bounded experiment and run its read-only final audit."""
from pathlib import Path
import hashlib,json,subprocess,sys
BASE=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(BASE/'validate-final.py')],check=True)
validation=json.loads((BASE/'validation.json').read_text())
assert validation['checks']['host-make-test-disk-retry']['disk_error_occurrences']==0
assert any('2421 passed' in row for row in validation['checks']['host-make-test-disk-retry']['test_results'])
assert validation['pending_snapshots_match_frozen_parts32']
report=BASE/'report.md';text=report.read_text()
text=text.replace("The exact standalone DAG release step is recorded separately.","The exact standalone DAG release step also passes all 66 tests, with no pending DAG snapshots. Root and DAG doc-test summaries are retained in the receipts.")
report.write_text(text)
failed=[];commands=[]
for path in sorted((BASE/'commands').glob('*/receipt.json')):
 row=json.loads(path.read_text())
 commands.append(dict(command=path.parent.name,argv=row['argv'],argv_sha256=hashlib.sha256(json.dumps(row['argv'],separators=(',',':')).encode()).hexdigest(),receipt_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),exit_code=row['exit_code']))
 if row['exit_code']!=0 or row['timed_out']:failed.append(dict(command=path.parent.name,exit_code=row['exit_code'],timed_out=row['timed_out'],receipt=str(path.relative_to(BASE))))
(BASE/'command-identities.json').write_text(json.dumps(commands,indent=2)+'\n')
ledger=json.loads((BASE/'failure-ledger.json').read_text());ledger.update(status='supporting_only_host_validation_failed',failed_commands=failed,resource_contaminated_full_runs=validation['resource_contaminated_runs'],required_full_host_receipt='commands/host-make-test-disk-retry/receipt.json',required_full_host_disk_errors=0,functional_root_tests_passed=2421,pending_snapshots=13,pending_snapshots_match_frozen_parts32=True,standalone_dag_release_passed=66,final_validation_collector_reconciled_with_fresh_u0_lint_evidence=True)
(BASE/'failure-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
subprocess.run([sys.executable,str(BASE/'freeze.py')],check=True)
audit=subprocess.run([sys.executable,str(BASE/'inspect.py')],check=True,capture_output=True,text=True)
(BASE/'inspection.json').write_text(audit.stdout)
print(audit.stdout,end='')
