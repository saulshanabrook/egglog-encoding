#!/usr/bin/env python3
"""Summarize fresh required host validation without accepting snapshots."""
from pathlib import Path
import hashlib,json,re,shutil
BASE=Path(__file__).resolve().parent
HOST=Path('/private/tmp/eggcc-sort-candidate')
U0=Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
def receipt(label):
    path=BASE/'commands'/label/'receipt.json';row=json.loads(path.read_text())
    return {'receipt':str(path.relative_to(BASE)),'argv':row['argv'],'exit_code':row['exit_code'],'timed_out':row['timed_out'],'stdout_sha256':row['stdout_sha256'],'stderr_sha256':row['stderr_sha256']}
def main():
    old={r['name']:r['sha256'] for r in json.loads((BASE.parent/'parts32-integration/eggcc-snapshot-comparison.json').read_text())}
    destination=BASE/'pending-snapshots';destination.mkdir(exist_ok=True)
    snapshots=[]
    for path in sorted(HOST.rglob('*.snap.new')):
        if 'target' in path.parts:continue
        sha=hashlib.sha256((path).read_bytes()).hexdigest();shutil.copy2(path,destination/path.name)
        snapshots.append({'name':path.name,'sha256':sha,'matches_parts32_name_and_hash':old.get(path.name)==sha})
    diagnostic_checks=[('src/rvsdg/optimize_direct_jumps.rs',236,'unnecessary_unwrap'),('dag_in_context/src/extractiongymfastergreedydag.rs',134,'unnecessary_unwrap'),('dag_in_context/src/fastercbcextractor.rs',991,'cloned_ref_to_slice_refs')]
    diagnostics=[]
    for name,line,lint in diagnostic_checks:
        assert (HOST/name).read_bytes()==(U0/name).read_bytes()
        diagnostics.append({'file':name,'line':line,'lint':lint,'file_byte_identical_to_u0':True})
    def clippy_errors(label):
        text=(BASE/'commands'/label/'stderr').read_text()
        return len(re.findall(r'^error:(?! could not compile)',text,re.M)),text
    nroot,root_text=clippy_errors('clippy-root');ndag,dag_text=clippy_errors('clippy-dag')
    assert nroot==1 and ndag==2 and 'scoped_reasoning.rs' not in root_text+dag_text
    engine_path=BASE.parent/'parts32-integration/commands/engine-make-check-process-access/receipt.json'
    engine=json.loads(engine_path.read_text());assert engine['exit_code']==0 and not engine['timed_out']
    u0_path=BASE.parent/'affine-integration/commands/validation-u0-release-make-test/receipt.json'
    u0=json.loads(u0_path.read_text());assert u0['exit_code']==0 and not u0['timed_out']
    first_full=receipt('host-make-test')
    first_stdout=(BASE/'commands/host-make-test/stdout').read_text()
    first_stderr=(BASE/'commands/host-make-test/stderr').read_text()
    full=receipt('host-make-test-retry-after-enospc')
    stdout=(BASE/'commands/host-make-test-retry-after-enospc/stdout').read_text();stderr=(BASE/'commands/host-make-test-retry-after-enospc/stderr').read_text()
    dag=receipt('dag-release-tests')
    first_raw=json.loads((BASE/'commands/host-make-test/receipt.json').read_text())
    retry_raw=json.loads((BASE/'commands/host-make-test-retry-after-enospc/receipt.json').read_text())
    assert first_raw['argv']==retry_raw['argv']==['make','test']
    assert first_raw['cwd']==retry_raw['cwd'] and first_raw['environment']==retry_raw['environment']
    retry_environment_exact=True
    result={'status':'native_gate_passed_full_host_validation_failed' if full['exit_code'] else 'required_host_validation_passed','isolated_host':str(HOST),'isolated_engine':'/private/tmp/encoding-sort-candidate','focused_tests':receipt('focused-initial'),'dag_library_tests':receipt('dag-library-tests'),'engine_registered_tests':receipt('engine-registered-tests'),'format_check':receipt('format-check'),'root_clippy':receipt('clippy-root'),'dag_clippy':receipt('clippy-dag'),'new_clippy_diagnostics':0,'pre_existing_clippy_diagnostics':diagnostics,'first_full_host_make_test':first_full,'first_full_host_test_result_summaries':re.findall(r'test result:.*',first_stdout),'first_full_host_enospc_failures':re.findall(r'^test (\S+).*FAILED$',first_stdout,re.M),'first_full_host_enospc_origin':'ten tiger invocations; jacobi-1d LLVM Opt IO failure, stderr explicitly reports output-stream ENOSPC','environmental_retry_without_source_change':True,'environmental_retry_explicit_environment_exact':retry_environment_exact,'full_host_make_test':full,'full_host_test_result_summaries':re.findall(r'test result:.*',stdout),'full_dag_release_tests':dag,'full_dag_release_test_summaries':re.findall(r'test result:.*',(BASE/'commands/dag-release-tests/stdout').read_text()),'pending_snapshots':snapshots,'pending_snapshot_count':len(snapshots),'pending_snapshots_equal_first_run':{row['name']:row['sha256'] for row in snapshots}=={row['name']:row['sha256'] for row in json.loads((BASE/'first-host-snapshots.json').read_text())},'all_pending_match_parts32':bool(snapshots) and all(r['matches_parts32_name_and_hash'] for r in snapshots),'u0_full_make_test_reused':{'path':str(u0_path),'sha256':hashlib.sha256((u0_path).read_bytes()).hexdigest(),'exit_code':u0['exit_code'],'scope':'prior fresh pinned-U0 source; all 771 admitted source hashes verified by freeze.py'},'engine_full_make_check_reused':{'path':str(engine_path),'sha256':hashlib.sha256((engine_path).read_bytes()).hexdigest(),'exit_code':engine['exit_code'],'scope':'all 884 retained Cargo/source files byte-identical to current Parts32 E1 tree; five changed files match frozen historical archive; not a fresh sort-engine check'},'snapshots_accepted':False,'semantic_revisions':0,'timing_campaign':False,'qualification':'supporting actual-host mechanism/native-code evidence only; no measured speedup or pre-existing compiler bug'}
    (BASE/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'host_exit':full['exit_code'],'dag_exit':dag['exit_code'],'pending_snapshots':len(snapshots),'match_parts32':result['all_pending_match_parts32'],'new_clippy_diagnostics':0}))
if __name__=='__main__':main()
