#!/usr/bin/env python3
"""Read-only causal, identity, command, output, and validation inspection."""
from pathlib import Path
import hashlib,json,re
BASE=Path(__file__).resolve().parent

def main():
    ids=json.loads((BASE/'identities.json').read_text())
    for name,expected in ids['files'].items():assert hashlib.sha256((BASE/name).read_bytes()).hexdigest()==expected,name
    manifests=json.loads((BASE/'source-files.json').read_text())
    for label,root in [('host',Path('/private/tmp/eggcc-sort-candidate')),('engine',Path('/private/tmp/encoding-sort-candidate'))]:
        for name,expected in manifests[label].items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,name
    assert hashlib.sha256((BASE/'bin/eggcc').read_bytes()).hexdigest()==ids['host_binary_sha256']
    for name,expected in json.loads((BASE/'tool-identities.json').read_text()).items():assert hashlib.sha256((Path(name)).read_bytes()).hexdigest()==expected,name
    engine_base=json.loads((BASE/'engine-base-verification.json').read_text());assert engine_base['status']=='passed' and engine_base['unchanged_code_and_manifest_files_at_base']==871
    for command in ids['commands']:
        p=BASE/'commands'/command['label']/'receipt.json';assert hashlib.sha256((p).read_bytes()).hexdigest()==command['receipt_sha256']
        receipt=json.loads(p.read_text());assert not receipt['timed_out'],command['label']
        assert hashlib.sha256((p.parent/'stdout').read_bytes()).hexdigest()==receipt['stdout_sha256']
        assert hashlib.sha256((p.parent/'stderr').read_bytes()).hexdigest()==receipt['stderr_sha256']
    positive=json.loads((BASE/'positive-results.json').read_text());modes={row['mode']:row for row in positive}
    optimized={'encoding','manual','cancellation-rescue','reverse-rescue'}
    for mode,row in modes.items():
        for output in row['outputs']:assert output['stdout']==output['expected']
        if mode=='source':continue
        reference=modes['encoding' if mode in optimized else 'u0']
        assert row['emitted_sha256']==reference['emitted_sha256'],mode
        assert row['main_sha256']==reference['main_sha256'],mode
    assert modes['u0']['emitted_sha256']!=modes['encoding']['emitted_sha256']
    assert modes['u0']['main_sha256']!=modes['encoding']['main_sha256']
    accepted={mode:[q for q in row['queries'] if q.get('accepted')] for mode,row in modes.items()}
    assert accepted['encoding'] and all(q['a_equal_c'] and q['b_equal_d'] and q['z_known_disequal_w'] and q['target_known_disequal'] and q['export'] and q['manual_closure_run']==False and q['bottom']==False for q in accepted['encoding'])
    checks={'cancellation-off':('a_equal_c',False),'identity-off':('a_equal_c',False),'reverse-off':('z_known_disequal_w',False),'forward-off':('target_known_disequal',False),'query-off':('target_queried',False),'bridge-off':('export',False),'application-off':('application_enabled',False),'cancellation-rescue':('intermediate_a_equal_c_rescue',True),'reverse-rescue':('intermediate_z_disequal_w_rescue',True)}
    for mode,(field,value) in checks.items():assert accepted[mode] and all(q[field]==value for q in accepted[mode]),mode
    for mode in optimized:assert all(q['export'] for q in accepted[mode]),mode
    assert all(q['order_key_marked']==False and q['a_equal_c'] and q['target_known_disequal'] for q in accepted['cancellation-rescue'])
    assert all(q['reverse_enabled']==False and q['z_known_disequal_w'] and q['target_known_disequal'] for q in accepted['reverse-rescue'])
    null=json.loads((BASE/'primitive-null.json').read_text())
    assert null['status']=='passed' and not null['primitive_mismatches'] and null['final_primitive_target_witness']==False
    assert null['graph_equal_after_removing_only_encoding_run_schedule'] and not null['equality_sort_comparison_or_propagation']
    for mode in ['primitive-only','seed-only']:
        assert accepted[mode] and all(not q['injectivity_saturated'] and not q['engine_witness_queries_run'] and not q['manual_closure_run'] and not q['export'] for q in accepted[mode])
    negative=json.loads((BASE/'negative-results.json').read_text())
    families={row['family'] for row in negative};assert len(families)==8,families
    for family in families:
        rows=[row for row in negative if row['family']==family];reference=next(row for row in rows if row['mode']=='u0')
        for row in rows:
            assert all(output['stdout']=='99\n' for output in row['outputs'])
            if row['mode']!='source':
                assert row['emitted_sha256']==reference['emitted_sha256'],(family,row['mode'])
                assert row['main_sha256']==reference['main_sha256'],(family,row['mode'])
            assert not any(q.get('accepted') for q in row['queries']),(family,row['mode'])
    assert (BASE/'fixtures/omitted-tag.bril').read_bytes()==(BASE/'fixtures/swapped-inputs-no-tag.bril').read_bytes()
    context=json.loads((BASE/'context-negative-results.json').read_text());assert len(context)==2
    assert context[0]['emitted_sha256']==context[1]['emitted_sha256'] and context[0]['main_sha256']==context[1]['main_sha256']
    assert not context[1]['queries']
    verified=json.loads((BASE/'verification.json').read_text());assert verified['status']=='passed'
    invalid=json.loads((BASE/'invalid-fold-results.json').read_text());assert len(invalid)==8 and all(row['outputs'][0]['stdout']=='7\n' for row in invalid)
    validation=json.loads((BASE/'validation.json').read_text());assert validation['new_clippy_diagnostics']==0 and not validation['snapshots_accepted']
    assert validation['environmental_retry_explicit_environment_exact'] and validation['pending_snapshots_equal_first_run'] and validation['all_pending_match_parts32']
    assert validation['pending_snapshot_count']==13 and validation['full_dag_release_tests']['exit_code']==0
    assert any('2421 passed; 0 failed' in summary for summary in validation['full_host_test_result_summaries'])
    assert 'No space left' not in (BASE/'commands/host-make-test-retry-after-enospc/stderr').read_text()
    assert validation['focused_tests']['exit_code']==0 and validation['format_check']['exit_code']==0 and validation['engine_registered_tests']['exit_code']==0 and validation['dag_library_tests']['exit_code']==0
    emitted={mode:(BASE/'matrix/positive'/mode/'optimized.bril').read_text() for mode in ['u0','encoding']}
    assert re.search(r'const 99\b',emitted['u0']) and not re.search(r'const 99\b',emitted['encoding'])
    assembly={mode:(BASE/'matrix/positive'/mode/'native/main.asm').read_text() for mode in ['u0','encoding']}
    assert '=99' in assembly['u0'] and '=99' not in assembly['encoding']
    counts={mode:len(re.findall(r'^\w+:\s+\S+',text.split('\n\n')[0],re.M)) for mode,text in assembly.items()}
    result={'status':'passed','qualification':'supporting actual-host mechanism and native-code evidence; full host validation remains unwaived; no bug or speedup claim','positive_native_checks':sum(len(row['outputs']) for row in positive),'negative_native_checks':sum(len(row['outputs']) for row in negative),'no_context_native_checks':sum(len(row['outputs']) for row in context),'invalid_fold_native_checks':len(invalid),'source_and_emitted_interpretations':verified['interpretations'],'generic_chain_and_both_intermediate_rescues':True,'u0_b1_seed_primitive_parity':True,'manual_encoding_parity':True,'causal_knockouts':sorted(checks),'primitive_only_executed_external_pass':True,'primitive_comparisons':len(null['primitive_comparisons']),'native_application_instructions':counts,'semantic_revisions':ids['semantic_revisions'],'timing_campaign':False}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
