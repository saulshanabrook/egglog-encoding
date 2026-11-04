from pathlib import Path
import json,hashlib,tarfile,datetime
R=Path(__file__).resolve().parent;B=R.parents[1];H=Path('/private/tmp/eggcc-alias-actual');E=Path('/private/tmp/encoding-alias-actual')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
admitted=json.loads((R/'admission.json').read_text());changed={};files=[]
archive=R/'final-source-r1.tar'
with tarfile.open(archive,'w') as out:
 for role,root in [('host',H),('engine',E)]:
  current={str(p.relative_to(root)):digest(p) for p in sorted(root.rglob('*')) if p.is_file() and not any(part in {'target','.venv','__pycache__','.git'} for part in p.relative_to(root).parts)}
  before=admitted['source_files'][role]
  changed[role]=[{'path':rel,'before':before.get(rel),'after':current.get(rel)} for rel in sorted(set(before)|set(current)) if before.get(rel)!=current.get(rel)]
  for relative,sha in current.items():
   name=role+'/'+relative;out.add(root/relative,arcname=name,recursive=False);files.append({'role':role,'relative':relative,'archive_path':name,'sha256':sha})
assert [x['path'] for x in changed['host']]==['dag_in_context/src/scoped_alias.rs'],changed['host']
assert changed['engine']==[],changed['engine']
assert all(digest(R/rel)==sha for rel,sha in admitted['inputs'].items())
u0_manifest=json.loads((B/'admission/source-files.json').read_text());u0=Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
assert all(digest(u0/rel)==sha for rel,sha in u0_manifest.items())
installation=json.loads((R/'inputs/installation.json').read_text())
historical_installation_drift=[{'path':row['path'],'recorded_sha256':row['sha256'],'task_start_and_current_sha256':digest(Path(row['path']))} for row in installation['files'] if digest(Path(row['path']))!=row['sha256']]
for row in installation['files']:
 relative=str(Path(row['path']).relative_to('/private/tmp/eggcc-alias-candidate'))
 assert digest(Path(row['path']))==admitted['source_files']['host'][relative]
assert len(historical_installation_drift)==1
positive=json.loads((R/'positive-results.json').read_text());negative=json.loads((R/'negative-results.json').read_text());inspection=json.loads((R/'inspection.json').read_text())
receipts=[(p,json.loads(p.read_text())) for p in sorted((R/'commands').glob('*/receipt.json'))]
failures=[{'label':p.parent.name,'exit_code':row['exit_code'],'launch_error':row['launch_error'],'timed_out':row['timed_out']} for p,row in receipts if row['exit_code']!=0 or row['timed_out']]
assert not any(row['timed_out'] for _,row in receipts)
assert all('EGGLOG_BENCH_MEMORY_GUARD' in row['absent_environment'] for _,row in receipts)
summary={
 'status':'failed-conservative-import-admission','family':'A1-mask-live-cell','actual_compiler_integration_attempted':True,'integration_accepted':False,
 'terminal_within_prescribed_attempt_budget':True,'semantic_law_refuted':False,
 'terminal_reason':'Initial attempt rejects Alloc PointerT(IntT); single revision fixes that and links import/metadata/context checks but rejects admitted auxiliary Expr-valued TupleRemoveAt and to-hoist rows. No further functional revision permitted. This is a bounded implementation failure, not evidence of semantic impossibility or a substantial-redesign requirement.',
 'functional_revision_count':1,'source_inputs_unchanged':True,
 'initial_focused_tests':{'passed':4,'failed':1,'registered':5},'revised_focused_tests':{'passed':3,'failed':3,'registered':6},'full_host_lib_tests':{'passed':67,'failed':3,'registered':70},
 'required_validation_passed':False,'full_make_check_executed':False,'full_make_check_not_executed_reason':'The new focused A1 tests and complete host library test suite fail; no acceptance or timing is possible. Engine sources are byte-identical to admission.',
 'positive_treatments':len(positive),'positive_native_rows':sum(len(x['outputs']) for x in positive),'negative_arms':len(negative),'negative_native_rows':sum(len(x['outputs']) for x in negative),'native_checks_total':sum(len(x['outputs']) for x in positive+negative),'all_native_checks_passed':True,'interpreter_arms':len(positive+negative),'all_original_result_interpreter_pairs_match':True,
 'exports':0,'positive_query_receipts':0,'controls_interpretation':'All actual modes reject before private query/transport/bridge; no fixed-input knockout or rescue causality was established by actual host execution.',
 'actual_binary_inspection':{k:v for k,v in inspection.items() if k!='rows'},'timing_taken':False,'compiler_bug_claim':False,'speedup_claim':False,
 'command_count':len(receipts),'captured_failures':failures,'timeouts':0,'memory_guard_absent':True,'raytracing_executed':False,
 'preservation':{'u0_files_verified':len(u0_manifest),'prior_initial_installation_files_unchanged_since_task_start':len(installation['files']),'historical_installation_manifest_drift':historical_installation_drift,'immutable_input_files_verified':len(admitted['inputs']),'engine_source_files_unchanged':len(admitted['source_files']['engine']),'host_changes_from_admitted_actual_copy':changed['host']},
 'frozen_source_archive':{'path':str(archive),'sha256':digest(archive),'files':len(files)},'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()
}
(R/'source-identities.json').write_text(json.dumps({'archive':str(archive),'archive_sha256':digest(archive),'files':files,'changed':changed},indent=2)+'\n')
(R/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(R/'acceptance.json').write_text(json.dumps({'candidate':'A1-mask-live-cell','valid_source_workload':'verified','private_generic_law':'initial standalone controls pass; revised actual import not reached','actual_import':'failed closed','transport':'unreached in actual compiler','bridge':'unreached in actual compiler; standalone parity test passes','existing_store_forward_consumer':'standalone parity test passes; actual compiler not enabled','manual_comparison':'actual arm identical because admission rejected','primitive_null':'actual arm not reached','knockout_rescue_causality':'not established','semantic_negative_controls':'source/native matrix passes fail-closed; several registered certificate tests blocked by failed positive','correctness_matrix':'passed on unchanged code','actual_code_opportunity':'none in attempted implementation','full_validation':'failed new A1 tests','performance':'not collected','qualifying_payoff':False},indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['status','command_count','positive_native_rows','negative_native_rows','native_checks_total','terminal_within_prescribed_attempt_budget','timing_taken']},indent=2))
