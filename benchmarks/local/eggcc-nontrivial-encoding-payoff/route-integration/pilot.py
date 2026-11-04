from pathlib import Path
import importlib.util,json
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('capture',BASE/'run.py');capture=importlib.util.module_from_spec(spec);spec.loader.exec_module(capture)
folder=BASE/'pilot';folder.mkdir(exist_ok=False)
capture.ENV['EGGCC_SCOPED_MODE']='encoding';capture.ENV['EGGCC_SCOPED_EVIDENCE']=str(folder/'evidence')
output=capture.run('pilot-emit',[BASE/'bin/eggcc','--with-context','--run-mode','optimize','--run-data-out',folder/'emit.json',BASE/'fixtures/source.bril'])
(folder/'optimized.bril').write_bytes(output)
queries=[q for p in sorted((folder/'evidence').glob('*.json')) for q in json.loads(p.read_text())['queries']]
result=dict(queries=queries,exports=sum(bool(q.get('export')) for q in queries),target99_retained=b'const 99' in output)
(BASE/'pilot.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!="queries"},indent=2))
