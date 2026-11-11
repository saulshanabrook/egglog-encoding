"""One retained guarded diagnostic attempt; no corpus admission or source mutation."""
import hashlib
import json
import re
import shlex
import shutil
from dataclasses import asdict
from pathlib import Path

from benchmarking.pilot import run_bounded_command
from scripts.paper_benchmarks import record_speq
from scripts.reproduction_process import exclusive_job
from scripts.speq_phi_diagnostic import materialize

ROOT = Path('/Users/saul/p/egglog-encoding')
OUT = ROOT / 'benchmarks/local/reproduction/speq-phi-diagnostic-0003'
LLVM = Path('/opt/homebrew/Cellar/llvm@17/17.0.6/bin')
ARTIFACT = ROOT / 'benchmarks/local/sources/speq/artifact'
SOURCES = ROOT / 'benchmarks/local/sources/speq/lleq'
record = {'status': 'running', 'steps': [], 'corpus_admission': False, 'device_execution': False, 'inputs': {}}


def step(name, command, *, expected_failure=False):
    row = {'name': name, 'command': [str(a) for a in command], 'status': 'running',
           'timeout_sec': 60, 'memory_limit_bytes': 5 * 1024**3, 'disk_reserve_bytes': 10 * 1024**3}
    record['steps'].append(row)
    (OUT / 'run.json').write_text(json.dumps(record, indent=2, default=str)+'\n')
    result = run_bounded_command(row['command'], OUT, OUT / name, timeout_sec=60,
                                 memory_limit_bytes=5 * 1024**3, disk_reserve_bytes=10 * 1024**3,
                                 require_guard=True, allow_warning_pressure=True)
    row.update(asdict(result))
    (OUT / 'run.json').write_text(json.dumps(record, indent=2, default=str)+'\n')
    print(name, result.status, round(result.wall_sec, 3), flush=True)
    if result.status != 'success' and not (expected_failure and result.status == 'failure' and result.returncode == 1):
        raise ValueError(f'{name}: {result.status}: {result.message}')
    return result


with exclusive_job(ROOT / 'benchmarks/local/reproduction/stages/.heavy-job.lock'):
    materialize(SOURCES, OUT)
    shutil.copyfile(__file__, OUT / 'guarded-driver.py')
    try:
        for source in [Path(__file__), Path(record_speq.__file__), LLVM / 'llvm-config', LLVM / 'clang++', LLVM / 'opt',
                       ROOT / 'scripts/paper_benchmarks/speq_rev_plugin.cpp']:
            record['inputs'][str(source)] = hashlib.sha256(source.read_bytes()).hexdigest()
        version = step('llvm-version', [LLVM/'llvm-config', '--version']).stdout_path.read_text().strip()
        if version != '17.0.6': raise ValueError(f'unreviewed LLVM version {version}')
        flags = shlex.split(step('llvm-flags', [LLVM/'llvm-config', '--cxxflags', '--ldflags', '--libs', 'core', 'analysis', 'irreader', 'passes', 'scalaropts', 'transformutils', 'ipo', 'support', '--system-libs']).stdout_path.read_text())
        prior = ROOT / 'benchmarks/local/reproduction/speq-phi-diagnostic-0002'
        prior_record = json.loads((prior/'run.json').read_text())
        for label in ['original','patched']:
            name = label+'-phi-harness.cpp'
            digest = hashlib.sha256((OUT/name).read_bytes()).hexdigest()
            if digest != prior_record['outputs'][name] or hashlib.sha256((prior/name).read_bytes()).hexdigest() != digest:
                raise ValueError('prior exact-function harness source changed')
            result = next(row for row in prior_record['steps'] if row['name']==label+'-harness')
            if result['returncode'] != (1 if label=='original' else 0): raise ValueError('prior harness outcome changed')
            for field in ['stdout_path','stderr_path']:
                path=Path(result[field]);expected=prior_record['outputs'][str(path.relative_to(prior))]
                if hashlib.sha256(path.read_bytes()).hexdigest()!=expected: raise ValueError('prior harness logs changed')
        record['harness_gate_source']={'receipt':str(prior/'run.json'),'sha256':hashlib.sha256((prior/'run.json').read_bytes()).hexdigest(),
                                      'reason':'exact original/patched harnesses already ran; unchanged function sources and logs verified'}
        wrapper = OUT / 'speq_rev_plugin.cpp'
        shutil.copyfile(ROOT / 'scripts/paper_benchmarks/speq_rev_plugin.cpp', wrapper)
        plugin = OUT / 'patched-rev-plugin.so'
        step('patched-plugin-build', [LLVM/'clang++', '-fPIC', '-shared', OUT/'patched/llvm/lib/Analysis/REVPass.cpp', wrapper,
                                     '-I'+str(OUT/'patched/llvm/include'), *flags, '-o', plugin])
        record['plugin_sha256'] = hashlib.sha256(plugin.read_bytes()).hexdigest()
        refs = {}
        for name, expected in record_speq.REFERENCE_ANALYSIS_SHA256.items():
            source = ARTIFACT / 'analysis' / (name+'.ll')
            if hashlib.sha256(source.read_bytes()).hexdigest()!=expected: raise ValueError('reference changed '+name)
            retained = OUT / (name+'.ll'); shutil.copyfile(source, retained)
            record['inputs'][str(source)] = expected
            result = step('reference-'+name, [LLVM/'opt', '-load-pass-plugin='+str(plugin), '-S', '-passes=print<revpass>', retained, '-disable-output'])
            match=re.fullmatch(r'REV Start\n(.*)REV End\n', result.stderr_path.read_text(), re.S)
            if not match: raise ValueError('unexpected reference region shape '+name)
            fir=match.group(1); digest=hashlib.sha256(fir.encode()).hexdigest()
            (OUT/(name+'.fir')).write_text(fir)
            refs[name]={'sha256':digest,'unchanged':digest==record_speq.REFERENCE_FIR_SHA256[name]}
        record['reference_fir']=refs
        if not all(v['unchanged'] for v in refs.values()): raise ValueError('reference FIR changed; needs independent review before EqSat diagnostic')
        previous=json.loads((ROOT/'benchmarks/local/reproduction/speq-polarity-diagnostic/receipt.json').read_text())
        app=Path(previous['command'][-1]); app_copy=OUT/'parboil-analysis.ll';shutil.copyfile(app,app_copy)
        record['inputs'][str(app)]=hashlib.sha256(app.read_bytes()).hexdigest()
        step('parboil-memoryssa',[LLVM/'opt','-passes=print<memoryssa>','-disable-output',app_copy])
        result=step('parboil-patched-fir',[LLVM/'opt','-load-pass-plugin='+str(plugin),'-S','-passes=print<revpass>',app_copy,'-disable-output'])
        firs=re.findall(r'REV Start\n(.*?)REV End\n',result.stderr_path.read_text(),re.S)
        if len(firs)!=1: raise ValueError('retained Parboil expected one region')
        fir=firs[0];(OUT/'parboil-patched.fir').write_text(fir)
        expected_phi=['if ptr 1 i8 %cmp17.not then %call4 else %call4.4','if ptr 1 i8 %cmp111.not then %call4.3 else %call4.5']
        record['parboil_phi_lines']=[line for line in fir.splitlines() if '= if ' in line]
        if not all(line in fir for line in expected_phi): raise ValueError('patched Parboil PHI endpoints differ; inspect before EqSat')
        settings=json.loads((ROOT/'benchmarks/local/reproduction/settings.json').read_text())['speq']
        python=Path(settings['paths']['speq_python']);record['inputs'][str(python)]=hashlib.sha256(python.read_bytes()).hexdigest()
        recorder=OUT/'diagnostic_eqsat.py'
        recorder.write_text('''import sys, json, hashlib\nfrom pathlib import Path\nsys.path.insert(0, '''+repr(str(ROOT))+''')\nfrom scripts.paper_benchmarks import record_speq as r\nout=Path(__file__).resolve().parent\nsource=Path('''+repr(str(ARTIFACT/'parseIR.py'))+''').read_text()\nassert hashlib.sha256(source.encode()).hexdigest()==r.PARSE_IR_SHA256\nadapted=out/'parseIR.py';adapted.write_text(r.adapt_parse_ir(source))\np=r.import_parse_ir(adapted);e=p.egraph\nrefs={name:(out/(name+'.fir')).read_text() for name in r.REFERENCE_FIR_SHA256}\nr.add_reference_rules(p,e,refs)\nmanifest={'regions':[], 'diagnostic_only':True, 'source_c_unchanged':True}\ncontexts=r.record_complete_regions(p,e,[(out/'parboil-patched.fir').read_text()],'parboil_hist',out,manifest)\nmanifest['expected_histogram']=any(row.get('kernel')=='histogram' for row in manifest['regions'])\n(out/'eqsat-result.json').write_text(json.dumps(manifest,indent=2,default=str)+'\\n')\n(out/'diagnostic-native-session.egg').write_text(e.as_egglog_string)\nprint(json.dumps({'expected_histogram':manifest['expected_histogram'],'regions':len(manifest['regions'])}))\n''')
        step('parboil-eqsat',[python,recorder])
        record['eqsat']=json.loads((OUT/'eqsat-result.json').read_text())
        record['status']='diagnostic-success'
    except Exception as error:
        record.update(status='stopped',reason=f'{type(error).__name__}: {error}')
        print(record['reason'],flush=True)
    finally:
        record['outputs']={str(p.relative_to(OUT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in OUT.rglob('*') if p.is_file() and p.name!='run.json'}
        (OUT/'run.json').write_text(json.dumps(record,indent=2,default=str)+'\n')
    print(json.dumps({k:record.get(k) for k in ['status','reason','parboil_phi_lines']},indent=2),flush=True)
