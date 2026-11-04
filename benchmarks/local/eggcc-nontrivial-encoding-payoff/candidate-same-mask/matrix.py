#!/usr/bin/env python3
"""Actual candidate correctness/causality capture. No confirmation timing."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import shutil
import sys

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('candidate',ROOT/'run.py')
candidate=importlib.util.module_from_spec(spec);spec.loader.exec_module(candidate)
capture=candidate.capture
BIN=Path(os.environ.get('CANDIDATE_BINARY',str(ROOT/'bin/eggcc')))
LOWER=ROOT.parent/'admission/bin/eggcc'
TAG=os.environ.get('CANDIDATE_MATRIX_TAG','')
MATRIX=ROOT/('matrix-'+TAG if TAG else 'matrix')
MODES=['off','seed-only','annotation-off','query-off','manual','encoding','bridge-off']

def compile_case(family,mode,source,context=True):
    folder=MATRIX/family/mode
    if folder.exists():
        for action in ['interp','emit']:
            label=f'{TAG+"-" if TAG else ""}{family}-{mode}-{action}'
            receipt=json.loads((ROOT/'commands'/label/'receipt.json').read_text())
            assert receipt['exit_code']==0 and not receipt['timed_out']
            assert receipt['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
            assert receipt['binary_sha256']==hashlib.sha256(BIN.read_bytes()).hexdigest()
            assert receipt['use_context']==context and receipt['scoped_mode']==mode
        return folder
    folder.mkdir(parents=True,exist_ok=False)
    capture.ENV.update(EGGCC_SCOPED_MODE=mode,RUST_LOG='info')
    for action,interp in [('interp',True),('emit',False)]:
        evidence=folder/(action+'-evidence');evidence.mkdir()
        capture.ENV['EGGCC_SCOPED_EVIDENCE']=str(evidence)
        argv=[BIN]
        if context:argv.append('--with-context')
        argv+=['--run-mode','optimize']
        if interp:argv.append('--interp')
        argv+=['--run-data-out',folder/(action+'.json'),source]
        label=f'{TAG+"-" if TAG else ""}{family}-{mode}-{action}'
        stdout=capture.run(label,argv,180)
        receipt_path=ROOT/'commands'/label/'receipt.json'
        receipt=json.loads(receipt_path.read_text())
        receipt.update(scoped_mode=mode,scoped_evidence=str(evidence),
            source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
            binary_sha256=hashlib.sha256(BIN.read_bytes()).hexdigest(),use_context=context)
        receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
        if not interp:(folder/'optimized.bril').write_bytes(stdout)
    return folder

def native(folder,label):
    label=(TAG+'-' if TAG else '')+label
    folder=Path(folder)
    output=folder/'native'
    if output.exists():
        assert (output/'program').is_file() and (output/'main.asm').is_file()
        receipt=json.loads((ROOT/'commands'/(label+'-lower')/'receipt.json').read_text())
        assert receipt['exit_code']==0 and not receipt['timed_out']
        return output/'program'
    output.mkdir()
    capture.ENV.pop('EGGCC_SCOPED_MODE',None)
    capture.ENV.pop('EGGCC_SCOPED_EVIDENCE',None)
    capture.run(label+'-lower',[LOWER,'--with-context','--run-mode','llvm','--optimize-egglog','false',
        '--optimize-bril-llvm','O3_O3','-o',output/'program','--llvm-output-dir',output/'program.ll',
        '--run-data-out',output/'lower.json',folder/'optimized.bril'],180)
    assembly=capture.run(label+'-disassemble',['/usr/bin/otool','-tvV',output/'program'],30).decode()
    (output/'program.asm').write_text(assembly)
    lines=assembly.splitlines();blocks=[]
    for i,line in enumerate(lines):
        if line not in ['__main:','_main:']:continue
        end=next((j for j in range(i+1,len(lines)) if lines[j].endswith(':') and not lines[j].startswith('0')),len(lines))
        blocks.append('\n'.join(lines[i:end]))
    (output/'main.asm').write_text('\n\n'.join(blocks)+'\n')
    return output/'program'

def main():
    fixtures=ROOT/'fixtures';fixtures.mkdir(exist_ok=True)
    cold=ROOT.parent/'scoped-screen/same-mask/source.bril'
    hot=ROOT.parent/'scoped-screen/hot-same-mask/source.bril'
    for name,path in [('cold',cold),('hot',hot)]:shutil.copy2(path,fixtures/(name+'.bril'))
    hot_spec=importlib.util.spec_from_file_location('hot',hot.parent/'run.py')
    hot_driver=importlib.util.module_from_spec(hot_spec);hot_spec.loader.exec_module(hot_driver)
    results=[]
    for family,args_cases,expected in [
        ('cold',[(0,1,1),(0,0,1),(0,2,1),(9223372036854775807,-9223372036854775808,1)],
            lambda a:'3\n' if (a[0]&a[2])==(a[1]&a[2]) else '7\n'),
        ('hot',hot_driver.CASES,hot_driver.exact_expected)]:
        for mode in MODES:
            folder=compile_case(family,mode,fixtures/(family+'.bril'))
            data=json.loads((folder/'interp.json').read_text())
            default=(0,1,1) if family=='cold' else (8,0,1,6)
            assert data['original_interpreted']==data['result_interpreted']==expected(default),(family,mode,data)
            binary=native(folder,family+'-'+mode)
            outputs=[]
            for i,args in enumerate(args_cases):
                stdout=capture.run(f'{TAG+"-" if TAG else ""}{family}-{mode}-native-{i}',[binary,*map(str,args)],30).decode()
                assert stdout==expected(args),(family,mode,args,stdout,expected(args))
                outputs.append({'args':args,'expected':expected(args),'stdout':stdout})
            receipts=[json.loads(p.read_text()) for p in sorted((folder/'emit-evidence').glob('query-*.json'))]
            results.append({'family':family,'mode':mode,'outputs':outputs,'queries':receipts,
                'native_main_sha256':hashlib.sha256((folder/'native/main.asm').read_bytes()).hexdigest()})
    (ROOT/(f'matrix-{TAG}-results.json' if TAG else 'matrix-results.json')).write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':main()
