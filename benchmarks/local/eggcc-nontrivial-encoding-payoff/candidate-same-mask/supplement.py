#!/usr/bin/env python3
"""Untouched-U0 comparison and real-compiler guard negatives."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import sys

ROOT=Path(__file__).resolve().parent
os.environ['CANDIDATE_MATRIX_TAG']='supplement'
os.environ['CANDIDATE_BINARY']=str(ROOT/'bin-invariants/eggcc')
spec=importlib.util.spec_from_file_location('matrix',ROOT/'matrix.py')
matrix=importlib.util.module_from_spec(spec);spec.loader.exec_module(matrix)
capture=matrix.capture

def main():
    results=[]
    original_binary=matrix.BIN
    for family,args,expected in [('cold',(0,1,1),'7\n'),('hot',(8,0,1,6),'48\n')]:
        matrix.BIN=matrix.LOWER
        capture.U0=Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
        capture.ENV['EGGCC_ROOT']=str(capture.U0)
        source=ROOT/'fixtures'/(family+'.bril')
        folder=matrix.compile_case(family+'-u0','off',source)
        binary=matrix.native(folder,family+'-u0')
        label='supplement-'+family+'-u0-native'
        retained=ROOT/'commands'/label/'stdout'
        actual=retained.read_text() if retained.exists() else capture.run(label,[binary,*map(str,args)],30).decode()
        assert actual==expected
        data=json.loads((folder/'interp.json').read_text())
        assert data['original_interpreted']==data['result_interpreted']==expected
        u0=(folder/'native/main.asm').read_bytes()
        b1=(ROOT/'matrix-invariants'/family/'off/native/main.asm').read_bytes()
        assert u0==b1,(family,'U0/B1 native code mismatch')
        results.append({'family':family,'u0_b1_entry_assembly_identical':True,
            'u0_entry_assembly_sha256':hashlib.sha256(u0).hexdigest(),
            'u0_b1_emitted_bril_identical':(folder/'optimized.bril').read_bytes()==(ROOT/'matrix-invariants'/family/'off/optimized.bril').read_bytes(),
            'stdout':actual})
    matrix.BIN=original_binary
    capture.U0=Path('/private/tmp/eggcc-same-mask-candidate')
    capture.ENV['EGGCC_ROOT']=str(capture.U0)
    for family,args,expected in [('cold',(0,1,1),'7\n'),('hot',(8,0,1,6),'48\n')]:
        folders=[]
        for mode in ['off','encoding']:
            folder=matrix.compile_case(family+'-no-context',mode,ROOT/'fixtures'/(family+'.bril'),False)
            data=json.loads((folder/'interp.json').read_text())
            assert data['original_interpreted']==data['result_interpreted']==expected
            assert not list((folder/'emit-evidence').iterdir())
            folders.append(folder)
        assert (folders[0]/'optimized.bril').read_bytes()==(folders[1]/'optimized.bril').read_bytes()
        results.append({'family':family,'no_context_off_encoding_emission_identical':True,'stdout':expected})
    fixture_dir=ROOT/'negative-fixtures';fixture_dir.mkdir(exist_ok=True)
    cold=(ROOT/'fixtures/cold.bril').read_text()
    hot=(ROOT/'fixtures/hot.bril').read_text()
    cases=[
        ('different-mask',(ROOT.parent/'scoped-screen/same-mask/negative.bril').read_text(),[1,1,1,0],'99\n'),
        ('different-shift',cold.replace('# ARGS: 0 1 1','# ARGS: 1 0 1')
            .replace('seven: int = const 7;','seven: int = const 7;\n  eight: int = const 8;')
            .replace('uy: int = add y seven;','uy: int = add y eight;'),[1,0,1],'99\n'),
        ('true-sibling',cold.replace('# ARGS: 0 1 1','# ARGS: 0 0 1')
            .replace('br outer .other .different;','br outer .different .other;'),[0,0,1],'99\n'),
        ('noninjective-division',cold.replace('seven: int = const 7;','seven: int = const 7;\n  two: int = const 2;')
            .replace('ux: int = add x seven;','dx: int = div x two;\n  ux: int = add dx seven;')
            .replace('uy: int = add y seven;','dy: int = div y two;\n  uy: int = add dy seven;'),[0,1,1],'99\n'),
        ('nonliteral-loop-initial',hot.replace('# ARGS: 8 0 1 6','# ARGS: 8 0 1 6 7')
            .replace('y: int, m: int)','y: int, m: int, k: int)')
            .replace('seven: int = const 7;','seven: int = id k;'),[8,0,1,6,7],'48\n'),
        ('updated-loop-slot',hot.replace('i: int = add i one;','seven: int = add seven one;\n  i: int = add i one;'),[8,0,1,6],'67\n'),
        ('other-index-loop-slot',hot.replace('i: int = add i one;','seven: int = id five;\n  i: int = add i one;'),[8,0,1,6],'34\n'),
    ]
    for name,text,args,expected in cases:
        source=fixture_dir/(name+'.bril')
        if source.exists():assert source.read_text()==text
        else:source.write_text(text)
        arms=[]
        for mode in ['off','manual','encoding']:
            folder=matrix.compile_case('negative-'+name,mode,source)
            data=json.loads((folder/'interp.json').read_text())
            assert data['original_interpreted']==data['result_interpreted']==expected,(name,mode,data)
            binary=matrix.native(folder,'negative-'+name+'-'+mode)
            label=f'supplement-negative-{name}-{mode}-native'
            retained=ROOT/'commands'/label/'stdout'
            actual=retained.read_text() if retained.exists() else capture.run(label,[binary,*map(str,args)],30).decode()
            assert actual==expected,(name,mode,actual)
            queries=[json.loads(p.read_text()) for p in sorted((folder/'emit-evidence').glob('query-*.json'))]
            arms.append({'mode':mode,'stdout':actual,'queries':queries})
        results.append({'negative':name,'args':args,'expected':expected,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'arms':arms})
    (ROOT/'supplement-results.json').write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':main()
