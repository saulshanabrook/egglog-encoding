#!/usr/bin/env python3
"""One bounded Pack32 oracle and native falsifier, without compiler changes."""
import difflib
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import signal
import subprocess
import time

ROOT=Path(__file__).resolve().parent
STUDY=ROOT.parent
U0=Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
BIN=STUDY/'admission/bin/eggcc'
LLVM=Path('/opt/homebrew/opt/llvm@18/bin')
ENV=dict(os.environ)
ENV.update(EGGCC_ROOT=str(U0),RAYON_NUM_THREADS='1',
    LLVM_SYS_180_PREFIX=str(LLVM.parent),LIBRARY_PATH='/opt/homebrew/lib',
    PATH=str(LLVM)+':'+os.environ['PATH'],PYTHONDONTWRITEBYTECODE='1')
for name in ('EGGLOG_BENCH_MEMORY_GUARD','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER',
    'RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','INSTA_UPDATE','INSTA_FORCE_PASS','MAKEFLAGS'):
    ENV.pop(name,None)

def packed_arithmetic(a,b,width=32):
    """Bril's wrapping mul/add model, including deliberately unbounded negatives."""
    value=(a*(1<<width)+b)&((1<<64)-1)
    return value if value<1<<63 else value-(1<<64)

def packed_bytes(a,b):
    """Independent two-field byte concatenation for the admitted 32-bit domain."""
    assert 0<=a<1<<32 and 0<=b<1<<32
    return int.from_bytes(a.to_bytes(4,'big')+b.to_bytes(4,'big'),'big',signed=True)

def output(args,kind='positive',manual=False):
    a,b,c,d,n=args
    bounds=(0<=a<(1<<32) or (kind=='missing-bound' and a>=0))
    if not(bounds and all(0<=v<1<<32 for v in (b,c,d)) and 0<=n<=1000000):
        return '-2\n'
    total=0
    for _ in range(n):
        # Positive source uses an independent byte-layout model. The negative
        # cases deliberately step outside that representation contract.
        if kind=='positive':
            pab=packed_bytes(a,b);pcd=packed_bytes(c,d);pca=packed_bytes(c,a)
        else:
            pab=packed_arithmetic(a,b)
            pcd=packed_arithmetic(c,d,16 if kind=='different-width' else 32)
            pca=packed_arithmetic(c,a)
        if pab!=pcd and kind!='unresolved-fields':
            score=3
        elif pca==pab:
            score=5
        elif manual or c!=d:
            score=7
        else:
            score=99
        total+=score
        a=(a+1)&0xffffffff;b=(b+3)&0xffffffff
        c=(c+1)&0xffffffff;d=(d+3)&0xffffffff
    return f'{total}\n'

def oracle():
    start=time.monotonic()
    widths=[]
    for width in range(1,9):
        words={}
        for a,b in itertools.product(range(1<<width),repeat=2):
            value=(a<<width)+b
            # Disjoint bit slices provide a separate decoding witness.
            bits=f'{value:0{width*2}b}'
            decoded=(int(bits[:width],2),int(bits[width:],2))
            assert decoded==(a,b)
            assert value not in words
            words[value]=(a,b)
        widths.append(dict(width=width,pairs=len(words)))
    edges=[0,1,2,(1<<16)-1,1<<16,(1<<31)-1,1<<31,(1<<32)-2,(1<<32)-1]
    pairs=list(itertools.product(edges,repeat=2))
    rng=random.Random(0x5041434b3332)
    pairs += [(rng.randrange(1<<32),rng.randrange(1<<32)) for _ in range(4096)]
    for a,b in pairs:
        arithmetic=packed_arithmetic(a,b)
        byteword=packed_bytes(a,b)
        assert arithmetic==byteword
        encoded=byteword.to_bytes(8,'big',signed=True)
        assert (int.from_bytes(encoded[:4],'big'),int.from_bytes(encoded[4:],'big'))==(a,b)
    negatives={
        'missing-high-bound':dict(left=[1<<32,0],right=[0,0],widths=[32,32]),
        'missing-low-bound':dict(left=[0,1<<32],right=[1,0],widths=[32,32]),
        'different-widths':dict(left=[0,1<<16],right=[1,0],widths=[32,16]),
        'two-fields-vary-high-can-equal':dict(left=[0,0],right=[0,1],widths=[32,32]),
        'two-fields-vary-low-can-equal':dict(left=[0,0],right=[1,0],widths=[32,32])}
    for name,row in negatives.items():
        left,right=row['left'],row['right']
        lhs=packed_arithmetic(*left,row['widths'][0]);rhs=packed_arithmetic(*right,row['widths'][1])
        row['left_word']=lhs;row['right_word']=rhs
        if name.startswith('two-fields'):
            assert lhs!=rhs and (left[0]==right[0] or left[1]==right[1])
        else:
            assert lhs==rhs and left!=right
    cases=[(1,2,1,2,8),(0,0,0,0,8),(0,1,1,1,8),
        (1<<31,7,1<<31,7,8),((1<<32)-1,(1<<32)-1,(1<<32)-1,(1<<32)-1,4),
        (1,2,1,2,0),(1,2,1,2,1),(1,2,1,2,1024),
        (-1,0,0,0,8),(1<<32,0,0,0,8),(1,2,1,2,-1)]
    rows=[dict(args=args,expected_stdout=output(args)) for args in cases]
    assert all(output(row['args'],manual=True)==row['expected_stdout'] for row in rows)
    negative_cases={'missing-bound':(1<<32,0,0,0,1),
        'different-width':(0,65537,1,1,1),'unresolved-fields':(1,0,0,0,1)}
    negative_rows=[]
    for kind,args in negative_cases.items():
        wanted=output(args,kind)
        manual=output(args,kind,True)
        assert wanted=='99\n' and manual=='7\n'
        negative_rows.append(dict(kind=kind,args=args,expected_stdout=wanted,
            invalid_manual_stdout=manual))
    result=dict(reduced_width_exhaustive=widths,full_width_pairs=len(pairs),
        injectivity='32-bit halves decode uniquely; signed interpretation preserves bits',
        generic_two_unresolved_children='Either child may equal its counterpart; neither is forced disequal',
        counterexamples=negatives,positive_rows=rows,negative_rows=negative_rows,
        elapsed_s=time.monotonic()-start)
    (ROOT/'oracle.json').write_text(json.dumps(result,indent=2)+'\n')
    print('oracle passed',flush=True)
    return rows,negative_rows

def run(label,argv,timeout=180):
    """Capture bounded command evidence and kill the whole process group on timeout."""
    folder=ROOT/'commands'/label;folder.mkdir(parents=True,exist_ok=False)
    argv=[str(a) for a in argv]
    start=time.monotonic()
    proc=subprocess.Popen(argv,cwd=U0,env=ENV,start_new_session=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    timed_out=False
    try:
        stdout,stderr=proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out=True;os.killpg(proc.pid,signal.SIGKILL);stdout,stderr=proc.communicate()
    (folder/'stdout').write_bytes(stdout);(folder/'stderr').write_bytes(stderr)
    receipt=dict(argv=argv,cwd=str(U0),timeout_s=timeout,elapsed_s=time.monotonic()-start,
        exit_code=proc.returncode,timed_out=timed_out,
        environment={k:ENV[k] for k in ('EGGCC_ROOT','RAYON_NUM_THREADS','LLVM_SYS_180_PREFIX',
            'LIBRARY_PATH','PATH','PYTHONDONTWRITEBYTECODE')},
        absent_environment=['EGGLOG_BENCH_MEMORY_GUARD'],
        files=[dict(path=a,sha256=hashlib.sha256(Path(a).read_bytes()).hexdigest())
            for a in argv if Path(a).is_file()],
        stdout_sha256=hashlib.sha256(stdout).hexdigest(),
        stderr_sha256=hashlib.sha256(stderr).hexdigest())
    (folder/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(label,proc.returncode,f'{receipt["elapsed_s"]:.2f}s',flush=True)
    assert proc.returncode==0 and not timed_out,stderr.decode(errors='replace')[-3500:]
    return stdout

def screen():
    rows,negative_rows=oracle()
    source=ROOT/'source.bril';manual=ROOT/'manual.bril';optimized=ROOT/'optimized.bril'
    before=source.read_text()
    after=before.replace('  br target .unexpected .expected;','  jmp .expected;')
    assert after!=before and not manual.exists()
    manual.write_text(after)
    (ROOT/'manual.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),
        after.splitlines(True),fromfile='source.bril',tofile='manual.bril')))
    identities=[BIN,BIN.parent/'tiger',U0/'runtime/rt.bc',U0/'runtime/rt.o',
        LLVM/'clang',LLVM/'opt',LLVM/'llvm-objdump',source,manual,Path(__file__),STUDY/'admission/manifest.json']
    (ROOT/'identities.json').write_text(json.dumps([dict(path=str(p),
        sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in identities],indent=2)+'\n')
    for role,path in [('source',source),('manual',manual)]:
        run(role+'-parse',[BIN,'--with-context','--run-mode','parse','--interp',
            '--run-data-out',ROOT/(role+'-parse.json'),path])
        data=json.loads((ROOT/(role+'-parse.json')).read_text())
        assert data['original_interpreted']==data['result_interpreted']=='56\n'
    graphs=ROOT/'egraphs';graphs.mkdir()
    optimized.write_bytes(run('source-emit',[BIN,'--with-context','--run-mode','optimize',
        '--egraph-out-dir',graphs,'--run-data-out',ROOT/'emit.json',source]))
    run('emitted-parse',[BIN,'--with-context','--run-mode','parse','--interp',
        '--run-data-out',ROOT/'emitted-parse.json',optimized])
    data=json.loads((ROOT/'emitted-parse.json').read_text())
    assert data['original_interpreted']==data['result_interpreted']=='56\n'
    binaries={}
    for role,path in [('source',source),('optimized',optimized),('manual',manual)]:
        out=ROOT/(role+'-native');out.mkdir()
        binary=out/'program'
        run(role+'-lower',[BIN,'--with-context','--run-mode','llvm',
            '--optimize-egglog','false','--optimize-bril-llvm','O3_O3','-o',binary,
            '--llvm-output-dir',out/'program.ll','--run-data-out',out/'lower.json',path])
        (out/'disassembly.txt').write_bytes(run(role+'-disassemble',
            [LLVM/'llvm-objdump','--disassemble','--no-show-raw-insn',binary]))
        binaries[role]=binary
    native=[]
    for num,row in enumerate(rows):
        actual={}
        for role,binary in binaries.items():
            value=run(f'native-{role}-{num:02}',[binary,*row['args']],30).decode()
            actual[role]=value
            assert value==row['expected_stdout'],(row,role,value)
        native.append({**row,'actual':actual})
    (ROOT/'native-results.json').write_text(json.dumps(native,indent=2)+'\n')
    for row in negative_rows:
        kind=row['kind'];out=ROOT/kind;out.mkdir()
        text=before.replace('# ARGS: 1 2 1 2 8','# ARGS: '+' '.join(map(str,row['args'])))
        if kind=='missing-bound':
            text=text.replace('  a_hi: bool = lt a base;','  a_hi: bool = const true;')
        elif kind=='different-width':
            text=text.replace('  pc_hi: int = mul c base;',
                '  other_base: int = const 65536;\n  pc_hi: int = mul c other_base;')
        else:
            text=text.replace('  br same_key .equal_key .different_key;','  jmp .equal_key;')
        path=out/'source.bril';path.write_text(text)
        run(kind+'-parse',[BIN,'--with-context','--run-mode','parse','--interp',
            '--run-data-out',out/'parse.json',path])
        emitted=out/'optimized.bril'
        emitted.write_bytes(run(kind+'-emit',[BIN,'--with-context','--run-mode','optimize',
            '--run-data-out',out/'emit.json',path]))
        run(kind+'-emitted-parse',[BIN,'--with-context','--run-mode','parse','--interp',
            '--run-data-out',out/'emitted-parse.json',emitted])
        for label in ('parse','emitted-parse'):
            data=json.loads((out/(label+'.json')).read_text())
            assert data['original_interpreted']==data['result_interpreted']==row['expected_stdout'],(kind,label,data)
        row['actual']={}
        for role,prog in [('source',path),('optimized',emitted)]:
            role_out=out/(role+'-native');role_out.mkdir();binary=role_out/'program'
            run(kind+'-'+role+'-lower',[BIN,'--with-context','--run-mode','llvm',
                '--optimize-egglog','false','--optimize-bril-llvm','O3_O3','-o',binary,
                '--llvm-output-dir',role_out/'program.ll','--run-data-out',role_out/'lower.json',prog])
            value=run(kind+'-'+role+'-native',[binary,*row['args']],30).decode()
            row['actual'][role]=value
            assert value==row['expected_stdout'],(kind,role,value,row)
    (ROOT/'negative-results.json').write_text(json.dumps(negative_rows,indent=2)+'\n')
    (ROOT/'completed.json').write_text(json.dumps(dict(status='bounded screen completed',
        positive_native_runs=len(native)*3,negative_native_runs=len(negative_rows)*2,
        timing_campaign=False,compiler_changes=False),indent=2)+'\n')

if __name__=='__main__':
    screen()
