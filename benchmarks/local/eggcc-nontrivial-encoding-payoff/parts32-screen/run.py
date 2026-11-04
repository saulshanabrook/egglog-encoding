#!/usr/bin/env python3
"""Bounded Parts32 oracle and U0/backend falsifier; no source-engine changes."""
import difflib
import hashlib
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

def high_bits(value,width):
    """Sign-extend a selected unsigned bit suffix; independent of signed shift."""
    unsigned=value&((1<<64)-1)
    selected=unsigned>>width
    return selected-(1<<(64-width)) if selected&(1<<(63-width)) else selected

def expected(args,kind='positive',manual=False):
    x,y,n=args
    if not 0<=n<=1000000:return '-2\n'
    total=0
    for _ in range(n):
        xb=x.to_bytes(8,'big',signed=True);yb=y.to_bytes(8,'big',signed=True)
        low_x=int.from_bytes(xb[4:],'big');low_y=int.from_bytes(yb[4:],'big')
        high_x=int.from_bytes(xb[:4],'big',signed=True)
        high_y=int.from_bytes(yb[:4],'big',signed=True)
        if kind=='wrong-width':high_x=high_bits(x,33);high_y=high_bits(y,33)
        if kind=='unequal-widths':high_y=high_bits(y,16)
        if x==y and kind!='missing-word-disequality':score=5
        elif low_x!=low_y and kind!='missing-low-equality':score=3
        elif manual or high_x!=high_y:score=7
        else:score=99
        total+=score
        x=((x+4294967297+(1<<63))%(1<<64))-(1<<63)
        y=((y+8589934593+(1<<63))%(1<<64))-(1<<63)
    return f'{total}\n'

def oracle():
    widths=[]
    for width in range(1,9):
        seen=set()
        for raw in range(1<<(2*width)):
            signed=raw if raw<1<<(2*width-1) else raw-(1<<(2*width))
            low=raw&((1<<width)-1)
            unsigned_high=raw>>width
            high=unsigned_high if unsigned_high<1<<(width-1) else unsigned_high-(1<<width)
            assert signed==(high<<width)+low
            assert (low,high) not in seen
            seen.add((low,high))
        widths.append(dict(field_width=width,words=len(seen)))
    edges=[-(1<<63),-(1<<63)+1,-(1<<32)-1,-(1<<32),-1,0,1,
        (1<<32)-1,1<<32,(1<<63)-2,(1<<63)-1]
    rng=random.Random(0x50415254533332)
    words=edges+[rng.randrange(-(1<<63),1<<63) for _ in range(4096)]
    for x in words:
        data=x.to_bytes(8,'big',signed=True)
        low=int.from_bytes(data[4:],'big')
        high=int.from_bytes(data[:4],'big',signed=True)
        assert low==x&0xffffffff and high==high_bits(x,32)==x>>32
        assert int.from_bytes(high.to_bytes(4,'big',signed=True)+low.to_bytes(4,'big'),
            'big',signed=True)==x
    pairs=[]
    for _ in range(2048):
        low=rng.randrange(1<<32)
        h1=rng.randrange(-(1<<31),1<<31);h2=rng.randrange(-(1<<31),1<<31)
        x=int.from_bytes(h1.to_bytes(4,'big',signed=True)+low.to_bytes(4,'big'),'big',signed=True)
        y=int.from_bytes(h2.to_bytes(4,'big',signed=True)+low.to_bytes(4,'big'),'big',signed=True)
        assert (x==y)==(h1==h2)
        if x!=y:assert high_bits(x,32)!=high_bits(y,32)
        pairs.append((x,y))
    cases=[(0,1<<32,8),(0,0,8),(1<<32,0,8),(0,1,8),
        (-(1<<63),-(1<<63)+(1<<32),8),((1<<63)-1,(1<<63)-1-(1<<32),8),
        (-1,(1<<32)-1,8),(0,1<<32,0),(0,1<<32,1),(0,1<<32,1024),(0,1<<32,-1)]
    rows=[dict(args=args,expected_stdout=expected(args)) for args in cases]
    assert all(expected(r['args'],manual=True)==r['expected_stdout'] for r in rows)
    negatives=[dict(kind='missing-word-disequality',args=(0,0,1)),
        dict(kind='wrong-width',args=(0,1<<32,1)),
        dict(kind='unequal-widths',args=(1<<48,1<<32,1)),
        dict(kind='missing-low-equality',args=(0,1,1))]
    for row in negatives:
        row['expected_stdout']=expected(row['args'],row['kind'])
        row['invalid_manual_stdout']=expected(row['args'],row['kind'],True)
        assert row['expected_stdout']=='99\n' and row['invalid_manual_stdout']=='7\n'
    result=dict(reduced_exhaustive=widths,full_width_words=len(words),
        same_low_pairs=len(pairs),positive_rows=rows,negative_rows=negatives,
        law='Signed high 32 bits and unsigned low 32 bits reconstruct every i64 word uniquely',
        compiler_invoked=False)
    (ROOT/'oracle.json').write_text(json.dumps(result,indent=2)+'\n')
    print('oracle passed',flush=True)
    return rows,negatives

def run(label,argv,timeout=180):
    """Capture command identity, streams and bounded process-group termination."""
    out=ROOT/'commands'/label;out.mkdir(parents=True,exist_ok=False)
    argv=[str(x) for x in argv];start=time.monotonic()
    proc=subprocess.Popen(argv,cwd=U0,env=ENV,start_new_session=True,
        stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    timed_out=False
    try:stdout,stderr=proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out=True;os.killpg(proc.pid,signal.SIGKILL);stdout,stderr=proc.communicate()
    (out/'stdout').write_bytes(stdout);(out/'stderr').write_bytes(stderr)
    receipt=dict(argv=argv,cwd=str(U0),timeout_s=timeout,elapsed_s=time.monotonic()-start,
        exit_code=proc.returncode,timed_out=timed_out,
        environment={k:ENV[k] for k in ('EGGCC_ROOT','RAYON_NUM_THREADS','LLVM_SYS_180_PREFIX',
            'LIBRARY_PATH','PATH','PYTHONDONTWRITEBYTECODE')},
        absent_environment=['EGGLOG_BENCH_MEMORY_GUARD'],
        files=[dict(path=a,sha256=hashlib.sha256(Path(a).read_bytes()).hexdigest())
            for a in argv if Path(a).is_file()],
        stdout_sha256=hashlib.sha256(stdout).hexdigest(),
        stderr_sha256=hashlib.sha256(stderr).hexdigest())
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(label,proc.returncode,f'{receipt["elapsed_s"]:.2f}s',flush=True)
    assert proc.returncode==0 and not timed_out,stderr.decode(errors='replace')[-3500:]
    return stdout

def screen():
    rows,negatives=oracle()
    source=ROOT/'source.bril';manual=ROOT/'manual.bril';emitted=ROOT/'optimized.bril'
    before=source.read_text();after=before.replace('  br target .unexpected .expected;','  jmp .expected;')
    assert before!=after and not manual.exists();manual.write_text(after)
    (ROOT/'manual.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),
        after.splitlines(True),fromfile='source.bril',tofile='manual.bril')))
    identity=[BIN,BIN.parent/'tiger',U0/'runtime/rt.bc',U0/'runtime/rt.o',LLVM/'clang',
        LLVM/'opt',LLVM/'llvm-objdump',source,manual,Path(__file__),STUDY/'admission/manifest.json']
    (ROOT/'identities.json').write_text(json.dumps([dict(path=str(p),
        sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in identity],indent=2)+'\n')
    for role,path in [('source',source),('manual',manual)]:
        run(role+'-parse',[BIN,'--with-context','--run-mode','parse','--interp',
            '--run-data-out',ROOT/(role+'-parse.json'),path])
        data=json.loads((ROOT/(role+'-parse.json')).read_text())
        assert data['original_interpreted']==data['result_interpreted']=='56\n'
    graph=ROOT/'egraphs';graph.mkdir()
    emitted.write_bytes(run('source-emit',[BIN,'--with-context','--run-mode','optimize',
        '--egraph-out-dir',graph,'--run-data-out',ROOT/'emit.json',source]))
    run('emitted-parse',[BIN,'--with-context','--run-mode','parse','--interp',
        '--run-data-out',ROOT/'emitted-parse.json',emitted])
    data=json.loads((ROOT/'emitted-parse.json').read_text())
    assert data['original_interpreted']==data['result_interpreted']=='56\n'
    binaries={}
    for role,path in [('source',source),('optimized',emitted),('manual',manual)]:
        out=ROOT/(role+'-native');out.mkdir();binary=out/'program'
        run(role+'-lower',[BIN,'--with-context','--run-mode','llvm',
            '--optimize-egglog','false','--optimize-bril-llvm','O3_O3','-o',binary,
            '--llvm-output-dir',out/'program.ll','--run-data-out',out/'lower.json',path])
        (out/'disassembly.txt').write_bytes(run(role+'-disassemble',
            [LLVM/'llvm-objdump','--disassemble','--no-show-raw-insn',binary]))
        binaries[role]=binary
    matrix=[]
    for num,row in enumerate(rows):
        actual={}
        for role,binary in binaries.items():
            value=run(f'native-{role}-{num:02}',[binary,*row['args']],30).decode()
            actual[role]=value
            assert value==row['expected_stdout'],(role,row,value)
        matrix.append({**row,'actual':actual})
    (ROOT/'native-results.json').write_text(json.dumps(matrix,indent=2)+'\n')
    for row in negatives:
        kind=row['kind'];out=ROOT/kind;out.mkdir()
        text=before.replace('# ARGS: 0 4294967296 8','# ARGS: '+' '.join(map(str,row['args'])))
        if kind=='missing-word-disequality':
            text=text.replace('  br same_word .same_word .different_word;','  jmp .different_word;')
        elif kind=='wrong-width':
            text=text.replace('  shift: int = const 32;','  shift: int = const 33;')
        elif kind=='unequal-widths':
            text=text.replace('  hy: int = shr y shift;',
                '  other_shift: int = const 16;\n  hy: int = shr y other_shift;')
        else:text=text.replace('  br same_low .same_low .different_low;','  jmp .same_low;')
        path=out/'source.bril';path.write_text(text)
        run(kind+'-parse',[BIN,'--with-context','--run-mode','parse','--interp',
            '--run-data-out',out/'parse.json',path])
        optimized=out/'optimized.bril'
        optimized.write_bytes(run(kind+'-emit',[BIN,'--with-context','--run-mode','optimize',
            '--run-data-out',out/'emit.json',path]))
        run(kind+'-emitted-parse',[BIN,'--with-context','--run-mode','parse','--interp',
            '--run-data-out',out/'emitted-parse.json',optimized])
        for label in ('parse','emitted-parse'):
            data=json.loads((out/(label+'.json')).read_text())
            assert data['original_interpreted']==data['result_interpreted']==row['expected_stdout'],(kind,label,data)
        row['actual']={}
        for role,prog in [('source',path),('optimized',optimized)]:
            native=out/(role+'-native');native.mkdir();binary=native/'program'
            run(kind+'-'+role+'-lower',[BIN,'--with-context','--run-mode','llvm',
                '--optimize-egglog','false','--optimize-bril-llvm','O3_O3','-o',binary,
                '--llvm-output-dir',native/'program.ll','--run-data-out',native/'lower.json',prog])
            actual=run(kind+'-'+role+'-native',[binary,*row['args']],30).decode()
            row['actual'][role]=actual
            assert actual==row['expected_stdout'],(kind,role,row,actual)
    (ROOT/'negative-results.json').write_text(json.dumps(negatives,indent=2)+'\n')
    (ROOT/'completed.json').write_text(json.dumps(dict(status='bounded screen completed',
        positive_native_runs=len(matrix)*3,negative_native_runs=len(negatives)*2,
        timing_campaign=False,compiler_changes=False),indent=2)+'\n')

if __name__=='__main__':screen()
