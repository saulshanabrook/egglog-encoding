#!/usr/bin/env python3
"""Bounded baseline/native falsifiers; contains no encoding or compiler edits."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
STUDY = ROOT.parent
U0 = Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
BIN = STUDY / 'admission/bin/eggcc'
ENV = dict(os.environ)
ENV.update(EGGCC_ROOT=str(U0), RAYON_NUM_THREADS='1',
           LLVM_SYS_180_PREFIX='/opt/homebrew/opt/llvm@18',
           LIBRARY_PATH='/opt/homebrew/lib',
           PATH='/opt/homebrew/opt/llvm@18/bin:' + os.environ['PATH'])
for name in ('EGGLOG_BENCH_MEMORY_GUARD', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
             'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'INSTA_UPDATE', 'INSTA_FORCE_PASS', 'MAKEFLAGS'):
    ENV.pop(name, None)

def run(label, argv, timeout=180):
    folder = ROOT / 'commands' / label
    folder.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    try:
        proc = subprocess.run([str(x) for x in argv], cwd=U0, env=ENV,
                              capture_output=True, timeout=timeout)
        stdout, stderr = proc.stdout, proc.stderr
        receipt = dict(exit_code=proc.returncode, timed_out=False)
    except subprocess.TimeoutExpired as exc:
        stdout, stderr = exc.stdout or b'', exc.stderr or b''
        receipt = dict(exit_code=None, timed_out=True)
    (folder / 'stdout').write_bytes(stdout)
    (folder / 'stderr').write_bytes(stderr)
    receipt.update(argv=[str(x) for x in argv], cwd=str(U0), timeout_s=timeout,
                   elapsed_s=time.monotonic()-start,
                   environment={k: ENV[k] for k in ('EGGCC_ROOT','RAYON_NUM_THREADS',
                       'LLVM_SYS_180_PREFIX','LIBRARY_PATH','PATH')},
                   absent_environment=['EGGLOG_BENCH_MEMORY_GUARD'],
                   stdout_sha256=hashlib.sha256(stdout).hexdigest(),
                   stderr_sha256=hashlib.sha256(stderr).hexdigest())
    (folder / 'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(label, receipt['exit_code'], f"{receipt['elapsed_s']:.2f}s", flush=True)
    if receipt['exit_code'] != 0:
        raise RuntimeError(f'{label} failed: {stderr.decode(errors="replace")[-2500:]}')
    return stdout

def lower(label, source):
    out = ROOT / label
    out.mkdir(exist_ok=True)
    run(label+'-lower', [BIN, '--with-context', '--run-mode', 'llvm',
        '--optimize-egglog', 'false', '--optimize-bril-llvm', 'O3_O3',
        '-o', out/'program', '--llvm-output-dir', out/'program.ll',
        '--run-data-out', out/'lower.json', source])
    return out/'program'

def wrap(x):
    return (x + 2**63) % 2**64 - 2**63

def expected(family, args):
    if family == 'cancellation':
        x,y,z = args
        if wrap(x+1) != wrap(y+1): return '3\n'
        if x == z: return '5\n'
        return '99\n' if wrap(y+7) == wrap(z+7) else '7\n'
    x,y,m = args
    if (x&m) == (y&m): return '3\n'
    return '99\n' if wrap(x+7) == wrap(y+7) else '7\n'

def canary():
    source = U0/'tests/passing/small/add.bril'
    run('cli-help', [BIN,'--help'])
    for mode in ('parse','optimize'):
        data = ROOT/f'canary-{mode}.json'
        run('canary-'+mode, [BIN,'--with-context','--run-mode',mode,'--interp',
                             '--run-data-out',data,source])
        obj = json.loads(data.read_text())
        assert obj['original_interpreted'] == obj['result_interpreted'] == '3\n'
        (ROOT/f'canary-{mode}-inspect.json').write_text(json.dumps(obj,indent=2)+'\n')
        print(json.dumps(obj),flush=True)
    binary = lower('canary-native', source)
    assert run('canary-native-run',[binary],30) == b'3\n'

def screen(family):
    folder=ROOT/family
    source=folder/'source.bril'
    manual=folder/'manual.bril'
    emit=folder/'optimized.bril'
    graph=folder/'egraphs';graph.mkdir(exist_ok=True)
    for label,path in [('source',source),('manual',manual)]:
        run(family+'-'+label+'-parse',[BIN,'--with-context','--run-mode','parse','--interp',
             '--run-data-out',folder/(label+'-parse.json'),path])
    run(family+'-optimize',[BIN,'--with-context','--run-mode','optimize','--interp',
          '--egraph-out-dir',graph,'--run-data-out',folder/'optimize.json',source])
    emitted=run(family+'-emit',[BIN,'--with-context','--run-mode','optimize',
          '--run-data-out',folder/'emit.json',source])
    emit.write_bytes(emitted)
    run(family+'-emitted-parse',[BIN,'--with-context','--run-mode','parse','--interp',
          '--run-data-out',folder/'emitted-parse.json',emit])
    for label in ('source-parse','manual-parse','optimize','emitted-parse'):
        data=json.loads((folder/(label+'.json')).read_text())
        assert data['original_interpreted'] == data['result_interpreted'] == '7\n', (label,data)
    binaries={label:lower(family+'/'+label+'-native', path)
              for label,path in [('source',source),('optimized',emit),('manual',manual)]}
    cases = ([(0,0,1),(2,2,3),(2,2,2),(0,1,1),
              (9223372036854775807,9223372036854775807,-9223372036854775808),
              (-9223372036854775808,-9223372036854775808,0)] if family=='cancellation'
             else [(0,1,1),(10,11,1),(0,0,1),(0,2,1),
                   (9223372036854775807,-9223372036854775808,1),
                   (-9223372036854775808,-9223372036854775807,1)])
    rows=[]
    for i,args in enumerate(cases):
        want=expected(family,args)
        row={'args':args,'expected_stdout':want,'actual':{}}
        for label,binary in binaries.items():
            actual=run(family+f'-native-{label}-{i}',[binary,*map(str,args)],30).decode()
            row['actual'][label]=actual
            assert actual==want,(family,label,args,actual,want)
        rows.append(row)
    (folder/'native-results.json').write_text(json.dumps(rows,indent=2)+'\n')

def negative(family):
    folder=ROOT/family
    source=folder/'negative.bril'
    emit=folder/'negative-optimized.bril'
    for mode in ('parse','optimize'):
        data=folder/('negative-'+mode+'.json')
        run(family+'-negative-'+mode,[BIN,'--with-context','--run-mode',mode,'--interp',
             '--run-data-out',data,source])
        obj=json.loads(data.read_text())
        assert obj['original_interpreted'] == obj['result_interpreted'] == '99\n'
    emit.write_bytes(run(family+'-negative-emit',[BIN,'--with-context','--run-mode','optimize',
         '--run-data-out',folder/'negative-emit.json',source]))
    args = [1,0,0] if family == 'cancellation' else [1,1,1,0]
    for label,path in [('source',source),('optimized',emit)]:
        binary=lower(family+'/negative-'+label+'-native',path)
        assert run(family+'-negative-'+label+'-native-run',[binary,*map(str,args)],30) == b'99\n'

if __name__ == '__main__':
    import sys
    if sys.argv[1]=='canary': canary()
    elif sys.argv[1]=='negative': negative(sys.argv[2])
    else: screen(sys.argv[1])
