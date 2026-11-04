#!/usr/bin/env python3
"""One bounded baseline/backend falsifier; no compiler changes or timed campaign."""
import difflib
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent
STUDY = ROOT.parent
U0 = Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0')
BIN = STUDY / 'admission/bin/eggcc'
LLVM = Path('/opt/homebrew/opt/llvm@18/bin')
ENV = dict(os.environ)
ENV.update(EGGCC_ROOT=str(U0), RAYON_NUM_THREADS='1',
           LLVM_SYS_180_PREFIX=str(LLVM.parent), LIBRARY_PATH='/opt/homebrew/lib',
           PATH=str(LLVM)+':'+os.environ['PATH'], RUST_LOG='info',
           PYTHONDONTWRITEBYTECODE='1')
for name in ('EGGLOG_BENCH_MEMORY_GUARD', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER',
             'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'INSTA_UPDATE', 'INSTA_FORCE_PASS', 'MAKEFLAGS'):
    ENV.pop(name, None)

def run(label, argv, timeout=180):
    """Capture argv, environment, result and streams, killing descendants on timeout."""
    folder = ROOT/'commands'/label
    folder.mkdir(parents=True, exist_ok=False)
    argv = [str(a) for a in argv]
    start = time.monotonic()
    proc = subprocess.Popen(argv, cwd=U0, env=ENV, start_new_session=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
    (folder/'stdout').write_bytes(stdout)
    (folder/'stderr').write_bytes(stderr)
    receipt = dict(argv=argv, cwd=str(U0), timeout_s=timeout,
        elapsed_s=time.monotonic()-start, exit_code=proc.returncode,
        timed_out=timed_out, pid=proc.pid,
        environment={k:ENV[k] for k in ('EGGCC_ROOT','RAYON_NUM_THREADS',
            'LLVM_SYS_180_PREFIX','LIBRARY_PATH','PATH','RUST_LOG','PYTHONDONTWRITEBYTECODE')},
        absent_environment=['EGGLOG_BENCH_MEMORY_GUARD'],
        files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
            for p in [Path(a) for a in argv] if p.is_file()],
        stdout_sha256=hashlib.sha256(stdout).hexdigest(),
        stderr_sha256=hashlib.sha256(stderr).hexdigest())
    (folder/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(label,proc.returncode,f'{receipt["elapsed_s"]:.2f}s',flush=True)
    if timed_out or proc.returncode != 0:
        raise RuntimeError(f'{label} failed: {stderr.decode(errors="replace")[-3500:]}')
    return stdout

def screen():
    source = ROOT/'source.bril'
    manual = ROOT/'manual.bril'
    before = source.read_text()
    assert before.count('  value: int = load pi;') == 1
    after = before.replace('  value: int = load pi;', '  value: int = id count;')
    assert not manual.exists()
    manual.write_text(after)
    (ROOT/'manual.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),
        after.splitlines(True),fromfile='source.bril',tofile='manual.bril')))
    identity_paths = [BIN,BIN.parent/'tiger',U0/'runtime/rt.bc',U0/'runtime/rt.o',
        LLVM/'clang',LLVM/'opt',LLVM/'llvm-objdump',source,manual,
        STUDY/'admission/manifest.json',Path(__file__)]
    (ROOT/'identities.json').write_text(json.dumps([
        dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
        for p in identity_paths],indent=2)+'\n')
    for role,path in [('source',source),('manual',manual)]:
        run(role+'-parse',[BIN,'--with-context','--run-mode','parse','--interp',
            '--run-data-out',ROOT/(role+'-parse.json'),path])
    graph = ROOT/'egraphs'
    graph.mkdir()
    optimized = ROOT/'optimized.bril'
    optimized.write_bytes(run('source-emit',[BIN,'--with-context','--run-mode','optimize',
        '--egraph-out-dir',graph,'--run-data-out',ROOT/'emit.json',source]))
    run('emitted-parse',[BIN,'--with-context','--run-mode','parse','--interp',
        '--run-data-out',ROOT/'emitted-parse.json',optimized])
    for role in ('source','manual','emitted'):
        data = json.loads((ROOT/(role+'-parse.json')).read_text())
        assert data['original_interpreted'] == data['result_interpreted'] == '28\n',(role,data)
    binaries = {}
    for role,path in [('source',source),('optimized',optimized),('manual',manual)]:
        out = ROOT/(role+'-native')
        out.mkdir()
        binary = out/'program'
        run(role+'-lower',[BIN,'--with-context','--run-mode','llvm',
            '--optimize-egglog','false','--optimize-bril-llvm','O3_O3',
            '-o',binary,'--llvm-output-dir',out/'program.ll',
            '--run-data-out',out/'lower.json',path])
        (out/'disassembly.txt').write_bytes(run(role+'-disassemble',
            [LLVM/'llvm-objdump','--disassemble','--no-show-raw-insn',binary]))
        binaries[role] = binary
    cases = [(0,1,8),(1,0,8),(0,1,0),(0,1,1),(0,0,8),(1,1,8),
             (-1,0,8),(0,2,8),(0,1,-1),(0,1,1000001),(0,1,1024)]
    rows = []
    for num,(i,j,n) in enumerate(cases):
        want = ('-2\n' if not (0<=i<2 and 0<=j<2 and 0<=n<=1000000)
            else '-1\n' if (i&1)==(j&1) else f'{n*(n-1)//2}\n')
        row = dict(args=[i,j,n],expected_stdout=want,actual={})
        for role,binary in binaries.items():
            actual = run(f'native-{role}-{num:02}',[binary,i,j,n],30).decode()
            row['actual'][role] = actual
            assert actual == want,(role,row)
        rows.append(row)
    (ROOT/'native-results.json').write_text(json.dumps(rows,indent=2)+'\n')
    (ROOT/'completed.json').write_text(json.dumps(dict(status='bounded screen completed',
        interpreter_witness='28\n',native_rows=len(rows),native_arms=list(binaries),
        timing_campaign=False,compiler_changes=False),indent=2)+'\n')

if __name__ == '__main__':
    screen()
