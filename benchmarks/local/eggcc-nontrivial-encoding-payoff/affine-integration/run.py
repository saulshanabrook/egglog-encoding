#!/usr/bin/env python3
"""Bounded affine-key correctness capture; elapsed times are diagnostics only."""
from pathlib import Path
import os,sys,json,hashlib,subprocess,signal,time
ROOT=Path(__file__).resolve().parent
U0=Path('/private/tmp/eggcc-affine-candidate')
ENV=dict(os.environ)
ENV.update(EGGCC_ROOT=str(U0),RUSTUP_TOOLCHAIN='1.91.0',CARGO_BUILD_JOBS='4',RUST_TEST_THREADS='4',RAYON_NUM_THREADS='1',LLVM_SYS_180_PREFIX='/opt/homebrew/opt/llvm@18',LIBRARY_PATH='/opt/homebrew/lib',PATH='/opt/homebrew/opt/llvm@18/bin:'+os.environ['PATH'],CARGO_TARGET_DIR='/private/tmp/eggcc-affine-candidate/target',PYTHONDONTWRITEBYTECODE='1')
for k in ['EGGLOG_BENCH_MEMORY_GUARD','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','INSTA_UPDATE','INSTA_FORCE_PASS','MAKEFLAGS']:ENV.pop(k,None)
def run(label,argv,timeout=180,cwd=None,check=True):
 out=ROOT/'commands'/label;out.mkdir(parents=True,exist_ok=False);argv=list(map(str,argv));start=time.monotonic()
 proc=subprocess.Popen(argv,cwd=cwd or U0,env=ENV,start_new_session=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE);timed_out=False
 try:stdout,stderr=proc.communicate(timeout=timeout)
 except subprocess.TimeoutExpired:timed_out=True;os.killpg(proc.pid,signal.SIGKILL);stdout,stderr=proc.communicate()
 (out/'stdout').write_bytes(stdout);(out/'stderr').write_bytes(stderr)
 receipt=dict(argv=argv,cwd=str(cwd or U0),timeout_s=timeout,elapsed_s=time.monotonic()-start,exit_code=proc.returncode,timed_out=timed_out,environment={k:ENV[k] for k in ['EGGCC_ROOT','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','RUST_TEST_THREADS','RAYON_NUM_THREADS','LLVM_SYS_180_PREFIX','LIBRARY_PATH','PATH','CARGO_TARGET_DIR','PYTHONDONTWRITEBYTECODE']},extra_environment={k:ENV[k] for k in ['UV_CACHE_DIR','UV_PYTHON','UV_OFFLINE'] if k in ENV},scoped_mode=ENV.get('EGGCC_SCOPED_MODE'),scoped_evidence=ENV.get('EGGCC_SCOPED_EVIDENCE'),absent_environment=['EGGLOG_BENCH_MEMORY_GUARD'],files=[dict(path=a,sha256=hashlib.sha256(Path(a).read_bytes()).hexdigest()) for a in argv if Path(a).is_file()],stdout_sha256=hashlib.sha256(stdout).hexdigest(),stderr_sha256=hashlib.sha256(stderr).hexdigest())
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(label,proc.returncode,f'{receipt["elapsed_s"]:.2f}s',flush=True)
 if check:assert proc.returncode==0 and not timed_out,stderr.decode(errors='replace')[-6000:]
 return stdout
if __name__=='__main__':run(sys.argv[1],sys.argv[2:],1800 if sys.argv[2]=='cargo' else 180)
