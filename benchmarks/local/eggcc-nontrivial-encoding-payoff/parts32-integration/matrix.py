#!/usr/bin/env python3
"""Actual compiler/native causal matrix. Does not collect performance samples."""
from pathlib import Path
import importlib.util,json,hashlib,shutil,re,sys,os
BASE=Path(__file__).resolve().parent
ROOT=Path(os.environ.get("PARTS32_OUTPUT_ROOT",str(BASE)))
spec=importlib.util.spec_from_file_location('capture',BASE/'run.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
c.ROOT=ROOT
SCREEN=BASE.parent/'parts32-arithmetic-screen';LOWER=BASE.parent/'admission/bin/eggcc';BIN=Path(os.environ.get('PARTS32_BINARY',str(BASE/'bin/eggcc')));LLVM=Path('/opt/homebrew/opt/llvm@18/bin')
MODES=['off','seed-only','primitive-only','forward-off','reverse-off','identity-off','high-rescue','query-off','manual','encoding','bridge-off','consumer-off','if-consumer-off']
def emit(family,mode,source,context=True):
 folder=ROOT/'matrix'/family/mode
 if folder.exists():
  assert (folder/'optimized.bril').is_file();return folder
 folder.mkdir(parents=True)
 c.ENV.update(EGGCC_SCOPED_MODE=mode);evidence=folder/'evidence';c.ENV['EGGCC_SCOPED_EVIDENCE']=str(evidence)
 argv=[LOWER if mode=='u0' else BIN]
 if context:argv+=['--with-context']
 argv+=['--run-mode','optimize','--run-data-out',folder/'emit.json',source]
 (folder/'optimized.bril').write_bytes(c.run(f'{family}-{mode}-emit',argv))
 c.ENV.pop('EGGCC_SCOPED_EVIDENCE',None);c.ENV['EGGCC_SCOPED_MODE']='off'
 c.run(f'{family}-{mode}-parse',[LOWER,'--with-context','--run-mode','parse','--interp','--run-data-out',folder/'parse.json',folder/'optimized.bril'])
 return folder
def native(folder,label):
 out=folder/'native'
 if out.exists():assert (out/'program').is_file();return out/'program'
 out.mkdir();c.ENV['EGGCC_SCOPED_MODE']='off';c.ENV.pop('EGGCC_SCOPED_EVIDENCE',None)
 c.run(label+'-lower',[LOWER,'--with-context','--run-mode','llvm','--optimize-egglog','false','--optimize-bril-llvm','O3_O3','-o',out/'program','--llvm-output-dir',out/'program.ll','--run-data-out',out/'lower.json',folder/'optimized.bril'])
 asm=c.run(label+'-disassemble',[LLVM/'llvm-objdump','--disassemble','--no-show-raw-insn',out/'program'],30).decode();(out/'program.asm').write_text(asm)
 blocks=[];lines=asm.splitlines()
 for i,line in enumerate(lines):
  if re.match(r'^[0-9a-f]+ <_?main>:',line):
   end=next((j for j in range(i+1,len(lines)) if re.match(r'^[0-9a-f]+ <.*>:',lines[j])),len(lines));blocks.append('\n'.join(lines[i:end]))
 (out/'main.asm').write_text('\n\n'.join(blocks)+'\n');return out/'program'
def receipts(folder):
 return [q for p in sorted((folder/'evidence').glob('boundary*.json')) for q in json.loads(p.read_text())['queries']]
def test(family,mode,source,rows,context=True):
 folder=emit(family,mode,source,context);binary=native(folder,family+'-'+mode);outputs=[]
 parse=json.loads((folder/'parse.json').read_text());assert parse['original_interpreted']==parse['result_interpreted'],parse
 for i,row in enumerate(rows):
  args=row['args'];want=row.get('expected_stdout',parse['original_interpreted']);out=c.run(f'{family}-{mode}-native-{i:02}',[binary,*map(str,args)],30).decode();assert out==want,(family,mode,args,out,want);outputs.append(dict(args=args,expected=want,stdout=out))
 return dict(family=family,mode=mode,source=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),emitted_sha256=hashlib.sha256((folder/'optimized.bril').read_bytes()).hexdigest(),main_sha256=hashlib.sha256((folder/'native/main.asm').read_bytes()).hexdigest(),outputs=outputs,queries=receipts(folder))
def main():
 phase=sys.argv[1] if len(sys.argv)>1 else 'positive';fixtures=ROOT/'fixtures';fixtures.mkdir(exist_ok=True)
 oracle=json.loads((SCREEN/'oracle.json').read_text());source=fixtures/'source.bril'
 if not source.exists():shutil.copy2(SCREEN/'source.bril',source)
 results=[]
 if phase=='positive':
  for mode in ['u0',*MODES]:results.append(test('positive',mode,source,oracle['positive_rows']))
 elif phase=='negative':
  for row in oracle['negative_rows']:
   kind=row['kind'];src=fixtures/(kind+'.bril')
   if not src.exists():shutil.copy2(SCREEN/kind/'source.bril',src)
   for mode in ['u0','off','seed-only','manual','encoding']:results.append(test(kind,mode,src,[row]))
 elif phase=='loop-negative':
  for field in ['mask','divisor']:
   src=fixtures/('changed-'+field+'.bril')
   if not src.exists():src.write_text(source.read_text().replace('  sum: int = add sum score;',f'  {field}: int = add {field} one;\n  sum: int = add sum score;'))
   for mode in ['u0','off','seed-only','manual','encoding']:results.append(test('changed-'+field,mode,src,[dict(args=[0,4294967296,8])]))
 elif phase=='context-negative':results.append(test('no-context','encoding',source,oracle['positive_rows'],False))
 else:raise ValueError(phase)
 (ROOT/(phase+'-results.json')).write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
