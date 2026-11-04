from pathlib import Path
import hashlib,json,sys
import run as capture
R=Path(__file__).resolve().parent
B=R.parents[1]
U0=B/'admission/bin/eggcc'
BIN=R/'bin/eggcc'
LLVM=Path('/opt/homebrew/opt/llvm@18/bin')
MODES=['u0','off','seed-only','seed-off','primitive-only','encoding','manual','reverse-off','shift-forward-off','cell-forward-off','query-off','transport-off','bridge-off','consumer-off','index-rescue','shift-rescue','cell-rescue','branch-alias-rescue']
ARGS=[(0,1,8),(1,0,8),(0,1,0),(0,1,1),(1,0,1024),(0,1,1000000),(0,0,8),(1,1,8),(-1,0,8),(2,0,8),(0,1,-1),(0,1,1000001)]
def oracle(args,variant='positive'):
 i,j,n=args
 if not (0<=i<2 and 0<=j<2 and 0<=n<=1000000):return '-2\n'
 if (i&1)==(j&(2 if variant=='different-mask' else 1)):return '-1\n'
 offsets=(i+1,j+(2 if variant=='different-shift' else 1))
 return str(0 if offsets[0]==offsets[1] or variant=='changed-pointer' else n*(n-1)//2)+'\n'
def case(family,mode,source,args,context=True):
 folder=R/'matrix'/family/mode;folder.mkdir(parents=True)
 capture.ENV.update(EGGCC_ALIAS_MODE='off' if mode=='u0' else mode,EGGCC_ALIAS_EVIDENCE=str(folder/'interp-evidence'))
 argv=[U0 if mode=='u0' else BIN]
 if context:argv+=['--with-context']
 argv+=['--run-mode','optimize']
 capture.run(f'{family}-{mode}-interp',[*argv,'--interp','--run-data-out',folder/'interp.json',source])
 interp=json.loads((folder/'interp.json').read_text())
 assert interp['original_interpreted']==interp['result_interpreted'],(family,mode,interp)
 capture.ENV['EGGCC_ALIAS_EVIDENCE']=str(folder/'evidence')
 emitted=capture.run(f'{family}-{mode}-emit',[*argv,'--egraph-out-dir',folder/'egraphs','--run-data-out',folder/'emit.json',source]);(folder/'optimized.bril').write_bytes(emitted)
 capture.ENV.pop('EGGCC_ALIAS_EVIDENCE',None);capture.ENV['EGGCC_ALIAS_MODE']='off'
 native=folder/'native';native.mkdir();binary=native/'program'
 capture.run(f'{family}-{mode}-lower',[U0,'--with-context','--run-mode','llvm','--optimize-egglog','false','--optimize-bril-llvm','O3_O3','-o',binary,'--llvm-output-dir',native/'program.ll','--run-data-out',native/'lower.json',folder/'optimized.bril'])
 asm=capture.run(f'{family}-{mode}-disassemble',[LLVM/'llvm-objdump','--disassemble','--no-show-raw-insn',binary],30);(native/'program.asm').write_bytes(asm)
 outputs=[]
 for idx,row in enumerate(args):
  expected=oracle(row,family);stdout=capture.run(f'{family}-{mode}-native-{idx:02}',[binary,*row],30).decode();outputs.append({'args':row,'expected_stdout':expected,'stdout':stdout});assert stdout==expected,(family,mode,row,stdout,expected)
 evidence=[json.loads(p.read_text()) for p in sorted((folder/'evidence').glob('*.json'))]
 result={'family':family,'mode':mode,'context':context,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'emitted_sha256':hashlib.sha256(emitted).hexdigest(),'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'outputs':outputs,'evidence':evidence,'timing_taken':False}
 (folder/'result.json').write_text(json.dumps(result,indent=2)+'\n');return result
phase=sys.argv[1];results=[]
if phase=='positive':
 for mode in MODES:results.append(case('positive',mode,R/'inputs/source.bril',ARGS))
elif phase=='negative':
 fixtures=R/'fixtures';fixtures.mkdir()
 source=(R/'inputs/source.bril').read_text()
 for variant,old,new,args in [('different-mask','mj: int = bitand j one;','mj: int = bitand j two;',[(1,1,8),(0,1,8)]),('different-shift','jj: int = add j one;','jj: int = add j two;',[(1,0,8)]),('changed-pointer','.body:\n','.body:\n  pi: ptr<int> = id pj;\n',[(0,1,8)])]:
  p=fixtures/(variant+'.bril');text=source.replace(old,new)
  if variant=='different-shift':text=text.replace('# ARGS: 0 1 8','# ARGS: 1 0 8')
  if variant=='different-mask':text=text.replace('# ARGS: 0 1 8','# ARGS: 1 1 8')
  p.write_text(text)
  for mode in ['u0','off','encoding','manual']:results.append(case(variant,mode,p,args))
 results.append(case('no-context','encoding',R/'inputs/source.bril',[(0,1,8)],False))
else:raise ValueError(phase)
(R/(phase+'-results.json')).write_text(json.dumps(results,indent=2)+'\n')
