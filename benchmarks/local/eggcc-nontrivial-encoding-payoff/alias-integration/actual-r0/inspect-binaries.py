from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parent
rows=json.loads((R/'positive-results.json').read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def machine_function(text,symbol):
 m=re.search(r'^([0-9a-f]+) <'+re.escape(symbol)+r'>:\n',text,re.M);assert m,symbol
 following=re.search(r'^[0-9a-f]+ <[^>]+>:\n',text[m.end():],re.M)
 body=text[m.end():m.end()+following.start()] if following else text[m.end():]
 lines=[line for line in body.splitlines() if line]
 parsed=[]
 for line in lines:
  i=re.match(r'^([0-9a-f]+):\s+(\S+)(?:\s+(.*))?',line);assert i,line
  parsed.append((int(i[1],16),i[2],i[3] or ''))
 loops=[]
 for pc,op,operands in parsed:
  target=re.match(r'0x([0-9a-f]+)',operands)
  if target and (op=='b' or op.startswith('b.')):
   start=int(target[1],16)
   if int(m[1],16)<=start<pc:
    instructions=[(a,o,v) for a,o,v in parsed if start<=a<=pc]
    loops.append({'start':hex(start),'end':hex(pc),'instruction_count':len(instructions),'stores':sum(o=='str' for _,o,_ in instructions),'loads':sum(o=='ldr' for _,o,_ in instructions),'instructions':[f'{hex(a)}: {o} {v}' for a,o,v in instructions]})
 return {'instruction_count':len(parsed),'instruction_sha256':hashlib.sha256(('\n'.join(lines)+'\n').encode()).hexdigest(),'loops':loops,'body':'\n'.join(lines)+'\n'}
def llvm_function(text,name):
 m=re.search(r'^define[^\n]* @'+re.escape(name)+r'\([^\n]*\{\n',text,re.M);assert m,name
 end=text.index('\n}',m.end());body=text[m.start():end+2]+'\n'
 return {'loads_i64':len(re.findall(r'= load i64,',body)),'stores_i64':len(re.findall(r'^\s+store i64 ',body,re.M)),'body':body}
result=[]
for row in rows:
 folder=R/'matrix/positive'/row['mode'];native=folder/'native'
 asm=(native/'program.asm').read_text();ll=(native/'program.ll').read_text()
 functions={name:machine_function(asm,name) for name in ['__main','_main']}
 llvm={name:llvm_function(ll,name) for name in ['_main','main']}
 for name,v in functions.items():(native/(name+'-compact.asm')).write_text(v.pop('body'))
 for name,v in llvm.items():(native/(name+'-compact.ll')).write_text(v.pop('body'))
 result.append({'mode':row['mode'],'binary_sha256':digest(native/'program'),'assembly_sha256':digest(native/'program.asm'),'emitted_sha256':row['emitted_sha256'],'actual_binary_functions':functions,'llvm_functions':llvm,'exports':sum(x['exports'] for x in row['evidence'])})
assert len({r['emitted_sha256'] for r in result})==1
assert len({r['actual_binary_functions']['_main']['instruction_sha256'] for r in result})==1
assert all(r['llvm_functions']['_main']['loads_i64']==1 and r['llvm_functions']['_main']['stores_i64']==2 for r in result)
assert all(any(loop['loads']==1 and loop['stores']==2 for loop in r['actual_binary_functions']['_main']['loops']) for r in result)
out={'status':'no-endpoint-opportunity-in-this-attempt','actual_binary_inspected':True,'causal_code_difference':False,'all_emitted_bril_identical':True,'all_native_process_main_instructions_identical':True,'all_keep_hot_loop_one_load_two_stores':True,'timing_eligible':False,'performance_samples_taken':False,'rows':result}
(R/'inspection.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
