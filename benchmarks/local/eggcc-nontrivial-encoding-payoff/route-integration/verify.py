#!/usr/bin/env python3
"""Independent tagged-Route laws and exact-header source/emitted oracles."""
from pathlib import Path
import importlib.util,json,random,re
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('capture',BASE/'run.py');capture=importlib.util.module_from_spec(spec);spec.loader.exec_module(capture)
U0=BASE.parent/'admission/bin/eggcc'
MODULUS=1<<64

def wrap(value):
 bits=value%MODULUS
 return bits if bits<1<<63 else bits-MODULUS

def oracle(args,*,omit=None,different_selector=False,multiplier=3,mixed_true=False):
 a,b,c,d,z,w,q,r=args;p=q<r;s=r<q if different_selector else p
 left=(a,b) if p else (b,a);right=(c,d) if s else (d,c)
 if any(x!=y for index,(x,y) in enumerate(zip(left,right)) if index!=omit):return '3\n'
 same=wrap(c+z)==wrap(a+w)
 if same!=mixed_true:return '5\n'
 return '99\n' if wrap(multiplier*z)==wrap(multiplier*w) else '7\n'

def interpreted(label,path,args,expected):
 dest=BASE/'interpreted'/f'{label}.bril';dest.parent.mkdir(parents=True,exist_ok=True)
 dest.write_text(re.sub(r'^# ARGS:.*$','# ARGS: '+' '.join(map(str,args)),path.read_text(),count=1,flags=re.M))
 data=dest.with_suffix('.json')
 capture.run('interp-'+label,[U0,'--with-context','--run-mode','parse','--interp','--run-data-out',data,dest],30)
 observed=json.loads(data.read_text())
 assert observed['original_interpreted']==expected,(label,args,observed,expected)
 assert observed['result_interpreted']==expected,(label,args,observed,expected)
 return dict(label=label,args=args,expected=expected,actual=expected)

def laws():
 count=0
 for width in range(2,9):
  values=range(1<<width)
  keys={}
  assert len({3*x%(1<<width) for x in values})==len(values)
  for p in [False,True]:
   for a in values:
    for b in values:
     key=(p,a if p else b,b if p else a)
     assert key not in keys or keys[key]==(p,a,b)
     keys[key]=(p,a,b);count+=1
 randomizer=random.Random(0xA017E)
 pairs=[(a,b) for a in [-(1<<63),-1,0,1,(1<<63)-1] for b in [-(1<<63),-1,0,1,(1<<63)-1]]
 pairs += [(randomizer.randrange(-(1<<63),1<<63),randomizer.randrange(-(1<<63),1<<63)) for _ in range(4096)]
 for a,b in pairs:
  for p in [False,True]:
   x,y=(a,b) if p else (b,a)
   assert ((x,y) if p else (y,x))==(a,b)
 # Omitting the tag permits two distinct inputs with the same routed payloads.
 left_p,left_a,left_b=True,0,1
 right_p,right_a,right_b=False,1,0
 assert (left_a if left_p else left_b,left_b if left_p else left_a)==(right_a if right_p else right_b,right_b if right_p else right_a)
 assert (left_p,left_a,left_b)!=(right_p,right_a,right_b)
 return dict(exhaustive_tagged_inputs=count,i64_pairs=len(pairs),selector_outcomes=2,untagged_counterexample=dict(left=[True,0,1],right=[False,1,0],payload_output=[0,1]),mul2_counterexample=[0,-(1<<63)])

def main():
 results=[]
 positive=json.loads((BASE/'positive-oracle.json').read_text())
 for row in positive:assert oracle(row['args'])==row['expected_stdout']
 configs={'omitted-first-output':dict(omit=0),'omitted-second-output':dict(omit=1),'selector-tag-mismatch':dict(different_selector=True),'swapped-payload-tag-omitted':dict(different_selector=True),'even-multiplier':dict(multiplier=2),'wrong-branch':dict(mixed_true=True)}
 for family,settings in [('positive',{}),*configs.items()]:
  source=BASE/'fixtures'/('source.bril' if family=='positive' else family+'.bril')
  rows=positive if family=='positive' else [dict(args=[int(x) for x in source.read_text().splitlines()[0].removeprefix('# ARGS:').split()],expected_stdout='99\n')]
  roles=[('source',source)]+[(p.parent.name,p) for p in sorted((BASE/'matrix'/family).glob('*/optimized.bril'))]
  for index,row in enumerate(rows):
   expected=oracle(row['args'],**settings);assert expected==row['expected_stdout'],(family,row,expected)
   for role,path in roles:results.append(interpreted(f'{family}-{role}-{index:02}',path,row['args'],expected))
 for path in sorted((BASE/'matrix/no-context-final').glob('*/optimized.bril')):
  for index,row in enumerate(positive):results.append(interpreted(f'no-context-{path.parent.name}-{index:02}',path,row['args'],row['expected_stdout']))
 (BASE/'verification.json').write_text(json.dumps(dict(laws=laws(),interpretations=results,count=len(results)),indent=2)+'\n')
if __name__=='__main__':main()
