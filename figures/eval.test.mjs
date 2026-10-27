import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {createRequire} from 'node:module';
import {existsSync, realpathSync} from 'node:fs';
import {delimiter, join} from 'node:path';
import test from 'node:test';

const cli = process.env.PATH.split(delimiter).map(p => join(p, 'vl2svg')).find(existsSync);
assert.ok(cli, 'Run make figures-test');
const toolkit = createRequire(realpathSync(cli));
const vega = await import(toolkit.resolve('vega'));
const {compile} = await import(toolkit.resolve('vega-lite'));
const input = (id, treatment, changes={}) => ({logical_id:id, label:id, family:'eggcc', file_sha256:id,
  fact_directory_sha256:'', treatment, validation_failures:{}, ...changes});
function group(id, treatment, values, changes={}) {
  const key={binary_sha256:'current',file_sha256:id,fact_directory_sha256:'',treatment,
    disequality_encoding:'nee',timeout_sec:300};
  return {key,labels:['figures'],samples:values.map((value,index)=>({...key,row_index:index,
    started_at:new Date(Date.UTC(2026,9,1,0,0,index)).toISOString(),status:'success',
    wall_sec:value,max_rss_bytes:value===null?null:value*1048576,...changes}))};
}
async function evaluate(name, inputs, groups, rounds=2) {
  const spec=JSON.parse(await readFile(new URL(`eval/${name}.vl.json`,import.meta.url),'utf8'));
  for(const p of spec.params) if(p.name==='selected_inputs')p.value=inputs;
    else if(p.name==='rounds')p.value=rounds;
    else if(p.name==='t_critical')p.value=rounds===1?null:12.706204736432095;
  const warnings=[];
  const logger=vega.logger(vega.Warn,undefined,(...args)=>warnings.push(args));
  const runtime=compile(spec,{logger}).spec;
  const loader=vega.loader();
  loader.load=async()=>JSON.stringify({grouped_schema_version:1,report_schema_version:5,groups});
  const view=new vega.View(vega.parse(runtime),{renderer:'none',loader,logger});
  try {
    await view.runAsync();
    const marks=[];
    function visit(item){if(item.mark&&item.datum)marks.push(item);for(const child of item.items??[])visit(child);}
    visit(view.scenegraph().root);
    assert.deepEqual(warnings,[]);
    return {marks,svg:await view.toSVG()};
  } finally {view.finalize();}
}
const find=(result,name)=>result.marks.filter(m=>m.mark.name===name+'_marks');

test('all five paper specs compile, preserve missing endpoints and render',async()=>{
  const modes=['egg-de','egg-ee','egg-nee','egg-oee','off'];
  const d=await evaluate('disequality-runtime',modes.map(t=>input('a',t)),[]);
  assert.equal(find(d,'absolute_status').length,5);
  assert.match(d.svg,/0\/2 observations/);
  for(const metric of ['runtime','memory']) {
    const math=['egg','egg-proof-testing','off','proof-testing'];
    const m=await evaluate(`math-${metric}`,math.map(t=>input('a',t)),[]);
    assert.equal(find(m,'ratio_status').length,2);
    const c=await evaluate(`corpus-${metric}-cdf`,['off','term','proof-testing'].map(t=>input('a',t)),[]);
    assert.equal(find(c,'cdf_coverage').length,2);
    assert.match(c.svg,/unresolved baseline 1/);
  }
});
test('newest N observations include failures and never borrow a moved label',async()=>{
  const a=group('a','off',[100,1,3]);
  const d=await evaluate('disequality-runtime',[input('a','off')],[a]);
  const mean=find(d,'absolute_means')[0].datum;
  assert.equal(mean.mean,2);
  assert.equal(mean.sample_n,2);
  assert.ok(Math.abs(mean.ci_high-(2+12.706204736432095))<1e-8);
  a.samples.at(-1).status='failure';
  const failed=await evaluate('disequality-runtime',[input('a','off')],[a]);
  assert.equal(find(failed,'absolute_means').length,0);
  a.labels=[];
  const moved=await evaluate('disequality-runtime',[input('a','off')],[a]);
  assert.equal(find(moved,'absolute_runs').length,0);
});
test('scope excludes unrelated cache groups and one run has a point but no interval',async()=>{
  const d=await evaluate('disequality-runtime',[input('a','off')],[group('a','off',[2]),group('b','off',[99])],1);
  assert.equal(find(d,'absolute_runs').length,1);
  assert.equal(find(d,'absolute_means')[0].datum.mean,2);
  assert.equal(find(d,'absolute_intervals').length,0);
  assert.match(d.svg,/CI unavailable/);
});
test('Math uses means, Student-t intervals and independent Fieller ratios for each engine',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const groups=treatments.map((t,i)=>group('a',t,i%2?[4,4]:[2,2]));
  for(const metric of ['runtime','memory']) {
    const m=await evaluate(`math-${metric}`,treatments.map(t=>input('a',t)),groups);
    assert.deepEqual(find(m,'ratio_points').map(p=>p.datum.ratio),[2,2]);
    assert.deepEqual(find(m,'ratio_intervals').map(p=>[p.datum.ratio_low,p.datum.ratio_high]),[[2,2],[2,2]]);
    assert.equal(find(m,'absolute_runs').length,8);
  }
});
test('CDF cohort uses >=.2 seconds without upper cutoff, shared denominator and 50/95 coverage',async()=>{
  const cases=[['boundary',.2],['slow',100],['fast',.199],['missing',1]];
  const inputs=cases.flatMap(([id])=>['off','term','proof-testing'].map(t=>input(id,t)));
  const groups=cases.flatMap(([id,v])=>[group(id,'off',[v,v]),group(id,'term',[v*2,v*2]),...(id==='missing'?[]:[group(id,'proof-testing',[v*3,v*3])])]);
  for(const metric of ['runtime','memory']) {
    const c=await evaluate(`corpus-${metric}-cdf`,inputs,groups);
    const dots=find(c,'cdf_points');
    assert.equal(dots.length,5);
    assert.ok(dots.every(p=>p.datum.cohort_n===3));
    assert.ok(!dots.some(p=>p.datum.workload_id==='fast'));
    assert.match(c.svg,/2\/3 valid/);
    assert.match(c.svg,/95% not established/);
    assert.match(c.svg,/50% measured coverage/);
  }
});
test('strict validation veto applies only to checked proofs, missing RSS cannot change cohort',async()=>{
  const inputs=['off','term','proof-testing'].map(t=>input('a',t,{validation_failures:{'current/300/nee':'Known strict failure'}}));
  const groups=['off','term','proof-testing'].map((t,i)=>group('a',t,[i+1,i+1]));
  const c=await evaluate('corpus-runtime-cdf',inputs,groups);
  assert.deepEqual(find(c,'cdf_points').map(p=>p.datum.mode),['Congruence']);
  groups[0].samples[0].max_rss_bytes=null;
  const memory=await evaluate('corpus-memory-cdf',inputs,groups);
  assert.equal(find(memory,'cdf_points').length,0);
  assert.match(memory.svg,/0\/1 valid/);
});

test('Fieller uncertainty retains an unbounded explanation and N1 ratios have no interval',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('a',t));
  const groups=treatments.map((t,i)=>group('a',t,i%2?[2,4]:[.1,10]));
  const m=await evaluate('math-runtime',inputs,groups);
  assert.equal(find(m,'ratio_points').length,2);
  assert.equal(find(m,'ratio_intervals').length,0);
  assert.match(m.svg,/Fieller interval unbounded or unavailable/);
  const one=await evaluate('math-runtime',inputs,treatments.map((t,i)=>group('a',t,[i%2?4:2])),1);
  assert.equal(find(one,'ratio_points').length,2);
  assert.equal(find(one,'ratio_intervals').length,0);
  assert.match(one.svg,/CI unavailable \(n=1\)/);
});

test('CDF ties use shared ranks, full tails and exact 95% inverse-CDF thresholds',async()=>{
  const inputs=['a','b','c','d'].flatMap(id=>['off','term','proof-testing'].map(t=>input(id,t)));
  const groups=['a','b','c','d'].flatMap((id,i)=>[group(id,'off',[1,1]),
    group(id,'term',[2,2]),group(id,'proof-testing',[[2,2,4,1000][i],[2,2,4,1000][i]])]);
  const c=await evaluate('corpus-runtime-cdf',inputs,groups);
  const checked=find(c,'cdf_points').filter(p=>p.datum.mode==='Checked proofs');
  assert.deepEqual(checked.map(p=>[p.datum.ratio,p.datum.cdf]),[[2,.5],[2,.5],[4,.75],[1000,1]]);
  assert.match(c.svg,/95% percentile ≤ 1.00e\+3×|95% percentile ≤ 1e\+3×|95% percentile ≤ 1000×/);
  assert.equal(find(c,'cdf_points_zoom').filter(p=>p.datum.mode==='Checked proofs').length,4);
});

test('a first-row timeout remains explicit when collection stopped before N',async()=>{
  const failed=group('a','off',[null],{status:'timed-out'});
  const d=await evaluate('disequality-runtime',[input('a','off')],[failed],10);
  assert.equal(find(d,'absolute_means').length,0);
  assert.match(d.svg,/1\/10 observations; 1 failed \(1 timeout\)/);
});

test('failed checked Math rows and unavailable ratios retain condition and engine axes',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('a',t));
  const groups=treatments.map((t,i)=>group('a',t,[i%2?null:2],i%2?{status:'failure',error_exit_code:86}:{}));
  for(const metric of ['runtime','memory']) {
    const result=await evaluate(`math-${metric}`,inputs,groups,1);
    const labels=result.marks.filter(m=>m.mark.role==='axis-label').map(m=>m.text);
    for(const label of ['Off · Egg','Checked · Egg','Off · Egglog','Checked · Egglog','Egg','Egglog'])
      assert.ok(labels.includes(label),`missing axis label: ${label}`);
    assert.equal(find(result,'absolute_runs').length,2);
    assert.equal(find(result,'ratio_points').length,0);
    assert.match(result.svg,/Checked · Egg: 1\/1 observations; 1 failed, 1 memory limit/);
    assert.match(result.svg,/Checked · Egglog: 1\/1 observations; 1 failed, 1 memory limit/);
    assert.match(result.svg,/Egg: Ratio unavailable/);
    assert.match(result.svg,/Egglog: Ratio unavailable/);
    const missing=await evaluate(`math-${metric}`,inputs,[],1);
    const missingLabels=missing.marks.filter(m=>m.mark.role==='axis-label').map(m=>m.text);
    for(const label of ['Off · Egg','Checked · Egg','Off · Egglog','Checked · Egglog','Egg','Egglog'])
      assert.ok(missingLabels.includes(label),`missing empty axis label: ${label}`);
  }
});

test('disequality statuses identify missing configurations without valid plotted marks',async()=>{
  const treatments=['egg-de','egg-ee','egg-nee','egg-oee','off'];
  const result=await evaluate('disequality-runtime',treatments.map(t=>input('a',t)),[]);
  for(const label of ['DE · Disegg','EE · Egg','NEE · Egg','OEE · Egg','NEE · Egglog'])
    assert.ok(find(result,'absolute_status').some(m=>m.datum.summary.startsWith(label+': ')));
});
