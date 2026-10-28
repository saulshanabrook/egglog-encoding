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
    disequality_encoding:'nee'};
  return {key,labels:['figures'],samples:values.map((value,index)=>({...key,row_index:index,
    started_at:new Date(Date.UTC(2026,9,1,0,0,index)).toISOString(),status:'success',timeout_sec:300,
    wall_sec:value,max_rss_bytes:value===null?null:value*1048576,...changes}))};
}
async function evaluate(name, inputs, groups, rounds=2) {
  const spec=JSON.parse(await readFile(new URL(`eval/${name}.vl.json`,import.meta.url),'utf8'));
  for(const p of spec.params) if(p.name==='selected_inputs')p.value=inputs.map(input=>({...input,
    selected_row_indices:input.selected_row_indices??groups.find(g=>g.labels.includes('figures')&&
      g.key.file_sha256===input.file_sha256&&g.key.fact_directory_sha256===input.fact_directory_sha256&&
      g.key.treatment===input.treatment)?.samples.slice(-rounds).map(row=>row.row_index)??[]}));
    else if(p.name==='rounds')p.value=rounds;
    else if(p.name==='t_critical')p.value=rounds===1?null:12.706204736432095;
  const warnings=[];
  const logger=vega.logger(vega.Warn,undefined,(...args)=>warnings.push(args));
  const runtime=compile(spec,{logger}).spec;
  const loader=vega.loader();
  loader.load=async()=>JSON.stringify({grouped_schema_version:2,report_schema_version:5,groups});
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
    assert.equal(find(c,'cdf_coverage').length,0);
    assert.match(c.svg,/unresolved baseline 1/);
  }
});
test('bound observations include failures and never borrow a moved label',async()=>{
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
    assert.match(c.svg,/50% coverage ≤/);
  }
});
test('strict validation veto applies only to checked proofs, missing RSS cannot change cohort',async()=>{
  const inputs=['off','term','proof-testing'].map(t=>input('a',t,{validation_failures:{'current/nee':'Known strict failure'}}));
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
  assert.equal(find(c,'cdf_thresholds').find(p=>p.datum.percentile===.95).datum.threshold_ratio,1000);
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

test('all figures use the bound original row IDs rather than a raw tail or recorded timeout',async()=>{
  for(const name of ['disequality-runtime','math-runtime','math-memory','corpus-runtime-cdf','corpus-memory-cdf']) {
    const treatments=name.startsWith('corpus')?['off','term','proof-testing']:
      name.startsWith('math')?['egg','egg-proof-testing','off','proof-testing']:['off'];
    const groups=treatments.map((t,i)=>group('a',t,[i+1,1000,i+1]));
    for(const g of groups) {
      g.samples[0].timeout_sec=600;
      g.samples[2].timeout_sec=120;
    }
    const inputs=treatments.map(t=>input('a',t,{selected_row_indices:[0,2]}));
    const result=await evaluate(name,inputs,groups);
    if(name.startsWith('corpus'))
      assert.deepEqual(find(result,'cdf_points').map(p=>p.datum.ratio),[2,3]);
    else
      assert.deepEqual(find(result,'absolute_means').map(p=>p.datum.mean),treatments.map((_,i)=>i+1));
    const empty=await evaluate(name,inputs.map(i=>({...i,selected_row_indices:[]})),groups);
    if(name.startsWith('corpus')) {
      assert.equal(find(empty,'cdf_points').length,0);
      assert.match(empty.svg,/unresolved baseline 1/);
    } else {
      assert.equal(find(empty,'absolute_runs').length,0);
      assert.match(empty.svg,/0\/2 observations/);
    }
  }
});

test('CDF family dots and direct 50/95 labels keep pooled ranks and intact glyph bounds',async()=>{
  const ids=['a','b','c','d'];
  const inputs=ids.flatMap((id,i)=>['off','term','proof-testing'].map(t=>input(id,t,{family:i%2?'misaal':'eggcc'})));
  const groups=ids.flatMap((id,i)=>[group(id,'off',[1,1]),group(id,'term',[2,2]),
    group(id,'proof-testing',[[2,2,4,1000][i],[2,2,4,1000][i]])]);
  for(const metric of ['runtime','memory']) {
    const result=await evaluate(`corpus-${metric}-cdf`,inputs,groups);
    const points=find(result,'cdf_points');
    const zoom=find(result,'cdf_points_zoom');
    assert.deepEqual(zoom.map(p=>[p.datum.workload_id,p.datum.mode,p.datum.ratio,p.datum.cdf]),
      points.map(p=>[p.datum.workload_id,p.datum.mode,p.datum.ratio,p.datum.cdf]));
    assert.notEqual(points.find(p=>p.datum.family==='eggcc').fill,points.find(p=>p.datum.family==='misaal').fill);
    const labels=[...find(result,'cdf_thresholds_zoom'),...find(result,'cdf_thresholds')];
    assert.equal(labels.length,4);
    assert.equal(labels.find(p=>p.datum.mode==='Checked proofs'&&p.datum.percentile===.95).datum.threshold_ratio,1000);
    for(const label of labels) {
      assert.ok(label.bounds.x1>=0&&label.bounds.x2<=310,`horizontal clipping: ${label.text}`);
      assert.ok(label.bounds.y1>=0&&label.bounds.y2<=label.mark.group.height,`vertical clipping: ${label.text}`);
    }
  }
});

test('Slotted compares exact physical endpoint rows per workload with Student-t and Fieller statistics',async()=>{
  for(const treatments of [['slotted-ref-multi','slotted'],['slotted-ref-nested','slotted-no-aliasing']]) {
    const inputs=['a','b'].flatMap((id,i)=>treatments.map(t=>input(id+'-'+t,t,{
      logical_id:id,label:`benchmarks/slotted/inputs/array/goal-2d-4f-N${i?10:2}.egg`,selected_row_indices:[0,2]})));
    const groups=['a','b'].flatMap(id=>treatments.map((t,i)=>group(id+'-'+t,t,[i?4:2,999,i?4:2])));
    const result=await evaluate('slotted-runtime',inputs,groups);
    assert.equal(find(result,'slotted_runs').filter(p=>p.opacity!==0).length,8);
    assert.deepEqual(find(result,'slotted_absolute_means').filter(p=>p.opacity!==0).map(p=>p.datum.mean),[2,4,2,4]);
    assert.deepEqual(find(result,'slotted_ratio_points').filter(p=>p.opacity!==0).map(p=>p.datum.ratio),[2,2]);
    assert.deepEqual(find(result,'slotted_ratio_intervals').filter(p=>p.opacity!==0).map(p=>[p.datum.ratio_low,p.datum.ratio_high]),[[2,2],[2,2]]);
    for(const guide of find(result,'slotted_equal')) {
      assert.equal(guide.y,0);
      assert.equal(guide.y2,guide.mark.group.height);
      assert.equal(guide.x2??guide.x,guide.x);
    }
    const runs=find(result,'slotted_runs').filter(p=>p.opacity!==0);
    assert.notEqual(runs.find(p=>p.datum.series==='Native Slotted').shape,runs.find(p=>p.datum.series==='Egglog encoding').shape);
    const labels=result.marks.filter(p=>p.mark.role==='axis-label').map(p=>p.text);
    assert.deepEqual(labels.filter(s=>s.startsWith('Array · N=')),['Array · N=2','Array · N=10']);
    assert.doesNotMatch(result.svg,/ratio_low, ratio_high/);
    assert.ok(!labels.some(label=>/goal-2d-4f-N|[.]egg$/.test(label)));
    for(const point of runs)assert.ok(point.bounds.y1>=0&&point.bounds.y2<=2*28,'run outside workload rows');
  }
});

test('Slotted empty, failed, zero-baseline and N1 conditions retain workload identity and explicit outcomes',async()=>{
  const treatments=['slotted-ref-multi','slotted'];
  const inputs=treatments.map(t=>input('a',t,{label:'benchmarks/slotted/inputs/logic/first-order-logic.egg'}));
  const empty=await evaluate('slotted-runtime',inputs,[]);
  assert.equal(find(empty,'slotted_ratio_points').filter(p=>p.opacity!==0).length,0);
  assert.match(empty.svg,/first-order-logic/);
  assert.match(empty.svg,/native 0\/2 runs; missing/);
  assert.match(empty.svg,/encoding 0\/2 runs; missing/);
  const failed=await evaluate('slotted-runtime',inputs,[group('a',treatments[0],[2,2]),
    group('a',treatments[1],[null,null],{status:'failure',error_exit_code:86})]);
  assert.equal(find(failed,'slotted_absolute_means').filter(p=>p.opacity!==0).length,1);
  assert.equal(find(failed,'slotted_ratio_points').filter(p=>p.opacity!==0).length,0);
  assert.match(failed.svg,/encoding 2\/2; 2 failed, 2 memory limit/);
  const zero=await evaluate('slotted-runtime',inputs,treatments.map((t,i)=>group('a',t,[i?2:0,i?2:0])));
  assert.equal(find(zero,'slotted_ratio_points').filter(p=>p.opacity!==0).length,0);
  assert.match(zero.svg,/native mean ≤0/);
  const one=await evaluate('slotted-runtime',inputs,treatments.map((t,i)=>group('a',t,[i?4:2])),1);
  assert.equal(find(one,'slotted_absolute_means').filter(p=>p.opacity!==0).length,0);
  assert.deepEqual(find(one,'slotted_runs').map(p=>p.datum.mean),[2,4]);
  assert.equal(find(one,'slotted_absolute_intervals').filter(p=>p.opacity!==0).length,0);
  assert.equal(find(one,'slotted_ratio_intervals').filter(p=>p.opacity!==0).length,0);
  assert.match(one.svg,/Pilot: one requested run\/configuration · no confidence intervals/);
  assert.doesNotMatch(one.svg,/n=1, no CI/);
  const resource=await evaluate('slotted-runtime',inputs,[group('a',treatments[0],[null],{status:'timed-out',timeout_sec:300}),
    group('a',treatments[1],[null],{status:'failure',error_exit_code:86,error_memory_limit_bytes:16*1024**3})],1);
  assert.match(resource.svg,/native timeout \(300 s\)/);
  assert.match(resource.svg,/encoding allocation limit \(16 GiB\)/);
  const rss=await evaluate('slotted-runtime',inputs,treatments.map(t=>group('a',t,[null],{status:'failure',error_message:'process-group RSS limit',error_memory_limit_bytes:10*1024**3})),1);
  assert.match(rss.svg,/memory limit \(10 GiB\)/);
  assert.doesNotMatch(rss.svg,/allocation limit/);
  const ten=await evaluate('slotted-runtime',inputs,treatments.map((t,i)=>group('a',t,Array(10).fill(i?4:2))),10);
  assert.equal(find(ten,'slotted_absolute_means').length,2);
  assert.deepEqual(find(ten,'slotted_ratio_intervals').map(p=>[p.datum.ratio_low,p.datum.ratio_high]),[[2,2]]);
  assert.match(ten.svg,/95% intervals: Student-t/);
  assert.doesNotMatch(ten.svg,/Pilot:/);
  const unbounded=await evaluate('slotted-runtime',inputs,[group('a',treatments[0],[.1,10]),group('a',treatments[1],[2,4])]);
  assert.equal(find(unbounded,'slotted_ratio_points').filter(p=>p.opacity!==0).length,1);
  assert.equal(find(unbounded,'slotted_ratio_intervals').filter(p=>p.opacity!==0).length,0);
  assert.match(unbounded.svg,/CI unbounded/);
});

test('Slotted full catalogs retain distinct readable rows and align the two comparison panels',async()=>{
  const names=[...Array.from({length:11},(_,n)=>`array/goal-2d-4f-N${n}.egg`),
    ...['batax','mmm','mmm_sum','mttkrp','ttm'].flatMap(k=>[1,2].map(p=>`sdql/${k}_${p===1?'1st':'2nd'}-44rules.egg`)),
    'logic/first-order-logic.egg','logic/first-order-logic2.egg'];
  const treatments=['slotted-ref-multi','slotted'];
  const inputs=names.flatMap((name,i)=>treatments.map(t=>input('case'+i,t,{label:'benchmarks/slotted/inputs/'+name})));
  const groups=names.flatMap((_,i)=>treatments.map((t,j)=>group('case'+i,t,[j?4:2,j?4:2])));
  for(const records of [groups,[]]) {
    const result=await evaluate('slotted-runtime',inputs,records);
    const rows=find(result,'slotted_status').sort((a,b)=>a.y-b.y);
    assert.equal(rows.length,23);
    assert.equal(new Set(rows.map(p=>p.y)).size,23,'workloads collapsed to a shared row');
    assert.ok(rows.at(-1).y-rows[0].y>=22*16,'plot height does not grow with workload count');
    const labels=result.marks.filter(p=>p.mark.role==='axis-label'&&rows.some(r=>r.datum.workload===p.text)).sort((a,b)=>a.y-b.y);
    assert.equal(labels.length,23);
    for(let i=1;i<labels.length;i++)assert.ok(labels[i-1].bounds.y2<labels[i].bounds.y1,`overlapping workload labels: ${labels[i].text}`);
    for(const mean of find(result,'slotted_absolute_means')) {
      const row=rows.find(p=>p.datum.logical_id===mean.datum.logical_id);
      assert.ok(Math.abs(mean.y+mean.height/2-mean.datum.series_offset-row.y)<1e-8,'absolute and ratio rows drifted');
    }
  }
});


test('absolute run jitter remains relative to its mean row in Math and disequality',async()=>{
  for(const name of ['disequality-runtime','math-runtime','math-memory']) {
    const treatments=name.startsWith('math')?['egg','egg-proof-testing','off','proof-testing']:['egg-de','egg-ee','egg-nee','egg-oee','off'];
    const result=await evaluate(name,treatments.map(t=>input('a',t)),treatments.map(t=>group('a',t,[2,4])));
    const means=find(result,'absolute_means');
    assert.equal(means.length,treatments.length);
    for(const run of find(result,'absolute_runs')) {
      const mean=means.find(m=>m.datum.input_id===run.datum.input_id);
      assert.ok(Math.abs(run.y-(mean.y+mean.height/2)-run.datum.jitter)<1e-8,`${name}: run jitter displaced from its mean row`);
      assert.ok(run.bounds.y1>=0&&run.bounds.y2<=treatments.length*(name.startsWith('math')?36:40));
    }
    if(name.startsWith('disequality'))for(const status of find(result,'absolute_status')) {
      const mean=means.find(m=>m.datum.input_id===status.datum.input_id);
      assert.ok(Math.abs(status.y-mean.y-mean.height/2)<1e-8,'disequality status and mean rows drifted');
    }
  }
});

test('Slotted symlog time axes keep zero, negative confidence bounds and sparse domains visible',async()=>{
  const treatments=['slotted-ref-multi','slotted'];
  const inputs=treatments.map(t=>input('a',t,{label:'benchmarks/slotted/inputs/array/goal-2d-4f-N0.egg'}));
  const cases=[[],treatments.map(t=>group('a',t,[null,null],{status:'timed-out'})),
    treatments.map(t=>group('a',t,[0,0])),treatments.map(t=>group('a',t,[.001,.001])),
    treatments.map(t=>group('a',t,[1,3]))];
  for(const groups of cases) {
    const result=await evaluate('slotted-runtime',inputs,groups);
    const labels=result.marks.filter(m=>m.mark.role==='axis-label'&&m.mark.group.datum?.scale==='concat_0_x');
    assert.ok(labels.length>0,'absolute axis label check did not run');
    assert.equal(new Set(labels.map(m=>m.text)).size,labels.length,'decimal axis values collapsed to the same label');
    if(groups[0]?.samples[0].wall_sec===.001)assert.ok(labels.some(m=>m.datum.value>0&&m.opacity!==0),'one-millisecond runtimes need a visible nonzero tick');
    for(const label of labels)assert.ok(label.bounds.x1>=-.5&&label.bounds.x2<=225.5,`absolute axis label outside its frame: ${label.text}`);
    for(const run of find(result,'slotted_runs'))assert.ok(Number.isFinite(run.x)&&run.x>=0&&run.x<=225,'zero or positive run absent from time domain');
    for(const ci of find(result,'slotted_absolute_intervals'))assert.ok(Number.isFinite(ci.x)&&Number.isFinite(ci.x2)&&ci.x>=0&&ci.x2<=225,'confidence interval clipped or lost');
    if(groups[0]?.samples[0].wall_sec===1) {
      assert.ok(find(result,'slotted_absolute_intervals').every(ci=>ci.datum.ci_low<0));
      assert.ok(labels.some(m=>m.datum.value<0),'negative confidence bounds need a negative axis tick');
    }
  }
});
