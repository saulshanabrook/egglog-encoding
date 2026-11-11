import assert from 'node:assert/strict';
import {readFile, readdir} from 'node:fs/promises';
import {createRequire} from 'node:module';
import {existsSync, realpathSync} from 'node:fs';
import {delimiter, join} from 'node:path';
import test from 'node:test';

const cli = process.env.PATH.split(delimiter).map(p => join(p, 'vl2svg')).find(existsSync);
assert.ok(cli, 'Run make check to use the pinned Vega environment');
const toolkit = createRequire(realpathSync(cli));
const vega = await import(toolkit.resolve('vega'));
const {compile} = await import(toolkit.resolve('vega-lite'));
const {figures} = JSON.parse(await readFile(new URL('catalog.json', import.meta.url), 'utf8'));
const input = (id, treatment, changes={}) => ({logical_id:id, label:id, family:'eggcc', file_sha256:id,
  binary_sha256:'current', memory_limit_bytes:null, treatment, exclusion:null, validation_failures:{}, ...changes});
function group(id, treatment, values, changes={}) {
  const key={binary_sha256:'current',file_sha256:id,treatment};
  return {key,labels:['figures'],samples:values.map((value,index)=>({...key,row_index:index,
    started_at:new Date(Date.UTC(2026,9,1,0,0,index)).toISOString(),status:'success',timeout_sec:300,
    wall_sec:value,max_rss_bytes:value===null?null:value*1048576,...changes}))};
}
async function evaluate(name, inputs, groups, rounds=2, boundSpec=null, treatmentsOverride=null) {
  const spec=boundSpec??JSON.parse(await readFile(new URL(figures[name].spec,import.meta.url),'utf8'));
  for(const p of spec.params) if(p.name==='selected_inputs')p.value=inputs.map(input=>({...input,
    selected_row_indices:input.selected_row_indices??groups.find(g=>g.labels.includes('figures')&&
      g.key.file_sha256===input.file_sha256&&
      g.key.treatment===input.treatment)?.samples.slice(-rounds).map(row=>row.row_index)??[]}));
    else if(p.name==='rounds')p.value=rounds;
    else if(p.name==='treatments')p.value=treatmentsOverride??figures[name].treatments;
    else if(p.name==='t_critical')p.value=({1:null,2:12.706204736432095,3:4.302652729749462,10:2.2621571628540993})[rounds];
  const warnings=[];
  const logger=vega.logger(vega.Warn,undefined,(...args)=>warnings.push(args));
  const runtime=compile(spec,{logger}).spec;
  const loader=vega.loader();
  loader.load=async()=>JSON.stringify({grouped_schema_version:7,report_schema_version:9,groups});
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

test('Math standard boxes preserve condition labels and selected arithmetic-mean ratio statistics',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('a',t,{selected_row_indices:[0,2,4]}));
  const groups=treatments.map((t,i)=>{
    const scale=[1,3,2,8][i];
    const record=group('a',t,[20*scale,999,21*scale,888,22*scale]);
    record.samples.forEach((row,j)=>row.max_rss_bytes=[300,99999,303,88888,306][j]*[1,5,2,12][i]*1048576);
    return record;
  });
  for(const records of [groups,[...groups].reverse()]) {
    const result=await evaluate('math-runtime',inputs,records,3);
    const boxes=result.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')&&p.mark.marktype==='rect');
    assert.equal(boxes.filter(p=>p.fill==='#d9d9d9').length,8,'four condition boxes per metric');
    assert.equal(find(result,'absolute_runs').length,0,'normal sample dots must not be overlaid');
    assert.equal(find(result,'absolute_means').length,0,'box medians must not be presented as arithmetic means');
    assert.equal(find(result,'absolute_intervals').length,0,'mean intervals belong in the exports');
    const points=find(result,'ratio_points');
    assert.deepEqual(points.filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.ratio),[3,4]);
    assert.deepEqual(points.filter(p=>p.datum.metric==='Peak RSS').map(p=>p.datum.ratio),[5,6]);
    assert.equal(find(result,'ratio_intervals').length,4);
    assert.equal(find(result,'ratio_cap_low').length,4);assert.equal(find(result,'ratio_cap_high').length,4);
    assert.equal(find(result,'ratio_equal').length,2);
    assert.ok(points.every(p=>p.shape==='square'&&p.fill==='#111111'));
    assert.equal(find(result,'ratio_status').length,0,'finite ratio intervals need no redundant text label');
    for(const {datum:ratio} of points) {
      const {baseline:b,candidate:c}=ratio;
      for(const estimate of [b,c]) {
        const scale=(ratio.metric==='Runtime'?[1,3,2,8]:[1,5,2,12])[treatments.indexOf(estimate.input.treatment)];
        const se=scale*(ratio.metric==='Runtime'?1:3)/Math.sqrt(3);
        assert.equal(estimate.mean,(ratio.metric==='Runtime'?21:303)*scale);
        assert.equal(estimate.sample_n,3);
        assert.deepEqual(estimate.input.selected_row_indices,[0,2,4]);
        assert.ok(Math.abs(estimate.ci_low-(estimate.mean-4.302652729749462*se))<1e-8);
        assert.ok(Math.abs(estimate.ci_high-(estimate.mean+4.302652729749462*se))<1e-8);
      }
      const a=b.mean**2-4.302652729749462**2*b.var_mean;
      const discriminant=(b.mean*c.mean)**2-a*(c.mean**2-4.302652729749462**2*c.var_mean);
      assert.ok(Math.abs(ratio.ratio_low-(b.mean*c.mean-Math.sqrt(discriminant))/a)<1e-8);
      assert.ok(Math.abs(ratio.ratio_high-(b.mean*c.mean+Math.sqrt(discriminant))/a)<1e-8);
    }
    const labels=result.marks.filter(p=>p.mark.role==='axis-label').map(p=>p.text);
    for(const condition of ['Proofs off · Egg','Proofs off · Egglog','Checked proofs · Egg','Checked proofs · Egglog'])
      assert.ok(labels.includes(condition),`missing explicit condition label ${condition}`);
  }
});

test('failed and missing Math endpoints retain every condition and explicit unavailable status',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('a',t));
  const groups=treatments.map((t,i)=>group('a',t,[i%2?null:2],i%2?{status:'memory-limited'}:{}));
  for(const records of [groups,[]]) {
    const result=await evaluate('math-runtime',inputs,records,1);
    const labels=result.marks.filter(m=>m.mark.role==='axis-label').map(m=>m.text);
    for(const label of ['Proofs off · Egg','Proofs off · Egglog','Checked proofs · Egg','Checked proofs · Egglog'])
      assert.ok(labels.includes(label),`missing condition label: ${label}`);
    assert.equal(find(result,'ratio_points').length,0);
    assert.ok(find(result,'ratio_status').every(p=>/Ratio unavailable/.test(p.datum.ratio_summary)));
    if(records.length) {
      assert.ok(find(result,'absolute_status').some(p=>/Checked · Egg: 1\/1 observations; 1 failed, 1 memory limit/.test(p.datum.condition_status)));
      assert.ok(find(result,'absolute_status').some(p=>/Checked · Egglog: 1\/1 observations; 1 failed, 1 memory limit/.test(p.datum.condition_status)));
    }
  }
});

test('missing or zero RSS and strict validation veto only affected boxes and estimates',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('a',t));
  const groups=treatments.map((t,i)=>group('a',t,[i%2?4:2,i%2?4:2]));
  groups[0].samples[0].max_rss_bytes=null;groups[2].samples[0].max_rss_bytes=0;
  const result=await evaluate('math-runtime',inputs,groups);
  assert.deepEqual(find(result,'ratio_points').map(p=>[p.datum.metric,p.datum.ratio]),[['Runtime',2],['Runtime',2]]);
  assert.equal(result.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')&&p.fill==='#d9d9d9').length,6);
  const strict=await evaluate('math-runtime',inputs.map(p=>({...p,validation_failures:{'current':'Known strict failure'}})),
    treatments.map((t,i)=>group('a',t,[i%2?4:2,i%2?4:2])));
  assert.equal(strict.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')&&p.fill==='#d9d9d9').length,6);
  assert.deepEqual(find(strict,'ratio_points').map(p=>[p.datum.engine,p.datum.metric]),[['Egg','Runtime'],['Egg','Peak RSS']]);
  assert.match(strict.svg,/Known strict failure/);
});

test('all figure designs preserve missing conditions and render without warnings',async()=>{
  for(const name of Object.keys(figures)) {
    const result=await evaluate(name,figures[name].treatments.map(t=>input('case',t)),[]);
    if(name==='disequality-runtime') {
      assert.equal(find(result,'absolute_status').length,4);
      assert.equal(find(result,'absolute_runs').length,0);
      assert.equal(find(result,'ratio_points').length,0);
    } else if(['slotted-runtime','slotted-multipattern-runtime'].includes(name)) {
      assert.equal(find(result,'slotted_ratio_status').length,1);
      assert.equal(find(result,'slotted_ratio_points').length,0);
    } else if(name.startsWith('corpus-')) {
      assert.doesNotMatch(result.svg,/unresolved baseline|failed,|missing|excluded/);
      assert.equal(find(result,'cdf_points').length,0,'empty corpus needs no overview');
    }
  }
});

test('disequality standard boxes show only native 1.5-IQR outliers, retaining DE and extlog',async()=>{
  assert.deepEqual(figures['disequality-runtime'].treatments,['egg-de','off']);
  assert.ok(['egg-ee','egg-oee'].every(t=>figures['disequality-runtime'].checks.includes(t)));
  const treatments=figures['disequality-runtime'].treatments;
  const groups=treatments.map((t,i)=>group('a',t,[1,1,1,1,1,1,1,1,1,100].map(v=>v*(i+1))));
  const result=await evaluate('disequality-runtime',treatments.map(t=>input('a',t)),groups,10);
  const labels=result.marks.filter(p=>p.mark.role==='axis-label').map(p=>p.text);
  for(const condition of ['Reference','extlog'])
    assert.ok(labels.includes(condition),`missing explicit condition label ${condition}`);
  const outliers=result.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')&&p.mark.marktype==='symbol');
  assert.equal(find(result,'absolute_runs').length,0,'there must be no all-run overlay');
  assert.equal(outliers.length,4,'one generated outlier per treatment and metric');
  for(const metric of ['Runtime','Peak RSS']) {
    assert.deepEqual(outliers.filter(p=>p.datum.metric===metric).map(p=>p.datum.value),[100,200]);
    for(const p of outliers.filter(p=>p.datum.metric===metric)) {
      assert.ok(p.bounds.x1>=0&&p.bounds.x2<=p.mark.group.width,'outliers must fit the absolute domain');
      assert.ok(p.bounds.y1>=0&&p.bounds.y2<=p.mark.group.height,'outliers must fit their treatment row');
      assert.equal(p.fill,'#111111');
    }
  }
  assert.equal(result.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')&&p.fill==='#d9d9d9').length,4);
  assert.doesNotMatch(result.svg,/NEE/);
  assert.match(result.svg,/extlog/);
  assert.match(result.svg,/Reference/);
  assert.equal(find(result,'ratio_points').length,0);
  assert.equal(find(result,'absolute_means').length,0);
});

test('disequality selection and incomplete/quarantined conditions never create misleading boxes',async()=>{
  const rows=group('a','off',[999,1,3]);
  const inputs=[input('a','off',{selected_row_indices:[1,2]})];
  const valid=await evaluate('disequality-runtime',inputs,[rows]);
  const outliers=valid.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')&&p.mark.marktype==='symbol');
  assert.equal(outliers.length,0,'unselected historical extremes must not become outliers');
  assert.equal(valid.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')&&p.fill==='#d9d9d9').length,2);
  rows.samples[2].status='timed-out';
  const failed=await evaluate('disequality-runtime',inputs,[rows]);
  assert.equal(failed.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')).length,0);
  assert.match(failed.svg,/1 failed, 1 timeout/);
  const excluded=await evaluate('disequality-runtime',[input('a','off',{selected_row_indices:[],exclusion:{kind:'expected-failure',reason:'known bug'}})],[rows]);
  assert.equal(excluded.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')).length,0);
  assert.match(excluded.svg,/Excluded \(expected-failure\)/);
  rows.labels=[];
  assert.equal((await evaluate('disequality-runtime',inputs,[rows])).marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')).length,0);
});

test('Slotted runtime ratios sort independently with one full-width panel and capped intervals',async()=>{
  for(const name of ['slotted-runtime','slotted-multipattern-runtime']) {
    const treatments=figures[name].treatments;
    const ids=['mmm_1st-44rules','mmm_2nd-44rules','ttm_1st-44rules'];
    const ratios=name==='slotted-runtime'?[12,.5,2]:[.5,12,2];
    const inputs=ids.flatMap(id=>treatments.map(t=>input(id+'-'+t,t,{logical_id:id,label:`${id}.egg`})));
    const groups=inputs.map((item,i)=>group(item.file_sha256,item.treatment,
      [20,21,22].map(v=>v*(i%2?ratios[Math.floor(i/2)]:1)),
      {max_rss_bytes:(i%2?1000000:1)*1048576}));
    const result=await evaluate(name,inputs,groups,3);
    const points=find(result,'slotted_ratio_points');
    assert.equal(points.length,3);
    assert.ok(points.every(p=>p.datum.metric==='Runtime'&&p.fill==='#111111'&&p.shape==='square'));
    const ordered=[...points].sort((a,b)=>a.y-b.y);
    assert.deepEqual(ordered.map(p=>p.datum.ratio),[.5,2,12]);
    assert.ok(points.every(p=>p.mark.group.width===500),'one panel uses the available width without magnifying fonts');
    assert.equal(find(result,'slotted_ratio_intervals').length,3);
    assert.equal(find(result,'slotted_ratio_cap_low').length,3);assert.equal(find(result,'slotted_ratio_cap_high').length,3);
    const guides=find(result,'slotted_equal');assert.equal(guides.length,1);
    for(const guide of guides){assert.equal(guide.y,0);assert.equal(guide.y2,guide.mark.group.height);assert.equal(guide.stroke,'#727880');}
    assert.equal(find(result,'slotted_runs').length,0);
    assert.ok(!result.marks.some(p=>p.mark.marktype==='line'),'no lines may connect workloads');
    assert.doesNotMatch(result.svg,/Peak RSS/);
    const labels=result.marks.filter(p=>p.mark.role==='axis-label').map(p=>p.text);
    for(const label of ['MMM · 1st','MMM · 2nd','TTM · 1st'])assert.equal(labels.filter(v=>v===label).length,1);
    const required=['0×','0.1×','0.25×','0.5×','0.75×','1×'];
    const ticks=result.marks.filter(p=>p.mark.role==='axis-label'&&required.includes(p.text)&&p.opacity!==0);
    assert.deepEqual(ticks.map(p=>p.text),required,'all sub-unit labels must remain visible');
    for(let i=1;i<ticks.length;i++)assert.ok(ticks[i].bounds.x1-ticks[i-1].bounds.x2>=2,'numeric tick labels need clear gaps');
    const grids=result.marks.filter(p=>p.mark.role==='axis-grid'&&p.opacity!==0);
    for(const value of [.1,.25,.5,.75,1])
      assert.ok(grids.some(p=>p.datum.value===value&&p.stroke==='#e8eaed'&&p.strokeWidth===.7),'light grid anchors complement the stronger dashed 1× guide');
  }
});

test('complete SDQL ratios pair the native multipattern fork with Egglog',async()=>{
  const name='slotted-multipattern-runtime';
  const treatments=figures[name].treatments;
  assert.deepEqual(treatments,['slotted-ref-multi','slotted']);
  assert.equal(figures[name].spec,figures['slotted-runtime'].spec,'both figures must share their authored transforms');
  const labels=['mmm_1st-44rules.egg','mmm_2nd-44rules.egg'];
  const inputs=labels.flatMap(label=>treatments.map(t=>input(label+'-'+t,t,{logical_id:label,label})));
  const groups=inputs.map((item,i)=>group(item.file_sha256,item.treatment,
    [20,21,22].map(value=>value*(i%2?[3,4][Math.floor(i/2)]:1)),
    {max_rss_bytes:(i%2?[5,6][Math.floor(i/2)]:1)*100*1048576}));
  const result=await evaluate(name,inputs,groups,3);
  const points=find(result,'slotted_ratio_points');
  assert.equal(points.length,2);
  assert.deepEqual(points.filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.ratio),[3,4]);
  assert.ok(points.every(p=>p.datum.metric==='Runtime'));
  assert.ok(points.every(p=>p.datum.baseline.input.treatment==='slotted-ref-multi'&&p.datum.candidate.input.treatment==='slotted'));
  assert.equal(find(result,'slotted_ratio_intervals').length,2);
  const axisLabelMarks=result.marks.filter(p=>p.mark.role==='axis-label');
  const axisLabels=axisLabelMarks.map(p=>p.text);
  assert.ok(axisLabelMarks.some(p=>p.text==='0.25×'&&p.opacity!==0),'the sub-unit scale includes a visible quarter reference');
  const halfTicks=axisLabelMarks.filter(p=>p.text==='0.5×'&&p.opacity!==0);
  assert.equal(halfTicks.length,1,'the runtime panel needs a visible 0.5× reference');
  for(const half of halfTicks) {
    const equal=axisLabelMarks.find(p=>p.mark===half.mark&&p.text==='1×');
    assert.ok(equal&&equal.opacity!==0,'the 1× reference must remain visible');
    assert.ok(half.bounds.x2+2<=equal.bounds.x1,'the 0.5× label must not crowd 1×');
  }
  assert.match(result.svg,/extlog \/ Reference \(symlog\)/);
  for(const label of ['MMM · 1st','MMM · 2nd'])
    assert.equal(axisLabels.filter(value=>value===label).length,1,'kernel/phase labels must appear once beside aligned panels');
});

test('complete multipattern figure retains the selected original SDQL rows',async()=>{
  const name='slotted-multipattern-runtime';
  const directory='../benchmarks/slotted/inputs/sdql/';
  assert.equal(figures[name].files[0],directory+'*.egg');
  const excluded=new Set(figures[name].files.slice(1).map(pattern=>pattern.slice(1)));
  const paths=(await readdir(new URL(directory,import.meta.url)))
    .filter(file=>file.endsWith('.egg')&&!excluded.has(directory+file)).sort()
    .map(file=>directory.slice(3)+file);
  assert.equal(paths.length,8);
  assert.ok(paths.every(path=>path.includes('/inputs/sdql/')&&!['batax_2nd-44rules.egg','mttkrp_2nd-44rules.egg'].includes(path.split('/').at(-1))));
  const inputs=paths.flatMap(path=>figures[name].treatments.map(t=>input(path+'-'+t,t,{logical_id:path,label:path})));
  const groups=inputs.map((item,i)=>group(item.file_sha256,item.treatment,
    [20,21,22].map(value=>value*(i%2?3:1)),{max_rss_bytes:(i%2?5:1)*100*1048576}));
  const result=await evaluate(name,inputs,groups,3);
  const points=find(result,'slotted_ratio_points');
  assert.equal(points.length,paths.length);
  assert.equal(find(result,'slotted_ratio_status').length,0);
  assert.ok(points.every(p=>p.datum.metric==='Runtime'&&p.datum.ratio===3));
  const labels=result.marks.filter(p=>p.mark.role==='axis-label').map(p=>p.text);
  const expected=paths.map(path=>{
    const stem=path.split('/').at(-1).replace(/\.egg$/,'');
    const kernel=stem.replace(/_(1st|2nd)-44rules$/,'');
    return ({batax:'BATAX',mmm:'MMM',mmm_sum:'ΣMMM',mttkrp:'MTTKRP',ttm:'TTM'}[kernel])+' · '+(stem.includes('_1st-')?'1st':'2nd');
  });
  assert.equal(new Set(expected).size,paths.length);
  for(const label of expected) {
    assert.equal(labels.filter(value=>value===label).length,1,'one full shared label for each workload');
    assert.ok(result.svg.includes('>'+label+'<'),'labels must render completely without truncation');
  }
  assert.deepEqual(new Set(points.map(p=>p.datum.candidate.input.label)),new Set(inputs.map(item=>item.label)));
});

test('Slotted retains failed, missing-metric, excluded and unbounded outcomes separately',async()=>{
  for(const name of ['slotted-runtime','slotted-multipattern-runtime']) {
    const treatments=figures[name].treatments;
    const inputs=treatments.map(t=>input(t,t,{logical_id:'a',label:'batax_1st-44rules.egg'}));
    const groups=inputs.map((item,i)=>group(item.file_sha256,item.treatment,i?[4,6]:[1,2]));
    groups[0].samples[0].max_rss_bytes=null;
    const result=await evaluate(name,inputs,groups);
    assert.deepEqual(find(result,'slotted_ratio_points').map(p=>p.datum.metric),['Runtime']);
    assert.ok(find(result,'slotted_ratio_status').every(p=>p.datum.metric==='Runtime'&&!/metric missing/.test(p.text)));
    const noRuntime=structuredClone(groups);noRuntime[0].samples[0].wall_sec=null;
    const missing=await evaluate(name,inputs,noRuntime);
    assert.equal(find(missing,'slotted_ratio_points').length,0);
    assert.ok(find(missing,'slotted_ratio_status').some(p=>/metric missing/.test(p.text)));
    groups[1].samples[0].status='memory-limited';
    const failed=await evaluate(name,inputs,groups);
    assert.equal(find(failed,'slotted_ratio_points').length,0);
    assert.match(failed.svg,/memory limit/);
    const excluded=await evaluate(name,inputs.map(i=>({...i,exclusion:{kind:'unsupported',reason:'recorded limitation'},selected_row_indices:[]})),groups);
    assert.match(excluded.svg,/excluded \(unsupported\)/);
    const one=await evaluate(name,inputs,inputs.map((item,i)=>group(item.file_sha256,item.treatment,[i?2:1])),1);
    assert.equal(find(one,'slotted_ratio_points').length,1);
    assert.equal(find(one,'slotted_ratio_intervals').length,0);
    assert.match(one.svg,/n=1; CI unavailable/);
  }
});

test('CDF recording aliases retain strict vetoes and baseline-wall cohort with missing RSS',async()=>{
  assert.deepEqual(figures['corpus-proof-recording-cdf'].treatments,['off','proofs']);
  const ids=[['boundary',.2],['slow',100],['fast',.199],['missing',1]];
  for(const [name,treatment] of [['congruence','term'],['proof-recording','proofs']]) {
    const inputs=ids.flatMap(([id])=>['off',treatment].map(t=>input(id,t)));
    const groups=ids.flatMap(([id,v])=>[group(id,'off',[v,v]),...(id==='missing'?[]:[group(id,treatment,[v*2,v*2])])]);
    const result=await evaluate(`corpus-${name}-cdf`,inputs,groups);
    const points=find(result,'cdf_points_zoom');
    assert.equal(points.length,4);
    assert.ok(points.every(p=>p.datum.cohort_n===3&&p.datum.saved_n===4&&p.datum.too_fast_n===1));
    assert.equal(find(result,'cdf_detail_status').length,0);
    assert.equal(find(result,'cdf_coverage').length,0);
    assert.doesNotMatch(result.svg,/failed,|missing|excluded|not established/);
    assert.equal(find(result,'cdf_points').length,0,'compact ratios need no overview');
    const vetoed=inputs.map(i=>({...i,validation_failures:{'current':'Known strict failure'}}));
    const strict=await evaluate(`corpus-${name}-cdf`,vetoed,groups);
    assert.equal(find(strict,'cdf_points_zoom').length,name==='proof-recording'?0:4);
    groups[0].samples[0].max_rss_bytes=null;
    const rss=await evaluate(`corpus-${name}-cdf`,inputs,groups);
    assert.ok(find(rss,'cdf_points_zoom').every(p=>p.datum.cohort_n===3));
    assert.equal(find(rss,'cdf_points_zoom').filter(p=>p.datum.metric==='Peak RSS').length,1);
  }
});

test('CDF overview appears only for metrics with tails and never changes ranks or denominator',async()=>{
  for(const [name,treatment] of [['congruence','term'],['proof-recording','proofs']]) {
    const ids=['a','b','c','d'];
    const inputs=ids.flatMap(id=>['off',treatment].map(t=>input(id,t)));
    const groups=ids.flatMap((id,i)=>[group(id,'off',[1,1]),group(id,treatment,[[2,2,4,1000][i],[2,2,4,1000][i]],{max_rss_bytes:2*1048576})]);
    const result=await evaluate(`corpus-${name}-cdf`,inputs,groups);
    const full=find(result,'cdf_points'),zoom=find(result,'cdf_points_zoom');
    assert.equal(full.length,4);assert.ok(full.every(p=>p.datum.metric==='Runtime'));
    assert.deepEqual(full.map(p=>[p.datum.ratio,p.datum.cdf]),[[2,.5],[2,.5],[4,.75],[1000,1]]);
    assert.equal(zoom.length,8);assert.ok(zoom.every(p=>p.datum.cohort_n===4));
    assert.equal(find(result,'cdf_thresholds').find(p=>p.datum.percentile===.95).datum.threshold_ratio,1000);
    for(const point of full)assert.ok(point.bounds.x1>=0&&point.bounds.x2<=point.mark.group.width);
    groups.at(-1).samples[0].status='failure';
    const partial=await evaluate(`corpus-${name}-cdf`,inputs,groups);
    assert.ok(find(partial,'cdf_points_zoom').every(p=>p.datum.measured_n===3&&p.datum.cohort_n===4));
    assert.doesNotMatch(partial.svg,/failed,|not established/);
  }
});

test('CDF overviews retain metric columns when just one has a tail',async()=>{
  for(const [runtimeTail,memoryTail] of [[false,false],[true,false],[false,true],[true,true]]) {
    const ids=['a','b','c','d'];
    const inputs=ids.flatMap(id=>['off','proofs'].map(t=>input(id,t)));
    const groups=ids.flatMap((id,i)=>[group(id,'off',[1,1]),
      group(id,'proofs',[runtimeTail&&i===3?1000:2,runtimeTail&&i===3?1000:2],
        {max_rss_bytes:(memoryTail&&i===3?1000:2)*1048576})]);
    const result=await evaluate('corpus-proof-recording-cdf',inputs,groups);
    const titles=result.marks.filter(p=>p.mark.role==='axis-title').map(p=>p.text);
    assert.deepEqual(titles.filter(title=>title.endsWith(' · full range')),
      [runtimeTail?'Runtime · full range':null,memoryTail?'Peak RSS · full range':null].filter(Boolean));
    const percentLabels=result.marks.filter(p=>p.mark.role==='axis-label'&&p.opacity!==0&&['0%','50%','100%'].includes(p.text));
    assert.equal(percentLabels.length,3+3*(Number(runtimeTail)+Number(memoryTail)),
      'only metrics with tails should show overview axes');
    for(const [metric,hasTail] of [['Runtime',runtimeTail],['Peak RSS',memoryTail]]) {
      const overview=find(result,'cdf_points').filter(p=>p.datum.metric===metric);
      assert.equal(overview.length,hasTail?4:0);
      if(hasTail) {
        const detail=find(result,'cdf_points_zoom').find(p=>p.datum.metric===metric);
        assert.equal(overview[0].mark.group.x,detail.mark.group.x,
          `${metric} overview must remain beneath its own detail panel`);
      }
    }
  }
});

test('CDF quarantines preserve coverage without measured points or altered denominator',async()=>{
  const result=await evaluate('corpus-proof-recording-cdf',[
    input('a','off'),input('a','proofs',{selected_row_indices:[],exclusion:{kind:'expected-failure',reason:'known table mismatch'}}),
    input('b','off'),input('b','proofs')
  ],[group('a','off',[1,1]),group('a','proofs',[99,99]),group('b','off',[1,1]),group('b','proofs',[2,2])]);
  assert.equal(find(result,'cdf_coverage').length,0);
  assert.doesNotMatch(result.svg,/failed,|excluded/);
  assert.ok(find(result,'cdf_points_zoom').every(p=>p.datum.cohort_n===2&&p.datum.measured_n===1&&p.datum.cdf===.5));
});

test('executed Vega Slotted statistics match the shared export fixture',async()=>{
  for(const name of ['slotted-runtime','slotted-multipattern-runtime']) {
    const fixture=JSON.parse(await readFile(new URL('../benchmarking/tests/figure_statistics.json',import.meta.url),'utf8'));
    for(const [i,treatment] of figures[name].treatments.entries()) {
      fixture.inputs[i].treatment=fixture.groups[i].key.treatment=treatment;
      for(const row of fixture.groups[i].samples)row.treatment=treatment;
    }
    const result=await evaluate(name,fixture.inputs,fixture.groups,fixture.rounds);
    const points=find(result,'slotted_ratio_points');
    assert.equal(points.length,1);
    for(const {datum:row} of points) {
      const expected=fixture.expected[row.metric];
      for(const field of ['ratio','ratio_low','ratio_high'])assert.ok(Math.abs(row[field]-expected[field])<1e-9,`${row.metric} ${field}`);
      assert.equal(row.baseline.mean,expected.baseline_mean);
      assert.equal(row.candidate.mean,expected.candidate_mean);
      assert.ok(Math.abs(row.candidate.ci_low-expected.candidate_ci_low)<1e-9);
      assert.ok(Math.abs(row.candidate.ci_high-expected.candidate_ci_high)<1e-9);
    }
  }
});

test('CDF empty, zero, single-run and failed samples retain finite reference-containing dynamic domains',async()=>{
  const treatment='proofs';
  const inputs=['off',treatment].map(t=>input('a',t));
  for(const [groups,rounds] of [
    [[],2],
    [[group('a','off',[1,1]),group('a',treatment,[0,0])],2],
    [[group('a','off',[1]),group('a',treatment,[1])],1],
    [[group('a','off',[1,1]),group('a',treatment,[null,null],{status:'timed-out'})],2]
  ]) {
    const result=await evaluate('corpus-proof-recording-cdf',inputs,groups,rounds);
    assert.doesNotMatch(result.svg,/NaN|Infinity|failed,|not established/);
    for(const point of find(result,'cdf_points_zoom')) {
      assert.ok(Number.isFinite(point.x)&&point.bounds.x1>=0&&point.bounds.x2<=point.mark.group.width);
      assert.ok(Number.isFinite(point.y)&&point.bounds.y1>=0&&point.bounds.y2<=point.mark.group.height);
    }
  }
  for(const [mode,treatment] of [['congruence','term'],['proof-recording','proofs']]) {
    const inputs=['a','b','c','d'].flatMap(id=>['off',treatment].map(t=>input(id,t)));
    const groups=[...['a','b','c'].map(id=>group(id,'off',[1,1])),group('a',treatment,[2,2])];
    const partial=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    assert.equal(find(partial,'cdf_detail_status').length,0);
    assert.equal(find(partial,'cdf_coverage').length,0);
    assert.ok(find(partial,'cdf_points_zoom').every(p=>p.datum.cohort_n===3&&p.datum.measured_n===1&&p.datum.unresolved_n===1));

  }
});


test('Math N1 and unbounded Fieller estimates remain explicit; finite endpoints retain bounds',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('case',t));
  const one=await evaluate('math-runtime',inputs,treatments.map((t,i)=>group('case',t,[i%2?4:2])),1);
  assert.equal(find(one,'ratio_points').length,4);
  assert.equal(find(one,'ratio_intervals').length,0);
  assert.match(one.svg,/CI unavailable \(n=1\)/);
  const unbounded=await evaluate('math-runtime',inputs,treatments.map((t,i)=>group('case',t,i%2?[2,4]:[.1,10])));
  assert.equal(find(unbounded,'ratio_points').length,4);
  assert.equal(find(unbounded,'ratio_intervals').length,0);
  assert.match(unbounded.svg,/Fieller interval unbounded or unavailable/);
});

test('Slotted interval/point alignment and status glyphs stay inside their workload rows',async()=>{
  const treatments=figures['slotted-runtime'].treatments;
  const labels=['batax_1st-44rules.egg','batax_2nd-44rules.egg','mmm_1st-44rules.egg'];
  const inputs=labels.flatMap((label,k)=>treatments.map(t=>input(`${k}-${t}`,t,{logical_id:`${k}`,label})));
  const groups=inputs.map((item,i)=>group(item.file_sha256,item.treatment,[20+i,21+i,22+i],{max_rss_bytes:(i+1)*100*1048576}));
  const result=await evaluate('slotted-runtime',inputs,groups,3);
  for(const point of find(result,'slotted_ratio_points')) {
    const interval=find(result,'slotted_ratio_intervals').find(p=>p.datum.logical_id===point.datum.logical_id&&p.datum.metric===point.datum.metric);
    assert.ok(Math.abs(interval.y-point.y)<1e-8,'ratio point and interval must align');
    assert.ok(point.bounds.y1>=0&&point.bounds.y2<=point.mark.group.height);
  }
  const missing=await evaluate('slotted-runtime',inputs,[],3);
  for(const status of find(missing,'slotted_ratio_status')) {
    assert.ok(status.bounds.x1>=0&&status.bounds.x2<=status.mark.group.width,'missing status must fit horizontally');
    assert.ok(status.bounds.y1>=0&&status.bounds.y2<=status.mark.group.height,'missing status must fit its row');
    assert.match(status.text,/Reference: 0\/3 runs; missing\nextlog: 0\/3 runs; missing/);
    assert.equal(status.dy,-5,'two endpoint messages keep multiline positioning');
  }
  for(const [endpoint,selected] of [
    ['extlog',groups.filter(g=>g.key.treatment.includes('ref-'))],
    ['Reference',groups.filter(g=>!g.key.treatment.includes('ref-'))]
  ]) {
    const standalone=await evaluate('slotted-runtime',inputs,selected,3);
    for(const status of find(standalone,'slotted_ratio_status')) {
      assert.equal(status.text,endpoint+': 0/3 runs; missing');
      assert.equal(status.dy,0,'a standalone status is one centered line');
      assert.ok(status.bounds.y1>=0&&status.bounds.y2<=status.mark.group.height);
    }
  }

});

test('CDF domains fit each metric, magnify compact data and separate heavy tails without changing ranks',async()=>{
  for(const [mode,treatment] of [['congruence','term'],['proof-recording','proofs']]) {
    for(const [times,rss,expected] of [
      [[1.1,2,2.3,2.7],[1.1,1.5,1.6,1.9],{'Runtime':[1,2.7,2.7],'Peak RSS':[1,1.9,1.9]}],
      [[2,3,4,200],[1.5,2,4,80],{'Runtime':[1,7,200],'Peak RSS':[1,6,80]}]
    ]) {
      const inputs=times.flatMap((_,i)=>['off',treatment].map(t=>input('case'+i,t)));
      const groups=times.flatMap((v,i)=>[group('case'+i,'off',[1,1]),group('case'+i,treatment,[v,v],{max_rss_bytes:rss[i]*1048576})]);
      const result=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
      for(const [metric,[minimum,zoom,full]] of Object.entries(expected)) {
        const points=find(result,'cdf_points_zoom').filter(p=>p.datum.metric===metric);
        assert.deepEqual(points.map(p=>p.datum.cdf),[.25,.5,.75,1]);
        assert.ok(points.every(p=>Math.abs(p.datum.zoom_min-minimum)<1e-8&&Math.abs(p.datum.zoom_max-zoom)<1e-8&&Math.abs(p.datum.full_max-full)<1e-8));
        const region=find(result,'cdf_zoom_region').find(p=>p.datum.metric===metric);
        if(full>zoom) {
        assert.ok(Math.abs(region.x-(4+(region.mark.group.width-8)*minimum/full))<1e-8,'overview shade must start at the zoom lower bound');
        assert.ok(Math.abs(region.x2-(4+(region.mark.group.width-8)*zoom/full))<1e-8,'overview shade must end at the zoom upper bound');
        } else assert.equal(region,undefined,'no overview when zoom covers all values');
        assert.ok(zoom-minimum<full,'compact data must still have a genuine baseline-context zoom');
        assert.equal(find(result,'cdf_detail_status').length,0,'complete figures need no valid-count badge');
      }
    }
  }
});

test('executed corpus coverage and bound SVG layout match the shared paper-export fixture',async()=>{
  const {corpus}=JSON.parse(await readFile(new URL('../benchmarking/tests/figure_statistics.json',import.meta.url),'utf8'));
  const authored=JSON.parse(await readFile(new URL(figures['corpus-proof-recording-cdf'].spec,import.meta.url),'utf8'));
  // The Python binder is independently checked against these same layout
  // values and whole-composition removal. Execute its bound shape here.
  const bound=structuredClone(authored);
  for(const p of bound.params)if(p.name==='view_domains'){delete p.expr;p.value=corpus.view_domains;}
  bound.vconcat.splice(1,1);
  const result=await evaluate('corpus-proof-recording-cdf',corpus.inputs,corpus.groups,3,bound);
  const points=find(result,'cdf_points_zoom');
  for(const metric of ['Runtime','Peak RSS']) {
    const rows=points.filter(p=>p.datum.metric===metric);
    assert.equal(rows.length,corpus.expected.measured_n);
    for(const {datum:row} of rows)for(const field of ['saved_n','cohort_n','measured_n','too_fast_n','unresolved_n','q50','q95'])
      assert.equal(row[field]??null,corpus.expected[field],`${metric} ${field}`);
  }
  assert.equal(find(result,'cdf_coverage').length,0);
  assert.doesNotMatch(result.svg,/failed,|missing|excluded|not established/);
  const raw=await evaluate('corpus-proof-recording-cdf',corpus.inputs,corpus.groups,3,authored);
  const percentAxes=r=>r.marks.filter(p=>p.mark.role==='axis-label'&&p.opacity!==0&&['0%','50%','100%'].includes(p.text));
  assert.equal(percentAxes(result).length,3,'the bound compact figure must have only the detail percentage axis');
  assert.equal(percentAxes(raw).length,3,'empty overview slots must not show percentage axes');
  const height=r=>Number(r.svg.match(/<svg[^>]* height="([^"]+)"/)[1]);
  assert.ok(height(raw)-height(result)>=65,'omitting the overview must remove its reserved height');
});

test('CDF titles distinguish congruence, recording-only and full checked proof work',async()=>{
  for(const [treatment,title,subtitle,mode] of [
    ['term','Congruence-only overhead','Congruence pass only; no proof recording.','Congruence'],
    ['proofs','Proof recording only','Includes congruence pass; excludes extraction and checking.','Proof recording'],
    ['proof-testing','Full proof overhead','Recording, extraction and checking; includes congruence pass.','Full proofs']
  ]) {
    const treatments=['off',treatment];
    const inputs=treatments.map(t=>input('case',t));
    const groups=treatments.map((t,i)=>group('case',t,[i?2:1,i?2:1]));
    const result=await evaluate('corpus-proof-recording-cdf',inputs,groups,2,null,treatments);
    assert.ok(result.svg.includes(title),`missing explicit title for ${treatment}`);
    assert.ok(result.svg.includes(subtitle),`missing work boundary for ${treatment}`);
    assert.ok(find(result,'cdf_points_zoom').every(p=>p.datum.mode===mode&&p.datum.ratio===2));
    const vetoed=await evaluate('corpus-proof-recording-cdf',inputs.map(i=>({...i,validation_failures:{'current':'Strict failure'}})),groups,2,null,treatments);
    assert.equal(find(vetoed,'cdf_points_zoom').length,treatment==='term'?2:0,'both timed proof modes retain the strict veto');
  }
});

test('the catalog retains separate congruence, recording-only and full-proof CDFs',async()=>{
  const comparisons=[
    ['corpus-congruence-cdf','term','Congruence-only overhead'],
    ['corpus-proof-recording-cdf','proofs','Proof recording only'],
    ['corpus-proofs-cdf','proof-testing','Full proof overhead']
  ];
  assert.equal(new Set(comparisons.map(([name])=>figures[name].spec)).size,1,'all CDFs share one authored specification');
  assert.ok(figures['corpus-proof-recording-cdf'].checks.includes('proof-testing'));
  for(const [name,treatment,title] of comparisons) {
    assert.deepEqual(figures[name].treatments,['off',treatment]);
    const result=await evaluate(name,['off',treatment].map(t=>input('case',t)),
      [group('case','off',[1,1]),group('case',treatment,[2,2])]);
    assert.ok(result.svg.includes(title));
    assert.equal(find(result,'cdf_points_zoom').length,2);
  }
});

test('Math absolute panels show only native outliers beyond the standard boxes',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const values=[1,1,1,1,1,1,1,1,1,100];
  const groups=treatments.map((t,i)=>group('a',t,values.map(v=>v*(i+1))));
  const result=await evaluate('math-runtime',treatments.map(t=>input('a',t)),groups,10);
  const outliers=result.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots')&&p.mark.marktype==='symbol');
  assert.equal(outliers.length,8,'exactly one generated flier per condition and metric');
  for(const metric of ['Runtime','Peak RSS'])
    assert.deepEqual(outliers.filter(p=>p.datum.metric===metric).map(p=>p.datum.value),[100,200,300,400]);
  assert.equal(find(result,'absolute_runs').length,0);
  assert.equal(find(result,'absolute_means').length,0);
  assert.ok(outliers.every(p=>p.fill==='#111111'));
});

test('capped asymmetric Fieller whiskers retain negative endpoints and align with uniform estimates',async()=>{
  for(const [name,treatments,prefix] of [
    ['math-runtime',['egg','egg-proof-testing','off','proof-testing'],'ratio'],
    ['slotted-runtime',['slotted-ref-nested','slotted-no-aliasing'],'slotted_ratio'],
    ['slotted-multipattern-runtime',['slotted-ref-multi','slotted'],'slotted_ratio']
  ]) {
    const inputs=treatments.map(t=>input(t,t,{logical_id:'a',label:'case.egg'}));
    const groups=inputs.map((item,i)=>group(item.file_sha256,item.treatment,i%2?[0,10,20]:[10,11,12]));
    const result=await evaluate(name,inputs,groups,3);
    const points=find(result,prefix+'_points').filter(p=>p.datum.metric==='Runtime');
    assert.equal(points.length,name==='math-runtime'?2:1);
    for(const point of points) {
      const row=point.datum;
      assert.ok(row.ratio_low<0&&row.ratio_high>row.ratio);
      assert.ok(Math.abs((row.ratio-row.ratio_low)-(row.ratio_high-row.ratio))>1e-4,'whiskers must use asymmetric Fieller endpoints');
      const interval=find(result,prefix+'_intervals').find(p=>p.datum.metric===row.metric&&p.datum.engine===row.engine&&p.datum.logical_id===row.logical_id);
      assert.ok(Math.abs(interval.y-point.y)<1e-8);
      for(const [end,position] of [['low','x'],['high','x2']]) {
        const cap=find(result,prefix+'_cap_'+end).find(p=>p.datum.metric===row.metric&&p.datum.engine===row.engine&&p.datum.logical_id===row.logical_id);
        assert.ok(Math.abs(cap.x+cap.width/2-interval[position])<1e-8,`${name} ${end} cap must meet the exact interval endpoint`);
        assert.ok(Math.abs(cap.y+cap.height/2-point.y)<1e-8);
        assert.ok(cap.bounds.x1>=0&&cap.bounds.x2<=cap.mark.group.width,'nonpositive endpoints must remain visible');
      }
      assert.equal(point.shape,'square');assert.equal(point.fill,'#111111');
    }
  }
});

test('native boxplot components stay monochrome and whisker caps remain shorter than row bands',async()=>{
  for(const name of ['disequality-runtime','math-runtime']) {
    const treatments=figures[name].treatments;
    const result=await evaluate(name,treatments.map(t=>input('case',t)),
      treatments.map((t,i)=>group('case',t,[i+1,i+1,i+1])),3);
    const components=result.marks.filter(p=>p.mark.name?.startsWith('absolute_boxplots'));
    assert.ok(components.length>0);
    for(const mark of components) {
      for(const color of [mark.fill,mark.stroke].filter(Boolean))
        assert.ok(['#111111','#333333','#d9d9d9'].includes(color),`unexpected default boxplot color ${color}`);
      if(mark.mark.marktype==='rect'&&mark.fill!=='#d9d9d9')
        assert.ok(mark.bounds.height()<=20,'whisker/median ticks must not span the full row band');
    }
  }
});
