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
    else if(p.name==='t_critical')p.value=({1:null,2:12.706204736432095,3:4.302652729749462,10:2.2621571628540993})[rounds];
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
  assert.equal(find(d,'absolute_status').length,10);
  assert.equal(find(d,'ratio_status').length,2);
  assert.match(d.svg,/0\/2 observations/);
  const math=['egg','egg-proof-testing','off','proof-testing'];
  const m=await evaluate('math-runtime',math.map(t=>input('a',t)),[]);
  assert.equal(find(m,'ratio_status').length,4);
  const slotted=['slotted-ref-nested','slotted-no-aliasing'];
  const s=await evaluate('slotted-runtime',slotted.map(t=>input('a',t)),[]);
  assert.equal(find(s,'slotted_status').length,4);
  assert.equal(find(s,'slotted_ratio_status').length,2);
  for(const [mode,treatment] of [['congruence','term'],['proofs','proof-testing']]) {
    const c=await evaluate(`corpus-${mode}-cdf`,['off',treatment].map(t=>input('a',t)),[]);
    assert.equal(find(c,'cdf_coverage').length,0);
    assert.match(c.svg,/unresolved baseline 1/);
  }
});
test('bound observations include failures and never borrow a moved label',async()=>{
  const a=group('a','off',[100,1,3]);
  const d=await evaluate('disequality-runtime',[input('a','off')],[a]);
  const means=find(d,'absolute_means');
  assert.equal(means.length,2);
  for(const {datum:mean} of means) {
    assert.equal(mean.mean,2);
    assert.equal(mean.sample_n,2);
    assert.ok(Math.abs(mean.ci_high-(2+12.706204736432095))<1e-8);
  }
  a.samples.at(-1).status='failure';
  const failed=await evaluate('disequality-runtime',[input('a','off')],[a]);
  assert.equal(find(failed,'absolute_means').length,0);
  a.labels=[];
  const moved=await evaluate('disequality-runtime',[input('a','off')],[a]);
  assert.equal(find(moved,'absolute_runs').length,0);
});
test('scope excludes unrelated cache groups and one run has points but no intervals',async()=>{
  const d=await evaluate('disequality-runtime',[input('a','off')],[group('a','off',[2]),group('b','off',[99])],1);
  assert.equal(find(d,'absolute_runs').length,2);
  assert.deepEqual(find(d,'absolute_means').map(p=>p.datum.mean),[2,2]);
  assert.equal(find(d,'absolute_intervals').length,0);
  assert.match(d.svg,/CI unavailable/);
});
test('Math pairs engines within proof modes while preserving selected Student-t and Fieller estimates',async()=>{
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
    assert.ok(result.marks.every(mark=>!mark.strokeDash?.some(Boolean)));
    const means=find(result,'absolute_means');
    assert.equal(find(result,'absolute_runs').length,24);
    assert.deepEqual(means.filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.mean),[21,63,42,168]);
    assert.deepEqual(means.filter(p=>p.datum.metric==='Peak RSS').map(p=>p.datum.mean),[303,1515,606,3636]);
    assert.deepEqual([...new Set(find(result,'absolute_runs').map(p=>p.datum.run.row_index))].sort(),[0,2,4]);
    for(const {datum:mean} of means) {
      const scale=(mean.metric==='Runtime'?[1,3,2,8]:[1,5,2,12])[treatments.indexOf(mean.input.treatment)];
      const se=scale*(mean.metric==='Runtime'?1:3)/Math.sqrt(3);
      assert.equal(mean.sample_n,3);
      assert.ok(Math.abs(mean.ci_low-(mean.mean-4.302652729749462*se))<1e-8);
      assert.ok(Math.abs(mean.ci_high-(mean.mean+4.302652729749462*se))<1e-8);
    }
    for(const metric of ['Runtime','Peak RSS']) {
      const rows=means.filter(p=>p.datum.metric===metric);
      assert.equal(new Set(rows.map(p=>p.y+p.height/2-p.datum.engine_offset)).size,2,'Math must have one row per proof mode');
      for(const mode of ['Off','Checked']) {
        const egg=rows.find(p=>p.datum.mode===mode&&p.datum.engine==='Egg');
        const egglog=rows.find(p=>p.datum.mode===mode&&p.datum.engine==='Egglog');
        assert.ok(egg.y<egglog.y,'paired engines must remain separated within their proof-mode row');
      }
      for(const mean of rows) {
        const ci=find(result,'absolute_intervals').find(p=>p.datum.metric===metric&&p.datum.input_id===mean.datum.input_id);
        assert.ok(Math.abs(ci.y-mean.y-mean.height/2)<1e-8,'mean and interval must use the same engine offset');
      }
    }
    const points=find(result,'ratio_points');
    assert.equal(points.length,4);
    assert.deepEqual(points.filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.ratio),[3,4]);
    assert.deepEqual(points.filter(p=>p.datum.metric==='Peak RSS').map(p=>p.datum.ratio),[5,6]);
    assert.equal(find(result,'ratio_intervals').length,4);
    for(const marks of [means,points])
      assert.ok(marks.find(p=>p.datum.metric==='Runtime').mark.group.x<marks.find(p=>p.datum.metric==='Peak RSS').mark.group.x,'runtime must be left of RSS');
    assert.ok(means[0].mark.group.mark.group.y<points[0].mark.group.mark.group.y,'absolute estimates must be above ratios');
    for(const {datum:ratio} of points) {
      const {baseline:b,candidate:c}=ratio;
      const t2=4.302652729749462**2;
      const a=b.mean**2-t2*b.var_mean;
      const discriminant=(b.mean*c.mean)**2-a*(c.mean**2-t2*c.var_mean);
      assert.ok(Math.abs(ratio.ratio_low-(b.mean*c.mean-Math.sqrt(discriminant))/a)<1e-8);
      assert.ok(Math.abs(ratio.ratio_high-(b.mean*c.mean+Math.sqrt(discriminant))/a)<1e-8);
    }
  }
});
test('disequality retains all absolute costs and compares Egglog NEE with native DE in both metrics',async()=>{
  const treatments=['egg-de','egg-ee','egg-nee','egg-oee','off'];
  const groups=treatments.map((t,i)=>group('a',t,[i+1,i+1,i+1],{max_rss_bytes:(i+1)*10*1048576}));
  groups.at(-1).samples.forEach(row=>row.max_rss_bytes=200*1048576);
  for(const records of [groups,[...groups].reverse()]) {
    const result=await evaluate('disequality-runtime',treatments.map(t=>input('a',t)),records,3);
    assert.ok(result.marks.every(mark=>!mark.strokeDash?.some(Boolean)));
    assert.equal(find(result,'absolute_runs').length,30);
    assert.equal(find(result,'absolute_means').length,10);
    const points=find(result,'ratio_points');
    assert.equal(points.length,2);
    assert.ok(points.every(p=>p.datum.native_condition==='DE · Disegg'));
    assert.deepEqual(points.filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.ratio),[5]);
    assert.deepEqual(points.filter(p=>p.datum.metric==='Peak RSS').map(p=>p.datum.ratio),[20]);
    assert.equal(find(result,'ratio_intervals').length,2);
    for(const marks of [find(result,'absolute_means'),points])
      assert.ok(marks.find(p=>p.datum.metric==='Runtime').mark.group.x<marks.find(p=>p.datum.metric==='Peak RSS').mark.group.x,'runtime must be left of RSS');
    assert.ok(find(result,'absolute_means')[0].mark.group.mark.group.y<points[0].mark.group.mark.group.y,'absolute estimates must be above ratios');
    assert.ok(points.every(p=>p.datum.ratio_low===p.datum.ratio&&p.datum.ratio_high===p.datum.ratio));
  }
});
test('CDF cohort uses >=.2 seconds without upper cutoff, shared denominator and 50/95 coverage',async()=>{
  const cases=[['boundary',.2],['slow',100],['fast',.199],['missing',1]];
  const inputs=cases.flatMap(([id])=>['off','term','proof-testing'].map(t=>input(id,t)));
  const groups=cases.flatMap(([id,v])=>[group(id,'off',[v,v]),group(id,'term',[v*2,v*2]),...(id==='missing'?[]:[group(id,'proof-testing',[v*3,v*3])])]);
  for(const mode of ['congruence','proofs']) {
    const c=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    const dots=find(c,'cdf_points');
    assert.equal(dots.length,mode==='congruence'?6:4);
    assert.ok(dots.every(p=>p.datum.cohort_n===3));
    assert.ok(!dots.some(p=>p.datum.workload_id==='fast'));
    assert.ok(dots.every(p=>p.datum.saved_n===4&&p.datum.too_fast_n===1&&p.datum.unresolved_n===0));
    if(mode==='proofs') {
      assert.match(c.svg,/2\/3 valid/);
      assert.match(c.svg,/95% not established/);
      assert.match(c.svg,/50% coverage ≤/);
    } else assert.ok(dots.every(p=>p.datum.cdf===1));
  }
});
test('strict validation veto applies only to checked proofs, missing RSS cannot change cohort',async()=>{
  const inputs=['off','term','proof-testing'].map(t=>input('a',t,{validation_failures:{'current/nee':'Known strict failure'}}));
  const groups=['off','term','proof-testing'].map((t,i)=>group('a',t,[i+1,i+1]));
  const congruence=await evaluate('corpus-congruence-cdf',inputs,groups);
  assert.deepEqual(find(congruence,'cdf_points').map(p=>p.datum.mode),['Congruence','Congruence']);
  const proofs=await evaluate('corpus-proofs-cdf',inputs,groups);
  assert.equal(find(proofs,'cdf_points').length,0);
  assert.match(proofs.svg,/Known strict failure|0\/1 valid/);
  groups[0].samples[0].max_rss_bytes=null;
  const missingRSS=await evaluate('corpus-congruence-cdf',inputs,groups);
  assert.deepEqual(find(missingRSS,'cdf_points').map(p=>p.datum.metric),['Runtime']);
  assert.match(missingRSS.svg,/0\/1 valid/);
  assert.ok(find(missingRSS,'cdf_points').every(p=>p.datum.saved_n===1&&p.datum.cohort_n===1));
  assert.deepEqual(find(missingRSS,'cdf_coverage').map(p=>p.text),['0 failed, 1 missing']);
});

test('Fieller uncertainty retains explanations and N1 ratios have points without intervals in both metrics',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('a',t));
  const groups=treatments.map((t,i)=>group('a',t,i%2?[2,4]:[.1,10]));
  const result=await evaluate('math-runtime',inputs,groups);
  assert.equal(find(result,'ratio_points').length,4);
  assert.equal(find(result,'ratio_intervals').length,0);
  assert.match(result.svg,/Fieller interval unbounded or unavailable/);
  const one=await evaluate('math-runtime',inputs,treatments.map((t,i)=>group('a',t,[i%2?4:2])),1);
  assert.equal(find(one,'ratio_points').length,4);
  assert.equal(find(one,'ratio_intervals').length,0);
  assert.match(one.svg,/CI unavailable \(n=1\)/);
  const native=['egg-de','egg-ee','egg-nee','egg-oee','off'];
  const d=await evaluate('disequality-runtime',native.map(t=>input('a',t)),native.map((t,i)=>group('a',t,[i===4?4:2])),1);
  assert.equal(find(d,'ratio_points').length,2);
  assert.equal(find(d,'ratio_intervals').length,0);
  assert.match(d.svg,/CI unavailable \(n=1\)/);
  const unbounded=await evaluate('disequality-runtime',native.map(t=>input('a',t)),
    native.map((t,i)=>group('a',t,i===4?[2,4]:[.1,10])));
  assert.equal(find(unbounded,'ratio_points').length,2);
  assert.equal(find(unbounded,'ratio_intervals').length,0);
  assert.match(unbounded.svg,/Fieller interval unbounded or unavailable/);
});

test('CDF ties use shared ranks, full tails and exact 95% inverse-CDF thresholds',async()=>{
  const inputs=['a','b','c','d'].flatMap(id=>['off','proof-testing'].map(t=>input(id,t)));
  const groups=['a','b','c','d'].flatMap((id,i)=>[group(id,'off',[1,1]),
    group(id,'proof-testing',[[2,2,4,1000][i],[2,2,4,1000][i]])]);
  const c=await evaluate('corpus-proofs-cdf',inputs,groups);
  for(const metric of ['Runtime','Peak RSS']) {
    const checked=find(c,'cdf_points').filter(p=>p.datum.metric===metric);
    assert.deepEqual(checked.map(p=>[p.datum.ratio,p.datum.cdf]),[[2,.5],[2,.5],[4,.75],[1000,1]]);
    assert.equal(find(c,'cdf_thresholds').find(p=>p.datum.metric===metric&&p.datum.percentile===.95).datum.threshold_ratio,1000);
    assert.equal(find(c,'cdf_points_zoom').filter(p=>p.datum.metric===metric).length,4);
  }
});

test('a first-row timeout remains explicit when collection stopped before N',async()=>{
  const failed=group('a','off',[null],{status:'timed-out'});
  const d=await evaluate('disequality-runtime',[input('a','off')],[failed],10);
  assert.equal(find(d,'absolute_means').length,0);
  assert.match(d.svg,/1\/10 observations; 1 failed \(1 timeout\)/);
});

test('failed and missing Math endpoints retain proof-mode rows and both engine identities',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('a',t));
  const groups=treatments.map((t,i)=>group('a',t,[i%2?null:2],i%2?{status:'failure',error_exit_code:86}:{}));
  const result=await evaluate('math-runtime',inputs,groups,1);
  const labels=result.marks.filter(m=>m.mark.role==='axis-label').map(m=>m.text);
  for(const label of ['Proofs off','Checked proofs','Egg','Egglog'])
    assert.ok(labels.includes(label),`missing axis label: ${label}`);
  assert.equal(find(result,'absolute_runs').length,4);
  assert.equal(find(result,'ratio_points').length,0);
  assert.ok(find(result,'absolute_status').some(p=>/Checked · Egg: 1\/1 observations; 1 failed, 1 memory limit/.test(p.datum.condition_status)));
  assert.ok(find(result,'absolute_status').some(p=>/Checked · Egglog: 1\/1 observations; 1 failed, 1 memory limit/.test(p.datum.condition_status)));
  assert.ok(find(result,'ratio_status').some(p=>p.datum.engine==='Egg'&&/Ratio unavailable/.test(p.datum.ratio_summary)));
  assert.ok(find(result,'ratio_status').some(p=>p.datum.engine==='Egglog'&&/Ratio unavailable/.test(p.datum.ratio_summary)));
  const missing=await evaluate('math-runtime',inputs,[],1);
  const missingLabels=missing.marks.filter(m=>m.mark.role==='axis-label').map(m=>m.text);
  for(const label of ['Proofs off','Checked proofs','Egg','Egglog'])
    assert.ok(missingLabels.includes(label),`missing empty axis label: ${label}`);
});

test('disequality statuses preserve every missing configuration in each metric',async()=>{
  const treatments=['egg-de','egg-ee','egg-nee','egg-oee','off'];
  const result=await evaluate('disequality-runtime',treatments.map(t=>input('a',t)),[]);
  for(const metric of ['Runtime','Peak RSS']) {
    for(const label of ['DE · Disegg','EE · Egg','NEE · Egg','OEE · Egg','NEE · Egglog'])
      assert.ok(find(result,'absolute_status').some(m=>m.datum.metric===metric&&m.datum.summary.startsWith(label+': ')));
    assert.equal(find(result,'ratio_status').filter(m=>m.datum.metric===metric).length,1);
  }
});

test('all figures use bound original row IDs rather than a raw tail or recorded timeout',async()=>{
  for(const name of ['disequality-runtime','math-runtime','corpus-congruence-cdf','corpus-proofs-cdf']) {
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
      assert.deepEqual(find(result,'cdf_points').map(p=>p.datum.ratio),name==='corpus-congruence-cdf'?[2,2]:[3,3]);
    else for(const metric of ['Runtime','Peak RSS'])
      assert.deepEqual(find(result,'absolute_means').filter(p=>p.datum.metric===metric).map(p=>p.datum.mean),treatments.map((_,i)=>i+1));
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

test('missing or zero RSS and strict proof validation cannot veto another metric or unchecked endpoint',async()=>{
  const treatments=['egg','egg-proof-testing','off','proof-testing'];
  const inputs=treatments.map(t=>input('a',t));
  const groups=treatments.map((t,i)=>group('a',t,[i%2?4:2,i%2?4:2]));
  groups[0].samples[0].max_rss_bytes=null;
  groups[2].samples[0].max_rss_bytes=0;
  const result=await evaluate('math-runtime',inputs,groups);
  assert.deepEqual(find(result,'ratio_points').map(p=>[p.datum.metric,p.datum.ratio]),[['Runtime',2],['Runtime',2]]);
  assert.equal(find(result,'absolute_means').filter(p=>p.datum.metric==='Peak RSS').length,2);
  const strict=await evaluate('math-runtime',inputs.map(p=>({...p,validation_failures:{'current/nee':'Known strict failure'}})),
    treatments.map((t,i)=>group('a',t,[i%2?4:2,i%2?4:2])));
  assert.ok(find(strict,'absolute_means').every(p=>p.datum.input.treatment!=='proof-testing'));
  assert.deepEqual(find(strict,'ratio_points').map(p=>[p.datum.engine,p.datum.metric]),[['Egg','Runtime'],['Egg','Peak RSS']]);
  assert.match(strict.svg,/Known strict failure/);
});

test('CDF family dots, pooled step lines and direct 50/95 labels retain ranks and intact glyph bounds',async()=>{
  const ids=['a','b','c','d'];
  const inputs=ids.flatMap((id,i)=>['off','term','proof-testing'].map(t=>input(id,t,{family:i%2?'misaal':'eggcc'})));
  const groups=ids.flatMap((id,i)=>[group(id,'off',[1,1]),group(id,'term',[2,2]),
    group(id,'proof-testing',[[2,2,4,1000][i],[2,2,4,1000][i]])]);
  for(const mode of ['congruence','proofs']) {
    const result=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    const points=find(result,'cdf_points');
    const zoom=find(result,'cdf_points_zoom');
    assert.deepEqual(zoom.map(p=>[p.datum.workload_id,p.datum.metric,p.datum.ratio,p.datum.cdf]),
      points.map(p=>[p.datum.workload_id,p.datum.metric,p.datum.ratio,p.datum.cdf]));
    assert.notEqual(points.find(p=>p.datum.family==='eggcc').fill,points.find(p=>p.datum.family==='misaal').fill);
    const labels=[...find(result,'cdf_thresholds_zoom'),...find(result,'cdf_thresholds')];
    assert.equal(labels.length,4);
    assert.equal(labels.find(p=>p.datum.metric==='Runtime'&&p.datum.percentile===.95).datum.threshold_ratio,mode==='proofs'?1000:2);
    for(const label of labels) {
      assert.ok(label.bounds.x1>=0&&label.bounds.x2<=label.mark.group.width,`horizontal clipping: ${label.text}`);
      if(label.mark.name==='cdf_thresholds_marks')
        assert.ok(label.bounds.y2<0,`full-range threshold must clear the tail dots: ${label.text}`);
      else assert.ok(label.bounds.y1>=0&&label.bounds.y2<=label.mark.group.height,`vertical clipping: ${label.text}`);
    }
    for(const point of [...points,...zoom.filter(p=>p.datum.ratio<=p.datum.zoom_max)]) {
      assert.ok(point.bounds.x1>=0&&point.bounds.x2<=point.mark.group.width,'circle clipped horizontally');
      assert.ok(point.bounds.y1>=0&&point.bounds.y2<=point.mark.group.height,'circle clipped vertically');
    }
    for(const [lineName,pointName] of [['cdf_line','cdf_points'],['cdf_line_zoom','cdf_points_zoom']]) {
      const lines=find(result,lineName);
      assert.equal(new Set(lines.map(p=>p.mark)).size,2,'each metric needs one pooled line, independent of family');
      assert.ok(lines.every(p=>p.stroke==='#374151'));
      for(const line of lines) {
        const siblings=line.mark.group.items;
        assert.ok(siblings.indexOf(line.mark)<siblings.indexOf(find(result,pointName).find(p=>p.datum.metric===line.datum.metric).mark),'CDF line must be below its circles');
      }
    }
  }
});

test('Slotted selects distinct runtime/RSS rows and computes per-case Student-t and Fieller intervals',async()=>{
  for(const treatments of [['slotted-ref-multi','slotted'],['slotted-ref-nested','slotted-no-aliasing']]) {
    const inputs=['a','b'].flatMap((id,i)=>treatments.map(t=>input(id+'-'+t,t,{
      logical_id:id,label:`benchmarks/slotted/inputs/array/goal-2d-4f-N${i?10:2}.egg`,selected_row_indices:[0,2,4]})));
    const groups=['a','b'].flatMap((id,k)=>treatments.map((t,i)=>{
      const scale=i?(k?12:3):(k?2:1);
      const memoryScale=i?(k?20:5):(k?2:1);
      const record=group(id+'-'+t,t,[20*scale,999,21*scale,888,22*scale]);
      record.samples.forEach((row,j)=>row.max_rss_bytes=[300,99999,303,88888,306][j]*memoryScale*1048576);
      return record;
    }));
    for(const records of [groups,[...groups].reverse()]) {
      const result=await evaluate('slotted-runtime',inputs,records,3);
      const runs=find(result,'slotted_runs');
      const means=find(result,'slotted_absolute_means');
      assert.equal(runs.length,24);
      assert.equal(means.length,8);
      assert.deepEqual(means.filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.mean),[21,63,42,252]);
      assert.deepEqual(means.filter(p=>p.datum.metric==='Peak RSS').map(p=>p.datum.mean),[303,1515,606,6060]);
      assert.deepEqual([...new Set(runs.map(p=>p.datum.run.row_index))].sort(),[0,2,4]);
      for(const mean of means) {
        assert.equal(mean.datum.sample_n,3);
        const expectedSE=mean.datum.mean/(mean.datum.metric==='Runtime'?21:101)/Math.sqrt(3);
        assert.ok(Math.abs(mean.datum.ci_high-mean.datum.mean-4.302652729749462*expectedSE)<1e-8);
        assert.ok(Math.abs(mean.datum.ci_low-mean.datum.mean+4.302652729749462*expectedSE)<1e-8);
        const middle=runs.find(p=>p.datum.input_id===mean.datum.input_id&&p.datum.metric===mean.datum.metric&&p.datum.run.row_index===2);
        assert.ok(Math.abs(middle.x-mean.x-mean.width/2)<1e-8,'middle observation and arithmetic mean must share x position');
      }
      const ratios=find(result,'slotted_ratio_points');
      assert.deepEqual(ratios.filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.ratio),[3,6]);
      assert.deepEqual(ratios.filter(p=>p.datum.metric==='Peak RSS').map(p=>p.datum.ratio),[5,10]);
      assert.equal(find(result,'slotted_ratio_intervals').length,4);
      for(const marks of [means,ratios])
        assert.ok(marks.find(p=>p.datum.metric==='Runtime').mark.group.x<marks.find(p=>p.datum.metric==='Peak RSS').mark.group.x,'runtime must be left of RSS');
      assert.ok(means[0].mark.group.mark.group.y<ratios[0].mark.group.mark.group.y,'absolute estimates must be above ratios');
      const guides=find(result,'slotted_equal');
      assert.equal(guides.length,2);
      for(const guide of guides)assert.ok(guide.y===0&&guide.y2===guide.mark.group.height,'ratio equality guide must span every workload row');
      for(const {datum:ratio} of ratios) {
        const {baseline:b,candidate:c}=ratio;
        const t2=4.302652729749462**2;
        const a=b.mean**2-t2*b.var_mean;
        const discriminant=(b.mean*c.mean)**2-a*(c.mean**2-t2*c.var_mean);
        assert.ok(Math.abs(ratio.ratio_low-(b.mean*c.mean-Math.sqrt(discriminant))/a)<1e-8);
        assert.ok(Math.abs(ratio.ratio_high-(b.mean*c.mean+Math.sqrt(discriminant))/a)<1e-8);
      }
      assert.notEqual(runs.find(p=>p.datum.series==='Native Slotted').shape,runs.find(p=>p.datum.series==='Egglog encoding').shape);
      const labels=result.marks.filter(p=>p.mark.role==='axis-label').map(p=>p.text);
      assert.equal(labels.filter(label=>label==='Array · N=2').length,2);
      assert.equal(labels.filter(label=>label==='Array · N=10').length,2);
      assert.ok(!labels.some(label=>/goal-2d-4f-N|[.]egg$/.test(label)));
      assert.match(result.svg,/Peak RSS/);
      assert.match(result.svg,/MiB/);
      for(const point of runs)assert.ok(point.bounds.y1>=0&&point.bounds.y2<=point.mark.group.height,'run outside workload rows');
    }
  }
});

test('Slotted missing RSS preserves runtime estimates and usable memory observations',async()=>{
  const treatments=['slotted-ref-nested','slotted-no-aliasing'];
  const inputs=treatments.map(t=>input('a-'+t,t,{logical_id:'a',label:'benchmarks/slotted/inputs/sdql/mmm_1st-44rules.egg'}));
  const groups=treatments.map((t,i)=>group('a-'+t,t,i?[4,5,6]:[1,2,3]));
  groups[0].samples.forEach((row,i)=>row.max_rss_bytes=i===1?null:(i+1)*10*1048576);
  groups[1].samples.forEach((row,i)=>row.max_rss_bytes=(i+1)*100*1048576);
  const result=await evaluate('slotted-runtime',inputs,groups,3);
  assert.deepEqual(find(result,'slotted_absolute_means').filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.mean),[2,5]);
  assert.deepEqual(find(result,'slotted_absolute_means').filter(p=>p.datum.metric==='Peak RSS').map(p=>p.datum.mean),[200]);
  assert.equal(find(result,'slotted_absolute_intervals').filter(p=>p.datum.metric==='Runtime').length,2);
  const memoryRuns=find(result,'slotted_runs').filter(p=>p.datum.metric==='Peak RSS'&&p.datum.series==='Native Slotted');
  assert.deepEqual(memoryRuns.map(p=>p.datum.value),[10,30]);
  const statuses=find(result,'slotted_status');
  assert.equal(statuses.length,1);
  assert.equal(statuses[0].datum.metric,'Peak RSS');
  assert.equal(statuses[0].datum.issue,'3/3 runs; metric missing');
  assert.deepEqual(find(result,'slotted_ratio_points').map(p=>[p.datum.metric,p.datum.ratio]),[['Runtime',2.5]]);
  assert.ok(find(result,'slotted_ratio_status').some(p=>p.datum.metric==='Peak RSS'));
});

test('Slotted empty, selected failures, resource bounds and N1 remain explicit for both metrics',async()=>{
  const treatments=['slotted-ref-multi','slotted'];
  const inputs=treatments.map(t=>input('a',t,{label:'benchmarks/slotted/inputs/logic/first-order-logic.egg'}));
  const empty=await evaluate('slotted-runtime',inputs,[]);
  assert.equal(find(empty,'slotted_runs').length,0);
  assert.equal(find(empty,'slotted_status').length,4);
  assert.match(empty.svg,/first-order-logic/);
  assert.match(empty.svg,/0\/2 runs; missing/);
  const records=[group('a',treatments[0],[999,1,3]),group('a',treatments[1],[999,4,6])];
  records[0].samples[0].status='timed-out';
  records[1].samples[2].status='timed-out';
  records[1].samples[2].timeout_sec=500;
  const selected=inputs.map(p=>({...p,selected_row_indices:[1,2]}));
  const failed=await evaluate('slotted-runtime',selected,records);
  assert.equal(find(failed,'slotted_absolute_means').length,2);
  assert.ok(find(failed,'slotted_absolute_means').every(p=>p.datum.series==='Native Slotted'));
  assert.deepEqual(find(failed,'slotted_status').map(p=>[p.datum.metric,p.datum.failed_n,p.datum.timeout_bound]),[['Runtime',1,500],['Peak RSS',1,500]]);
  assert.ok(find(failed,'slotted_runs').every(p=>p.datum.run.row_index!==0),'excluded historical failure must not enter either metric');
  const one=await evaluate('slotted-runtime',inputs,treatments.map((t,i)=>group('a',t,[i?4:2],{max_rss_bytes:(i?400:200)*1048576})),1);
  assert.equal(find(one,'slotted_absolute_means').length,0);
  assert.deepEqual(find(one,'slotted_runs').map(p=>p.datum.mean),[2,4,200,400]);
  assert.equal(find(one,'slotted_absolute_intervals').length,0);
  assert.deepEqual(find(one,'slotted_ratio_points').map(p=>[p.datum.metric,p.datum.ratio]),[['Runtime',2],['Peak RSS',2]]);
  assert.equal(find(one,'slotted_ratio_intervals').length,0);
  assert.match(one.svg,/n=1; CI unavailable/);
  const resource=await evaluate('slotted-runtime',inputs,[group('a',treatments[0],[null],{status:'timed-out',timeout_sec:500}),
    group('a',treatments[1],[null],{status:'failure',error_exit_code:86,error_memory_limit_bytes:16*1024**3})],1);
  assert.equal(find(resource,'slotted_status').length,4);
  assert.match(resource.svg,/timeout \(500 s\)/);
  assert.match(resource.svg,/allocation limit \(16 GiB\)/);
  const rss=await evaluate('slotted-runtime',inputs,treatments.map(t=>group('a',t,[null],{status:'failure',error_message:'process-group RSS limit',error_memory_limit_bytes:10*1024**3})),1);
  assert.match(rss.svg,/memory limit \(10 GiB\)/);
  assert.doesNotMatch(rss.svg,/allocation limit/);
  const ten=await evaluate('slotted-runtime',inputs,treatments.map((t,i)=>group('a',t,Array(10).fill(i?4:2))),10);
  assert.equal(find(ten,'slotted_absolute_means').length,4);
  assert.equal(find(ten,'slotted_absolute_intervals').length,4);
  assert.doesNotMatch(ten.svg,/Pilot:/);
});

test('Slotted custom full catalogs keep distinct rows aligned between time and memory',async()=>{
  const names=[...Array.from({length:11},(_,n)=>`array/goal-2d-4f-N${n}.egg`),
    ...['batax','mmm','mmm_sum','mttkrp','ttm'].flatMap(k=>[1,2].map(p=>`sdql/${k}_${p===1?'1st':'2nd'}-44rules.egg`)),
    'logic/first-order-logic.egg','logic/first-order-logic2.egg'];
  const treatments=['slotted-ref-multi','slotted'];
  const inputs=names.flatMap((name,i)=>treatments.map(t=>input('case'+i,t,{label:'benchmarks/slotted/inputs/'+name})));
  const groups=names.flatMap((_,i)=>treatments.map((t,j)=>group('case'+i,t,[j?4:2,j?4:2],{max_rss_bytes:(j?400:200)*1048576})));
  for(const records of [groups,[]]) {
    const result=await evaluate('slotted-runtime',inputs,records);
    const rows=[...find(result,'slotted_absolute_means'),...find(result,'slotted_status')];
    for(const metric of ['Runtime','Peak RSS']) {
      const yPositions=new Set(rows.filter(p=>p.datum.metric===metric).map(p=>p.y+(p.height??0)/2-p.datum.series_offset));
      assert.equal(yPositions.size,23,'workloads collapsed to a shared row');
      assert.ok(Math.max(...yPositions)-Math.min(...yPositions)>=22*16,'plot height does not grow with workload count');
    }
    const labels=result.marks.filter(p=>p.mark.role==='axis-label'&&rows.some(r=>r.datum.workload===p.text));
    assert.equal(labels.length,46);
    for(const mark of new Set(labels.map(p=>p.mark))) {
      const column=labels.filter(p=>p.mark===mark).sort((a,b)=>a.y-b.y);
      assert.equal(column.length,23);
      for(let i=1;i<column.length;i++)assert.ok(column[i-1].bounds.y2<column[i].bounds.y1,`overlapping workload labels: ${column[i].text}`);
    }
    for(const mean of find(result,'slotted_absolute_means').filter(p=>p.datum.metric==='Runtime')) {
      const memory=rows.find(p=>p.datum.metric==='Peak RSS'&&p.datum.input_id===mean.datum.input_id);
      assert.ok(Math.abs(mean.y+mean.height/2-memory.y-memory.height/2)<1e-8,'time and memory rows drifted');
    }
  }
});


test('absolute run jitter remains relative to its mean row and shares engine glyphs across metrics',async()=>{
  for(const name of ['disequality-runtime','math-runtime']) {
    const treatments=name.startsWith('math')?['egg','egg-proof-testing','off','proof-testing']:['egg-de','egg-ee','egg-nee','egg-oee','off'];
    const result=await evaluate(name,treatments.map(t=>input('a',t)),treatments.map(t=>group('a',t,[2,4])));
    const means=find(result,'absolute_means');
    assert.equal(means.length,treatments.length*2);
    for(const run of find(result,'absolute_runs')) {
      const mean=means.find(m=>m.datum.input_id===run.datum.input_id&&m.datum.metric===run.datum.metric);
      assert.ok(Math.abs(run.y-(mean.y+mean.height/2)-run.datum.jitter)<1e-8,`${name}: run jitter displaced from its mean row`);
      assert.ok(run.bounds.y1>=0&&run.bounds.y2<=run.mark.group.height);
      const other=find(result,'absolute_runs').find(p=>p.datum.input_id===run.datum.input_id&&p.datum.metric!==run.datum.metric&&p.datum.run.row_index===run.datum.run.row_index);
      assert.equal(run.shape,other.shape);
      assert.equal(run.fill,other.fill);
      assert.equal(run.datum.jitter,other.datum.jitter);
      const encoded=name==='math-runtime'?run.datum.engine==='Egglog':run.datum.input.treatment==='off';
      assert.equal(run.shape,encoded?'triangle-up':'circle');
      assert.equal(run.fill,encoded?'#b36c48':'#477b9e');
    }
  }
});

test('Math and disequality keep runtime domains independent of thousand-MiB RSS',async()=>{
  for(const name of ['disequality-runtime','math-runtime']) {
    const treatments=name.startsWith('math')?['egg','egg-proof-testing','off','proof-testing']:['egg-de','egg-ee','egg-nee','egg-oee','off'];
    const result=await evaluate(name,treatments.map(t=>input('a',t)),
      treatments.map(t=>group('a',t,[.001,.001],{max_rss_bytes:1000*1048576})));
    for(const run of find(result,'absolute_runs')) {
      assert.ok(Number.isFinite(run.x)&&run.x>run.mark.group.width*.8,'metric domain pooled runtime with RSS or ignored its extent');
      assert.ok(run.bounds.x1>=0&&run.bounds.x2<=run.mark.group.width,'run glyph clipped at a domain boundary');
    }
  }
});

test('Slotted independent metric axes retain zero, negative confidence bounds and sparse domains',async()=>{
  const treatments=['slotted-ref-multi','slotted'];
  const inputs=treatments.map(t=>input('a',t,{label:'benchmarks/slotted/inputs/array/goal-2d-4f-N0.egg'}));
  const cases=[[],treatments.map(t=>group('a',t,[null,null],{status:'timed-out'})),
    treatments.map(t=>group('a',t,[0,0],{max_rss_bytes:1000*1048576})),
    treatments.map(t=>group('a',t,[.001,.001],{max_rss_bytes:1000*1048576})),
    treatments.map(t=>group('a',t,[1,3],{max_rss_bytes:1000*1048576}))];
  for(const groups of cases) {
    const result=await evaluate('slotted-runtime',inputs,groups);
    const axes=result.marks.filter(m=>m.mark.role==='axis-label'&&typeof m.datum.value==='number');
    assert.ok(axes.length>0,'numeric axis label check did not run');
    for(const label of axes) {
      assert.ok(label.bounds.x1>=-.5&&label.bounds.x2<=label.mark.group.mark.group.width+.5,`axis label outside its frame: ${label.text}`);
      if(!label.text.endsWith('×'))
        assert.equal(Number(label.text.replaceAll(',','').replace('−','-')),label.datum.value,'absolute tick formatting must preserve fractional seconds');
    }
    for(const run of find(result,'slotted_runs'))assert.ok(Number.isFinite(run.x)&&run.x>=0&&run.x<=run.mark.group.width,'zero or positive run absent from its metric domain');
    for(const ci of find(result,'slotted_absolute_intervals'))assert.ok(Number.isFinite(ci.x)&&Number.isFinite(ci.x2)&&ci.x>=0&&ci.x2<=ci.mark.group.width,'confidence interval clipped or lost');
    if(groups[0]?.samples[0].wall_sec===.001) {
      const runs=find(result,'slotted_runs');
      assert.ok(runs.filter(p=>p.datum.metric==='Runtime').every(p=>p.x>p.mark.group.width*.6),'runtime domain must not be pooled with thousand-MiB RSS');
      assert.ok(axes.some(m=>m.datum.value>0&&m.datum.value<.01&&m.opacity!==0),'one-millisecond runtimes need a visible nonzero tick');
    }
    if(groups[0]?.samples[0].wall_sec===1) {
      assert.ok(find(result,'slotted_absolute_intervals').filter(p=>p.datum.metric==='Runtime').every(ci=>ci.datum.ci_low<0));
      assert.ok(axes.some(m=>m.datum.value<0),'negative confidence bounds need a negative axis tick');
      assert.equal(find(result,'slotted_ratio_points').length,2);
      assert.equal(find(result,'slotted_ratio_intervals').length,1);
      assert.ok(find(result,'slotted_ratio_status').some(p=>p.datum.metric==='Runtime'&&/unbounded/.test(p.datum.summary)));
    }
  }
});


test('CDF metric panels use distinct time/RSS ratios and zoom domains without double-counting workloads',async()=>{
  for(const [mode,treatment] of [['congruence','term'],['proofs','proof-testing']]) {
    const inputs=['a','b'].flatMap(id=>['off',treatment].map(t=>input(id,t)));
    const groups=['a','b'].flatMap((id,i)=>[group(id,'off',[1,1]),
      group(id,treatment,[i?6:0,i?6:0],{max_rss_bytes:(i?10:2)*1048576})]);
    const result=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    const dots=find(result,'cdf_points_zoom');
    assert.deepEqual(dots.filter(p=>p.datum.metric==='Runtime').map(p=>p.datum.ratio),[0,6]);
    assert.deepEqual(dots.filter(p=>p.datum.metric==='Peak RSS').map(p=>p.datum.ratio),[2,10]);
    assert.ok(dots.every(p=>p.datum.cohort_n===2&&p.datum.measured_n===2));
    assert.ok(dots.every(p=>p.datum.saved_n===2&&p.datum.cohort_n===2));
    assert.match(result.svg,/Zoom 0–6× baseline/);
    assert.match(result.svg,/Zoom 1–10× baseline/);
    for(const dot of dots) {
      assert.ok(dot.bounds.x1>=0&&dot.bounds.x2<=dot.mark.group.width,'boundary circle clipped horizontally');
      assert.ok(dot.bounds.y1>=0&&dot.bounds.y2<=dot.mark.group.height,'100% circle clipped vertically');
    }
    for(const row of groups.at(-1).samples)row.wall_sec=1000;
    const tails=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    for(const metric of ['Runtime','Peak RSS']) {
      const endpoint=find(tails,'cdf_points').find(p=>p.datum.metric===metric&&p.datum.workload_id==='b');
      assert.ok(Math.abs(endpoint.x-(endpoint.mark.group.width-4))<1e-8,'full-range domain must use only its own metric extent');
    }
    groups.at(-1).samples[0].status='timed-out';
    const failed=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    assert.ok(find(failed,'cdf_points').every(p=>p.datum.cohort_n===2&&p.datum.cdf===.5));
    assert.deepEqual(find(failed,'cdf_coverage').map(p=>p.text),['1 failed, 0 missing']);
    groups[1].samples.forEach(row=>row.max_rss_bytes=null);
    const mixed=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    assert.deepEqual(find(mixed,'cdf_coverage').map(p=>p.text),['1 failed, 1 missing']);
    groups[1].samples[0].status='timed-out';
    const both=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    assert.deepEqual(find(both,'cdf_coverage').map(p=>p.text),['2 failed, 0 missing']);
  }
});


test('CDF domains fit each metric, magnify compact data and separate heavy tails without changing ranks',async()=>{
  for(const [mode,treatment] of [['congruence','term'],['proofs','proof-testing']]) {
    for(const [times,rss,expected] of [
      [[1.1,2,2.3,2.7],[1.1,1.5,1.6,1.9],{'Runtime':[1,2.7,2.7],'Peak RSS':[1,1.9,1.9]}],
      [[2,3,4,200],[1.5,2,4,80],{'Runtime':[1,7,200],'Peak RSS':[1,6,80]}]
    ]) {
      const inputs=times.flatMap((_,i)=>['off',treatment].map(t=>input('case'+i,t)));
      const groups=times.flatMap((v,i)=>[group('case'+i,'off',[1,1]),group('case'+i,treatment,[v,v],{max_rss_bytes:rss[i]*1048576})]);
      const result=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
      for(const [metric,[minimum,zoom,full]] of Object.entries(expected)) {
        const points=find(result,'cdf_points').filter(p=>p.datum.metric===metric);
        assert.deepEqual(points.map(p=>p.datum.cdf),[.25,.5,.75,1]);
        assert.ok(points.every(p=>Math.abs(p.datum.zoom_min-minimum)<1e-8&&Math.abs(p.datum.zoom_max-zoom)<1e-8&&Math.abs(p.datum.full_max-full)<1e-8));
        const region=find(result,'cdf_zoom_region').find(p=>p.datum.metric===metric);
        assert.ok(Math.abs(region.x-(4+(region.mark.group.width-8)*minimum/full))<1e-8,'overview shade must start at the zoom lower bound');
        assert.ok(Math.abs(region.x2-(4+(region.mark.group.width-8)*zoom/full))<1e-8,'overview shade must end at the zoom upper bound');
        assert.ok(zoom-minimum<full,'compact data must still have a genuine baseline-context zoom');
        assert.equal(find(result,'cdf_detail_status').find(p=>p.datum.metric===metric).text,'4/4 valid');
      }
    }
  }
});

test('CDF empty, zero, single-run and failed samples retain finite reference-containing dynamic domains',async()=>{
  const treatment='proof-testing';
  const inputs=['off',treatment].map(t=>input('a',t));
  for(const [groups,rounds] of [
    [[],2],
    [[group('a','off',[1,1]),group('a',treatment,[0,0])],2],
    [[group('a','off',[1]),group('a',treatment,[1])],1],
    [[group('a','off',[1,1]),group('a',treatment,[null,null],{status:'timed-out'})],2]
  ]) {
    const result=await evaluate('corpus-proofs-cdf',inputs,groups,rounds);
    for(const status of find(result,'cdf_detail_status')) {
      const {zoom_min,zoom_max,full_max}=status.datum;
      assert.ok([zoom_min,zoom_max,full_max].every(Number.isFinite));
      assert.ok(zoom_min<=1&&zoom_max>=1&&full_max>=zoom_max&&zoom_max>zoom_min);
    }
    for(const point of find(result,'cdf_points_zoom')) {
      assert.ok(Number.isFinite(point.x)&&point.bounds.x1>=0&&point.bounds.x2<=point.mark.group.width);
      assert.ok(Number.isFinite(point.y)&&point.bounds.y1>=0&&point.bounds.y2<=point.mark.group.height);
    }
  }
  for(const [mode,treatment] of [['congruence','term'],['proofs','proof-testing']]) {
    const inputs=['a','b','c','d'].flatMap(id=>['off',treatment].map(t=>input(id,t)));
    const groups=[...['a','b','c'].map(id=>group(id,'off',[1,1])),group('a',treatment,[2,2])];
    const partial=await evaluate(`corpus-${mode}-cdf`,inputs,groups);
    assert.deepEqual(find(partial,'cdf_coverage').map(p=>p.text),['0 failed, 2 missing']);
    for(const status of find(partial,'cdf_detail_status')) {
      assert.match(status.text,/1\/3 valid · unresolved baseline 1\n50%\/95% not established/);
      assert.ok(status.bounds.x1>=0&&status.bounds.x2<=status.mark.group.width,'status must fit its metric panel');
      assert.ok(status.bounds.y2<=0,'status must remain above the plot');
    }
  }
});
