import assert from 'node:assert/strict';
import {existsSync, realpathSync} from 'node:fs';
import {readFile} from 'node:fs/promises';
import {createRequire} from 'node:module';
import {delimiter, join} from 'node:path';
import test from 'node:test';
import {spawnSync} from 'node:child_process';

const cli = process.env.PATH.split(delimiter).map(path => join(path, 'vl2svg')).find(existsSync);
assert.ok(cli, 'Run make figures-expanded-test');
const toolkit = createRequire(realpathSync(cli));
const vega = await import(toolkit.resolve('vega'));
const {compile} = await import(toolkit.resolve('vega-lite'));

function workload(id, family = 'eggcc') {
  return {id, label: id, family, iteration: family === 'math-growth' ? 11 : null,
    file_sha256: id, fact_directory_sha256: '', aliases: [], unavailable_reason: '', validation_failures: {}};
}
function group(id, treatment, seconds, changes = {}) {
  const key = {binary_sha256: 'current', file_sha256: id, fact_directory_sha256: '',
    treatment, timeout_sec: 300, disequality_encoding: 'nee'};
  return {key, labels: ['figures'], samples: seconds.map((value, row_index) => ({
    ...key, row_index, started_at: `2026-10-01T00:00:${String(row_index).padStart(2, '0')}Z`,
    status: 'success', wall_sec: value, max_rss_bytes: value * 1048576, target_label: 'older-label',
    error_message: null, ...changes,
  }))};
}
async function evaluate(chart, workloads, groups) {
  const spec = JSON.parse(await readFile(new URL(`expanded/${chart}.vl.json`, import.meta.url), 'utf8'));
  assert.equal(spec.data.url, '../../.reports-grouped.json');
  const warnings = [];
  const logger = vega.logger(vega.Warn, undefined, (...args) => warnings.push(args));
  const runtime = compile(spec, {logger}).spec;
  const loader = vega.loader();
  loader.load = async url => JSON.stringify(url.includes('figure-inventory')
    ? {id: 1, timeout_sec: 300, min_wall_sec: 0.1, max_wall_sec: 30, workloads, exclusions: []}
    : {grouped_schema_version: 1, report_schema_version: 5, groups});
  const view = new vega.View(vega.parse(runtime), {renderer: 'none', loader, logger});
  try {
    await view.runAsync();
    const svg = await view.toSVG();
    assert.deepEqual(warnings, []);
    assert.doesNotMatch(svg, /NaN|Infinity/);
    const marks = [];
    function collect(item) {
      if (item.mark?.role === 'mark') marks.push({name: item.mark.name, datum: {...item.datum},
        x: item.x, y: item.y, text: item.text});
      for (const child of item.items ?? []) collect(child);
    }
    collect(view.scenegraph().root);
    return {marks, svg};
  } finally { view.finalize(); }
}
function points(marks, mode = 'Record + extract', metric = 'Time') {
  return marks.filter(m => m.name === 'pooled_points_marks' && m.datum.candidate_mode === mode && m.datum.metric === metric);
}

test('Math uses all samples, current manifest hashes and latest label membership', async () => {
  const groups = [group('math', 'egg', [1]), group('math', 'off', [2, 4]),
    group('math', 'egg-proof-extraction', [4, 5, 6]), group('math', 'proof-extraction', [5, 7, 9, 11])];
  groups.push({...group('math', 'egg', [1000]), labels: []});
  groups.push(group('stale-input', 'off', [1000]));
  const {marks, svg} = await evaluate('math-cutoff-11', [workload('math', 'math-growth')], groups);
  const means = marks.filter(m => m.name === 'time_means_marks');
  assert.deepEqual(means.map(m => m.datum.mean), [1, 3, 5, 8]);
  assert.deepEqual(means.map(m => m.datum.selected), [1, 2, 3, 4]);
  assert.equal(marks.filter(m => m.name === 'time_runs_marks').length, 10);
  assert.match(svg, /4 runs/);
});

test('Math preserves successful dots and reports failed and absent endpoints', async () => {
  const failed = group('math', 'off', [2, 3]); failed.samples[1].status = 'failure';
  const {marks, svg} = await evaluate('math-cutoff-11', [workload('math', 'math-growth')], [failed]);
  assert.equal(marks.filter(m => m.name === 'time_runs_marks').length, 1);
  assert.equal(marks.filter(m => m.name === 'time_means_marks').length, 0);
  assert.match(svg, /execution failed/); assert.match(svg, /no observations/);
});

test('CDF uses ratios of means with unequal counts and shared cohort denominators', async () => {
  const inputs = ['a', 'b', 'c'].map(id => workload(id));
  const groups = [group('a', 'off', [1, 3]), group('a', 'proof-extraction', [4]), group('a', 'proofs', [2, 2, 2]),
    group('b', 'off', [1]), group('b', 'proof-extraction', [4, 4, 4]),
    group('c', 'off', [1]), group('c', 'proof-extraction', [1000], {status: 'timed-out'})];
  const {marks, svg} = await evaluate('proof-overhead-cdf', inputs, groups);
  assert.deepEqual(points(marks).map(m => [m.datum.ratio, m.datum.cdf]), [[2, 1 / 3], [4, 2 / 3]]);
  assert.equal(points(marks, 'Record').length, 1);
  assert.ok(points(marks).every(m => m.datum.n === 3));
  assert.equal(points(marks, 'Record + extract', 'Memory').length, 2);
  assert.match(svg, /timeout/); assert.match(svg, /90% not established/);
});

test('Time window is strict and missing RSS or proof outcomes never select the cohort', async () => {
  const inputs = ['fast', 'slow', 'selected', 'missing'].map(id => workload(id));
  const groups = [group('fast', 'off', [.1]), group('slow', 'off', [30]),
    group('selected', 'off', [1], {max_rss_bytes: null}), group('selected', 'proof-extraction', [3])];
  const {marks, svg} = await evaluate('proof-overhead-cdf', inputs, groups);
  assert.equal(points(marks).length, 1); assert.equal(points(marks)[0].datum.n, 1);
  assert.equal(points(marks, 'Record + extract', 'Memory').length, 0);
  assert.match(svg, /Baseline unresolved|unresolved/);
});

test('Matching strict failures suppress proof conclusions without changing the baseline cohort', async () => {
  const input = workload('bad'); input.validation_failures['current/300/nee'] = 'Strict proof validation failed';
  const groups = [group('bad', 'off', [1]), group('bad', 'proofs', [2]), group('bad', 'proof-extraction', [3])];
  const {marks, svg} = await evaluate('proof-overhead-cdf', [input], groups);
  assert.equal(points(marks).length, 0); assert.equal(points(marks, 'Record').length, 0);
  assert.match(svg, /Strict proof validation failed/); assert.match(svg, /0\/1 valid/);
  input.validation_failures = {'older-binary/300/nee': 'Stale error'};
  const refreshed = await evaluate('proof-overhead-cdf', [input], groups);
  assert.equal(points(refreshed.marks).length, 1);
});

test('An empty cache preserves expected Math rows and source blockers in the CDF', async () => {
  const math = await evaluate('math-cutoff-11', [workload('math', 'math-growth')], []);
  assert.match(math.svg, /Off · Egg/); assert.match(math.svg, /On · Egglog/);
  const missing = workload('source-missing'); missing.file_sha256 = '';
  const cdf = await evaluate('proof-overhead-cdf', [missing], []);
  assert.match(cdf.svg, /No selected replays yet/); assert.equal(points(cdf.marks).length, 0);
});

test('Ties share the cumulative rank and thresholds use the complete selected denominator', async () => {
  const inputs = ['a', 'b', 'c', 'd'].map(id => workload(id));
  const groups = inputs.flatMap((input, index) => [group(input.id, 'off', [1]),
    group(input.id, 'proof-extraction', [index < 2 ? 2 : index === 2 ? 4 : 1000])]);
  const {marks} = await evaluate('proof-overhead-cdf', inputs, groups);
  assert.deepEqual(points(marks).map(m => [m.datum.ratio, m.datum.cdf]), [[2, .5], [2, .5], [4, .75], [1000, 1]]);
  const labels = marks.filter(m => m.name === 'percentile_labels_marks' && m.datum.metric === 'Time');
  assert.deepEqual(labels.map(m => [m.datum.percentile, m.datum.ratio]), [[.5, 2], [.9, 1000]]);
  assert.ok(labels.every(m => m.x >= 0 && m.x <= 300 && m.y >= 0 && m.y <= 185));
});

// The collector and Vega own their respective calculations; use identical rows
// to guard their shared population policy, including former window boundaries.
test('Vega cohort agrees with Python for all matching samples and failures', async () => {
  const cases = [
    ['one', [1]], ['ten', Array(10).fill(1)], ['thirty', Array(30).fill(1)],
    ['boundary-fast', [.1]], ['boundary-slow', [30]], ['empty', []],
    ['all-not-latest-ten', [...Array(20).fill(.05), ...Array(10).fill(.15)]],
    ['old-failure', Array(35).fill(1)],
  ];
  const baselines = cases.map(([id, values]) => group(id, 'off', values));
  baselines.at(-1).samples[0].status = 'failure';
  const reference = spawnSync('uv', ['run', '--locked', 'python', '-c',
    'import json,sys; from benchmarking.baseline_selection import classify_baseline; ' +
    'print(json.dumps([classify_baseline(rows).status for rows in json.load(sys.stdin)]))'],
    {cwd: new URL('../', import.meta.url), input: JSON.stringify(baselines.map(g => g.samples)), encoding: 'utf8'});
  assert.equal(reference.status, 0, reference.stderr);
  const expected = JSON.parse(reference.stdout).flatMap((status, i) => status === 'selected' ? [cases[i][0]] : []);
  const groups = [...baselines, ...cases.map(([id]) => group(id, 'proof-extraction', [2]))];
  const {marks} = await evaluate('proof-overhead-cdf', cases.map(([id]) => workload(id)), groups);
  assert.deepEqual(points(marks).map(m => m.datum.workload_id).sort(), expected.sort());
});
