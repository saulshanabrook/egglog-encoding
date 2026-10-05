import assert from 'node:assert/strict';
import {existsSync, realpathSync} from 'node:fs';
import {mkdtemp, readFile, rm, writeFile} from 'node:fs/promises';
import {createRequire} from 'node:module';
import {delimiter, join} from 'node:path';
import test from 'node:test';
import {fileURLToPath, pathToFileURL} from 'node:url';

// Resolve the same pinned toolkit placed on PATH by the Makefile's npx command.
const cli = process.env.PATH.split(delimiter).map(path => join(path, 'vl2svg')).find(existsSync);
assert.ok(cli, 'Run make figures-parameter-test');
const toolkit = createRequire(realpathSync(cli));
const vega = await import(toolkit.resolve('vega'));
const {compile} = await import(toolkit.resolve('vega-lite'));
const conditions = ['DE · Disegg', 'EE · Egg', 'NEE · Egg', 'OEE · Egg', 'NE · Egglog', 'EE · Egglog'];
const treatments = ['egg-de', 'egg-ee', 'egg-nee', 'egg-oee', 'off', 'off'];

// These synthetic records exercise the generic snapshot contract. They are
// temporary test inputs, never written to the benchmark cache or shared export.
function group(index, count) {
  const key = {
    binary_sha256: `sha256:binary-${index}`, file_sha256: `sha256:file-${index < 4 ? 'in' : 'egg'}`,
    fact_directory_sha256: '', treatment: treatments[index], timeout_sec: 300,
    disequality_encoding: index === 5 ? 'ee' : 'nee',
  };
  return {key, labels: ['figures'], samples: Array.from({length: count}, (_, run) => ({
    ...key, row_index: index * 100 + run,
    report_schema_version: 5, started_at: new Date(Date.UTC(2026, 8, 30, 0, 0, index * 100 + run)).toISOString(),
    status: 'success', wall_sec: index * 20 + run + 1, max_rss_bytes: null,
    target_label: 'original-label', target_source: '.', target_path: '/test', target_git_ref: 'HEAD',
    target_git_sha: 'test-revision', target_is_dirty: false,
    file_path: `benchmarks/disequality/parameter-analysis.${index < 4 ? 'in' : 'egg'}`, fact_directory_path: null,
    error_exit_code: null, error_signal: null, error_message: null, timing_summary: null,
  }))};
}

async function evaluate(t, groups) {
  const spec = JSON.parse(await readFile(new URL('parameter-analysis.vl.json', import.meta.url), 'utf8'));
  assert.equal(spec.data.url, '../.reports-grouped.json');
  assert.equal(spec.data.format.property, undefined);
  const directory = await mkdtemp(fileURLToPath(new URL('parameter-test-', import.meta.url)));
  t.after(() => rm(directory, {recursive: true, force: true}));
  const snapshot = join(directory, 'grouped.json');
  await writeFile(snapshot, JSON.stringify({grouped_schema_version: 1, report_schema_version: 5, groups}));
  spec.data.url = pathToFileURL(snapshot).href;
  const warnings = [];
  const logger = vega.logger(vega.Warn, undefined, (...args) => warnings.push(args));
  const runtime = compile(spec, {logger}).spec;
  assert.equal(runtime.data.filter(source => source.url).length, 1);
  const view = new vega.View(vega.parse(runtime), {renderer: 'none', logger});
  t.after(() => view.finalize());
  await view.runAsync();
  assert.deepEqual(warnings, []);
  const marks = {};
  function visit(item) {
    if (item.name) marks[item.name] = item.items;
    for (const child of item.items ?? []) visit(child);
  }
  visit(view.scenegraph().root);
  return {marks, svg: await view.toSVG()};
}

test('all observations and positive sample counts share one zero-based linear scale', async t => {
  const counts = [1, 2, 3, 5, 11, 13];
  const groups = counts.map((count, index) => group(index, count));
  const {marks, svg} = await evaluate(t, groups);
  const runs = marks.parameter_runs_marks;
  const means = marks.parameter_means_marks;
  assert.equal(runs.length, 35);
  assert.equal(means.length, 6);
  assert.deepEqual(means.map(mark => mark.datum.selected), counts);
  assert.deepEqual(means.map(mark => mark.datum.mean), [1, 21.5, 42, 63, 86, 107]);
  const pixelsPerSecond = runs[0].x / runs[0].datum.seconds;
  for (const run of runs) assert.ok(Math.abs(run.x - run.datum.seconds * pixelsPerSecond) < 1e-8);
  assert.equal(marks.parameter_notice_marks.length, 0);
  for (const condition of conditions) assert.ok(svg.includes(condition));
  assert.ok(svg.includes('107 s (13)'));
});

test('failures, timeouts and invalid measurements keep good dots but suppress their means', async t => {
  const groups = conditions.map((_, index) => group(index, 3));
  groups[0].samples = groups[0].samples.slice(0, 1);
  groups[0].samples[0].wall_sec = 0;
  groups[1].samples[0].status = 'failure';
  groups[1].samples[0].wall_sec = 9999;
  groups[2].samples[0].status = 'timed-out';
  groups[2].samples[0].wall_sec = null;
  groups[3].samples[0].wall_sec = -1;
  groups[4].samples[0].wall_sec = null;
  groups[5].samples = [];
  const {marks, svg} = await evaluate(t, groups);
  assert.equal(marks.parameter_runs_marks.length, 9);
  assert.equal(marks.parameter_means_marks.length, 1);
  assert.equal(marks.parameter_means_marks[0].datum.mean, 0);
  assert.equal(marks.parameter_status_marks.length, 6);
  assert.equal(marks.parameter_notice_marks.length, 1);
  assert.match(svg, /2\/3 successful; 1 failed; no mean/);
  assert.match(svg, /2\/3 successful; 1 timed out; no mean/);
  assert.match(svg, /2\/3 successful; no mean/);
  assert.match(svg, /No observations/);
});

test('an empty generic snapshot still renders six missing rows', async t => {
  const {marks, svg} = await evaluate(t, []);
  assert.equal(marks.parameter_runs_marks.length, 0);
  assert.equal(marks.parameter_means_marks.length, 0);
  assert.equal(marks.parameter_status_marks.length, 6);
  assert.equal(marks.parameter_notice_marks.length, 1);
  for (const condition of conditions) assert.ok(svg.includes(condition));
});

test('newest exact group wins without pooling, truncating or falling back to older successes', async t => {
  const older = group(0, 12);
  const latest = group(0, 2);
  latest.key.file_sha256 = 'sha256:new-input';
  latest.samples.forEach((sample, index) => Object.assign(sample, {
    file_sha256: latest.key.file_sha256, started_at: `2026-09-30T01:00:0${index}Z`, wall_sec: index + 2,
  }));
  latest.samples[1].status = 'failure';
  latest.samples.reverse();
  const {marks, svg} = await evaluate(t, [latest, older]);
  assert.equal(marks.parameter_runs_marks.length, 1);
  assert.equal(marks.parameter_runs_marks[0].datum.seconds, 2);
  assert.equal(marks.parameter_means_marks.length, 0);
  assert.match(svg, /1\/2 successful; 1 failed; no mean/);
});

test('timestamp ties use physical row order and retain every selected-identity sample', async t => {
  const older = group(0, 1);
  const latest = group(0, 2);
  latest.key.file_sha256 = 'sha256:new-input';
  latest.samples.forEach((sample, index) => Object.assign(sample, {
    file_sha256: latest.key.file_sha256, started_at: older.samples[0].started_at,
    row_index: 10 + index, wall_sec: 4 + index * 2,
  }));
  // Another recorded path for the identical bytes belongs to the same cache
  // identity; its newer row participates once this group has an approved input.
  latest.samples[1].file_path = 'same-input-elsewhere.in';
  const {marks} = await evaluate(t, [latest, older]);
  assert.equal(marks.parameter_runs_marks.length, 2);
  assert.equal(marks.parameter_means_marks[0].datum.mean, 5);
});

test('alias, physical input, treatment, encoding, timeout and fact directory filter candidates', async t => {
  const input = conditions.map((_, index) => group(index, 1));
  input[0].labels = ['old-alias'];
  input[1].samples[0].file_path = 'benchmarks/disequality/parameter-analysis.egg';
  input[2].key.treatment = 'egg';
  input[3].key.timeout_sec = 301;
  input[4].key.fact_directory_sha256 = 'unexpected-facts';
  input[5].key.disequality_encoding = 'other-encoding';
  const {marks} = await evaluate(t, input);
  assert.equal(marks.parameter_runs_marks.length, 0);
  assert.equal(marks.parameter_means_marks.length, 0);
  assert.equal(marks.parameter_status_marks.length, 6);
});
