#!/usr/bin/env python3
"""Inspect captured QR7 artifacts without running compilers or workloads."""
import hashlib
import json
import os
from pathlib import Path
import re

ROOT = Path(os.environ.get('QR7_OUTPUT_ROOT', str(Path(__file__).resolve().parent)))


def entry_summary(text):
    labels = list(re.finditer(r'^([A-Za-z0-9_.]+):', text, re.M))
    graph = {label.group(1): set() for label in labels}
    for index, label in enumerate(labels):
        block = text[label.end():labels[index+1].start() if index+1 < len(labels) else len(text)]
        graph[label.group(1)].update(target for target in re.findall(r'label %([A-Za-z0-9_.]+)', block)
                                     if target in graph)
    indices, lowlinks, stack, active, cycles = {}, {}, [], set(), []

    def visit(node):
        indices[node] = lowlinks[node] = len(indices)
        stack.append(node)
        active.add(node)
        for target in graph[node]:
            if target not in indices:
                visit(target)
                lowlinks[node] = min(lowlinks[node], lowlinks[target])
            elif target in active:
                lowlinks[node] = min(lowlinks[node], indices[target])
        if lowlinks[node] == indices[node]:
            component = []
            while True:
                value = stack.pop()
                active.remove(value)
                component.append(value)
                if value == node:
                    break
            if len(component) > 1 or node in graph[node]:
                cycles.append(sorted(component))

    for node in graph:
        if node not in indices:
            visit(node)
    return dict(sha256=hashlib.sha256(text.encode()).hexdigest(),
                load_i64=len(re.findall(r'\bload i64\b', text)),
                store_i64=len(re.findall(r'\bstore i64\b', text)),
                vector_integer_adds=len(re.findall(r'\badd <2 x i64>', text)),
                cyclic_basic_block_components=cycles)


def main():
    positive = json.loads((ROOT / 'positive-results.json').read_text())
    by = {row['mode']: row for row in positive}
    report = dict(functions={}, causal={}, gates={}, performance_acceptance=False)
    for row in positive:
        mode = row['mode']
        llvm = (ROOT / 'matrix/positive' / mode / 'native/program.ll').read_text()
        report['functions'][mode] = {}
        for name in ['main', '_main']:
            match = re.search(r'^define [^\n]*@' + name + r'\([^\n]*\n.*?^\}', llvm, re.M | re.S)
            if match is None:
                raise RuntimeError(f'missing native function {mode}/{name}')
            report['functions'][mode][name] = entry_summary(match.group(0) + '\n')
        events = []
        relation_rows = 0
        for path in sorted((ROOT / 'matrix/positive' / mode / 'egraphs').glob('*.json')):
            nodes = json.loads(path.read_text())['nodes']
            relation_rows += sum(node['op'] == 'Qr7MustAlias' for node in nodes.values())
            for node in nodes.values():
                if node['op'] == 'DidMemOptimization':
                    events.extend(nodes[child]['op'] for child in node['children'])
        report['causal'][mode] = dict(queries=row['queries'], relation_rows=relation_rows, events=events)
    for a,b in [('u0','off'),('u0','seed-only'),('u0','primitive-only'),('encoding','manual'),
                ('encoding','x-rescue'),('encoding','key-rescue')]:
        assert by[a]['emitted_sha256'] == by[b]['emitted_sha256'], (a,b,'emitted')
        assert report['functions'][a] == report['functions'][b], (a,b,'native')
    for mode in ['cancellation-off', 'identity-off', 'query-off', 'transport-off', 'bridge-off', 'consumer-off']:
        assert by[mode]['emitted_sha256'] == by['u0']['emitted_sha256'], (mode,'knockout emitted')
        assert report['functions'][mode] == report['functions']['u0'], (mode,'knockout native')
    for mode in ['encoding', 'manual', 'x-rescue', 'key-rescue']:
        assert any(query.get('export') for query in by[mode]['queries']), mode
        assert any('QR7 must-alias store forward' in event for event in report['causal'][mode]['events']), mode
    assert report['causal']['consumer-off']['relation_rows'] > 0
    assert not any('QR7 must-alias store forward' in event for event in report['causal']['consumer-off']['events'])
    for mode in ['seed-only', 'primitive-only']:
        queries = [query for query in by[mode]['queries'] if query.get('accepted')]
        assert queries, mode
        for query in queries:
            assert query['quotient_seeded'] and query['remainder_seeded']
            assert not query['engine_witness_queries_run'] and not query['injectivity_saturated']
            assert query['manual_receipts'] is None and query['address_equal'] is None and not query['export']
    assert report['functions']['u0']['main']['cyclic_basic_block_components']
    assert not report['functions']['encoding']['main']['cyclic_basic_block_components']
    for phase in ['negative', 'context-negative', 'loop-negative']:
        rows = json.loads((ROOT / (phase + '-results.json')).read_text())
        for row in rows:
            assert not any(query.get('export') for query in row['queries']), row['family']
            assert all(output['stdout'] == output['expected_stdout'] for output in row['outputs'])
    report['gates'] = dict(output_and_causal_assertions_passed=True, same_source_manual_matched=True,
                           primitive_null=True, consumer_isolated=True,
                           actual_entry_loop_eliminated=True, timing_collected=False)
    target = ROOT / 'inspection.json'
    if target.exists():
        raise RuntimeError(f'refusing to overwrite {target}')
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['gates'], indent=2))


if __name__ == '__main__':
    main()
