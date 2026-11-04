#!/usr/bin/env python3
"""Prospective correctness/causal matrix; no timing collector is provided."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

import run as capture

BASE = Path(__file__).resolve().parent
ROOT = Path(os.environ.get('QR7_OUTPUT_ROOT', str(BASE)))
U0 = BASE.parent / 'admission/bin/eggcc'
BIN = Path(os.environ.get('QR7_BINARY', str(BASE / 'bin/eggcc')))
LLVM = Path('/opt/homebrew/opt/llvm@18/bin')
MODES = ['u0', 'off', 'seed-only', 'primitive-only', 'encoding', 'manual',
         'cancellation-off', 'identity-off', 'x-rescue', 'key-rescue',
         'query-off', 'transport-off', 'bridge-off', 'consumer-off']
spec = importlib.util.spec_from_file_location('qr7_oracle', BASE.parent / 'qr7-screen/oracle.py')
oracle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def case(family, mode, source, rows, context=True):
    folder = ROOT / 'matrix' / family / mode
    folder.mkdir(parents=True, exist_ok=False)
    capture.ROOT = ROOT
    capture.ENV.update(EGGCC_SCOPED_MODE='off' if mode == 'u0' else mode,
                       EGGCC_SCOPED_EVIDENCE=str(folder / 'interp-evidence'))
    argv = [U0 if mode == 'u0' else BIN]
    if context:
        argv.append('--with-context')
    argv += ['--run-mode', 'optimize']
    capture.run(f'{family}-{mode}-interp', [*argv, '--interp',
                '--run-data-out', folder / 'interp.json', source])
    data = json.loads((folder / 'interp.json').read_text())
    if data['original_interpreted'] != data['result_interpreted']:
        raise RuntimeError(f'interpreter mismatch in {family}/{mode}')
    evidence = folder / 'evidence'
    capture.ENV['EGGCC_SCOPED_EVIDENCE'] = str(evidence)
    emitted = capture.run(f'{family}-{mode}-emit', [*argv, '--egraph-out-dir', folder / 'egraphs',
                          '--run-data-out', folder / 'emit.json', source])
    (folder / 'optimized.bril').write_bytes(emitted)
    capture.ENV.pop('EGGCC_SCOPED_EVIDENCE', None)
    capture.ENV['EGGCC_SCOPED_MODE'] = 'off'
    native = folder / 'native'
    native.mkdir()
    binary = native / 'program'
    capture.run(f'{family}-{mode}-lower', [U0, '--with-context', '--run-mode', 'llvm',
                '--optimize-egglog', 'false', '--optimize-bril-llvm', 'O3_O3',
                '-o', binary, '--llvm-output-dir', native / 'program.ll',
                '--run-data-out', native / 'lower.json', folder / 'optimized.bril'])
    assembly = capture.run(f'{family}-{mode}-disassemble',
                           [LLVM / 'llvm-objdump', '--disassemble', '--no-show-raw-insn', binary], 30)
    (native / 'program.asm').write_bytes(assembly)
    outputs = []
    for index, row in enumerate(rows):
        args, expected = row['args'], row['expected_stdout']
        stdout = capture.run(f'{family}-{mode}-native-{index:03}', [binary, *args], 30).decode()
        outputs.append(dict(args=args, expected_stdout=expected, stdout=stdout))
        if stdout != expected:
            (folder / 'partial-outputs.json').write_text(json.dumps(outputs, indent=2) + '\n')
            raise RuntimeError(f'wrong output in {family}/{mode}: {outputs[-1]}')
    queries = [query for path in sorted(evidence.glob('boundary-*.json'))
               for query in json.loads(path.read_text())['queries']]
    result = dict(family=family, mode=mode, context=context, source=str(source),
                  source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  emitted_sha256=hashlib.sha256(emitted).hexdigest(),
                  binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  outputs=outputs, queries=queries, performance_samples=False)
    (folder / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    phase = sys.argv[1]
    rows = []
    if phase == 'positive':
        arguments = [(12,12,8), (0,0,0), (0,0,1), (63,63,1024), (7,7,8),
                     (5,12,8), (12,13,8), (-1,0,8), (64,64,8), (1,1,-1), (1,1,10000001)]
        expected = [dict(args=list(args), expected_stdout=oracle.expected(args)) for args in arguments]
        for mode in MODES:
            rows.append(case('positive', mode, BASE / 'fixtures/source.bril', expected))
    elif phase == 'negative':
        for name, variant, args in [('omit-quotient-v2', 'omit-quotient', (5,12,8)),
                                    ('omit-remainder-v2', 'omit-remainder', (7,8,8)),
                                    ('different-divisor', 'different-divisor', (8,9,8))]:
            expected = [dict(args=list(args), expected_stdout=oracle.expected(args, variant))]
            for mode in ['u0', 'off', 'seed-only', 'primitive-only', 'manual', 'encoding']:
                rows.append(case(name, mode, BASE / 'fixtures' / (name + '.bril'), expected))
    elif phase == 'context-negative':
        rows.append(case('no-context', 'encoding', BASE / 'fixtures/source.bril',
                         [dict(args=[12,12,8], expected_stdout='28\n')], context=False))
    elif phase == 'loop-negative':
        text = (BASE / 'fixtures/source.bril').read_text()
        source = ROOT / 'fixtures/changed-pointer.bril'
        source.parent.mkdir(parents=True, exist_ok=True)
        if source.exists():
            raise RuntimeError(f'refusing to overwrite {source}')
        source.write_text(text.replace('.body:\n', '.body:\n  pi: ptr<int> = ptradd pi one;\n'))
        for mode in ['u0', 'off', 'manual', 'encoding']:
            rows.append(case('changed-pointer', mode, source,
                             [dict(args=[12,12,8], expected_stdout='-24\n')]))
    else:
        raise ValueError(f'unknown matrix phase: {phase}')
    result = ROOT / (phase + '-results.json')
    if result.exists():
        raise RuntimeError(f'refusing to overwrite {result}')
    result.write_text(json.dumps(rows, indent=2) + '\n')


if __name__ == '__main__':
    main()
