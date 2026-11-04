#!/usr/bin/env python3
"""Independent exact-integer QR oracle, not a compiler rewrite evaluator."""
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent

def qr(x, divisor=7):
    if divisor <= 0:
        raise ValueError('first fragment requires a fixed positive divisor')
    quotient = abs(x) // divisor
    if x < 0:
        quotient = -quotient
    return quotient, x - divisor * quotient

def expected(args, variant='source'):
    x, y, n = args
    if not (0 <= x < 64 and 0 <= y < 64 and 0 <= n <= 10_000_000):
        return '-9\n'
    qx, rx = qr(x)
    qy, ry = qr(y, 8 if variant == 'different-divisor' else 7)
    if variant != 'omit-quotient' and qx != qy:
        return '-1\n'
    if variant != 'omit-remainder' and rx != ry:
        return '-2\n'
    return f'{n * (n - 1) // 2 if x == y else -3 * n}\n'

def verify():
    rng = random.Random(7019)
    values = [-(2**63), -(2**63)+1, -8, -7, -6, -1, 0, 1, 6, 7, 8,
              2**63-2, 2**63-1]
    values += [rng.randrange(-(2**63), 2**63) for _ in range(10_000)]
    for x in values:
        q, r = qr(x)
        assert x == 7*q + r
        assert -(2**63) <= 7*q < 2**63
        assert -6 <= r <= 6
        assert (r == 0 or (r > 0) == (x > 0))
        assert (q*7 + r + 2**63) % 2**64 - 2**63 == x
    for x in range(64):
        for y in range(64):
            assert (qr(x) == qr(y)) == (x == y)
    negatives = [
        {'variant': 'omit-quotient', 'args': [5, 12, 8], 'expected': '-24\n',
         'reason': 'remainders equal, quotients differ'},
        {'variant': 'omit-remainder', 'args': [7, 8, 8], 'expected': '-24\n',
         'reason': 'quotients equal, remainders differ'},
        {'variant': 'different-divisor', 'args': [8, 9, 8], 'expected': '-24\n',
         'reason': 'QR7(8)=QR8(9)=(1,1), but 8!=9'},
    ]
    for row in negatives:
        assert expected(row['args'], row['variant']) == row['expected']
        assert row['expected'] != '28\n'
    rejected = []
    for divisor in (0, -1):
        try:
            qr(-(2**63), divisor)
        except ValueError as exc:
            rejected.append({'divisor': divisor, 'status': 'rejected-before-evaluation',
                             'reason': str(exc)})
        else:
            raise AssertionError('unsafe divisor admitted')
    result = {
        'status': 'passed', 'fixed_divisor': 7,
        'law_proof': 'For equal ordered pairs (q,r), exact reconstruction x=7q+r=y proves injectivity. Quotient truncates toward zero. For divisor 7, q*7 and r remain representable.',
        'sampled_signed_i64_values': len(values), 'sampling_is_not_exhaustive': True,
        'exhaustive_workload_domain_pairs': 64**2,
        'guard_counterexamples': negatives,
        'unsafe_divisors': rejected,
        'variable_or_mixed_divisor_admission': 'unsupported; matching fixed divisor identity required',
        'negative_divisor_note': '-1 is excluded from the first portable native fragment; LLVM signed division has the MIN/-1 exceptional case. No unsafe native operation is executed.',
        'nonmatching_source_paths': [
            {'args': [5,12,8], 'expected': expected([5,12,8])},
            {'args': [12,13,8], 'expected': expected([12,13,8])},
        ],
    }
    (ROOT/'oracle-results.json').write_text(json.dumps(result, indent=2)+'\n')
    return result

if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
