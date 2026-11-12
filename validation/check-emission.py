"""Compile-only equality checks; never execute source workload schedules."""
from pathlib import Path
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
SOURCE = Path('/tmp/slotted-mmm-nested-substitution')
CANDIDATE = SOURCE / 'target/release/egglog-experimental'
STAGE09 = Path('/tmp/slotted-mmm-bench-09/target/release/egglog-experimental')
OLD10 = Path('/tmp/slotted-mmm-bench-10/target/release/egglog-experimental')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def emit(binary, flags, source, destination):
    command = [str(binary), '--slotted', *flags, '--mode', 'desugar', str(source)]
    with destination.open('wb') as out, destination.with_suffix('.log').open('wb') as err:
        subprocess.run(command, cwd=SOURCE, stdout=out, stderr=err, check=True)
    return command


results = []
for name, binary, flags in [
    ('multipattern', STAGE09, []),
    ('nested', OLD10, ['--slotted-no-aliasing']),
]:
    for source in sorted((SOURCE / 'benchmarks/slotted/inputs/sdql').glob('*-44rules.egg')):
        before = HERE / f'{name}-{source.stem}-before.egg'
        after = HERE / f'{name}-{source.stem}-after.egg'
        commands = [emit(binary, flags, source, before), emit(CANDIDATE, flags, source, after)]
        count = int(subprocess.check_output([str(HERE / 'check-emission'), str(before), str(after)]))
        results.append(dict(mode=name, source=str(source.relative_to(SOURCE)), source_sha256=sha(source),
                            baseline_binary=str(binary), baseline_binary_sha256=sha(binary),
                            baseline_emitted_sha256=sha(before), candidate_emitted_sha256=sha(after),
                            emitted_bytes_identical=True, parsed_canonical_commands_identical=True,
                            command_count=count, commands=commands))

source = Path('/tmp/slotted-mmm-production/mixed-round-snapshot.egg')
for mode, option in [('proof-check', '--slotted-proof-checks'), ('proof-prove', '--proofs')]:
    for nested in [False, True]:
        name = f'{mode}-' + ('nested' if nested else 'multipattern')
        flags = [option, *(['--slotted-no-aliasing'] if nested else [])]
        before, after = HERE / f'{name}-before.egg', HERE / f'{name}-after.egg'
        commands = [emit(STAGE09, flags, source, before), emit(CANDIDATE, flags, source, after)]
        count = int(subprocess.check_output([str(HERE / 'check-emission'), str(before), str(after)]))
        results.append(dict(mode=name, source=str(source), source_sha256=sha(source),
                            baseline_binary=str(STAGE09), baseline_binary_sha256=sha(STAGE09),
                            baseline_emitted_sha256=sha(before), candidate_emitted_sha256=sha(after),
                            emitted_bytes_identical=True, parsed_canonical_commands_identical=True,
                            command_count=count, commands=commands))

assert len(results) == 24
payload = dict(candidate_binary=str(CANDIDATE), candidate_binary_sha256=sha(CANDIDATE),
               baseline_stage09='bf13e3ac9d6c548244e3ac937eb4a13b62c3e142',
               old_stage10='fb04877229a0f720d9198cb68c5bf4468aca53dc',
               validation='compile-only; no workload execution or performance measurements',
               results=results)
(HERE / 'emission-equivalence.json').write_text(json.dumps(payload, indent=2) + '\n')
print(f'{len(results)} emitted programs identical; {sum(r["command_count"] for r in results)} parsed commands per endpoint')
