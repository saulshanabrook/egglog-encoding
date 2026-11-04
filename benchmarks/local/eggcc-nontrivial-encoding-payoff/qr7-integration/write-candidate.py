#!/usr/bin/env python3
"""Install the retained QR7 source template into its fresh isolated host."""
import difflib
import hashlib
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parent
HOST = Path('/private/tmp/eggcc-qr7-candidate')


def main():
    if (ROOT / 'candidate-identities.json').exists():
        raise RuntimeError('candidate already written; preserve its identities')
    admission = json.loads((ROOT / 'source-admission.json').read_text())
    if admission['status'] != 'sources-reconstructed-not-built':
        raise RuntimeError('unexpected source admission')
    target = HOST / 'dag_in_context/src/scoped_qr7.rs'
    if target.exists():
        raise RuntimeError('scoped_qr7.rs already exists')
    target.write_bytes((ROOT / 'scoped_qr7.rs').read_bytes())
    lib = HOST / 'dag_in_context/src/lib.rs'
    source = lib.read_text()
    anchor = 'pub mod schedule;\n'
    assert source.count(anchor) == 1
    source = source.replace(anchor, anchor + 'mod scoped_qr7;\n')
    anchor = ('    let loop_context_unions =\n'
              '        context_cache.get_unions_with_sharing(&mut printed, &mut tree_state, &mut term_cache);\n')
    assert source.count(anchor) == 1
    hook = '''
    if use_context {
        for (write_addr, load_addr) in scoped_qr7::analyze(&program) {
            let write_term = write_addr.to_egglog_with(&mut tree_state);
            let write_var = print_with_intermediate_helper(
                &tree_state.termdag, write_term, &mut term_cache, &mut printed,
            );
            let load_term = load_addr.to_egglog_with(&mut tree_state);
            let load_var = print_with_intermediate_helper(
                &tree_state.termdag, load_term, &mut term_cache, &mut printed,
            );
            writeln!(printed, "(Qr7MustAlias {write_var} {load_var})").unwrap();
        }
    }
    if std::env::var("EGGCC_SCOPED_MODE").as_deref() != Ok("consumer-off") {
        writeln!(printed, "(Qr7ForwardEnabled)").unwrap();
    }
'''
    lib.write_text(source.replace(anchor, anchor + hook))
    memory = HOST / 'dag_in_context/src/optimizations/mem_simple.egg'
    source = memory.read_text()
    source += '''

; Query-local QR7 must-alias bridge. No pointer equality reaches extraction.
(relation Qr7MustAlias (Expr Expr))
(relation Qr7ForwardEnabled ())
(rule ((Qr7ForwardEnabled)
       (Qr7MustAlias write-addr load-addr)
       (= write (Top (Write) write-addr write-val state))
       (= load (Bop (Load) load-addr write)))
      ((union (Get load 0) write-val)
       (union (Get load 1) write)
       (DidMemOptimization "QR7 must-alias store forward"))
      :ruleset mem-simple)
'''
    memory.write_text(source)
    changed = ['Cargo.toml', 'Cargo.lock', 'dag_in_context/Cargo.toml',
               'dag_in_context/Cargo.lock', 'dag_in_context/src/lib.rs',
               'dag_in_context/src/optimizations/mem_simple.egg',
               'dag_in_context/src/scoped_qr7.rs']
    patch = []
    base = ROOT.parent / 'parts32-integration/eggcc-parts32-candidate.tar'
    with tarfile.open(base) as archive:
        for relative in changed:
            try:
                original = archive.extractfile(relative).read().decode()
            except KeyError:
                original = ''
            current = (HOST / relative).read_text()
            patch.extend(difflib.unified_diff(original.splitlines(True), current.splitlines(True),
                                             fromfile='a/' + relative, tofile='b/' + relative))
    (ROOT / 'eggcc-candidate.patch').write_text(''.join(patch))
    files = [dict(path=str(HOST / name), relative=name,
                  sha256=hashlib.sha256((HOST / name).read_bytes()).hexdigest()) for name in changed]
    files.extend(dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())
                 for path in sorted(ROOT.glob('*.py')))
    (ROOT / 'candidate-identities.json').write_text(json.dumps(
        dict(status='written-not-built', files=files, cargo_executed=False,
             compiler_executed=False, native_executed=False, timing_taken=False), indent=2) + '\n')
    print(json.dumps({'status': 'written-not-built', 'files': len(files)}))


if __name__ == '__main__':
    main()
