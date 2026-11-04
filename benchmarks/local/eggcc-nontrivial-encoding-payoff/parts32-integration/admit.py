from pathlib import Path
import subprocess,tarfile,io,json,hashlib,shutil
root=Path('/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/parts32-integration')
rows=[]
for dest,source,rev in [('/private/tmp/eggcc-parts32-candidate','/private/tmp/eggcc-nontrivial-encoding-payoff-u0','a0bbec127f83249074a46af3fd6f6126c90fe0fb'),('/private/tmp/encoding-parts32-candidate','/Users/saul/p/wt/egglog-encoding/eggcc-encoding-payoff','392b6d6b48b5bc307a5b9c981c957fc0a09e23e5')]:
 p=Path(dest);p.mkdir()
 archive=subprocess.check_output(['git','-C',source,'archive',rev])
 (root/(p.name+'.tar')).write_bytes(archive)
 with tarfile.open(fileobj=io.BytesIO(archive)) as t:t.extractall(p,filter='data')
 rows.append(dict(path=dest,source_git=source,revision=rev,archive_sha256=hashlib.sha256(archive).hexdigest()))
selected=Path('/private/tmp/eggcc-same-mask-candidate');candidate=Path('/private/tmp/eggcc-parts32-candidate')
for rel in ['Cargo.toml','Cargo.lock','dag_in_context/Cargo.toml','dag_in_context/Cargo.lock','dag_in_context/src/lib.rs']:
 (candidate/rel).write_text((selected/rel).read_text().replace('/private/tmp/encoding-same-mask-candidate','/private/tmp/encoding-parts32-candidate'))
encoding=Path('/private/tmp/encoding-parts32-candidate');admission=json.loads((root.parent/'candidate-same-mask/source-admission.json').read_text())
for row in admission['retained_e1_delta']:
 rel=row['path'];shutil.copy2(Path('/private/tmp/encoding-same-mask-candidate')/rel,encoding/rel)
# The inherited transport code is copied before the Parts32 implementation replaces its query theory.
shutil.copy2(selected/'dag_in_context/src/scoped_reasoning.rs',candidate/'dag_in_context/src/scoped_reasoning.rs')
for rel in ['rt.bc','rt.o']:shutil.copy2(Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0/runtime')/rel,candidate/'runtime'/rel)
(root/'source-admission.json').write_text(json.dumps(dict(roots=rows,selected_encoding=admission,original_runtime_reused=True),indent=2)+'\n')
