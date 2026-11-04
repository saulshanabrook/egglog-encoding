from pathlib import Path
import importlib.util
BASE=Path('/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/route-integration')
spec=importlib.util.spec_from_file_location('capture',BASE/'run.py');capture=importlib.util.module_from_spec(spec);spec.loader.exec_module(capture)
u0=Path('/private/tmp/eggcc-nontrivial-encoding-payoff-u0');capture.ENV['EGGCC_ROOT']=str(u0);capture.ENV['CARGO_TARGET_DIR']='/private/tmp/eggcc-affine-u0-validation-target'
capture.run('u0-root-clippy',['cargo','clippy','--offline','--locked','--tests','--','-D','warnings'],1800,cwd=u0,check=False)
