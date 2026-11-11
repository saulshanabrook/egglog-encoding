"""Prepare genuine emitted scripts only; never import populations or launch Racket."""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
import sys
from types import CodeType, FunctionType, ModuleType, SimpleNamespace

MIRROR = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(MIRROR))
from scripts import reproduction_misaal_patterns as repair

ROOT = Path('/Users/saul/p/egglog-encoding')
CHECKOUT = ROOT / 'benchmarks/local/reproduction/stages/misaal-prerequisites/prepare/de24509065a91a0011099031af73b866aad56a8f4ccd70149684696c620846b1/attempt-0001/environment/sources/MISAAL'
EVIDENCE = ROOT / 'benchmarks/local/reproduction/diagnostics/misaal-parameter-abi-evidence-0001'
OUTPUT = Path(__file__).resolve().parent

def module_from_actual_methods(path: Path, helper: str) -> ModuleType:
    source = path.read_text()
    tree = ast.parse(source)
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'PatternAbstractor')
    code = compile(source, str(path), 'exec', dont_inherit=True)
    class_code = next(n for n in code.co_consts if isinstance(n, CodeType) and n.co_name == 'PatternAbstractor')
    method_codes = {n.co_name: n for n in class_code.co_consts if isinstance(n, CodeType)}
    module = ModuleType('patterns.PatternUtils')
    module.__file__ = str(path)
    methods = {'__module__': module.__name__}
    for method in cls.body:
        if isinstance(method, ast.FunctionDef):
            defaults = tuple(ast.literal_eval(n) for n in method.args.defaults) or None
            methods[method.name] = FunctionType(method_codes[method.name], vars(module), method.name, defaults)
    module.PatternAbstractor = type('PatternAbstractor', (), methods)
    helper_code = compile(helper, str(CHECKOUT / 'lib/utils/DSLInstructionUtils.py'), 'exec', dont_inherit=True)
    cond_code = next(n for n in helper_code.co_consts if isinstance(n, CodeType) and n.co_name == 'emit_racket_cond')
    module.emit_racket_cond = FunctionType(cond_code, vars(module), 'emit_racket_cond')
    return module

def emit(module: ModuleType, general: bool, header: str) -> str:
    captures = []
    def capture(statements):
        captures.append(header + '\n' + '\n'.join(statements) + '\n')
        return SimpleNamespace(returncode=1)
    basename = 'general-depth1' if general else 'ordinary-depth2'
    module.tempfile = SimpleNamespace(_get_candidate_names=lambda: iter([basename]))
    module.execute_racket_file = capture
    instance = module.PatternAbstractor.__new__(module.PatternAbstractor)
    instance.examples_limit = None
    if general:
        result = instance.generate_param_expr_general({0: [2, 4, 6], 1: [1, 2, 3], 2: [5, 7, 11]}, 0, depth=1, exclude_regs=[1])
    else:
        result = instance.generate_param_expr({0: [1, 2, 3]}, {0: [2, 4, 6], 1: [5, 7, 11]}, 0, depth=2, only_src_params=False, exclude_regs=[1])
    assert result == (False, None) and len(captures) == 1
    return captures[0]

def main():
    assert not (OUTPUT / 'manifest.json').exists(), 'Prepared evidence already exists; use a new diagnostic directory.'
    source_path = CHECKOUT / 'lib/patterns/PatternUtils.py'
    paper_path = EVIDENCE / 'c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4-PatternUtils.py'
    helper_path = CHECKOUT / 'lib/utils/DSLInstructionUtils.py'
    helper = helper_path.read_text()
    header = next(ast.literal_eval(n.value) for n in ast.parse(helper).body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'HYDRIDE_HEADER' for t in n.targets))
    pins = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in [source_path, paper_path, helper_path, CHECKOUT / 'misaal/synthesis/param_abstract.rkt', Path(repair.__file__), Path(__file__)]}
    assert pins[str(paper_path)] == '9f6fd97c8bd27d2b59f2f0edc57c364ab6eb5a8c1c2c6ffd7e616a79bc74be29'
    current = module_from_actual_methods(source_path, helper)
    paper = module_from_actual_methods(paper_path, helper)
    original = dict(vars(current.PatternAbstractor))
    baseline = {name: emit(current, general, header) for name, general in [('ordinary-depth2',False),('general-depth1',True)]}
    request = {'checkout': str(CHECKOUT), 'revision':'44ff893445d664cd87f52b08a138260ed2015ba8', 'parameter_abi':repair.PARAMETER_ABI_CONTRACT, 'source_hashes': dict(repair.PARAMETER_ABI_SOURCE_SHA256)}
    receipt = {}
    programs = {}
    with repair.restore_parameter_abi(current, request, receipt, lambda: None):
        for name, general in [('ordinary-depth2',False),('general-depth1',True)]:
            actual = emit(current, general, header)
            assert actual == emit(paper, general, header)
            assert actual != baseline[name]
            programs[name] = {'text':actual,'expected_exit':0,'result_file': name+'.temp'}
            programs[name+'-unadapted'] = {'text':baseline[name],'expected_exit':'nonzero, specifically synthesize-param-expression arity mismatch expected 4 given 5'}
        for name,value in original.items():
            if name not in {'emit_synthesize_query','generate_param_expr_general'}:
                assert vars(current.PatternAbstractor)[name] is value
    assert vars(current.PatternAbstractor) == original
    for path,sha in pins.items():
        assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == sha
    for name,entry in programs.items():
        text=entry.pop('text')
        path=OUTPUT/(name+'.rkt')
        path.write_text(text)
        entry.update(path=str(path),sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    (OUTPUT/'manifest.json').write_text(json.dumps({'status':'prepared-offline-only','admitted':False,'proof_admitted':False,'source_pins':pins,'adaptation_receipt':receipt,'programs':programs,'method_instantiation':'exact full-module CodeType; module imports and populations never executed','capture_boundary':'original helper header plus unmodified real generated statements; launch intercepted with returncode1 to avoid absent solver result files','request':request,'required_native_guards':{'timeout_sec':60,'process_group_rss_bytes':5*1024**3,'host_reserve_bytes':2*1024**3,'minimum_disk_bytes':10*1024**3,'shared_heavy_lock':True},'native_runtime':'Must use completed pinned Racket/Rosette/Hydride/MISAAL runtime and verify actual resolved source-package identities before execution'},indent=2)+'\n')
    print(json.dumps({'status':'prepared-offline-only','programs':len(programs),'unchanged_original_class_methods':len(receipt['parameter_abi']['original_methods'])}))

if __name__ == '__main__':
    main()
