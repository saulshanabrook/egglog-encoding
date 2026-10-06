"""Exercise live capture handoffs with tiny fake tools, never native validation."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from types import ModuleType
from typing import Any

import pytest

from scripts import misaal_reproduction as misaal


@pytest.fixture
def protocol_request(tmp_path: Path) -> Path:
    checkout = tmp_path / "source"
    compiler = checkout / "lib/compiler"
    compiler.mkdir(parents=True)
    (checkout / "lib/patterns").mkdir()
    (compiler / "EggLogCompiler.py").write_text(
        "from misaal_capture import capture_helper\nimport subprocess as sb\n"
        "from types import SimpleNamespace\nclass EggLogCompiler: pass\n"
        "def is_pattern_valid_egg(filename, backend='original/configured/backend'):\n"
        "    compiler = SimpleNamespace(egglog_bin=backend)\n"
        "    result = capture_helper(compiler.egglog_bin, filename, quiet=False)\n"
        "    return result.returncode == 0\n"
    )
    pattern_utils = checkout / "lib/patterns/PatternUtils.py"
    pattern_utils.write_text(
        "from misaal_capture import capture_helper\nimport subprocess as sb\nfrom types import SimpleNamespace\n"
        "def is_pattern_valid_egg(filename, backend='original/configured/backend'):\n"
        "    compiler = SimpleNamespace(egglog_bin=backend)\n"
        "    result = capture_helper(compiler.egglog_bin, filename, quiet=True)\n"
        "    sb.run('rm ' + filename, shell=True)\n"
        "    return result.returncode == 0\n"
    )
    (compiler / "HydrideCompiler.py").write_text(
        "from compiler.EggLogCompiler import EggLogCompiler\nclass HydrideCompiler(EggLogCompiler): pass\n"
    )
    tools = {
        "backend": (
            "import os, sys\nprint('(Seed)')\nfrom pathlib import Path\n"
            "if Path(sys.argv[1]).read_text() == 'rejected input': sys.exit(9)\n"
            "if os.environ.get('PROTOCOL_MULTI_ROOT'): print('(Seed)')\n"
            "sys.exit(7 if os.environ.get('PROTOCOL_BACKEND_FAILURE') else 0)\n"
        ),
        "generator": "",
    }
    for name, script in tools.items():
        executable = tmp_path / name
        executable.write_text(f"#!{sys.executable}\n" + script)
        executable.chmod(0o755)
    request: dict[str, Any] = {
        "case_id": "protocol-only",
        "revision": "a" * 40,
        "checkout": str(checkout),
        "source_hashes": {
            str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [*compiler.glob("*.py"), pattern_utils]
        },
        "generator_command": [str(tmp_path / "generator"), "{output}"],
        "expected_generator_outputs": ["generator.a", "generator.ll"],
        "environment": {"PATH": os.environ["PATH"]},
    }
    for name in ("python", "backend", "generator"):
        executable = Path(sys.executable).resolve() if name == "python" else tmp_path / name
        request[name] = str(executable)
        request[name + "_sha256"] = hashlib.sha256(executable.read_bytes()).hexdigest()
    request_path = tmp_path / "request.json"
    request_path.write_text(json.dumps(request))
    return request_path


ARM_EMPTY_PROGRAM = """from compiler.HydrideCompiler import HydrideCompiler
from utils.egg_config import EGG_PKG_PATH
from sema.hexsemantics_new import semantics as hvx_semantics
from sema.x86SemanticsAllArgs import semantcs as x86_semantics
from sema.halide_decomposed import halide_decomposed as halide_semantics
from sema.hvx_swizzles_decomposed import hvx_swizzles_decomposed as hvx_swizzles
from sema.x86_swizzles_decomposed import x86_swizzles_decomposed as x86_swizzles
from sema.arm_swizzles_decomposed import arm_swizzles_decomposed as arm_swizzles
from sema.ARMSema import arm_semantics
from sema.repairs_sema import repair_semantics
from utils.DSLInstructionUtils import parse_dict_with_bounded
import sys

misaal_input_patterns = []
from patterns.ARM import arm_patterns as misaal_output_patterns
misaal_patterns = misaal_input_patterns + misaal_output_patterns
halide_dsl_list = parse_dict_with_bounded(halide_semantics)
misaal_input = halide_dsl_list
inst_dict = parse_dict_with_bounded(arm_semantics)
swizzle_dict = parse_dict_with_bounded(arm_swizzles)
misaal_output = inst_dict + swizzle_dict
so_path = "{legalizer}"
llvm_flags = ["-arm-hydride-legalize"]
intrin = "{hydride}/codegen-generator/tools/low-level-codegen/wrappers/arm_wrappers.c.ll"
HYDRIDE_ROOT = "{hydride}"
# Defining Tests\x20
tests = []
if len(tests) == 0:
	sys.exit(0)
# Defining MISAAL Rewrite compiler
misaal_compiler = HydrideCompiler(misaal_patterns, src_dsl_list = misaal_input, target_dsl_list = misaal_output,
    run_iterations = 5, egg_pkg_path = EGG_PKG_PATH, tests = tests, llvm_so_path = so_path, llvm_flags =  llvm_flags,
    intrinsics_file =  intrin, hydride_root_path =  HYDRIDE_ROOT, llvm_out_file_name = "{prefix}")
# Invoke compiler and print stats
misaal_compiler.compile_hydride()
misaal_compiler.run_llvm_legalizer()
misaal_compiler.print_stats()
"""


@pytest.fixture
def source_request(protocol_request: Path) -> Path:
    request = json.loads(protocol_request.read_text())
    checkout = Path(request["checkout"])
    request.update(
        revision="44ff893445d664cd87f52b08a138260ed2015ba8",
        configuration={"target": "arm"},
        pattern_cache_contract={
            "environment": "MISAAL_PATTERN_CACHE_DIR",
            "required": "adapter supplies a fresh empty attempt-owned directory before child imports",
            "generation": "unchanged",
            "default": "source lib/patterns when variable is absent",
        },
    )
    request["environment"]["MISAAL_DISABLE_FRONTEND_PATTERNS"] = "1"
    modules = {
        "utils/egg_config.py": 'EGG_PKG_PATH = "original/configured/backend"\n',
        "utils/DSLInstructionUtils.py": "def parse_dict_with_bounded(value): return []\n",
    }
    for module, symbol in {
        "hexsemantics_new": "semantics",
        "x86SemanticsAllArgs": "semantcs",
        "halide_decomposed": "halide_decomposed",
        "hvx_swizzles_decomposed": "hvx_swizzles_decomposed",
        "x86_swizzles_decomposed": "x86_swizzles_decomposed",
        "arm_swizzles_decomposed": "arm_swizzles_decomposed",
        "ARMSema": "arm_semantics",
        "repairs_sema": "repair_semantics",
    }.items():
        modules[f"sema/{module}.py"] = f"{symbol} = {{}}\n"
    modules["patterns/ARM.py"] = """import os
from pathlib import Path
cache = Path(os.environ['MISAAL_PATTERN_CACHE_DIR'])
with Path('pattern-imports.txt').open('a') as log: log.write('import\n')
if (cache / 'ARM_abstract.pickle').exists():
    arm_patterns = ['abstract']
elif (cache / 'ARM.pickle').exists():
    arm_patterns = ['raw']
    (cache / 'ARM_abstract.pickle').write_text('abstract fixture')
else:
    arm_patterns = ['raw']
    (cache / 'ARM.pickle').write_text('raw fixture')
""".replace("log.write('import\n')", "log.write('import\\n')")
    for relative, content in modules.items():
        path = checkout / "lib" / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    request["source_hashes"].update(
        {
            str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (checkout / "lib").rglob("*.py")
        }
    )
    protocol_request.write_text(json.dumps(request))
    return protocol_request


@pytest.fixture
def export_request(source_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    request = json.loads(source_request.read_text())
    checkout = Path(request["checkout"])
    request.update(egglog_export=misaal.EGGLOG_EXPORT, expected_generator_outputs=[])
    request["environment"].update(
        LEGALIZERS_DIR=str(checkout / "absent-selectors"), HYDRIDE_DIR=str(checkout / "Hydride")
    )
    # Source/preparation verification is independently owned; these protocol tests
    # inject only its API boundary. All adapter source/tool hashes remain checked.
    module = ModuleType("scripts.reproduction_misaal_export")
    module.__dict__.update(verify_export_request=lambda request: None, EXPORT_SOURCE_SHA256={})
    monkeypatch.setitem(sys.modules, module.__name__, module)
    for target, symbol in (("halide", "Halide_patterns"), ("hvx", "HVX_patterns"), ("x86", "x86_patterns")):
        name = {"halide": "Halide", "hvx": "HVX", "x86": "x86"}[target]
        (checkout / f"lib/patterns/{name}.py").write_text(f"""import os
from pathlib import Path
cache = Path(os.environ['MISAAL_PATTERN_CACHE_DIR'])
with Path('pattern-imports.txt').open('a') as log: log.write({target + chr(10)!r})
if (cache / '{target}_abstract.pickle').exists(): pass
elif (cache / '{target}.pickle').exists(): (cache / '{target}_abstract.pickle').write_text('abstract fixture')
else: (cache / '{target}.pickle').write_text('raw fixture')
{symbol} = []
""")
    compiler = checkout / "lib/compiler/HydrideCompiler.py"
    compiler.write_text("""import os
from pathlib import Path
from compiler.EggLogCompiler import EggLogCompiler
class HydrideCompiler(EggLogCompiler):
    def __init__(self, patterns, **options):
        self.input_tests = options['tests']
        self.egglog_bin = options['egg_pkg_path']
        self.output_file_path = 'test.out'
    def get_rosette_expression_str(self, input_expr, output_expr, function_name):
        return '; ' + function_name + '\\n' + output_expr
    def recursive_rewrite(self, raw):
        if os.environ.get('PROTOCOL_RECURSIVE_EXIT'): raise SystemExit(0)
        self.execute_egglog_file(str(raw))
        self.swizzle(raw)
    def swizzle(self, raw): self.execute_egglog_file(str(raw))
    def compile_hydride(self):
        if os.environ.get('PROTOCOL_EARLY_EXIT'): raise SystemExit(0)
        if os.environ.get('PROTOCOL_COMPILE_FAILURE'): raise ValueError('original compile failed')
        if os.environ.get('PROTOCOL_TRY_LLVM'): self.run_llvm_legalizer()
        if os.environ.get('PROTOCOL_HELPERS'):
            from compiler.EggLogCompiler import is_pattern_valid_egg as compiler_helper
            from patterns.PatternUtils import is_pattern_valid_egg as pattern_helper
            for index, helper in enumerate((compiler_helper, pattern_helper)):
                for accepted in (True, False):
                    helper_input = Path(f'helper-input-{index}-{accepted}.egg')
                    helper_input.write_text('accepted input' if accepted else 'rejected input')
                    assert helper(str(helper_input)) is accepted
        raw = Path('input.egg')
        raw.write_text('(datatype E (Seed))\\n(let srcexpr (Seed))\\n(run 5)\\n(extract srcexpr)\\n')
        try:
            self.execute_egglog_file(str(raw))
            self.recursive_rewrite(raw)
        except ValueError:
            if not os.environ.get('PROTOCOL_SWALLOW_BACKEND_FAILURE'): raise
        tests = self.input_tests[:-1] if os.environ.get('PROTOCOL_MISSING_RESULT') else self.input_tests
        results = [self.get_rosette_expression_str(expr, '(Seed)', name) for name, expr in tests]
        if os.environ.get('PROTOCOL_CHANGED_SELECTED'): results.append('extra')
        Path(self.output_file_path).write_text('\\n'.join(results))
    def print_stats(self): pass
""")
    request["source_hashes"].update(
        {
            str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (checkout / "lib").rglob("*.py")
        }
    )
    generator = Path(request["generator"])
    generator.write_text(f"""#!{sys.executable}
import json, os, subprocess, sys
from pathlib import Path
assert os.environ['MISAAL_EXPORT_MODE'] == 'egglog-only-v1'
events = Path(os.environ['MISAAL_EXPORT_EVENTS'])
assert events.is_absolute() and not events.exists()
rows = []
modules = functions = children = 0
def emit(event, **fields):
    row = dict(schema='misaal-export-v1', seq=len(rows), event=event, **fields)
    if event == 'child_begin' and os.environ.get('PROTOCOL_ACTIVE_EVENT_DRIFT'): row['child_id'] += 1
    rows.append(row)
    with events.open('a') as stream: stream.write(json.dumps(row) + '\\n')
target = os.environ.get('PROTOCOL_TARGET', 'arm')
semantics, pattern, wrapper, flag, so = {{
    'arm': ('arm','ARM import arm_patterns','arm_wrappers.c.ll','arm','libARMLegalizer.so'),
    'hexagon': ('hvx','HVX import HVX_patterns','hvx_wrappers.ll','hex','libHVXLegalizer.so'),
    'x86': ('x86','x86 import x86_patterns','x86_wrappers.c.ll','x86','libx86LegalizerAllArgs.so'),
}}[target]
empty = {ARM_EMPTY_PROGRAM!r}.format(legalizer=str(Path(os.environ['LEGALIZERS_DIR']) / so),
    hydride=os.environ['HYDRIDE_DIR'], prefix=os.environ['MISAAL_CAPTURE_LLVM_PREFIX'])
empty = empty.replace('from patterns.ARM import arm_patterns', 'from patterns.' + pattern)
empty = empty.replace('parse_dict_with_bounded(arm_semantics)', 'parse_dict_with_bounded(' + semantics + '_semantics)')
empty = empty.replace('parse_dict_with_bounded(arm_swizzles)', 'parse_dict_with_bounded(' + semantics + '_swizzles)')
empty = empty.replace('arm_wrappers.c.ll', wrapper).replace('-arm-hydride-legalize', '-' + flag + '-hydride-legalize')
empty = empty.replace('run_iterations = 5', 'run_iterations = ' + os.environ.get('MISAAL_EQ_SAT_ITERS', '5'))
if 'MISAAL_DISABLE_FRONTEND_PATTERNS' not in os.environ:
    empty = empty.replace('misaal_input_patterns = []',
        'from patterns.Halide import Halide_patterns as misaal_input_patterns')
real = empty.replace('tests = []\\n', "tests = []\\ntest_0_name = 'hydride_expr_0'\\n"
    "test_0_str = 'shared input'\\ntests.append((test_0_name, test_0_str))\\n"
    "test_1_name = 'hydride_expr_1'\\ntest_1_str = 'shared input'\\ntests.append((test_1_name, test_1_str))\\n")
programs = ([empty] * int(os.environ.get('PROTOCOL_INITIAL_EMPTY', '0'))
    + [real] * int(os.environ.get('PROTOCOL_REAL_COUNT', '2'))
    + [empty] * int(os.environ.get('PROTOCOL_EMPTY_COUNT', '2')))
if os.environ.get('PROTOCOL_LATE_NONEMPTY'): programs.append(real)
def run_function(mid, program):
    global functions, children
    fid = functions; functions += 1
    emit('function_begin', module_id=mid, function_id=fid, name_hex=('func_' + str(fid)).encode().hex())
    if 'HALIDE_COMPILE_LLVM' in os.environ:
        emit('function_end', module_id=mid, function_id=fid)
        return
    script = os.environ['HYDRIDE_BENCHMARK'] + '_misaal.py'
    if os.environ.get('PROTOCOL_TEMPLATE_DRIFT'): program += "raise ValueError('unexpected source')\\n"
    Path(script).write_text(program)
    cid = children; children += 1
    emit('child_begin', module_id=mid, function_id=fid, child_id=cid, script_hex=script.encode().hex())
    outcome = subprocess.run(['python3', script], check=False)
    if outcome.returncode and not os.environ.get('PROTOCOL_IGNORE_CHILD_FAILURE'): sys.exit(outcome.returncode)
    emit('child_end', module_id=mid, function_id=fid, child_id=cid, returncode=outcome.returncode)
    emit('function_end', module_id=mid, function_id=fid)
if os.environ.get('PROTOCOL_SHARED_RUNTIME'):
    emit('module_begin', module_id=0, parent_module_id=None, name_hex=b'shared_runtime'.hex(),
        target_hex=target.encode().hex(), function_count=0, submodule_count=0)
    emit('module_end', module_id=0)
    modules = 1
    emit('export_complete', root_module_id=0, module_count=1, function_count=0, child_count=0)
for root in range(int(os.environ.get('PROTOCOL_ROOTS', '1'))):
    rid = modules; modules += 1
    emit('module_begin', module_id=rid, parent_module_id=None, name_hex=b'root'.hex(),
        target_hex=target.encode().hex(), function_count=1, submodule_count=1)
    mid = modules; modules += 1
    emit('module_begin', module_id=mid, parent_module_id=rid, name_hex=b'leaf'.hex(),
        target_hex=target.encode().hex(), function_count=len(programs)-1, submodule_count=0)
    for program in programs[:-1]: run_function(mid, program)
    emit('module_end', module_id=mid)
    run_function(rid, programs[-1])
    emit('module_end', module_id=rid)
    emit('export_complete', root_module_id=rid, module_count=modules, function_count=functions, child_count=children)
mutation = os.environ.get('PROTOCOL_LEDGER_MUTATION')
if mutation == 'missing-complete': rows.pop()
elif mutation == 'count': rows[-1]['child_count'] += 1
elif mutation == 'module-count': rows[0]['function_count'] += 1
elif mutation == 'parent': rows[1]['parent_module_id'] = None
elif mutation == 'function-id': next(row for row in rows if row['event']=='function_end')['function_id'] = 999
elif mutation == 'child-id': next(row for row in rows if row['event']=='child_end')['child_id'] = 999
elif mutation == 'nonzero-child': next(row for row in rows if row['event']=='child_end')['returncode'] = 1
elif mutation == 'sequence': rows[-1]['seq'] += 1
elif mutation == 'duplicate': rows.insert(-1, rows[-2])
elif mutation == 'target-hex': rows[0]['target_hex'] = 'ff'
elif mutation == 'unknown': rows[-1]['event'] = 'unknown'
elif mutation == 'drop-child': rows = [row for row in rows if row.get('child_id') != 0]
if mutation: events.write_text(''.join(json.dumps(row)+'\\n' for row in rows))
if os.environ.get('PROTOCOL_REMOVE_BOUNDARY'): Path('children/terminal-export.json').unlink()
if os.environ.get('PROTOCOL_CACHE_CHANGE'): next(Path('pattern-cache').glob('*.pickle')).write_text('changed')
if os.environ.get('PROTOCOL_SELECTED_CHANGE'):
    Path('children/child-0000/selected-expressions.txt').write_text('changed')
if os.environ.get('PROTOCOL_EXECUTION_CHANGE'): Path('children/child-0000/egglog-export.py').write_text('changed')
if os.environ.get('PROTOCOL_NATIVE_OUTPUT'): Path('unexpected.ll').write_text('forbidden')
if os.environ.get('PROTOCOL_PARENT_FAILURE'): sys.exit(19)
""")
    request["generator_sha256"] = hashlib.sha256(generator.read_bytes()).hexdigest()
    # LLVM binaries and selector files are deliberately absent in the request.
    for key in ("llvm_as", "llvm_as_sha256", "legalizer", "legalizer_sha256"):
        request.pop(key, None)
    source_request.write_text(json.dumps(request))
    wrapper = tmp_path / "export_adapter.py"
    wrapper.write_text(
        f"import sys\nsys.path.insert(0, {str(Path(__file__).resolve().parents[1])!r})\n"
        "from types import ModuleType\n"
        "module = ModuleType('scripts.reproduction_misaal_export')\n"
        "module.verify_export_request = lambda request: None\n"
        "module.EXPORT_SOURCE_SHA256 = {}\n"
        "sys.modules[module.__name__] = module\n"
        "from scripts import misaal_reproduction as adapter\n"
        "adapter.__file__ = __file__\nraise SystemExit(adapter.main())\n"
    )
    monkeypatch.setattr(misaal, "__file__", str(wrapper))
    return source_request


@pytest.mark.parametrize(
    "target,real,initial", [("arm", 1, 0), ("arm", 3, 1), ("hexagon", 1, 0), ("hexagon", 3, 0), ("x86", 2, 0)]
)
def test_export_closes_all_source_work_and_skips_llvm(
    export_request: Path, tmp_path: Path, target: str, real: int, initial: int
) -> None:
    request = json.loads(export_request.read_text())
    request["configuration"] = {"target": target}
    request["environment"].update(
        PROTOCOL_TARGET=target, PROTOCOL_REAL_COUNT=str(real), PROTOCOL_INITIAL_EMPTY=str(initial)
    )
    if target == "hexagon":
        request["environment"].pop("MISAAL_DISABLE_FRONTEND_PATTERNS")
        request["environment"]["MISAAL_EQ_SAT_ITERS"] = "3"
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "export-attempt"
    assert misaal.run_frontend(export_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_kind"] == misaal.EXPORT_SOURCE_KIND
    assert record["native_outputs"] == [] and record["native_codegen"] == "not_requested"
    assert record["source_capture_complete"] and record["source_completion"]["enumeration"]["modules"] == 2
    assert len(record["invocations"]) == real * 3 == len(record["workloads"])
    assert {call["caller"] for call in record["invocations"]} == {"compile_hydride", "recursive_rewrite", "swizzle"}
    assert len({call["sha256"] for call in record["invocations"]}) == 1  # Keep every repeated source call.
    assert not list(attempt.glob("**/legalize-*")) and not list(attempt.glob("*.ll"))
    assert len((attempt / "pattern-imports.txt").read_text().splitlines()) == (real + initial) * (
        2 if target == "hexagon" else 1
    )
    children = [json.loads(Path(item["path"]).read_text()) for item in record["children"]]
    for child in children[initial : initial + real]:
        completion = child["egglog_export"]["compilation"]
        assert completion["status"] == "complete" and completion["input_count"] == 2
        assert [row["name"] for row in completion["named_results"]] == ["hydride_expr_0", "hydride_expr_1"]
        assert Path(completion["selected"]["path"]).read_text() == "; hydride_expr_0\n(Seed)\n; hydride_expr_1\n(Seed)"
    assert all(child["egglog_export"]["source_exit_code"] == 0 for child in children[-2:])


@pytest.mark.parametrize(
    "mutation",
    [
        "missing-complete",
        "count",
        "module-count",
        "parent",
        "function-id",
        "child-id",
        "nonzero-child",
        "sequence",
        "duplicate",
        "target-hex",
        "unknown",
        "drop-child",
    ],
)
def test_export_rejects_incomplete_or_changed_source_ledger(
    export_request: Path, tmp_path: Path, mutation: str
) -> None:
    request = json.loads(export_request.read_text())
    request["environment"].update(PROTOCOL_LEDGER_MUTATION=mutation, PROTOCOL_EMPTY_COUNT="0", PROTOCOL_REAL_COUNT="1")
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "ledger-failure"
    assert misaal.run_frontend(export_request, attempt) == 1
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_capture_complete"] is False and record["workloads"] == []


@pytest.mark.parametrize(
    "failure",
    [
        "COMPILE_FAILURE",
        "EARLY_EXIT",
        "RECURSIVE_EXIT",
        "ACTIVE_EVENT_DRIFT",
        "TRY_LLVM",
        "MISSING_RESULT",
        "CHANGED_SELECTED",
        "LATE_NONEMPTY",
        "TEMPLATE_DRIFT",
        "REMOVE_BOUNDARY",
        "CACHE_CHANGE",
        "SELECTED_CHANGE",
        "EXECUTION_CHANGE",
        "NATIVE_OUTPUT",
        "PARENT_FAILURE",
        "SWALLOW_BACKEND_FAILURE",
    ],
)
def test_export_retains_complete_independent_calls_and_parent_failure(
    export_request: Path, tmp_path: Path, failure: str
) -> None:
    request = json.loads(export_request.read_text())
    request["environment"]["PROTOCOL_" + failure] = "1"
    if failure == "SWALLOW_BACKEND_FAILURE":
        request["environment"]["PROTOCOL_BACKEND_FAILURE"] = "1"
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "failed-export"
    retained = failure in {"RECURSIVE_EXIT", "MISSING_RESULT", "CHANGED_SELECTED", "LATE_NONEMPTY", "PARENT_FAILURE"}
    assert misaal.run_frontend(export_request, attempt) == (0 if retained else 1)
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_capture_complete"] is False
    assert bool(record["workloads"]) == retained
    if retained:
        assert record["parent_failure"]["reason"]
        assert record["source_completion"]["scope"] == "completed-independent-egglog-calls"
        assert all(call["status"] == "success" and call["output_contract"] for call in record["invocations"])
    assert not list(attempt.glob("**/legalize-*"))


def test_export_multiple_root_enumeration_and_zero_optimizer_helpers(export_request: Path, tmp_path: Path) -> None:
    request = json.loads(export_request.read_text())
    request["environment"].update(PROTOCOL_ROOTS="2", PROTOCOL_REAL_COUNT="0", PROTOCOL_EMPTY_COUNT="1")
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "helper-export"
    assert misaal.run_frontend(export_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert record["source_capture_complete"] and record["status"] == "source-helper" and record["workloads"] == []
    assert record["export_enumeration"]["roots"] == 2 and record["export_enumeration"]["children"] == 2
    assert not (attempt / "children/terminal-export.json").exists()


@pytest.mark.parametrize(
    "mutation",
    ["contract", "native-policy", "native-outputs", "request-mode", "request-events", "ambient-mode", "ambient-events"],
)
def test_export_request_rejects_ambiguous_activation(
    export_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str
) -> None:
    request = json.loads(export_request.read_text())
    if mutation == "contract":
        request["egglog_export"] = None
    elif mutation == "native-policy":
        request["terminal_empty_child"] = "arm-empty-terminal-v1"
    elif mutation == "native-outputs":
        request["expected_generator_outputs"] = ["unexpected.ll"]
    elif mutation.startswith("request-"):
        request["environment"]["MISAAL_EXPORT_" + mutation.removeprefix("request-").upper()] = "injected"
    else:
        monkeypatch.setenv("MISAAL_EXPORT_" + mutation.removeprefix("ambient-").upper(), "injected")
    export_request.write_text(json.dumps(request))
    with pytest.raises(ValueError):
        misaal.run_frontend(export_request, tmp_path / "not-started")
    assert not (tmp_path / "not-started").exists()


@pytest.mark.parametrize("halide", ["cold", "raw", "abstract"])
@pytest.mark.parametrize("hvx", ["cold", "raw", "abstract"])
def test_export_terminal_state_binds_both_independent_hvx_caches(tmp_path: Path, halide: str, hvx: str) -> None:
    cache = tmp_path / "pattern-cache"
    cache.mkdir()
    for stem, cache_state in (("halide", halide), ("hvx", hvx)):
        if cache_state != "cold":
            (cache / f"{stem}.pickle").write_text(stem + " raw")
        if cache_state == "abstract":
            (cache / f"{stem}_abstract.pickle").write_text(stem + " abstract")
    selected = tmp_path / "selected-expressions.txt"
    selected.write_text("retained original selection")
    request = {"configuration": {"target": "hexagon"}, "environment": {}}
    state = misaal.terminal_state(tmp_path, selected, request)
    assert state["cache_state"] == {"halide": halide, "hvx": hvx}
    assert set(state["cache_sha256"]) == {path.name for path in cache.iterdir()}
    assert state["selected"] == str(selected) and "feedback" not in state
    for stem in ("halide", "hvx"):
        changed = cache / f"{stem}.pickle"
        previous = changed.read_bytes() if changed.exists() else None
        changed.write_text("changed independently")
        assert misaal.terminal_state(tmp_path, selected, request) != state
        if previous is None:
            changed.unlink()
        else:
            changed.write_bytes(previous)


@pytest.mark.parametrize(
    "mutation",
    [
        None,
        "frontend",
        "patterns",
        "semantics",
        "swizzles",
        "flags",
        "wrapper",
        "iterations",
        "dynamic-input",
        "extra-statement",
        "legalizer-call",
    ],
)
def test_export_exact_child_edit_preserves_original_graph_text(
    export_request: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutation: str | None
) -> None:
    request = json.loads(export_request.read_text())
    attempt = tmp_path / "recognition"
    directory = attempt / "children/child-0000"
    directory.mkdir(parents=True)
    prefix = str(attempt / "unused-feedback")
    monkeypatch.setenv("MISAAL_CAPTURE_LLVM_PREFIX", prefix)
    source = ARM_EMPTY_PROGRAM.format(
        legalizer=str(Path(request["environment"]["LEGALIZERS_DIR"]) / "libARMLegalizer.so"),
        hydride=request["environment"]["HYDRIDE_DIR"],
        prefix=prefix,
    )
    source = source.replace(
        "tests = []\n",
        "tests = []\ntest_0_name = 'original'\ntest_0_str = 'unchanged graph'\n"
        "tests.append((test_0_name, test_0_str))\n",
    )
    replacements = {
        "frontend": ("misaal_input_patterns = []", "misaal_input_patterns = list()"),
        "patterns": ("patterns.ARM", "patterns.HVX"),
        "semantics": ("parse_dict_with_bounded(arm_semantics)", "parse_dict_with_bounded(hvx_semantics)"),
        "swizzles": ("parse_dict_with_bounded(arm_swizzles)", "parse_dict_with_bounded(hvx_swizzles)"),
        "flags": ("-arm-hydride-legalize", "-hex-hydride-legalize"),
        "wrapper": ("arm_wrappers.c.ll", "hvx_wrappers.ll"),
        "iterations": ("run_iterations = 5", "run_iterations = 6"),
        "dynamic-input": ("test_0_str = 'unchanged graph'", "test_0_str = str('unchanged graph')"),
        "extra-statement": ("tests = []", "tests = []\nprint('unexpected')"),
        "legalizer-call": ("misaal_compiler.run_llvm_legalizer()", "misaal_compiler.run_llvm_legalizer(1)"),
    }
    if mutation:
        before, after = replacements[mutation]
        source = source.replace(before, after)
    program = attempt / "source_misaal.py"
    program.write_text(source)
    record: dict[str, Any] = {}
    if mutation:
        with pytest.raises(ValueError):
            misaal.source_child_program(request, program, directory, record)
    else:
        execution = misaal.source_child_program(request, program, directory, record)
        assert execution.read_text() == source.replace("misaal_compiler.run_llvm_legalizer()\n", "")
        assert program.read_text() == source
        assert record["egglog_export"]["inputs"][0]["expression"] == "unchanged graph"


def test_export_failed_empty_still_blocks_later_real_child(export_request: Path, tmp_path: Path) -> None:
    request = json.loads(export_request.read_text())
    module = Path(request["checkout"]) / "lib/utils/egg_config.py"
    module.write_text(
        module.read_text() + "from pathlib import Path\nif Path('pattern-imports.txt').exists(): raise SystemExit(0)\n"
    )
    request["source_hashes"]["lib/utils/egg_config.py"] = hashlib.sha256(module.read_bytes()).hexdigest()
    request["environment"].update(
        PROTOCOL_REAL_COUNT="1", PROTOCOL_EMPTY_COUNT="1", PROTOCOL_IGNORE_CHILD_FAILURE="1", PROTOCOL_LATE_NONEMPTY="1"
    )
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "ignored-empty-failure"
    assert misaal.run_frontend(export_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert len(record["workloads"]) == 3  # all completed calls belong to the first child
    assert record["parent_failure"]["reason"]
    assert all("child-0000" in call["child"] for call in record["invocations"])
    empty = json.loads((attempt / "children/child-0001/capture.json").read_text())
    real = json.loads((attempt / "children/child-0002/capture.json").read_text())
    assert "SystemExit: 0" in empty["error"]
    assert "Nonempty export child follows" in real["error"]
    assert empty["status"] == real["status"] == "failure"
    assert real["invocations"] == []
    assert (attempt / "children/terminal-export.json").is_file()


@pytest.mark.parametrize("value", ["0", "1"])
def test_export_no_synthesis_flag_and_zero_function_runtime_are_helpers(
    export_request: Path, tmp_path: Path, value: str
) -> None:
    request = json.loads(export_request.read_text())
    request["environment"].update(HALIDE_COMPILE_LLVM=value, PROTOCOL_SHARED_RUNTIME="1")
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "no-synthesis"
    assert misaal.run_frontend(export_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert record["status"] == "source-helper" and record["source_capture_complete"]
    assert record["children"] == record["invocations"] == record["workloads"] == record["native_outputs"] == []
    assert record["export_enumeration"]["roots"] == 2 and record["export_enumeration"]["modules"] == 3


def test_materialized_calls_keep_original_order_after_failed_call(tmp_path: Path) -> None:
    raw = tmp_path / "source.egg"
    raw.write_text("(datatype E (A))\n(let root (A))\n(run 1)\n(extract root)\n")
    stdout = raw.with_suffix(".stdout.log")
    stdout.write_text("(A)\n")
    child = tmp_path / "capture.json"
    child.write_text(
        json.dumps(
            {
                "invocations": [
                    {"status": "failure", "index": 0, "error": "original backend failure"},
                    {
                        "status": "success",
                        "index": 1,
                        "raw": str(raw),
                        "sha256": hashlib.sha256(raw.read_bytes()).hexdigest(),
                        "stdout_sha256": hashlib.sha256(stdout.read_bytes()).hexdigest(),
                    },
                ]
            }
        )
    )
    record: dict[str, Any] = {"invocations": [], "source_kind": misaal.EXPORT_SOURCE_KIND}
    misaal.materialize_invocations([child], tmp_path / "replays", record)
    assert len(record["invocations"]) == 1 and record["invocations"][0]["source_order"] == 1
    assert record["failed_invocations"][0]["index"] == 0
    assert record["materialization"] == {"expected_sessions": 1, "materialized_sessions": 1, "complete": True}


def test_child_entrypoint_resolves_repository_modules_outside_checkout(tmp_path: Path) -> None:
    result = subprocess.run(
        [
            sys.executable,
            str(Path(misaal.__file__).resolve()),
            "child",
            "--request",
            str(tmp_path / "missing.json"),
            "--output",
            str(tmp_path / "output"),
            "--",
            str(tmp_path / "generated_misaal.py"),
        ],
        cwd=tmp_path,
        env={key: value for key, value in os.environ.items() if key != "PYTHONPATH"},
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode != 0
    assert "FileNotFoundError" in result.stderr
    assert "ModuleNotFoundError" not in result.stderr


def test_explicit_helpers_execute_and_keep_boolean_rejections_and_deleted_inputs(
    export_request: Path, tmp_path: Path
) -> None:
    request = json.loads(export_request.read_text())
    request["environment"].update(PROTOCOL_HELPERS="1", PROTOCOL_REAL_COUNT="1")
    export_request.write_text(json.dumps(request))
    attempt = tmp_path / "actual-helpers"
    assert misaal.run_frontend(export_request, attempt) == 0
    record = json.loads((attempt / "capture.json").read_text())
    assert record["helper_accounting"] == {
        "status": "success",
        "calls": 4,
        "accepted": 2,
        "rejected": 2,
        "admitted_workloads": 0,
    }
    assert len(record["invocations"]) == len(record["workloads"]) == 3
    child = json.loads((attempt / "children/child-0000/capture.json").read_text())
    for helper, accepted in zip(child["helper_invocations"], (True, False, True, False), strict=True):
        assert helper["accepted"] is accepted and helper["returncode"] == (0 if accepted else 9)
        assert helper["status"] == "success" and helper["admitted_as_workload"] is False
        raw = Path(helper["raw"])
        assert raw.read_text() == ("accepted input" if accepted else "rejected input")
        assert helper["sha256"] == hashlib.sha256(raw.read_bytes()).hexdigest()
        assert helper["stdout_sha256"] == hashlib.sha256(raw.with_suffix(".stdout.log").read_bytes()).hexdigest()
    assert not list(attempt.glob("helper-input-1-*.egg"))
