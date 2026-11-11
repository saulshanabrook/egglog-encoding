"""Opt-in, source-pinned MISAAL pattern preparation adaptations."""

from __future__ import annotations

import ast
import hashlib
import inspect
import marshal
import time
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from pathlib import Path
from types import CodeType, FunctionType, ModuleType
from typing import Any

CONTRACT = "exact-render-last-v1"
SOURCE_SHA256 = {
    "patterns.PatternUtils": (
        "lib/patterns/PatternUtils.py",
        "e89b1a4c9dda901f2416100dbc6b5e47554264e00eb755c52c669f48b54eb8d5",
    ),
    "compiler.Pattern": (
        "lib/compiler/Pattern.py",
        "aa82c2f0378242316e6ed1dffebf0add9419d27ba65039185df8fd315e3ba826",
    ),
    "common.Instructions": (
        "Hydride/code-synthesizer/dsl-ir/common/Instructions.py",
        "a6d267428a19017dcec7e6b4931e20256d16dde38f0fd4679b31fe2cadd34a26",
    ),
    "common.Types": (
        "Hydride/code-synthesizer/dsl-ir/common/Types.py",
        "aa2056271dcb75e5c9c8c1aaab0d026c2e005e748414a38ab1441bc4d0633d01",
    ),
}

PARAMETER_ABI_CONTRACT = "c098-four-argument-v1"
PARAMETER_ABI_SOURCE_SHA256 = {
    "lib/patterns/PatternUtils.py": "e89b1a4c9dda901f2416100dbc6b5e47554264e00eb755c52c669f48b54eb8d5",
    "misaal/synthesis/param_abstract.rkt": "762f379a373b30c965d8bb3760b2908515f52945e58a76c820c11da2fa6c2b47",
}
# Exact c098 ABI boundaries; all other 44ff source bytes remain in this virtual
# module. In particular, depth 1 still allows arithmetic in the paper grammar.
_PARAMETER_ABI_REPLACEMENTS = (
    (
        """    def emit_synthesize_query(self, test_cases, depth = 2, num_src_regs = 2, exclude_regs = [], reg_only = False):
        reg_only_str = "#t" if reg_only else "#f"
        return "(synthesize-param-expression {} {} {} (list {}) {})".format(test_cases, depth, num_src_regs - 1, " ".join([str(reg) for reg in exclude_regs]), reg_only_str)""",  # noqa: E501
        """    def emit_synthesize_query(self, test_cases, depth = 2, num_src_regs = 2, exclude_regs = []):
        return "(synthesize-param-expression {} {} {} (list {}))".format(test_cases, depth, num_src_regs - 1, " ".join([str(reg) for reg in exclude_regs]))""",  # noqa: E501
    ),
    (
        '        synthesis_query = self.emit_synthesize_query("param-test-cases", depth = depth, exclude_regs = exclude_regs, reg_only = True)',  # noqa: E501
        '        synthesis_query = self.emit_synthesize_query("param-test-cases", depth = depth, exclude_regs = exclude_regs)',  # noqa: E501
    ),
)


@contextmanager
def restore_parameter_abi(
    module: ModuleType,
    request: dict[str, Any],
    record: dict[str, Any],
    persist: Callable[[], None],
) -> Iterator[None]:
    """Restore the executable paper ABI, without asserting register-only intent.

    The unchanged Racket callee has four parameters. Restore only the original
    Python emitter and its general call, keeping newer validation/simplification.
    Compile the full source so loaded-code checks retain CPython's exact module
    compilation semantics. Never execute that module or write checkout files.
    """
    requested = request.get("parameter_abi")
    if requested is None:
        yield
        return
    if requested != PARAMETER_ABI_CONTRACT or request.get("revision") != "44ff893445d664cd87f52b08a138260ed2015ba8":
        raise ValueError("Unsupported MISAAL parameter ABI contract")
    observation: dict[str, Any] = {
        "contract": PARAMETER_ABI_CONTRACT,
        "status": "verifying",
        "semantics": "mixed-revision restoration of executable c098 paper ABI; register-only intent unvalidated",
        "paper_revision": "c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4",
        "implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "sources": {},
        "original_methods": {},
        "adapted_methods": {},
    }
    record["parameter_abi"] = observation
    originals: dict[str, FunctionType] = {}
    abstractor: Any = None
    persist()
    try:
        checkout = Path(request["checkout"]).resolve()
        sources = {}
        for relative, expected in PARAMETER_ABI_SOURCE_SHA256.items():
            path = checkout / relative
            contents = path.read_bytes()
            if (
                request.get("source_hashes", {}).get(relative) != expected
                or hashlib.sha256(contents).hexdigest() != expected
            ):
                raise ValueError(f"Parameter ABI source identity changed: {relative}")
            sources[relative] = contents
            observation["sources"][relative] = expected
        source_path = checkout / "lib/patterns/PatternUtils.py"
        if module.__name__ != "patterns.PatternUtils" or Path(module.__file__ or "").resolve() != source_path.resolve():
            raise ValueError("Parameter ABI imported an unexpected module")
        source = sources["lib/patterns/PatternUtils.py"].decode()
        syntax = ast.parse(source)
        class_syntax = next(
            item for item in syntax.body if isinstance(item, ast.ClassDef) and item.name == "PatternAbstractor"
        )
        code = compile(source, str(source_path), "exec", dont_inherit=True)
        class_code = next(
            item for item in code.co_consts if isinstance(item, CodeType) and item.co_name == "PatternAbstractor"
        )
        methods = {item.co_name: item for item in class_code.co_consts if isinstance(item, CodeType)}
        abstractor = module.PatternAbstractor
        if (
            type(abstractor) is not type
            or abstractor.__module__ != module.__name__
            or abstractor.__qualname__ != "PatternAbstractor"
            or {name for name, value in vars(abstractor).items() if isinstance(value, FunctionType)} != set(methods)
        ):
            raise ValueError("Parameter ABI class was already replaced")
        for definition in class_syntax.body:
            if not isinstance(definition, ast.FunctionDef):
                continue
            function = vars(abstractor)[definition.name]
            defaults = tuple(ast.literal_eval(value) for value in definition.args.defaults) or None
            if (
                not isinstance(function, FunctionType)
                or function.__module__ != module.__name__
                or function.__globals__ is not vars(module)
                or function.__qualname__ != f"PatternAbstractor.{definition.name}"
                or function.__code__ != methods[definition.name]
                or function.__defaults__ != defaults
                or type(function.__defaults__) is not type(defaults)
                or (
                    defaults is not None
                    and [type(value) for value in function.__defaults__ or ()] != [type(value) for value in defaults]
                )
                or function.__kwdefaults__ is not None
                or function.__closure__ is not None
            ):
                raise ValueError(f"Parameter ABI loaded method differs from pinned source: {definition.name}")
            observation["original_methods"][definition.name] = hashlib.sha256(
                marshal.dumps(function.__code__)
            ).hexdigest()
        adapted = source
        for before, after in _PARAMETER_ABI_REPLACEMENTS:
            if adapted.count(before) != 1:
                raise ValueError("Parameter ABI source boundary changed")
            adapted = adapted.replace(before, after, 1)
        observation["adapted_source_sha256"] = hashlib.sha256(adapted.encode()).hexdigest()
        adapted_code = compile(adapted, str(source_path), "exec", dont_inherit=True)
        adapted_class = next(
            item
            for item in adapted_code.co_consts
            if isinstance(item, CodeType) and item.co_name == "PatternAbstractor"
        )
        replacements = {item.co_name: item for item in adapted_class.co_consts if isinstance(item, CodeType)}
        for name in ("emit_synthesize_query", "generate_param_expr_general"):
            original = vars(abstractor)[name]
            originals[name] = original
            defaults = original.__defaults__
            if name == "emit_synthesize_query":
                assert defaults is not None
                defaults = defaults[:-1]
            replacement = FunctionType(replacements[name], vars(module), name, defaults)
            setattr(abstractor, name, replacement)
            observation["adapted_methods"][name] = hashlib.sha256(marshal.dumps(replacement.__code__)).hexdigest()
        observation["status"] = "active"
        persist()
        yield
        observation["status"] = "complete"
    except BaseException as error:
        observation.update(status="failure", error=f"{type(error).__name__}: {error}")
        raise
    finally:
        for name, original in originals.items():
            setattr(abstractor, name, original)
        persist()


def deduplicate_patterns(patterns: list[Any], context: type[Any]) -> list[Any]:
    """Keep the last original object for each exact, unoriented rendered pair.

    The pinned equality deliberately renders every non-Context endpoint as
    "Reg" and ignores pattern metadata. Preserve both quirks. These keys are
    local because the original abstractor can subsequently mutate expressions.
    """
    if len(patterns) < 2:
        return list(patterns)
    seen: set[tuple[str, str]] = set()
    survivors = []
    for pattern in reversed(patterns):
        left = pattern.src_expr.emit_context_expr_string() if isinstance(pattern.src_expr, context) else "Reg"
        right = pattern.target_expr.emit_context_expr_string() if isinstance(pattern.target_expr, context) else "Reg"
        key = (left, right) if left <= right else (right, left)
        if key not in seen:
            seen.add(key)
            survivors.append(pattern)
    survivors.reverse()
    return survivors


@contextmanager
def accelerate_pattern_preparation(
    module: ModuleType,
    request: dict[str, Any],
    record: dict[str, Any],
    persist: Callable[[], None],
    lock: Any,
) -> Iterator[None]:
    """Install only the reviewed repair; retain incomplete phases on interruption.

    Source verification includes the actual loaded classes, not only files in a
    checkout that Python may have bypassed. Cache branches and helper validators
    are unchanged. With no request flag this context has no effects.
    """
    requested = request.get("pattern_deduplication")
    if requested is None:
        yield
        return
    if requested != CONTRACT or request.get("revision") != "44ff893445d664cd87f52b08a138260ed2015ba8":
        raise ValueError("Unsupported MISAAL pattern-deduplication contract")
    observation: dict[str, Any] = {
        "contract": CONTRACT,
        "status": "verifying",
        "implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "sources": {},
        "phases": [],
        "cache_behavior": "unchanged cold/raw/abstract transitions",
    }
    record["pattern_preparation"] = observation
    originals: dict[str, Any] = {}
    persist()
    try:
        compiled_sources = {}
        loaded = [
            module,
            inspect.getmodule(module.Pattern),
            inspect.getmodule(module.Context),
            inspect.getmodule(module.Reg),
        ]
        if {item.__name__ for item in loaded if item is not None} != set(SOURCE_SHA256):
            raise ValueError("Pattern preparation imported unexpected implementation modules")
        for item in loaded:
            assert item is not None
            relative, expected = SOURCE_SHA256[item.__name__]
            path = (Path(request["checkout"]) / relative).resolve()
            if Path(item.__file__ or "").resolve() != path or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                raise ValueError(f"Pattern preparation source identity changed: {relative}")
            observation["sources"][relative] = expected
            compiled_sources[item.__name__] = compile(path.read_text(), str(path), "exec", dont_inherit=True)
        for function in (
            module.create_patterns,
            module.prune_redundant_patterns,
            module.deduplicate_patterns,
            module.Pattern.equal_to,
            module.Context.emit_context_expr_string,
        ):
            if function.__module__ not in SOURCE_SHA256:
                raise ValueError("Pattern preparation function was already replaced")
            relative, _ = SOURCE_SHA256[function.__module__]
            if Path(function.__code__.co_filename).resolve() != (Path(request["checkout"]) / relative).resolve():
                raise ValueError("Pattern preparation function was already replaced")
            expected_code = compiled_sources[function.__module__]
            for name in function.__qualname__.split("."):
                candidates = [
                    code for code in expected_code.co_consts if isinstance(code, CodeType) and code.co_name == name
                ]
                if len(candidates) != 1:
                    raise ValueError("Pattern preparation function was already replaced")
                expected_code = candidates[0]
            if function.__code__ != expected_code:
                raise ValueError("Pattern preparation loaded code differs from its pinned source")

        def timed(name: str, operation: Callable[..., Any]) -> Callable[..., Any]:
            def run(*args: Any, **kwargs: Any) -> Any:
                values = args[0] if args else kwargs["props" if name == "create_patterns" else "patterns"]
                frame = inspect.currentframe()
                caller = frame.f_back.f_code.co_filename if frame is not None and frame.f_back is not None else None
                del frame
                entry: dict[str, Any] = {
                    "phase": name,
                    "caller": caller,
                    "status": "running",
                    "started_monotonic_sec": time.monotonic(),
                    "input_count": sum(len(value) for value in values) if name == "create_patterns" else len(values),
                }
                with lock:
                    observation["phases"].append(entry)
                    persist()
                try:
                    result = operation(*args, **kwargs)
                    entry.update(status="success", output_count=len(result))
                    return result
                except BaseException as error:
                    entry.update(status="failure", error=f"{type(error).__name__}: {error}")
                    raise
                finally:
                    entry["finished_monotonic_sec"] = time.monotonic()
                    entry["wall_sec"] = entry["finished_monotonic_sec"] - entry["started_monotonic_sec"]
                    with lock:
                        persist()

            return run

        for name in ("create_patterns", "prune_redundant_patterns", "deduplicate_patterns"):
            originals[name] = getattr(module, name)
            operation = (
                originals[name]
                if name != "deduplicate_patterns"
                else lambda patterns: deduplicate_patterns(patterns, module.Context)
            )
            setattr(module, name, timed(name, operation))
        observation["status"] = "observing"
        persist()
        yield
        observation["status"] = "complete"
    except BaseException as error:
        observation.update(status="failure", error=f"{type(error).__name__}: {error}")
        raise
    finally:
        for name, original in originals.items():
            setattr(module, name, original)
        persist()
