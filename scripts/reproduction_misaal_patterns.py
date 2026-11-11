"""Opt-in, source-pinned acceleration of MISAAL's exact pattern deduplication."""

from __future__ import annotations

import hashlib
import inspect
import time
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from pathlib import Path
from types import CodeType, ModuleType
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
