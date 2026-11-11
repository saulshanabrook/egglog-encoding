"""Enforce module ownership, dependency direction, and an acyclic package."""

from __future__ import annotations

import ast
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


def python_modules() -> tuple[Path, ...]:
    """Return every repo-owned Python module checked by the tooling."""

    return (
        ROOT / "bench.py",
        *sorted((ROOT / "benchmarking").rglob("*.py")),
        *sorted((ROOT / "tests").rglob("*.py")),
    )


def module_name(path: Path) -> str:
    parts = list(path.relative_to(ROOT).with_suffix("").parts)
    if parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def imported_module_names(path: Path) -> set[str]:
    """Resolve static absolute and relative imports to dotted module names."""

    current = module_name(path)
    package = current if path.name == "__init__.py" else current.rpartition(".")[0]
    imported: set[str] = set()
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            base_parts = package.split(".") if package else []
            if node.level > 1:
                base_parts = base_parts[: -(node.level - 1)]
            if node.module is not None:
                base_parts.extend(node.module.split("."))
            base = ".".join(base_parts) if node.level else node.module or ""
            if base:
                imported.add(base)
            imported.update(f"{base}.{alias.name}" if base else alias.name for alias in node.names)
    return imported


def forbidden_imports(imports: set[str], forbidden: frozenset[str]) -> set[str]:
    return {
        imported for imported in imports for root in forbidden if imported == root or imported.startswith(root + ".")
    }


def test_every_python_module_has_an_ownership_docstring() -> None:
    missing = [
        str(path.relative_to(ROOT))
        for path in python_modules()
        if ast.get_docstring(ast.parse(path.read_text(encoding="utf-8"))) is None
    ]
    assert not missing, f"Python modules without ownership docstrings: {', '.join(missing)}"


def test_package_initializers_are_docstring_only() -> None:
    initializers = (
        *sorted((ROOT / "benchmarking").rglob("__init__.py")),
        *sorted((ROOT / "tests").rglob("__init__.py")),
    )
    for path in initializers:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        assert len(tree.body) == 1
        assert ast.get_docstring(tree) is not None


RUNNER_LAYERS = frozenset(
    {
        "benchmarking.benchmark",
        "benchmarking.collection",
        "benchmarking.processes",
        "benchmarking.profile",
        "benchmarking.targets",
    }
)

DEPENDENCY_RULES = (
    (
        "benchmarking/reports/store.py",
        RUNNER_LAYERS
        | frozenset(
            {
                "benchmarking.reports.analysis",
                "benchmarking.reports.catalog",
                "benchmarking.reports.interactive",
                "benchmarking.reports.interactive_runtime",
                "benchmarking.reports.presentation",
                "benchmarking.reports.render",
                "rich",
                "scipy",
            }
        ),
    ),
    (
        "benchmarking/reports/analysis.py",
        RUNNER_LAYERS
        | frozenset(
            {
                "benchmarking.reports.catalog",
                "benchmarking.reports.interactive",
                "benchmarking.reports.presentation",
                "benchmarking.reports.render",
                "rich",
            }
        ),
    ),
    (
        "benchmarking/reports/catalog.py",
        RUNNER_LAYERS
        | frozenset(
            {
                "benchmarking.reports.analysis",
                "benchmarking.reports.presentation",
                "benchmarking.reports.render",
                "benchmarking.reports.store",
                "rich",
                "scipy",
            }
        ),
    ),
    (
        "benchmarking/reports/render.py",
        frozenset(
            {
                "benchmarking.models",
                "benchmarking.reports.analysis",
                "benchmarking.reports.presentation",
                "benchmarking.reports.store",
            }
        ),
    ),
    (
        "benchmarking/reports/interactive_runtime.py",
        frozenset({"benchmarking.reports.interactive", "http.server", "importlib", "webbrowser"}),
    ),
)


@pytest.mark.parametrize(("relative_path", "forbidden"), DEPENDENCY_RULES)
def test_dependency_boundaries(relative_path: str, forbidden: frozenset[str]) -> None:
    imports = imported_module_names(ROOT / relative_path)
    assert not forbidden_imports(imports, forbidden)


def test_report_package_does_not_import_runner_layers() -> None:
    violations = {
        str(path.relative_to(ROOT)): forbidden_imports(imported_module_names(path), RUNNER_LAYERS)
        for path in sorted((ROOT / "benchmarking/reports").rglob("*.py"))
    }
    assert not {path: imports for path, imports in violations.items() if imports}


def test_benchmarking_import_graph_is_acyclic() -> None:
    modules = {module_name(path): path for path in sorted((ROOT / "benchmarking").rglob("*.py"))}
    graph = {
        name: {dependency for dependency in imported_module_names(path) if dependency in modules}
        for name, path in modules.items()
    }
    active: list[str] = []
    complete: set[str] = set()

    def visit(name: str) -> None:
        if name in active:
            cycle = [*active[active.index(name) :], name]
            pytest.fail("Static import cycle: " + " -> ".join(cycle))
        if name in complete:
            return
        active.append(name)
        for dependency in sorted(graph[name]):
            visit(dependency)
        active.pop()
        complete.add(name)

    for name in sorted(modules):
        visit(name)
