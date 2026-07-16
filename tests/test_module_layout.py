"""Enforce documented Python ownership and one-way package dependencies."""

from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def python_modules() -> tuple[Path, ...]:
    """Return every repo-owned Python module checked by the tooling."""

    return (
        ROOT / "bench.py",
        *sorted((ROOT / "benchmarking").rglob("*.py")),
        *sorted((ROOT / "tests").rglob("*.py")),
    )


def module_name(path: Path) -> str:
    """Return the importable dotted name for one repo-owned module."""

    parts = list(path.relative_to(ROOT).with_suffix("").parts)
    if parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def imported_module_names(path: Path) -> set[str]:
    """Resolve absolute and relative imports to dotted module names."""

    current = module_name(path)
    package = current if path.name == "__init__.py" else current.rpartition(".")[0]
    imported: set[str] = set()
    tree = ast.parse(path.read_text(encoding="utf-8"))
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        if node.level:
            package_parts = package.split(".") if package else []
            parent_count = node.level - 1
            base_parts = package_parts[: len(package_parts) - parent_count] if parent_count else package_parts
            if node.module is not None:
                base_parts.extend(node.module.split("."))
            base = ".".join(base_parts)
        else:
            base = node.module or ""
        if base:
            imported.add(base)
        if node.module is None:
            imported.update(f"{base}.{alias.name}" if base else alias.name for alias in node.names)
    return imported


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
        assert isinstance(tree.body[0], ast.Expr)
        assert isinstance(tree.body[0].value, ast.Constant)
        assert isinstance(tree.body[0].value.value, str)


def test_data_boundary_does_not_import_runner_or_presentation_dependencies() -> None:
    forbidden = {
        "argparse",
        "benchmarking.benchmark",
        "benchmarking.collection",
        "benchmarking.output",
        "benchmarking.processes",
        "benchmarking.profile",
        "benchmarking.targets",
        "pandas",
        "pandera",
        "rich",
    }
    data_modules = (
        ROOT / "benchmarking/reports/records.py",
        ROOT / "benchmarking/reports/database.py",
        ROOT / "benchmarking/reports/results.py",
    )
    violations: list[str] = []
    for path in data_modules:
        for name in imported_module_names(path):
            if any(name == item or name.startswith(item + ".") for item in forbidden):
                violations.append(f"{path.relative_to(ROOT)} imports {name}")

    assert not violations, "; ".join(violations)


def test_report_package_does_not_import_runner_layers() -> None:
    """Keep report analysis and presentation independent of CLI orchestration."""

    forbidden = {
        "benchmarking.benchmark",
        "benchmarking.benchmark_config",
        "benchmarking.collection",
        "benchmarking.output",
        "benchmarking.processes",
        "benchmarking.profile",
        "benchmarking.targets",
    }
    violations: list[str] = []
    for path in sorted((ROOT / "benchmarking/reports").rglob("*.py")):
        for name in imported_module_names(path):
            if any(name == item or name.startswith(item + ".") for item in forbidden):
                violations.append(f"{path.relative_to(ROOT)} imports {name}")

    assert not violations, "; ".join(violations)


def test_benchmarking_import_graph_is_acyclic() -> None:
    """Keep module ownership enforceable by rejecting static import cycles."""

    modules = {module_name(path): path for path in sorted((ROOT / "benchmarking").rglob("*.py"))}
    graph = {
        name: {dependency for dependency in imported_module_names(path) if dependency in modules}
        for name, path in modules.items()
    }
    state: dict[str, int] = {}
    stack: list[str] = []
    cycle: list[str] | None = None

    def visit(name: str) -> None:
        nonlocal cycle
        state[name] = 1
        stack.append(name)
        for dependency in sorted(graph[name]):
            if cycle is not None:
                return
            if state.get(dependency, 0) == 0:
                visit(dependency)
            elif state[dependency] == 1:
                cycle = [*stack[stack.index(dependency) :], dependency]
                return
        stack.pop()
        state[name] = 2

    for name in sorted(modules):
        if state.get(name, 0) == 0:
            visit(name)
        if cycle is not None:
            break

    assert cycle is None, "Static import cycle: " + " -> ".join(cycle or ())
