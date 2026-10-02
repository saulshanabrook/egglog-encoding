"""A prepared runtime stays bound to its actual source, tools, and isolation."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_misaal_runtime as runtime


@pytest.fixture
def runtime_request(tmp_path: Path) -> dict[str, Any]:
    checkout = tmp_path / "source"
    checkout.mkdir()
    source = checkout / "parameter.rkt"
    source.write_text("source API tested by preparation")
    executables = {}
    for name in ("racket", "raco", "z3"):
        path = tmp_path / name
        path.write_text(name)
        executables[name] = {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    environment = {"PLTADDONDIR": str(tmp_path / "addon"), "PATH": str(tmp_path / "bin") + ":"}
    seal = {
        "schema": runtime.CONTRACT,
        "status": "source-api-compatible",
        "checkout": str(checkout),
        "files": {str(source): hashlib.sha256(source.read_bytes()).hexdigest()},
        "executables": executables,
        "environment": environment,
    }
    path = tmp_path / "runtime.json"
    path.write_text(json.dumps(seal))
    return {
        "racket_runtime": {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()},
        "racket": executables["racket"]["path"],
        "checkout": str(checkout),
        "parameter_abi": runtime.PARAMETER_ABI_CONTRACT,
        "racket_group_containment": runtime.GROUP_CONTRACT,
        "environment": environment.copy(),
    }


def test_runtime_allows_only_pinned_environment_with_appended_search_path(runtime_request: dict[str, Any]) -> None:
    runtime_request["environment"]["PATH"] += "/usr/bin"
    assert runtime.verify_runtime(runtime_request)["status"] == "source-api-compatible"


@pytest.mark.parametrize(
    "changed", ["manifest", "source", "racket", "raco", "z3", "checkout", "abi", "group", "environment", "path"]
)
def test_runtime_drift_is_rejected(runtime_request: dict[str, Any], changed: str) -> None:
    if changed == "manifest":
        Path(runtime_request["racket_runtime"]["path"]).write_text("changed manifest")
    elif changed == "source":
        (Path(runtime_request["checkout"]) / "parameter.rkt").write_text("changed source")
    elif changed in {"racket", "raco", "z3"}:
        Path(runtime_request["racket"]).with_name(changed).write_text("changed executable")
    elif changed == "checkout":
        runtime_request["checkout"] += "-other"
    elif changed == "abi":
        runtime_request["parameter_abi"] = "unknown"
    elif changed == "group":
        runtime_request["racket_group_containment"] = "uncontained"
    elif changed == "environment":
        runtime_request["environment"]["PLTADDONDIR"] = "/outside"
    else:
        runtime_request["environment"]["PATH"] = "/outside:" + runtime_request["environment"]["PATH"]
    with pytest.raises(ValueError):
        runtime.verify_runtime(runtime_request)
