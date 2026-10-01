"""Run and classify complete native captures at explicit family boundaries."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
STOP_STATUSES = {"resource-stopped", "memory-limit", "timed-out", "cancelled", "interrupted"}


def misaal_request(case: dict[str, Any], settings: dict[str, Any], root: Path = ROOT) -> dict[str, Any]:
    """Verify the selected request and its referenced files before cache lookup."""
    from scripts.misaal_reproduction import EGGLOG_EXPORT, verified_request

    path = root / settings["paths"]["requests"] / f"{case['id']}.json"
    if (
        settings.get("egglog_export") != EGGLOG_EXPORT
        or json.loads(path.read_text()).get("egglog_export") != EGGLOG_EXPORT
    ):
        raise ValueError("MISAAL native lowering is disabled; prepare the Egglog export requests first")
    request = verified_request(root / settings["paths"]["requests"] / f"{case['id']}.json")
    if (
        request["case_id"] != case["id"]
        or request.get("source") != case["source"]
        or request.get("configuration") != case["configuration"]
    ):
        raise ValueError("MISAAL request case, source, or configuration differs from the inventory")
    source = Path(request["checkout"]) / case["source"]
    if source.is_dir():
        source = source / "src" / f"{source.name}_generator.cpp"
    relative = str(source.relative_to(request["checkout"]))
    if relative not in request["source_hashes"]:
        raise ValueError("MISAAL request must pin the selected source generator")
    return request


def capture_case(case: dict[str, Any], settings: dict[str, Any], output: Path) -> dict[str, Any]:
    """Delegate in-process so each adapter owns its monitored native process group."""
    family = case["family"]
    if case.get("input_kind") is not None:
        from scripts.reproduction_published import capture_published

        return capture_published(case, settings, output)
    paths = {key: (ROOT / value).absolute() for key, value in settings["paths"].items() if value is not None}
    timeout = float(settings.get("timeout_sec", 300))
    if family in ("dialegg", "speq"):
        from scripts.dialegg_speq_complete import complete_capture

        args = argparse.Namespace(
            **{"speq_rev_plugin": None, **paths},
            family=family,
            case=[case["id"]],
            output=output,
            timeout_sec=timeout,
            speq_frontend_flag=settings.get("frontend_flags", []),
            speq_phi_polarity_repair=settings.get("phi_polarity_repair", False),
            speq_c99_frontend_repair=settings.get("c99_frontend_repair"),
        )
        code = complete_capture(args)
        manifest = json.loads((output / "manifest.json").read_text())
        capture = manifest["families"][family]
        row = capture["cases"].get(case["id"], {"status": "pending", "reason": "stopped before this case"})
        if code == 2:
            stop = capture["operational_stop"]
            row = {**row, "status": stop["status"], "reason": stop.get("message") or row.get("reason")}
        return dict(row)
    if family in ("eggcc", "churchroad"):
        from scripts.suite_capture_eggcc_churchroad import capture_complete

        source_case = {**case, "native_options": case["configuration"].get("native_options", [])}
        if (
            family == "churchroad"
            and case["id"].startswith("churchroad-later-")
            and case.get("repository") == "https://github.com/gussmith23/churchroad-evaluation"
        ):
            if "source_root" not in paths:
                return {"status": "pending", "reason": "later Churchroad evaluation source_root is not configured"}
            source_case.update(
                source=str(paths["source_root"] / case["source"]),
                revision=settings["revision"],
                top_module_name=case["configuration"]["top_module_name"],
                architecture=case["configuration"]["architecture"],
            )
        records = capture_complete(
            family,
            [source_case],
            output,
            paths["checkout"],
            paths["binary"],
            paths["egglog"],
            timeout_sec=timeout,
            validate_ordinary=False,
        )
        return dict(records[0])
    if family == "misaal":
        from scripts.misaal_reproduction import capture_misaal

        request = paths["requests"] / f"{case['id']}.json"
        if not request.is_file():
            return {"status": "pending", "reason": f"complete native request not prepared: {request}"}
        misaal_request(case, settings)
        return dict(capture_misaal(request, output))
    if family == "hardboiled":
        from scripts.suite_capture_hardboiled_misaal import capture_hardboiled, prepare_hardboiled_capture

        output.mkdir(parents=True)
        capture_hardboiled(
            paths["checkout"],
            paths["build"],
            output / "native",
            paths["sidecar"],
            {case["id"]},
            optimization_only=True,
            library=paths["library"],
            compiler=str(paths["compiler"]),
            case_records=[case],
            revision=settings["revision"],
            timeout_sec=timeout,
        )
        return dict(prepare_hardboiled_capture(output / "native/cases.json", output / "replays")[0])
    raise ValueError(f"unknown reproduction family {family}")


def capture_outcome(capture: dict[str, Any]) -> str:
    """Propagate nested adapter safety stops before considering completion."""
    stack: list[Any] = [capture]
    while stack:
        value = stack.pop()
        if isinstance(value, dict):
            if value.get("status") in STOP_STATUSES:
                return str(value["status"])
            stack.extend(value.values())
        elif isinstance(value, list):
            stack.extend(value)
    if capture.get("resource_stop"):
        return "resource-stopped"
    if capture["status"] == "reproduced":
        if not capture.get("workloads") or capture.get("source_completion", {}).get("status") not in {
            "success",
            "complete",
        }:
            raise ValueError("adapter reported reproduction without successful source completion and replay outputs")
        materialization = capture.get("materialization", {})
        sessions = capture.get("sessions") or capture.get("invocations")
        count = len(sessions) if sessions else int(bool(capture.get("output_contract")))
        if (
            not count
            or materialization.get("complete") is not True
            or materialization.get("expected_sessions") != count
            or materialization.get("materialized_sessions") != count
        ):
            raise ValueError("adapter reported reproduction without complete replay materialization")
        return "success"
    return str(capture["status"])
