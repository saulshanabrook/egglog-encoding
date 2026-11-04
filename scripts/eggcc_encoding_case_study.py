#!/usr/bin/env python3
"""Collect, verify and plot a fixed full-eggcc case study; never build binaries."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import math
import os
import platform
import re
import statistics
import sys
from collections.abc import Iterator, Sequence
from dataclasses import asdict
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

# Permit the documented `python scripts/…` invocation from any directory.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from benchmarking.processes import run_command  # noqa: E402

SCHEMA_VERSION = 1
RSS_SCOPE = "wait4 child rusage.ru_maxrss; platform-normalized, not simultaneous process-group peak"
FORBIDDEN_FLAGS = {
    "--interp",
    "--run-data-out",
    "--add-timing",
    "--profile-out",
    "--debug-dir",
    "--egraph-out-dir",
    "--time-ilp",
}


def sha256(path: Path) -> str:
    """Hash large binaries without materializing them in memory."""

    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def write_json(path: Path, value: Any) -> None:
    """Replace a checkpoint atomically, leaving the previous one intact on interruption."""

    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def load_study(path: Path) -> dict[str, Any]:
    """Resolve the intentionally small, case-specific manifest against its own directory."""

    study: dict[str, Any] = json.loads(path.read_text(encoding="utf-8"))
    if study["schema_version"] != SCHEMA_VERSION:
        raise ValueError("unsupported study schema_version")
    if not study["study_id"] or not study["cases"] or not study["arms"]:
        raise ValueError("study_id, cases and arms must be nonempty")
    study.setdefault("warmups", 1)
    study.setdefault("observations", 10)
    study.setdefault("timeout_sec", 300)
    study.setdefault("artifacts", [])
    study.setdefault("claims", {"real_bug": None, "optimization": None})
    for name, minimum in (("warmups", 0), ("observations", 1), ("timeout_sec", 1)):
        if type(study[name]) is not int or study[name] < minimum:
            raise ValueError(f"{name} must be an integer >= {minimum}")
    for group in ("cases", "arms", "artifacts"):
        identities: set[str] = set()
        for item in study[group]:
            if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", item["id"]) or item["id"] in identities:
                raise ValueError(f"{group} ids must be unique filename-safe identifiers")
            identities.add(item["id"])
            fields = {"cases": ("input",), "arms": ("binary", "cwd"), "artifacts": ("path",)}[group]
            for field in fields:
                item[field] = str((path.parent / item[field]).resolve())
            if group in ("cases", "artifacts") and not item["origin"]:
                raise ValueError(f"{group} require a source origin")
    for arm in study["arms"]:
        if not arm["engine"] or not arm["configuration"]:
            raise ValueError("arms require engine and configuration labels")
        arm.setdefault("env", {})
        if not Path(arm["cwd"]).is_dir():
            raise ValueError(f"arm cwd is not a directory: {arm['cwd']}")
        if not os.access(arm["binary"], os.X_OK):
            raise ValueError(f"arm binary is not executable: {arm['binary']}")
        flags = {arg.split("=", 1)[0] for arg in arm["args"]}
        if flags & FORBIDDEN_FLAGS:
            raise ValueError(
                f"collector owns interpretation/receipt flags; diagnostics are excluded: {flags & FORBIDDEN_FLAGS}"
            )
        args = arm["args"]
        if "--run-mode" not in args or args[args.index("--run-mode") + 1] != "optimize":
            raise ValueError("each arm must explicitly select --run-mode optimize")
    for case in study["cases"]:
        if "args" in case:
            raise ValueError("input variants must use retained # ARGS: fixtures; positional CLI arguments are unused")
    for artifact in study["artifacts"]:
        if artifact.get("kind") == "tests":
            receipt = json.loads(Path(artifact["path"]).read_text(encoding="utf-8"))
            if (
                receipt["status"] != "success"
                or type(receipt["selected_tests"]) is not int
                or receipt["selected_tests"] <= 0
            ):
                raise ValueError(f"test receipt must report success and nonzero selected_tests: {artifact['id']}")
    artifact_ids = {artifact["id"] for artifact in study["artifacts"]}
    for name, field in (("real_bug", "baseline_reproducer"), ("optimization", "transformation")):
        claim = study["claims"][name]
        if claim is not None:
            if not claim["description"] or claim[field] not in artifact_ids:
                raise ValueError(f"{name} claim requires description and a retained {field} artifact")
            if name == "real_bug" and not claim["violated_invariant"]:
                raise ValueError("real_bug requires a sound violated_invariant for manual review")
    return study


def provenance(study: dict[str, Any]) -> list[dict[str, str]]:
    """Bind binaries, inputs and externally supplied source/configuration receipts to bytes."""

    files = (
        [{"kind": "binary", "id": arm["id"], "path": arm["binary"], "origin": arm["engine"]} for arm in study["arms"]]
        + [
            {"kind": "input", "id": case["id"], "path": case["input"], "origin": case["origin"]}
            for case in study["cases"]
        ]
        + [
            {"kind": "artifact", "id": artifact["id"], "path": artifact["path"], "origin": artifact["origin"]}
            for artifact in study["artifacts"]
        ]
    )
    return [{**entry, "sha256": sha256(Path(entry["path"]))} for entry in files]


def schedule(study: dict[str, Any]) -> Iterator[tuple[str, int, dict[str, Any], dict[str, Any]]]:
    """Check all configurations first, then rotate arm order on each repetition."""

    arms = study["arms"]
    for phase, count in (("correctness", 1), ("warmup", study["warmups"]), ("measurement", study["observations"])):
        for repetition in range(count):
            order = arms[repetition % len(arms) :] + arms[: repetition % len(arms)]
            for case in study["cases"]:
                for arm in order:
                    yield phase, repetition, case, arm


def invocation(arm: dict[str, Any], case: dict[str, Any], phase: str, receipt: Path) -> list[str]:
    """Keep compiler treatment identical across interpreted and timing invocations."""

    return [
        arm["binary"],
        *arm["args"],
        *(["--interp"] if phase == "correctness" else []),
        "--run-data-out",
        str(receipt),
        case["input"],
    ]


def check_receipt(row: dict[str, Any]) -> None:
    """Require a complete CLI run and explicit, non-null interpreter agreement."""

    if row["status"] != "success" or row["exit_code"] != 0 or row["signal"] is not None or row["error"] is not None:
        raise ValueError(f"incomplete compiler run: {row['status']}: {row.get('error')}")
    path = Path(row["receipt_path"])
    if sha256(path) != row["receipt_sha256"]:
        raise ValueError(f"changed compiler receipt: {path}")
    receipt = json.loads(path.read_text(encoding="utf-8"))
    if (
        receipt != row["receipt"]
        or not {"original_interpreted", "result_interpreted", "eggcc_compile_time"} <= receipt.keys()
    ):
        raise ValueError("missing or inconsistent compiler receipt")
    original, result = receipt.get("original_interpreted"), receipt.get("result_interpreted")
    if row["phase"] == "correctness":
        if not isinstance(original, str) or not isinstance(result, str):
            raise ValueError("missing non-null original/result interpreter outputs")
        if original != result:
            raise ValueError("original/result interpreter outputs differ")
    elif original is not None or result is not None:
        raise ValueError("timing invocation unexpectedly interpreted the program")
    if row["phase"] != "correctness":
        if type(row["wall_sec"]) not in (float, int) or not math.isfinite(row["wall_sec"]) or row["wall_sec"] <= 0:
            raise ValueError("missing positive finite measured wall time")
        if type(row["max_rss_bytes"]) is not int or row["max_rss_bytes"] <= 0:
            raise ValueError("missing positive measured wait4 peak RSS")


def collect(study_path: Path, results_path: Path) -> dict[str, Any]:
    """Checkpoint every run and retain failures; never collect timing after a failed check."""

    study = load_study(study_path)
    if results_path.exists():
        raise ValueError(f"results already exist; choose a fresh result path: {results_path}")
    receipts = results_path.with_suffix(".receipts")
    receipts.mkdir(parents=True, exist_ok=False)
    results: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "study_path": str(study_path),
        "study_sha256": sha256(study_path),
        "study": study,
        "provenance": provenance(study),
        "status": "collecting",
        "rows": [],
        "started_utc": datetime.now(UTC).isoformat(),
        "host": {"platform": platform.platform(), "python": sys.version},
        "rss_scope": RSS_SCOPE,
        "timing_scope": (
            "compiler process wall time including CLI JSON receipt; excludes interpretation; not program execution"
        ),
    }
    write_json(results_path, results)
    try:
        for phase, repetition, case, arm in schedule(study):
            if provenance(study) != results["provenance"] or sha256(study_path) != results["study_sha256"]:
                raise ValueError("study/input/binary/artifact provenance changed during collection")
            receipt = receipts / f"{phase}-{repetition:02}-{case['id']}-{arm['id']}.json"
            command = invocation(arm, case, phase, receipt)
            overrides = {"RUST_LOG": "error", **arm["env"]}
            effective_env = {**os.environ, **overrides}
            row: dict[str, Any] = {
                "phase": phase,
                "repetition": repetition,
                "case": case["id"],
                "arm": arm["id"],
                "engine": arm["engine"],
                "configuration": arm["configuration"],
                "command": command,
                "cwd": arm["cwd"],
                "env_overrides": overrides,
                # Bind the entire effective environment without disclosing inherited credentials.
                "environment_sha256": {
                    key: hashlib.sha256(value.encode()).hexdigest() for key, value in sorted(effective_env.items())
                },
                "inherited_environment": {
                    key: effective_env[key]
                    for key in ("PATH", "LANG", "LC_ALL", "RUSTUP_TOOLCHAIN", "RAYON_NUM_THREADS", "OMP_NUM_THREADS")
                    if key in effective_env
                },
                "receipt_path": str(receipt),
                "receipt_sha256": None,
                "receipt": None,
                "rss_scope": RSS_SCOPE,
                "wall_sec": None,
                "max_rss_bytes": None,
                "status": "failure",
                "exit_code": None,
                "signal": None,
                "error": None,
            }
            results["rows"].append(row)
            print(f"{phase} {repetition + 1}: {case['id']} / {arm['id']}", file=sys.stderr)
            try:
                run = run_command(command, Path(arm["cwd"]), study["timeout_sec"], overrides)
                if phase != "correctness":
                    row.update(asdict(run.timing))
                row.update(status=run.status, exit_code=0 if run.status == "success" else None)
                if run.error is not None:
                    row.update(error=run.error.message, exit_code=run.error.exit_code, signal=run.error.signal)
                if receipt.exists():
                    row["receipt_sha256"] = sha256(receipt)
                    row["receipt"] = json.loads(receipt.read_text(encoding="utf-8"))
                check_receipt(row)
            except (OSError, ValueError) as error:
                row["error"] = str(error)
                if row["status"] == "success":
                    row["status"] = "failure"
                raise ValueError(f"{phase} {case['id']}/{arm['id']}: {error}") from error
            finally:
                write_json(results_path, results)
        verify(study_path, results_path, require_complete=False)
        results["status"] = "complete"
    except BaseException as error:
        results["status"] = "interrupted" if isinstance(error, (KeyboardInterrupt, SystemExit)) else "failure"
        results["error"] = str(error)
        raise
    finally:
        write_json(results_path, results)
    return results


def verify(study_path: Path, results_path: Path, *, require_complete: bool = True) -> dict[str, Any]:
    """Check current provenance, complete schedule, test counts and correctness receipts."""

    study = load_study(study_path)
    results: dict[str, Any] = json.loads(results_path.read_text(encoding="utf-8"))
    if (
        results["schema_version"] != SCHEMA_VERSION
        or results["study_sha256"] != sha256(study_path)
        or results["study"] != study
    ):
        raise ValueError("study manifest provenance mismatch")
    if provenance(study) != results["provenance"]:
        raise ValueError("input/binary/artifact provenance mismatch")
    if require_complete and results["status"] != "complete":
        raise ValueError(f"collection is incomplete: {results['status']}")
    if results["rss_scope"] != RSS_SCOPE:
        raise ValueError("unexpected RSS measurement scope")
    expected = list(schedule(study))
    if len(results["rows"]) != len(expected):
        raise ValueError("missing or extra correctness/warmup/measured rows")
    for row, (phase, repetition, case, arm) in zip(results["rows"], expected, strict=True):
        if (row["phase"], row["repetition"], row["case"], row["arm"]) != (phase, repetition, case["id"], arm["id"]):
            raise ValueError("row identity/order does not match interleaved schedule")
        if row["command"] != invocation(arm, case, phase, Path(row["receipt_path"])) or row["cwd"] != arm["cwd"]:
            raise ValueError("recorded invocation provenance mismatch")
        if (row["engine"], row["configuration"], row["rss_scope"], row["env_overrides"]) != (
            arm["engine"],
            arm["configuration"],
            RSS_SCOPE,
            {"RUST_LOG": "error", **arm["env"]},
        ):
            raise ValueError("recorded treatment/environment provenance mismatch")
        for key, value in {**row["env_overrides"], **row["inherited_environment"]}.items():
            if row["environment_sha256"].get(key) != hashlib.sha256(value.encode()).hexdigest():
                raise ValueError("recorded environment hash mismatch")
        check_receipt(row)
    return results


def figure_data(results: dict[str, Any]) -> list[dict[str, Any]]:
    """Derive per-case summaries directly from every measured observation; no aggregate."""

    summaries = []
    for case in results["study"]["cases"]:
        for arm in results["study"]["arms"]:
            rows = [
                row
                for row in results["rows"]
                if (row["phase"], row["case"], row["arm"]) == ("measurement", case["id"], arm["id"])
            ]
            values: dict[str, Any] = {"case": case["id"], "arm": arm["id"], "n": len(rows)}
            for metric in ("wall_sec", "max_rss_bytes"):
                raw = [row[metric] for row in rows]
                values[metric] = {
                    "raw": raw,
                    "median": statistics.median(raw),
                    "min": min(raw),
                    "max": max(raw),
                    "stdev": statistics.stdev(raw) if len(raw) > 1 else None,
                }
            summaries.append(values)
    return summaries


def figures(study_path: Path, results_path: Path, output_dir: Path) -> None:
    """Export standalone scientific figures and their raw-value source and compact table."""

    results = verify(study_path, results_path)
    try:
        matplotlib = importlib.import_module("matplotlib")
        matplotlib.use("Agg")
        pyplot = importlib.import_module("matplotlib.pyplot")
    except ImportError as error:
        raise ValueError("figures requires matplotlib==3.10.7; see the documented pinned uv invocation") from error
    output_dir.mkdir(parents=True, exist_ok=True)
    summaries = figure_data(results)
    write_json(
        output_dir / "figure-data.json",
        {
            "study_sha256": sha256(study_path),
            "results_sha256": sha256(results_path),
            "rss_scope": RSS_SCOPE,
            "spread": "min/max and sample standard deviation of observations; not confidence intervals",
            "summaries": summaries,
        },
    )
    table = [
        "| Case | Arm | n | Compiler wall s: median [min, max]; SD | wait4 peak MiB: median [min, max]; SD |",
        "| --- | --- | ---: | ---: | ---: |",
    ]
    for summary in summaries:
        cells = []
        for metric, scale in (("wall_sec", 1), ("max_rss_bytes", 1024**2)):
            values = summary[metric]
            sd = "unavailable (n=1)" if values["stdev"] is None else f"{values['stdev'] / scale:.4g}"
            cells.append(
                f"{values['median'] / scale:.4g} [{values['min'] / scale:.4g}, {values['max'] / scale:.4g}]; {sd}"
            )
        table.append(f"| {summary['case']} | {summary['arm']} | {summary['n']} | {' | '.join(cells)} |")
    table.extend(
        [
            "",
            f"RSS: {RSS_SCOPE}. Wall time is compiler process elapsed time, not generated-program performance.",
            "Spread is observational, not a confidence interval. Warmups and interpreted checks are excluded.",
        ]
    )
    (output_dir / "table.md").write_text("\n".join(table) + "\n", encoding="utf-8")
    with matplotlib.rc_context({"svg.fonttype": "none", "svg.hashsalt": "eggcc-encoding-case-study", "font.size": 10}):
        for case in results["study"]["cases"]:
            data = [summary for summary in summaries if summary["case"] == case["id"]]
            figure, axes = pyplot.subplots(1, 2, figsize=(10, max(3, 1.6 + len(data) * 0.5)), layout="constrained")
            for axis, metric, scale, label in zip(
                axes,
                ("wall_sec", "max_rss_bytes"),
                (1, 1024**2),
                ("Compiler elapsed time (s)", "wait4 child peak RSS (MiB)"),
                strict=True,
            ):
                for index, summary in enumerate(data):
                    values = summary[metric]
                    raw = [value / scale for value in values["raw"]]
                    offsets = [
                        index + (position - (len(raw) - 1) / 2) * 0.16 / max(1, len(raw) - 1)
                        for position in range(len(raw))
                    ]
                    axis.plot(
                        [values["min"] / scale, values["max"] / scale], [index, index], color="#505050", linewidth=1.5
                    )
                    axis.scatter(raw, offsets, marker="o", facecolors="none", edgecolors="#24578a", s=22, zorder=3)
                    axis.scatter([values["median"] / scale], [index], marker="|", color="#171717", s=140, zorder=4)
                axis.set_yticks(range(len(data)), [f"{row['arm']} (n={row['n']})" for row in data])
                axis.invert_yaxis()
                axis.set_xlim(0, max(row[metric]["max"] / scale for row in data) * 1.06)
                axis.set_xlabel(label)
                axis.grid(axis="x", color="#dddddd", linewidth=0.6)
                axis.set_axisbelow(True)
                axis.spines[["top", "right"]].set_visible(False)
            figure.suptitle(case.get("label", case["id"]))
            figure.supxlabel(
                "Open circles: observations; black tick: median; line: min-max. "
                "RSS is not simultaneous process-group peak.",
                fontsize=8,
            )
            for extension in ("svg", "pdf"):
                metadata = {"Date": None} if extension == "svg" else {"CreationDate": None, "ModDate": None}
                figure.savefig(output_dir / f"{case['id']}.{extension}", metadata=metadata)
            pyplot.close(figure)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="operation", required=True)
    for operation in ("collect", "verify", "figures"):
        subparser = subparsers.add_parser(operation)
        subparser.add_argument("study", type=Path)
        subparser.add_argument("results", type=Path)
        if operation == "figures":
            subparser.add_argument("output_dir", type=Path)
    args = parser.parse_args(argv)
    study, results = args.study.expanduser().resolve(), args.results.expanduser().resolve()
    try:
        if args.operation == "collect":
            collect(study, results)
        elif args.operation == "verify":
            verify(study, results)
        else:
            figures(study, results, args.output_dir.expanduser().resolve())
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        print(f"{args.operation}: {error}", file=sys.stderr)
        return 1
    print(
        f"{args.operation}: verified {results}" if args.operation == "verify" else f"{args.operation}: wrote {results}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
