"""Own run directories, append-only rows, per-process log paths, and Markdown summaries."""

from __future__ import annotations

import json
import os
import re
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast

from .jsonio import serialize_json_line, write_json_document, write_text_document

_RUN_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{0,127}\Z")


@dataclass
class ResultStore:
    """One exclusive, append-only ``.paper-results/<run-id>`` directory."""

    run_id: str
    path: Path
    manifest_path: Path
    runs_path: Path
    logs_path: Path
    summary_path: Path
    status_path: Path

    @classmethod
    def create(cls, results_root: Path, run_id: str) -> ResultStore:
        """Create one never-overwritten result directory."""

        if _RUN_ID.fullmatch(run_id) is None:
            raise ValueError(f"invalid paper run id: {run_id!r}")
        root = results_root.expanduser().resolve(strict=False)
        root.mkdir(parents=True, exist_ok=True)
        path = root / run_id
        path.mkdir(exist_ok=False)
        logs_path = path / "logs"
        logs_path.mkdir()
        runs_path = path / "runs.jsonl"
        runs_path.touch(exist_ok=False)
        return cls(
            run_id=run_id,
            path=path,
            manifest_path=path / "manifest.json",
            runs_path=runs_path,
            logs_path=logs_path,
            summary_path=path / "summary.md",
            status_path=path / "status.json",
        )

    def write_manifest(self, manifest: dict[str, object]) -> None:
        """Write the immutable run plan before any child process starts."""

        if self.manifest_path.exists():
            raise ValueError(f"paper run manifest already exists: {self.manifest_path}")
        write_json_document(self.manifest_path, manifest)

    def append(self, record: dict[str, object]) -> None:
        """Durably append one complete process record."""

        encoded = serialize_json_line(record) + b"\n"
        with self.runs_path.open("ab") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())

    def write_summary(self, summary: str) -> None:
        """Write the exact Markdown returned on stdout."""

        write_text_document(self.summary_path, summary)

    def write_status(self, state: str, *, success: bool | None = None, error: str | None = None) -> None:
        """Atomically publish the latest lifecycle state for this run."""

        write_json_document(
            self.status_path,
            {"error": error, "run_id": self.run_id, "state": state, "success": success},
        )


def read_run_records(path: Path) -> list[dict[str, Any]]:
    """Read process rows in physical append order."""

    records: list[dict[str, Any]] = []
    payload = path.read_bytes()
    lines = payload.splitlines(keepends=True)
    for index, line in enumerate(lines):
        if index == len(lines) - 1 and not line.endswith(b"\n"):
            break
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            raise
        if not isinstance(value, dict):
            raise ValueError(f"paper process row is not an object: {path}")
        records.append(cast(dict[str, Any], value))
    return records


def render_markdown_summary(
    manifest: dict[str, object],
    records: list[dict[str, object]],
) -> str:
    """Render a status-preserving report whose aggregates use successes only."""

    selection = _object(manifest, "selection")
    artifact = _object(manifest, "artifact")
    repository = _object(manifest, "repository")
    machine = _object(manifest, "machine")
    lanes = _object_list(manifest, "lanes")
    evaluations = selection.get("evaluations")
    evaluation_text = ", ".join(str(value) for value in evaluations) if isinstance(evaluations, list) else ""
    lines = [
        f"# Paper Artifact Run `{manifest['run_id']}`",
        "",
        f"- Preset: `{selection.get('preset')}`",
        f"- Evaluations: {evaluation_text}",
        f"- Artifact archive SHA-256: `{artifact.get('archive_sha256')}`",
        f"- Repository commit: `{repository.get('git_sha')}`",
        f"- Repository dirty: `{'yes' if repository.get('is_dirty') else 'no'}`",
        f"- Repository diff SHA-256: `{repository.get('diff_sha256', '-')}`",
        f"- Machine: `{machine.get('system')} {machine.get('machine')}`",
        "",
        "## Lane Summary",
        "",
        (
            "Wall aggregates include successful timed observations only; "
            "timeouts and infrastructure errors remain statuses."
        ),
        "",
        "| Evaluation | Lane | Success | Failure | Timed out | Infra error | Not run | Median wall |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for lane in lanes:
        evaluation = str(lane.get("evaluation"))
        name = str(lane.get("name"))
        observations = [
            record
            for record in records
            if record.get("phase") == "observation"
            and record.get("evaluation") == evaluation
            and record.get("lane") == name
        ]
        statuses = [record.get("status") for record in observations]
        successful = [record for record in observations if record.get("status") == "success"]
        walls = [float(value) for record in successful if isinstance((value := record.get("wall_sec")), int | float)]
        planned = lane.get("observations")
        planned_count = len(planned) if isinstance(planned, list) else len(observations)
        lines.append(
            "| "
            + " | ".join(
                (
                    _cell(evaluation),
                    _cell(name),
                    str(statuses.count("success")),
                    str(statuses.count("failure")),
                    str(statuses.count("timed-out")),
                    str(statuses.count("infrastructure-error")),
                    str(max(0, planned_count - len(observations))),
                    _format_wall(statistics.median(walls) if walls else None),
                )
            )
            + " |"
        )

    observations = [record for record in records if record.get("phase") == "observation"]
    lines.extend(
        [
            "",
            "## Timed Observations",
            "",
            "| Evaluation | Lane | Round | Status | Wall |",
            "| --- | --- | ---: | --- | ---: |",
        ]
    )
    for record in observations:
        lines.append(
            "| "
            + " | ".join(
                (
                    _cell(record.get("evaluation")),
                    _cell(record.get("lane")),
                    _cell(record.get("round")),
                    _cell(record.get("status")),
                    _format_wall(_number(record.get("wall_sec"))),
                )
            )
            + " |"
        )

    hooks = [record for record in records if record.get("phase") in {"build", "prepare", "validate"}]
    if hooks:
        lines.extend(
            [
                "",
                "## Untimed Hooks",
                "",
                "| Evaluation | Lane | Phase | Command | Status |",
                "| --- | --- | --- | --- | --- |",
            ]
        )
        for record in hooks:
            lines.append(
                "| "
                + " | ".join(
                    _cell(record.get(key)) for key in ("evaluation", "lane", "phase", "command_label", "status")
                )
                + " |"
            )
    return "\n".join(lines) + "\n"


def _object(parent: dict[str, object], key: str) -> dict[str, object]:
    value = parent.get(key)
    if not isinstance(value, dict):
        raise ValueError(f"paper run manifest field {key!r} is not an object")
    return cast(dict[str, object], value)


def _object_list(parent: dict[str, object], key: str) -> list[dict[str, object]]:
    value = parent.get(key)
    if not isinstance(value, list) or not all(isinstance(item, dict) for item in value):
        raise ValueError(f"paper run manifest field {key!r} is not an object list")
    return cast(list[dict[str, object]], value)


def _cell(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def _number(value: object) -> float | None:
    if isinstance(value, int | float) and not isinstance(value, bool):
        return float(value)
    return None


def _format_wall(value: float | None) -> str:
    return "-" if value is None else f"{value:.3f} s"
