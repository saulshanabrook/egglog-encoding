"""Import compact per-figure observations and preserve their frozen selections."""

from __future__ import annotations

import gzip
import json
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast

from .reports.store import GROUPED_SCHEMA_VERSION, REPORT_SCHEMA_VERSION, GroupedReport, GroupedReportRecord

FIGURE_DATA_VERSION = 3


@dataclass
class FigureData:
    """Selected observations and frozen settings for one portable figure export."""

    name: str
    spec: dict[str, Any]
    grouped: GroupedReport
    provenance: dict[str, Any]
    ast_records: tuple[dict[str, Any], ...] = ()


def observation_identity(row: dict[str, Any]) -> str:
    """Compare measured observations independently of cache offsets and unused profiling."""
    return json.dumps(
        {key: value for key, value in row.items() if key not in ("row_index", "source_row_index", "timing_summary")},
        sort_keys=True,
        separators=(",", ":"),
    )


def grouped_figure(rows: list[dict[str, Any]], label: str) -> GroupedReport:
    """Build a plot-only snapshot without changing the raw timing-cache schema."""
    groups: dict[tuple[str, str, str, int], dict[str, Any]] = {}
    for row in rows:
        identity = (row["binary_sha256"], row["file_sha256"], row["treatment"], row["threads"])
        group = groups.setdefault(
            identity,
            {
                "key": dict(zip(("binary_sha256", "file_sha256", "treatment", "threads"), identity, strict=True)),
                "labels": [label],
                "samples": [],
            },
        )
        group["samples"].append(row)
    return GroupedReport(
        cast(
            GroupedReportRecord,
            {
                "grouped_schema_version": GROUPED_SCHEMA_VERSION,
                "report_schema_version": REPORT_SCHEMA_VERSION,
                "groups": list(groups.values()),
                "exclusions": {},
            },
        ),
        "selected figure observations",
    )


def read_figure_json(path: Path) -> dict[str, Any]:
    """Accept plain or gzip sidecars without depending on the producer's filesystem."""
    if not path.exists():
        path = Path(str(path) + ".gz")
    with gzip.open(path, "rt", encoding="utf-8") if path.suffix == ".gz" else path.open(encoding="utf-8") as handle:
        return cast(dict[str, Any], json.load(handle))


def import_figure(name: str, directory: Path) -> FigureData:
    """Load raw selected observations and saved bindings, never the original data.url."""
    path = directory / f"{name}.results.json"
    if not path.exists():
        path = directory / f"{name}.results.json.gz"
    with gzip.open(path, "rt", encoding="utf-8") if path.suffix == ".gz" else path.open(encoding="utf-8") as handle:
        result = json.load(handle)
    if result["figure"] != name or result.get("figure_data_version") != FIGURE_DATA_VERSION:
        raise ValueError(f"unsupported figure data in {path}; regenerate exports with the current renderer")
    spec = read_figure_json(directory / f"{name}.bound.vl.json")
    parameters = {parameter["name"]: parameter["value"] for parameter in spec.get("params", []) if "value" in parameter}
    inputs = deepcopy(parameters["selected_inputs"])
    conditions = {
        (row["logical_id"], row["treatment"], row["binary_sha256"], row["file_sha256"], row["threads"]): row
        for row in result["conditions"]
    }
    rows: list[dict[str, Any]] = []
    identifiers: dict[tuple[int, str], int] = {}
    for item in inputs:
        identity = (item["logical_id"], item["treatment"], item["binary_sha256"], item["file_sha256"], item["threads"])
        condition = conditions.get(identity)
        if condition is None:
            raise ValueError(f"{name}: saved condition does not match its bound identity: {identity}")
        observations = condition["observations"]
        if len(observations) != len(item["selected_row_indices"]):
            raise ValueError(f"{name}: saved observations do not match the bound selection in {path}")
        selected = []
        for index, observation in zip(item["selected_row_indices"], observations, strict=True):
            if observation["row_index"] != index:
                raise ValueError(f"{name}: selected observation {index} is absent or out of order in {path}")
            row = {key: value for key, value in observation.items() if key != "timing_summary"}
            if (row["binary_sha256"], row["file_sha256"], row["treatment"], row["threads"]) != (
                identity[2],
                identity[3],
                identity[1],
                identity[4],
            ):
                raise ValueError(f"{name}: observation does not match its recorded input/engine identity")
            key = (index, observation_identity(row))
            if key not in identifiers:
                identifiers[key] = len(rows)
                row.setdefault("source_row_index", index)
                row["row_index"] = len(rows)
                rows.append(row)
            if identifiers[key] in selected:
                raise ValueError(f"{name}: duplicate selected observation {index}")
            selected.append(identifiers[key])
        item["selected_row_indices"] = selected
    for parameter in spec["params"]:
        if parameter["name"] == "selected_inputs":
            parameter["value"] = inputs
    ast_records: tuple[dict[str, Any], ...] = ()
    if name == "slotted-runtime":
        ast = read_figure_json(directory / "slotted-runtime.ast.json")
        ast_records = tuple(
            {
                **{key: value for key, value in ast.items() if key != "rows"},
                **row.get("measurement_source", {}),
                "row": row,
            }
            for row in ast["rows"]
        )
    return FigureData(
        name,
        spec,
        grouped_figure(rows, parameters["target_label"]),
        result.get("provenance", {}),
        ast_records,
    )


def merge_observations(rows: list[dict[str, Any]], incoming: list[dict[str, Any]]) -> None:
    """Deduplicate overlapping caches by multiplicity, retaining distinct identical samples."""
    from collections import Counter

    known = Counter(observation_identity(row) for row in rows)
    occurrences: Counter[str] = Counter()
    for original in incoming:
        identity = observation_identity(original)
        occurrences[identity] += 1
        if occurrences[identity] > known[identity]:
            row = {key: value for key, value in original.items() if key != "timing_summary"}
            row.setdefault("source_row_index", row["row_index"])
            row["row_index"] = len(rows)
            rows.append(row)


def reuse_figure(data: FigureData, report_path: Path, no_runs: bool, overrides: dict[str, Any], console: Any) -> None:
    """Fill only recorded identities, requiring the original executable and input bytes."""
    from datetime import datetime

    from .engines import TREATMENT_SPECS
    from .reports.store import CacheKey, IndexedRecord, ReportStore, select_records

    parameters = {parameter["name"]: parameter["value"] for parameter in data.spec["params"] if "value" in parameter}
    parameters.update(overrides)
    if "rounds" in overrides:
        from scipy import stats

        parameters["t_critical"] = (
            None if parameters["rounds"] == 1 else float(stats.t.ppf(0.975, parameters["rounds"] - 1))
        )
    rows: list[dict[str, Any]] = [dict(row) for row in data.grouped.records]
    store = None
    for item in parameters["selected_inputs"]:
        if item.get("exclusion") or item.get("validation_issue"):
            continue
        if "memory_limit_bytes" in overrides:
            item["memory_limit_bytes"] = (
                parameters["memory_limit_bytes"] if TREATMENT_SPECS[item["treatment"]].allocator_limit else None
            )
        key = CacheKey(item["binary_sha256"], item["file_sha256"], item["treatment"], item["threads"])
        selected = [rows[index] for index in item["selected_row_indices"]]
        if overrides:
            selected = [
                indexed.record
                for indexed in select_records(
                    tuple(
                        IndexedRecord(row["row_index"], datetime.fromisoformat(row["started_at"]), cast(Any, row))
                        for row in selected
                    ),
                    parameters["rounds"],
                    parameters["timeout_sec"],
                    item["memory_limit_bytes"],
                )
            ]
        while len(selected) < parameters["rounds"] and all(row["status"] == "success" for row in selected):
            if store is None:
                store = ReportStore(report_path)
            candidates = store.latest_records(
                key, parameters["rounds"], parameters["timeout_sec"], item["memory_limit_bytes"]
            )
            merge_observations(rows, [{**row.record, "row_index": row.row_index} for row in candidates])
            available: list[dict[str, Any]] = [
                cast(dict[str, Any], indexed.record)
                for indexed in select_records(
                    tuple(
                        IndexedRecord(row["row_index"], datetime.fromisoformat(row["started_at"]), cast(Any, row))
                        for row in rows
                        if (row["binary_sha256"], row["file_sha256"], row["treatment"], row["threads"])
                        == (key.binary_sha256, key.file_sha256, key.treatment, key.threads)
                    ),
                    parameters["rounds"] if overrides else len(rows),
                    parameters["timeout_sec"],
                    item["memory_limit_bytes"],
                )
            ]
            if overrides:
                selected = available
            else:
                pinned = {row["row_index"] for row in selected}
                extra = [row for row in available if row["row_index"] not in pinned]
                deficit = parameters["rounds"] - len(selected)
                selected.extend(extra[-deficit:])
            missing = parameters["rounds"] - len(selected)
            if missing <= 0 or any(row["status"] != "success" for row in selected):
                break
            if no_runs:
                raise ValueError(
                    f"{data.name}: {item['label']} / {item['treatment']}: missing {missing} observations "
                    f"for recorded {key.binary_sha256}/{key.file_sha256}; --no-runs forbids collection"
                )
            before = store.row_count
            collect_recorded(
                data,
                item,
                rows,
                store,
                parameters,
                missing,
                console,
                cached_statuses=tuple(row["status"] for row in selected),
            )
            if store.row_count == before:
                raise ValueError(f"{data.name}: collection produced no new observations")
        item["selected_row_indices"] = [row["row_index"] for row in selected]
    for parameter in data.spec["params"]:
        if parameter["name"] in parameters:
            parameter["value"] = parameters[parameter["name"]]
    data.grouped = grouped_figure(rows, parameters["target_label"])


def collect_recorded(
    data: FigureData,
    item: dict[str, Any],
    rows: list[dict[str, Any]],
    store: Any,
    parameters: dict[str, Any],
    missing: int,
    console: Any,
    *,
    cached_statuses: tuple[Any, ...] = (),
) -> None:
    """Recover and verify a frozen endpoint before handing its missing runs to the collector."""
    import os

    from .collection import BenchmarkRequest, BenchmarkRunPlan, CollectionPlan, collect
    from .engines import TREATMENT_SPECS
    from .models import BuiltBinary, EndpointRequest, FileSpec, ResolvedTarget, TargetRequest, TargetRow
    from .targets import sha256_file

    reference = next((row for row in rows if row["binary_sha256"] == item["binary_sha256"]), None)
    metadata = (
        {key: reference[f"target_{key}"] for key in ("source", "path", "git_ref", "git_sha", "is_dirty")}
        if reference is not None
        else data.provenance.get("target")
    )
    if metadata is None:
        raise ValueError(f"{data.name}: recorded target provenance is unavailable; choose --target for a new identity")
    # Historical measurements must not move live cache label pointers.
    row = TargetRow(**{key: value for key, value in metadata.items() if key != "label"}, label=None)
    checkout = Path(row.path)
    treatment = TREATMENT_SPECS[item["treatment"]]
    directory = Path(treatment.target_directory or os.environ.get("CARGO_TARGET_DIR", "target"))
    binary = (directory if directory.is_absolute() else checkout / directory) / "release" / treatment.binary_name
    if not binary.is_file() or sha256_file(binary) != item["binary_sha256"]:
        raise ValueError(
            f"{data.name}: original {treatment.binary_name} {item['binary_sha256']} is unavailable or changed; "
            "choose --target to measure a new identity"
        )
    physical = next((sample for sample in rows if sample["file_sha256"] == item["file_sha256"]), None)
    path = Path(physical["file_path"] if physical is not None else item["label"])
    candidates = (path, checkout / path)
    source = next((path for path in candidates if path.is_file() and sha256_file(path) == item["file_sha256"]), None)
    if source is None:
        raise ValueError(
            f"{data.name}: original input {item['file_sha256']} is unavailable or changed; no runs collected"
        )
    file = FileSpec(str(source), source.resolve(), item["file_sha256"])
    request = TargetRequest(raw=str(checkout), source=str(checkout), label=None)
    target = ResolvedTarget(
        request,
        row,
        item["binary_sha256"],
        binary,
        (BuiltBinary(treatment.binary_name, item["binary_sha256"], binary),),
        treatment.binary_name,
    )
    endpoint = EndpointRequest(
        request,
        item["treatment"],
        memory_limit_bytes=item["memory_limit_bytes"],
        threads=item["threads"],
        requested_threads=item["requested_threads"],
    )
    run = BenchmarkRunPlan(
        file,
        item["treatment"],
        parameters["rounds"],
        cached_statuses,
        missing,
        memory_limit_bytes=item["memory_limit_bytes"],
        threads=item["threads"],
        requested_threads=item["requested_threads"],
    )
    collect(
        store,
        (CollectionPlan(target, (run,)),),
        (BenchmarkRequest(endpoint, (file,)),),
        {request: target},
        parameters["timeout_sec"],
        console,
    )


def merge_grouped(local: GroupedReport, imports: list[FigureData], label: str) -> GroupedReport:
    """Overlay compact imports without persisting them as full profiling-cache records."""
    rows: list[dict[str, Any]] = []
    merge_observations(rows, [dict(row) for row in local.records])
    for data in imports:
        merge_observations(rows, [dict(row) for row in data.grouped.records])
    return grouped_figure(rows, label)


def restyle_figure(data: FigureData, spec_path: Path) -> None:
    """Replace drawing code while preserving every recorded selection/settings parameter."""
    spec = json.loads(spec_path.read_text(encoding="utf-8"))
    saved = {parameter["name"]: parameter for parameter in data.spec["params"]}
    names = set()
    for parameter in spec.setdefault("params", []):
        names.add(parameter["name"])
        if parameter["name"] in saved and "value" in saved[parameter["name"]]:
            parameter.pop("expr", None)
            parameter["value"] = saved[parameter["name"]]["value"]
    spec["params"].extend(parameter for name, parameter in saved.items() if name not in names)
    data.spec = spec
