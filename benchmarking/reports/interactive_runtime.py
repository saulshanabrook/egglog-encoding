"""Recompute interactive benchmark catalogs from one immutable cache snapshot.

This module is the environment-neutral core shared by native artifact creation
and the Pyodide browser runtime.  It discovers selector choices from every row
in the loaded JSONL and atomically replaces the published all-sections catalog.
Incomplete selections remain valid so the shared report can show its precise
missing-result cells.  HTML generation, browser startup, and filesystem export
belong in :mod:`interactive`.
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import cast

from ..models import BenchmarkEndpoint, ComparisonSpec, FileSpec, ResolvedTarget, TargetRequest, TargetRow
from .catalog import CellTone, ReportCatalog, ReportCell, ReportMessage, report_id
from .comparison import build_report_catalog, report_file_labels
from .records import ReportRecord
from .store import ReportStore

type JsonScalar = str | int | float | bool | None
type JsonValue = JsonScalar | list[JsonValue] | dict[str, JsonValue]


@dataclass(frozen=True)
class InteractiveScope:
    """One exact cache-backed comparison selected in the browser."""

    baseline_endpoint_id: str
    candidate_endpoint_id: str
    file_ids: tuple[str, ...]
    timeout_sec: int
    rounds: int


@dataclass(frozen=True)
class _EndpointChoice:
    endpoint_id: str
    endpoint: BenchmarkEndpoint


@dataclass(frozen=True)
class _FileChoice:
    file_id: str
    file: FileSpec


class _DisplayPathStore(ReportStore):
    """Load a Pyodide virtual file while retaining its host display path."""

    def __init__(self, path: Path, display_path: str) -> None:
        self._display_path = display_path
        super().__init__(path)

    @property
    def display_path(self) -> str:
        return self._display_path


class InteractiveRuntime:
    """Own one cache universe and its last successfully published comparison."""

    def __init__(
        self,
        store: ReportStore,
        initial_scope: object,
    ) -> None:
        self._store = store
        (
            self._endpoint_choices,
            self._file_choices,
            self._timeouts,
            self._max_rounds,
        ) = _cache_universe(store.records)
        self._endpoint_by_id = {choice.endpoint_id: choice.endpoint for choice in self._endpoint_choices}
        self._file_by_id = {choice.file_id: choice.file for choice in self._file_choices}

        scope = self._parse_scope(initial_scope)
        comparison = self._comparison(scope)
        self._scope = scope
        self._catalog = build_report_catalog(store, comparison, "rulesets")

    @classmethod
    def from_path(
        cls,
        path: Path,
        display_path: str,
        initial_scope_json: str,
    ) -> InteractiveRuntime:
        """Load the browser's virtual JSONL and restore its initial scope."""

        store = _DisplayPathStore(path, display_path)
        return cls(store, json.loads(initial_scope_json))

    def payload(self) -> dict[str, JsonValue]:
        """Return the last successfully published selectors and catalog."""

        return self._payload(
            self._scope,
            self._catalog,
            self._endpoint_choices,
            self._file_choices,
        )

    def initial_payload(self, comparison: ComparisonSpec) -> dict[str, JsonValue]:
        """Present the exact native invocation before cache-only retargeting."""

        scope = self._parse_scope(scope_for_comparison(comparison))
        selected_endpoints = (comparison.baseline, comparison.candidate)
        endpoint_ids = {_endpoint_id(endpoint) for endpoint in selected_endpoints}
        endpoint_choices = tuple(
            _EndpointChoice(_endpoint_id(endpoint), endpoint) for endpoint in selected_endpoints
        ) + tuple(choice for choice in self._endpoint_choices if choice.endpoint_id not in endpoint_ids)
        file_ids = {_file_id(file) for file in comparison.files}
        file_choices = tuple(_FileChoice(_file_id(file), file) for file in comparison.files) + tuple(
            choice for choice in self._file_choices if choice.file_id not in file_ids
        )
        catalog = build_report_catalog(self._store, comparison, "rulesets")
        return self._payload(scope, catalog, endpoint_choices, file_choices)

    def apply(self, value: object) -> dict[str, JsonValue]:
        """Compute and publish a requested scope, leaving prior state on error."""

        scope = self._parse_scope(value)
        comparison = self._comparison(scope)
        catalog = build_report_catalog(self._store, comparison, "rulesets")
        payload = self._payload(
            scope,
            catalog,
            self._endpoint_choices,
            self._file_choices,
        )
        self._scope = scope
        self._catalog = catalog
        return payload

    def apply_json(self, request_json: str) -> str:
        """Return a JSON success/error envelope convenient for the JS bridge."""

        try:
            payload = self.apply(json.loads(request_json))
        except (KeyError, TypeError, ValueError) as error:
            result: dict[str, JsonValue] = {"ok": False, "error": str(error)}
        else:
            result = {"ok": True, "payload": payload}
        return json.dumps(result, ensure_ascii=False, separators=(",", ":"))

    def _comparison(self, scope: InteractiveScope) -> ComparisonSpec:
        files = tuple(self._file_by_id[file_id] for file_id in scope.file_ids)
        return ComparisonSpec(
            self._endpoint_by_id[scope.baseline_endpoint_id],
            self._endpoint_by_id[scope.candidate_endpoint_id],
            files,
            scope.rounds,
            scope.timeout_sec,
        )

    def _parse_scope(self, value: object) -> InteractiveScope:
        request = _object(value, "scope request")
        baseline_id = _string(request, "baseline_endpoint_id")
        candidate_id = _string(request, "candidate_endpoint_id")
        _require_known(baseline_id, self._endpoint_by_id, "baseline endpoint")
        _require_known(candidate_id, self._endpoint_by_id, "candidate endpoint")
        if baseline_id == candidate_id:
            raise ValueError("baseline and candidate endpoints must be different")
        file_ids = _string_list(request, "file_ids")
        _require_known_subset(file_ids, self._file_by_id, "file")
        timeout_sec = _positive_int(request, "timeout_sec")
        if timeout_sec not in self._timeouts:
            raise ValueError(f"unknown timeout: {timeout_sec}s")
        rounds = _positive_int(request, "rounds")
        if rounds > self._max_rounds:
            raise ValueError(f"rounds must not exceed cached maximum: {self._max_rounds}")
        return InteractiveScope(baseline_id, candidate_id, file_ids, timeout_sec, rounds)

    def _payload(
        self,
        scope: InteractiveScope,
        catalog: ReportCatalog,
        endpoint_choices: Sequence[_EndpointChoice],
        file_choices: Sequence[_FileChoice],
    ) -> dict[str, JsonValue]:
        selected = set(scope.file_ids)
        labels = report_file_labels(tuple(choice.file for choice in file_choices))
        return {
            "report_path": self._store.display_path,
            "selectors": {
                "endpoints": [
                    {
                        "id": choice.endpoint_id,
                        "label": _endpoint_label(choice.endpoint),
                        "target": choice.endpoint.target.display_label,
                        "git_sha": choice.endpoint.target.row.git_sha,
                        "dirty": choice.endpoint.target.row.is_dirty,
                        "backend": choice.endpoint.backend,
                        "treatment": choice.endpoint.treatment,
                    }
                    for choice in endpoint_choices
                ],
                "baseline_endpoint_id": scope.baseline_endpoint_id,
                "candidate_endpoint_id": scope.candidate_endpoint_id,
                "files": [
                    {
                        "id": choice.file_id,
                        "label": labels[choice.file],
                        "selected": choice.file_id in selected,
                    }
                    for choice in file_choices
                ],
                "timeouts_sec": list(self._timeouts),
                "timeout_sec": scope.timeout_sec,
                "rounds": scope.rounds,
                "max_rounds": self._max_rounds,
            },
            "sections": _catalog_payload(catalog),
        }


def scope_for_comparison(comparison: ComparisonSpec) -> dict[str, JsonValue]:
    """Serialize one native comparison as the browser runtime's initial scope."""

    return {
        "baseline_endpoint_id": _endpoint_id(comparison.baseline),
        "candidate_endpoint_id": _endpoint_id(comparison.candidate),
        "file_ids": [_file_id(file) for file in comparison.files],
        "timeout_sec": comparison.timeout_sec,
        "rounds": comparison.rounds,
    }


def _catalog_payload(catalog: ReportCatalog) -> list[JsonValue]:
    """Adapt the shared renderer-neutral catalog to eval-live's JSON contract."""

    sections: list[JsonValue] = []
    for section in catalog.sections:
        blocks: list[JsonValue] = []
        for block in section.blocks:
            if isinstance(block, ReportMessage):
                blocks.append(
                    {
                        "kind": "message",
                        "id": block.id,
                        "title": block.title,
                        "text": block.text,
                        "tone": block.tone,
                    }
                )
                continue
            blocks.append(
                {
                    "kind": "table",
                    "id": block.id,
                    "name": block.title,
                    "caption": block.caption,
                    "columns": [
                        {"id": column.id, "name": column.label, "alignment": column.alignment}
                        for column in block.columns
                    ],
                    "rows": [
                        {column.id: _cell_payload(cell) for column, cell in zip(block.columns, row.cells, strict=True)}
                        for row in block.rows
                    ],
                }
            )
        sections.append({"id": section.id, "title": section.title, "blocks": blocks})
    return sections


def _cache_universe(
    records: Sequence[ReportRecord],
) -> tuple[
    tuple[_EndpointChoice, ...],
    tuple[_FileChoice, ...],
    tuple[int, ...],
    int,
]:
    endpoint_rows: dict[str, tuple[tuple[datetime, int], ReportRecord]] = {}
    file_rows: dict[str, tuple[tuple[datetime, int], ReportRecord]] = {}
    timeouts: set[int] = set()
    counts: Counter[tuple[str, str, int]] = Counter()
    for row_index, record in enumerate(records):
        order_key = (datetime.fromisoformat(record["started_at"]), row_index)
        endpoint_id = _record_endpoint_id(record)
        file_id = _record_file_id(record)
        if endpoint_id not in endpoint_rows or order_key > endpoint_rows[endpoint_id][0]:
            endpoint_rows[endpoint_id] = (order_key, record)
        if file_id not in file_rows or order_key > file_rows[file_id][0]:
            file_rows[file_id] = (order_key, record)
        timeout_sec = record["timeout_sec"]
        timeouts.add(timeout_sec)
        counts[endpoint_id, file_id, timeout_sec] += 1

    endpoints = tuple(
        sorted(
            (
                _EndpointChoice(endpoint_id, _endpoint_from_record(record))
                for endpoint_id, (_order, record) in endpoint_rows.items()
            ),
            key=lambda choice: (
                choice.endpoint.target.display_label,
                choice.endpoint.backend,
                choice.endpoint.treatment,
                choice.endpoint.target.binary_sha256,
            ),
        )
    )
    files = tuple(
        sorted(
            (_FileChoice(file_id, _file_from_record(record)) for file_id, (_order, record) in file_rows.items()),
            key=lambda choice: (
                choice.file.display_path,
                str(choice.file.fact_directory or ""),
                choice.file.sha256,
                choice.file.fact_directory_sha256,
            ),
        )
    )
    return endpoints, files, tuple(sorted(timeouts)), max(counts.values())


def _endpoint_from_record(record: ReportRecord) -> BenchmarkEndpoint:
    row = TargetRow(
        record["target_source"],
        record["target_path"],
        record["target_git_ref"],
        record["target_git_sha"],
        record["target_is_dirty"],
        record["target_label"],
    )
    target = ResolvedTarget(
        TargetRequest(row.label or row.source, row.source, row.label),
        row,
        record["binary_sha256"],
        None,
    )
    return BenchmarkEndpoint(target, record["backend"], record["treatment"])


def _file_from_record(record: ReportRecord) -> FileSpec:
    fact_path = record["fact_directory_path"]
    return FileSpec(
        record["file_path"],
        Path(record["file_path"]),
        record["file_sha256"],
        None if fact_path is None else Path(fact_path),
        record["fact_directory_sha256"],
    )


def _endpoint_id(endpoint: BenchmarkEndpoint) -> str:
    return report_id("endpoint", *endpoint.cache_identity)


def _record_endpoint_id(record: ReportRecord) -> str:
    return report_id("endpoint", record["binary_sha256"], record["backend"], record["treatment"])


def _endpoint_label(endpoint: BenchmarkEndpoint) -> str:
    dirty = " dirty" if endpoint.target.row.is_dirty else ""
    short_git_sha = endpoint.target.row.git_sha[:12]
    target = endpoint.target.display_label
    git = f"{short_git_sha}{dirty}"
    target_and_git = git if target == short_git_sha else f"{target} · {git}"
    return f"{target_and_git} · {endpoint.backend}/{endpoint.treatment}"


def _file_id(file: FileSpec) -> str:
    return report_id("file", file.sha256, file.fact_directory_sha256)


def _record_file_id(record: ReportRecord) -> str:
    return report_id("file", record["file_sha256"], record["fact_directory_sha256"])


def _cell_payload(cell: ReportCell) -> JsonValue:
    primitive = isinstance(cell.raw, (str, int, bool))
    if cell.tone == "default" and primitive and cell.display == _primitive_display(cell.raw):
        return cell.raw
    payload: dict[str, JsonValue] = {"value": cell.raw, "text": cell.display}
    style = _tone_style(cell.tone)
    if style:
        payload["style"] = style
    return payload


def _primitive_display(value: JsonScalar) -> str:
    if value is True:
        return "true"
    if value is False:
        return "false"
    return str(value)


def _tone_style(tone: CellTone) -> dict[str, JsonValue]:
    if tone == "positive":
        return {"color": "green"}
    if tone == "negative":
        return {"color": "red"}
    if tone == "warning":
        return {"color": "yellow"}
    if tone == "error":
        return {"color": "red", "bold": True}
    if tone == "muted":
        return {"dim": True}
    return {}


def _object(value: object, name: str) -> Mapping[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{name} must be a JSON object")
    return cast(Mapping[str, object], value)


def _string(request: Mapping[str, object], key: str) -> str:
    value = request.get(key)
    if not isinstance(value, str):
        raise ValueError(f"{key} must be a string")
    return value


def _string_list(request: Mapping[str, object], key: str) -> tuple[str, ...]:
    value = request.get(key)
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{key} must be a JSON array of strings")
    values = cast(list[str], value)
    if not values:
        raise ValueError(f"{key} must not be empty")
    if len(set(values)) != len(values):
        raise ValueError(f"{key} must not contain duplicates")
    return tuple(values)


def _positive_int(request: Mapping[str, object], key: str) -> int:
    value = request.get(key)
    if isinstance(value, bool) or not isinstance(value, int):
        raise ValueError(f"{key} must be an integer")
    if value < 1:
        raise ValueError(f"{key} must be positive")
    return value


def _require_known(value: str, choices: Mapping[str, object], name: str) -> None:
    if value not in choices:
        raise ValueError(f"unknown {name} id: {value}")


def _require_known_subset(values: Sequence[str], choices: Mapping[str, object], name: str) -> None:
    unknown = tuple(value for value in values if value not in choices)
    if unknown:
        raise ValueError(f"unknown {name} id(s): {', '.join(unknown)}")
