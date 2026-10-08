"""Recompute interactive benchmark catalogs from one immutable cache snapshot.

This module is the environment-neutral core shared by native artifact creation
and the Pyodide browser runtime.  It discovers selector choices from every row
in the grouped snapshot and atomically replaces the published all-sections catalog.
Incomplete selections remain valid so the shared report can show its precise
missing-result cells.  HTML generation, browser startup, and filesystem export
belong in :mod:`interactive`.
"""

from __future__ import annotations

import json
from collections import Counter
from collections.abc import Sequence
from dataclasses import asdict, dataclass, replace
from datetime import datetime
from pathlib import Path
from typing import NotRequired, TypedDict, cast

from ..engines import TREATMENT_SPECS, Engine
from ..models import (
    BenchmarkEndpoint,
    ComparisonSpec,
    DisequalityEncoding,
    EngineBinary,
    FileSpec,
    ResolvedTarget,
    TargetRequest,
    TargetRow,
    Treatment,
)
from .catalog import CellTone, ReportCatalog, ReportCell, ReportMessage, report_id
from .presentation import build_report_catalog, report_file_labels
from .store import GroupedReport, ReportRecord, parse_grouped_report

type JsonScalar = str | int | float | bool | None
type JsonValue = JsonScalar | list[JsonValue] | dict[str, JsonValue]


class _TargetContext(TypedDict):
    source: str
    path: str
    git_ref: str
    git_sha: str
    is_dirty: bool
    label: str | None


class _EndpointContext(TypedDict):
    target: _TargetContext
    binary_sha256: str
    treatment: Treatment
    disequality_encoding: DisequalityEncoding


class _ScopeRequest(TypedDict):
    """The expected request shape emitted by the embedded JavaScript form."""

    baseline_endpoint_id: str
    candidate_endpoint_id: str
    file_ids: list[str]
    timeout_sec: int
    rounds: int
    suite_mode: NotRequired[bool]
    validation_issues: NotRequired[dict[str, str]]
    initial_endpoints: NotRequired[list[_EndpointContext]]
    report_notes: NotRequired[list[str]]


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


class _FileSnapshot(TypedDict):
    display_path: str
    absolute_path: str
    sha256: str
    fact_directory: str | None
    fact_directory_sha256: str


class _EngineInput(_FileSnapshot):
    engine: Engine


class _InitialFile(_FileSnapshot):
    engine_inputs: list[_EngineInput]


class InitialScope(_ScopeRequest):
    """Generated initial selection, including logical-to-physical input bindings."""

    files: list[_InitialFile]


class InteractiveRuntime:
    """Own one cache universe and its last successfully published comparison."""

    def __init__(
        self,
        store: GroupedReport,
        initial_scope: InitialScope,
    ) -> None:
        self._store = store
        (
            self._endpoint_choices,
            self._file_choices,
            self._timeouts,
            self._max_rounds,
        ) = _cache_universe(store.records)
        # Observations identify physical inputs, which can differ from the selected
        # logical file. Keep its initial selection and bindings outside the grouped data.
        choices = {choice.file_id: choice for choice in self._file_choices}
        for logical in initial_scope["files"]:
            file = FileSpec(
                logical["display_path"],
                Path(logical["absolute_path"]),
                logical["sha256"],
                None if logical["fact_directory"] is None else Path(logical["fact_directory"]),
                logical["fact_directory_sha256"],
            )
            file_id = _file_id(file)
            if file_id in choices:
                file = choices[file_id].file
            inputs = tuple(
                (
                    item["engine"],
                    FileSpec(
                        item["display_path"],
                        Path(item["absolute_path"]),
                        item["sha256"],
                        None if item["fact_directory"] is None else Path(item["fact_directory"]),
                        item["fact_directory_sha256"],
                    ),
                )
                for item in logical["engine_inputs"]
            )
            choices[file_id] = _FileChoice(file_id, replace(file, engine_inputs=inputs))
        self._file_choices = tuple(choices.values())
        self._endpoint_by_id = {choice.endpoint_id: choice.endpoint for choice in self._endpoint_choices}
        self._file_by_id = {choice.file_id: choice.file for choice in self._file_choices}

        self._suite_mode = initial_scope.get("suite_mode", False)
        self._validation_issues = initial_scope.get("validation_issues", {})
        self._report_notes = tuple(initial_scope.get("report_notes", ()))
        # Interrupted collection and skipped inputs can have no measurement rows.
        # Seed only absent identities; cached selectors retain latest provenance.
        for context in initial_scope.get("initial_endpoints", []):
            target_row = TargetRow(**context["target"])
            endpoint = BenchmarkEndpoint(
                ResolvedTarget(
                    TargetRequest(target_row.label or target_row.source, target_row.source, target_row.label),
                    target_row,
                    context["binary_sha256"],
                    None,
                    engine_binaries=(
                        EngineBinary(TREATMENT_SPECS[context["treatment"]].engine, context["binary_sha256"], None),
                    ),
                    primary_engine=TREATMENT_SPECS[context["treatment"]].engine,
                ),
                context["treatment"],
                context["disequality_encoding"],
            )
            endpoint_id = _endpoint_id(endpoint)
            if endpoint_id not in self._endpoint_by_id:
                self._endpoint_by_id[endpoint_id] = endpoint
                self._endpoint_choices += (_EndpointChoice(endpoint_id, endpoint),)
        self._timeouts = tuple(sorted({*self._timeouts, initial_scope["timeout_sec"]}))
        scope = self._parse_scope(initial_scope, initial=True)
        self._validation_endpoint_ids = frozenset((scope.baseline_endpoint_id, scope.candidate_endpoint_id))
        self._validation_timeout_sec = scope.timeout_sec
        self._validation_file_ids = frozenset(scope.file_ids)
        self._max_rounds = max(self._max_rounds, scope.rounds)
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
        """Load the browser's typed grouped snapshot and restore its initial scope."""

        store = parse_grouped_report(path.read_bytes(), display_path)
        return cls(store, cast(InitialScope, json.loads(initial_scope_json)))

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
        matching_validation = (
            frozenset((scope.baseline_endpoint_id, scope.candidate_endpoint_id)) == self._validation_endpoint_ids
            and scope.timeout_sec == self._validation_timeout_sec
        )
        validation_issues = []
        for file_id in scope.file_ids:
            if matching_validation and file_id in self._validation_file_ids:
                reason = self._validation_issues.get(file_id)
            else:
                reason = None
            if reason:
                validation_issues.append((self._file_by_id[file_id], reason))
        return ComparisonSpec(
            self._endpoint_by_id[scope.baseline_endpoint_id],
            self._endpoint_by_id[scope.candidate_endpoint_id],
            files,
            scope.rounds,
            scope.timeout_sec,
            validation_issues=tuple(validation_issues),
            suite_mode=self._suite_mode,
            report_notes=self._report_notes,
        )

    def _parse_scope(self, value: object, *, initial: bool = False) -> InteractiveScope:
        if not isinstance(value, dict):
            raise ValueError("scope request must be a JSON object")
        request = cast(_ScopeRequest, value)
        baseline_id = request.get("baseline_endpoint_id")
        candidate_id = request.get("candidate_endpoint_id")
        raw_file_ids = request.get("file_ids")
        timeout_sec = request.get("timeout_sec")
        rounds = request.get("rounds")
        if not isinstance(baseline_id, str) or not isinstance(candidate_id, str):
            raise ValueError("endpoint ids must be strings")
        if not isinstance(raw_file_ids, list) or not all(isinstance(file_id, str) for file_id in raw_file_ids):
            raise ValueError("file_ids must be a list of strings")
        if not isinstance(timeout_sec, int) or isinstance(timeout_sec, bool):
            raise ValueError("timeout_sec must be an integer")
        if not isinstance(rounds, int) or isinstance(rounds, bool):
            raise ValueError("rounds must be an integer")

        if baseline_id not in self._endpoint_by_id:
            raise ValueError(f"unknown baseline endpoint id: {baseline_id}")
        if candidate_id not in self._endpoint_by_id:
            raise ValueError(f"unknown candidate endpoint id: {candidate_id}")
        if baseline_id == candidate_id:
            raise ValueError("baseline and candidate endpoints must be different")
        file_ids = tuple(raw_file_ids)
        if not file_ids:
            raise ValueError("file_ids must not be empty")
        if len(set(file_ids)) != len(file_ids):
            raise ValueError("file_ids must not contain duplicates")
        unknown_files = tuple(file_id for file_id in file_ids if file_id not in self._file_by_id)
        if unknown_files:
            raise ValueError(f"unknown file id(s): {', '.join(unknown_files)}")
        if timeout_sec not in self._timeouts:
            raise ValueError(f"unknown timeout: {timeout_sec}s")
        if rounds < 1:
            raise ValueError("rounds must be positive")
        if rounds > self._max_rounds and not initial:
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


def scope_for_comparison(comparison: ComparisonSpec) -> InitialScope:
    """Serialize one native comparison as the browser runtime's initial scope."""

    scope: InitialScope = {
        "baseline_endpoint_id": _endpoint_id(comparison.baseline),
        "candidate_endpoint_id": _endpoint_id(comparison.candidate),
        "file_ids": [_file_id(file) for file in comparison.files],
        "timeout_sec": comparison.timeout_sec,
        "rounds": comparison.rounds,
        "files": [
            {
                "display_path": file.display_path,
                "absolute_path": str(file.absolute_path),
                "sha256": file.sha256,
                "fact_directory": None if file.fact_directory is None else str(file.fact_directory),
                "fact_directory_sha256": file.fact_directory_sha256,
                "engine_inputs": [
                    {
                        "engine": engine,
                        "display_path": physical.display_path,
                        "absolute_path": str(physical.absolute_path),
                        "sha256": physical.sha256,
                        "fact_directory": None if physical.fact_directory is None else str(physical.fact_directory),
                        "fact_directory_sha256": physical.fact_directory_sha256,
                    }
                    for engine, physical in file.engine_inputs
                ],
            }
            for file in comparison.files
        ],
        "suite_mode": comparison.suite_mode,
        "validation_issues": {_file_id(file): reason for file, reason in comparison.validation_issues},
        "report_notes": list(comparison.report_notes),
        "initial_endpoints": [
            {
                "target": cast(_TargetContext, asdict(endpoint.target.row)),
                "binary_sha256": endpoint.cache_identity[0],
                "treatment": endpoint.treatment,
                "disequality_encoding": endpoint.disequality_encoding,
            }
            for endpoint in (comparison.baseline, comparison.candidate)
        ],
    }
    return scope


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
                choice.endpoint.treatment,
                choice.endpoint.cache_identity[0],
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
    return endpoints, files, tuple(sorted(timeouts)), max(counts.values(), default=0)


def _endpoint_from_record(record: ReportRecord) -> BenchmarkEndpoint:
    row = TargetRow(
        record["target_source"],
        record["target_path"],
        record["target_git_ref"],
        record["target_git_sha"],
        record["target_is_dirty"],
        record["target_label"],
    )
    engine = TREATMENT_SPECS[record["treatment"]].engine
    target = ResolvedTarget(
        TargetRequest(row.label or row.source, row.source, row.label),
        row,
        record["binary_sha256"],
        None,
        engine_binaries=(EngineBinary(engine, record["binary_sha256"], None),),
        primary_engine=engine,
    )
    return BenchmarkEndpoint(target, record["treatment"], record["disequality_encoding"])


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
    return report_id("endpoint", record["binary_sha256"], record["treatment"], record["disequality_encoding"])


def _endpoint_label(endpoint: BenchmarkEndpoint) -> str:
    dirty = " dirty" if endpoint.target.row.is_dirty else ""
    short_git_sha = endpoint.target.row.git_sha[:12]
    target = endpoint.target.display_label
    git = f"{short_git_sha}{dirty}"
    target_and_git = git if target == short_git_sha else f"{target} · {git}"
    encoding = f"/{endpoint.disequality_encoding}" if TREATMENT_SPECS[endpoint.treatment].engine == "egglog" else ""
    return f"{target_and_git} · {endpoint.treatment}{encoding}"


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
    if tone == "emphasis":
        return {"bold": True}
    if tone == "warning":
        return {"color": "yellow"}
    if tone == "error":
        return {"color": "red", "bold": True}
    if tone == "muted":
        return {"dim": True}
    return {}
