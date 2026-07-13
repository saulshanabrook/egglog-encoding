"""Shared data model: plain dataclasses and type aliases used by every module.

No pandas/pandera at runtime (the schema lives in ``report_frame.py``), so
``tables.py`` imports cleanly under Pyodide.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Any, Literal, TextIO, cast

if TYPE_CHECKING:
    from pandera.typing import DataFrame

    from report_frame import ReportFrame

Status = Literal["success", "timed-out", "failure"]
Treatment = Literal["off", "term", "proofs"]

# Result classification vocabulary shared by the classifiers and both renderers.
# Meaning is centralized here; the Rich (cli) and CSS (eval-live) style maps that
# interpret these are renderer-specific.
ResultStatus = Literal[
    "faster",
    "slower",
    "less",
    "more",
    "unclear",
    "established",
    "not established",
    "point only",
    "invalid",
    "descriptive",
]
RESULT_STATUSES: tuple[ResultStatus, ...] = (
    "faster",
    "slower",
    "less",
    "more",
    "unclear",
    "established",
    "not established",
    "point only",
    "invalid",
    "descriptive",
)


@dataclass(frozen=True)
class TargetRow:
    source: str
    path: str
    git_ref: str
    git_sha: str
    is_dirty: bool
    label: str | None = None


@dataclass(frozen=True)
class FileSpec:
    display_path: str
    absolute_path: Path
    sha256: str


@dataclass(frozen=True)
class BenchmarkSpec:
    files: tuple[FileSpec, ...]
    treatments: tuple[Treatment, ...]
    rounds: int
    timeout_sec: int


@dataclass(frozen=True)
class ReportDestination:
    path: Path | None
    stream: TextIO | None = None

    @property
    def display_path(self) -> str:
        return "-" if self.path is None else str(self.path)


@dataclass(frozen=True)
class TargetRequest:
    raw: str
    source: str
    label: str | None

    @property
    def is_label_lookup(self) -> bool:
        return self.label is not None and self.source == ""


@dataclass(frozen=True)
class ResolvedTarget:
    request: TargetRequest
    row: TargetRow
    binary_sha256: str
    binary_path: Path | None

    @property
    def display_label(self) -> str:
        if self.row.label:
            return self.row.label
        if self.row.git_ref != "HEAD":
            return self.row.git_ref
        if self.row.git_sha:
            return self.row.git_sha[:12]
        return Path(self.row.path).name


@dataclass(frozen=True)
class EstimateKey:
    binary_sha256: str
    file_sha256: str
    treatment: Treatment
    timeout_sec: int


@dataclass(frozen=True)
class CellSummary:
    rows: DataFrame[ReportFrame]
    samples: tuple[float, ...]
    status_counts: dict[str, int]
    mean: float | None
    ci_low: float | None
    ci_high: float | None
    issue: str | None

    @property
    def ok(self) -> bool:
        return self.issue is None and self.mean is not None


CellMap = dict[tuple[str, Treatment], CellSummary]
TargetCellMaps = dict[ResolvedTarget, CellMap]


@dataclass(frozen=True)
class RatioSummary:
    point: float | None
    ci_low: float | None
    ci_high: float | None
    issue: str | None

    @property
    def ok(self) -> bool:
        return self.issue is None and self.point is not None


@dataclass(frozen=True)
class ReportTarget:
    """A target in the active report scope — a serializable projection of a
    ``ResolvedTarget`` (no binary path). ``binary_sha256`` is the grouping identity;
    ``label`` is for display."""

    binary_sha256: str
    label: str
    source: str
    path: str
    git_ref: str
    git_sha: str
    is_dirty: bool


@dataclass(frozen=True)
class ReportFile:
    sha256: str
    display_path: str


@dataclass(frozen=True)
class ReportSelection:
    """Authoritative scope of a report: exactly which targets, files, treatments,
    rounds, and timeout the active run measured. Built by the runner and carried
    into every renderer (serialized into eval-live ``metadata`` for the browser),
    so no renderer reconstructs scope from historical cache rows."""

    targets: tuple[ReportTarget, ...]
    files: tuple[ReportFile, ...]
    treatments: tuple[Treatment, ...]
    rounds: int
    timeout_sec: int


def build_report_selection(targets: Sequence[ResolvedTarget], spec: BenchmarkSpec) -> ReportSelection:
    """The authoritative scope for a run — built by the runner from resolved targets."""
    return ReportSelection(
        targets=tuple(
            ReportTarget(
                binary_sha256=target.binary_sha256,
                label=target.display_label,
                source=target.row.source,
                path=target.row.path,
                git_ref=target.row.git_ref,
                git_sha=target.row.git_sha,
                is_dirty=target.row.is_dirty,
            )
            for target in targets
        ),
        files=tuple(ReportFile(sha256=file.sha256, display_path=file.display_path) for file in spec.files),
        treatments=spec.treatments,
        rounds=spec.rounds,
        timeout_sec=spec.timeout_sec,
    )


def report_selection_to_dict(selection: ReportSelection) -> dict[str, Any]:
    """JSON-safe dict for embedding in the eval-live page."""
    return {
        "targets": [asdict(target) for target in selection.targets],
        "files": [asdict(file) for file in selection.files],
        "treatments": list(selection.treatments),
        "rounds": selection.rounds,
        "timeout_sec": selection.timeout_sec,
    }


def report_selection_from_dict(data: dict[str, Any]) -> ReportSelection:
    return ReportSelection(
        targets=tuple(ReportTarget(**target) for target in data["targets"]),
        files=tuple(ReportFile(**file) for file in data["files"]),
        treatments=cast("tuple[Treatment, ...]", tuple(data["treatments"])),
        rounds=int(data["rounds"]),
        timeout_sec=int(data["timeout_sec"]),
    )


def selection_targets(selection: ReportSelection) -> list[ResolvedTarget]:
    """Rebuild ``ResolvedTarget`` objects (no binary path) from the selection.

    Lossless for rendering: ``binary_sha256`` is the grouping identity and
    ``row.label`` carries the display label, so ``display_label`` round-trips.
    """
    resolved: list[ResolvedTarget] = []
    for target in selection.targets:
        row = TargetRow(
            source=target.source,
            path=target.path,
            git_ref=target.git_ref,
            git_sha=target.git_sha,
            is_dirty=target.is_dirty,
            label=target.label,
        )
        request = TargetRequest(raw=target.source, source=target.source, label=target.label)
        resolved.append(ResolvedTarget(request=request, row=row, binary_sha256=target.binary_sha256, binary_path=None))
    return resolved


def selection_spec(selection: ReportSelection) -> BenchmarkSpec:
    files = tuple(
        FileSpec(display_path=file.display_path, absolute_path=Path(file.display_path), sha256=file.sha256)
        for file in selection.files
    )
    return BenchmarkSpec(
        files=files, treatments=selection.treatments, rounds=selection.rounds, timeout_sec=selection.timeout_sec
    )
