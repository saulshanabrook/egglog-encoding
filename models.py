"""Shared data model: plain dataclasses and type aliases used by every module.

No pandas/pandera at runtime (the schema lives in ``report_frame.py``), so
``tables.py`` imports cleanly under Pyodide.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Literal, TextIO

if TYPE_CHECKING:
    from pandera.typing import DataFrame

    from report_frame import ReportFrame

Status = Literal["success", "timed-out", "failure"]
Treatment = Literal["off", "term", "proofs"]


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
