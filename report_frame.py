"""Pandera schema and validation for the benchmark report frame.

Kept separate from ``models.py``/``tables.py`` so pandera stays off the compute
path, which must import under Pyodide (where pandera is unavailable). Only the
Python-side runner and terminal renderer import this.
"""

from __future__ import annotations

from typing import Any

import pandas as pd
import pandera.pandas as pa
from pandera.typing import DataFrame, Series

from models import BACKEND_SPECS


class ReportFrame(pa.DataFrameModel):
    class Config:
        strict = True
        coerce = True

    row_index: Series[int] = pa.Field(ge=0)
    started_at: Series[pd.Timestamp]
    status: Series[str] = pa.Field(isin=["success", "timed-out", "failure"])
    target_label: Series[str] = pa.Field(nullable=True)
    target_source: Series[str]
    target_path: Series[str]
    target_git_ref: Series[str]
    target_git_sha: Series[str]
    target_is_dirty: Series[bool]
    binary_sha256: Series[str]
    file_path: Series[str]
    file_sha256: Series[str]
    backend: Series[str] = pa.Field(isin=list(BACKEND_SPECS))
    treatment: Series[str] = pa.Field(isin=["off", "term", "proofs"])
    timeout_sec: Series[int] = pa.Field(gt=0)
    wall_sec: Series[float] = pa.Field(nullable=True, ge=0)
    user_sec: Series[float] = pa.Field(nullable=True, ge=0)
    system_sec: Series[float] = pa.Field(nullable=True, ge=0)
    cpu_wall_ratio: Series[float] = pa.Field(nullable=True, ge=0)
    max_rss_bytes: Series[int] = pa.Field(nullable=True, ge=0, coerce=True)
    error_exit_code: Series[int] = pa.Field(nullable=True, coerce=True)
    error_signal: Series[int] = pa.Field(nullable=True, coerce=True)
    error_message: Series[str] = pa.Field(nullable=True)

    @pa.dataframe_check
    def success_rows_have_wall_time(cls, frame: pd.DataFrame) -> pd.Series[Any]:  # type: ignore[misc]
        return frame["status"].ne("success") | frame["wall_sec"].notna()

    @pa.dataframe_check
    def timeout_rows_have_no_timing(cls, frame: pd.DataFrame) -> pd.Series[Any]:  # type: ignore[misc]
        timing_columns = ["wall_sec", "user_sec", "system_sec", "cpu_wall_ratio", "max_rss_bytes"]
        return frame["status"].ne("timed-out") | frame[timing_columns].isna().all(axis=1)


def report_columns() -> list[str]:
    return list(ReportFrame.to_schema().columns)


def persisted_report_columns() -> list[str]:
    return [column for column in report_columns() if column != "row_index"]


def validate_report_frame(frame: pd.DataFrame) -> DataFrame[ReportFrame]:
    return DataFrame[ReportFrame](ReportFrame.validate(frame, lazy=True))
