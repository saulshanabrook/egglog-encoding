"""Paper exports share bound identities, quarantine decisions and Vega statistics."""

from __future__ import annotations

import io
import json
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest
from rich.console import Console

from benchmarking import figures
from benchmarking.engines import Treatment
from benchmarking.figure_results import corpus_view_domains, figure_results, latex_results
from benchmarking.models import Exclusion, FileSpec
from benchmarking.reports.store import GroupedReport, ReportStore

from .report_fixtures import make_record, make_target, write_report
from .test_figures import catalog_fixture


def test_export_statistics_match_shared_executed_vega_fixture() -> None:
    fixture = json.loads(Path(__file__).with_name("figure_statistics.json").read_text())
    grouped = GroupedReport(
        {"groups": fixture["groups"], "exclusions": {}, "grouped_schema_version": 7, "report_schema_version": 9},
        "fixture",
    )
    result = figure_results("slotted-runtime", fixture["inputs"], grouped, 3, 4.302652729749462)
    (comparison,) = result["comparisons"]
    for metric, label in (("runtime", "Runtime"), ("memory", "Peak RSS")):
        expected = fixture["expected"][label]
        values = comparison["metrics"][metric]
        assert values["ratio"] == pytest.approx(expected["ratio"])
        assert values["ci_low"] == pytest.approx(expected["ratio_low"])
        assert values["ci_high"] == pytest.approx(expected["ratio_high"])
        assert values["baseline_n"] == values["candidate_n"] == 3
        assert result["conditions"][1]["metrics"][metric]["mean"] == expected["candidate_mean"]
        assert result["conditions"][1]["metrics"][metric]["ci_low"] == pytest.approx(expected["candidate_ci_low"])
    assert result["conditions"][0]["selected_row_indices"] == [0, 2, 4]
    assert result["conditions"][1]["selected_row_indices"] == [10, 12, 14]
    macros, table = latex_results(result)
    assert macros.startswith("%% GENERATED FILE") and table.startswith("%% GENERATED FILE")
    assert "slotted-runtime/batax-1st-44rules/slotted-no-aliasing-over-slotted-ref-nested/runtime/ratio" in macros
    assert "Kernel/phase" in table and "BATAX / 1st & 3 [" in table
    assert " & 5 [" in table and "Peak RSS" in table
    assert "slotted-no-aliasing / slotted-ref-nested" not in table


def test_exports_preserve_invalid_missing_and_unbounded_results_and_escape_tex() -> None:
    fixture = json.loads(Path(__file__).with_name("figure_statistics.json").read_text())
    for item in fixture["inputs"]:
        item["label"] = r"case_100% & cost$#{}~^\end"
    fixture["groups"][0]["samples"][0]["max_rss_bytes"] = float("nan")
    grouped = GroupedReport(
        {"groups": fixture["groups"], "exclusions": {}, "grouped_schema_version": 7, "report_schema_version": 9},
        "fixture",
    )
    result = figure_results("slotted-runtime", fixture["inputs"], grouped, 3, 4.302652729749462)
    memory = result["comparisons"][0]["metrics"]["memory"]
    assert memory["ratio"] is None and memory["ci_low"] is None
    assert memory["issue"] == "measurement unavailable"
    assert result["conditions"][0]["observations"][0]["max_rss_bytes"] is None
    json.dumps(result, allow_nan=False)
    macros, table = latex_results(result)
    assert "\\textnormal{unavailable}" in macros
    assert r"case\_100\% \& cost\$\#\{\}\textasciitilde{}\textasciicircum{}\textbackslash{}end" in table
    for item in fixture["inputs"]:
        item["selected_row_indices"] = item["selected_row_indices"][:1]
    one = figure_results("slotted-runtime", fixture["inputs"], grouped, 1, None)
    runtime = one["comparisons"][0]["metrics"]["runtime"]
    assert runtime["ratio"] == 3 and runtime["ci_low"] is None
    assert "n < 2" in runtime["issue"]
    assert "CI unavailable" in latex_results(one)[1]
    fixture["groups"][0]["samples"][0]["wall_sec"] = 0.1
    fixture["groups"][0]["samples"][2]["wall_sec"] = 100
    for item in fixture["inputs"]:
        item["selected_row_indices"] = [
            row["row_index"]
            for row in fixture["groups"][0 if item["treatment"] == "slotted-ref-nested" else 1]["samples"][:3]
        ]
    unbounded = figure_results("slotted-runtime", fixture["inputs"], grouped, 3, 4.302652729749462)
    runtime = unbounded["comparisons"][0]["metrics"]["runtime"]
    assert runtime["ratio"] is not None and runtime["ci_low"] is None
    assert runtime["issue"] == "Fieller interval undefined"


def test_corpus_exports_keep_shared_denominators_and_unestablished_coverage_thresholds() -> None:
    fixture = json.loads(Path(__file__).with_name("figure_statistics.json").read_text())
    inputs = []
    groups: list[Any] = []
    for i, (label, baseline, failure) in enumerate(
        (("boundary", 0.2, False), ("failed", 100, True), ("fast", 0.199, False))
    ):
        for j, treatment in enumerate(("off", "proofs")):
            key = {
                "binary_sha256": "current",
                "file_sha256": label,
                "treatment": treatment,
            }
            indices = [i * 10 + j * 3 + k for k in range(3)]
            inputs.append(
                {
                    **fixture["inputs"][j],
                    "label": label,
                    "logical_id": label,
                    "file_sha256": label,
                    "treatment": treatment,
                    "selected_row_indices": indices,
                }
            )
            groups.append(
                {
                    "key": key,
                    "labels": ["figures"],
                    "samples": [
                        {
                            **fixture["groups"][j]["samples"][0],
                            **key,
                            "row_index": index,
                            "wall_sec": baseline * (2 if j else 1),
                            "max_rss_bytes": (2 if j else 1) * 1048576,
                            "status": "failure" if failure and j else "success",
                        }
                        for index in indices
                    ],
                }
            )
    grouped = GroupedReport(
        {"groups": groups, "exclusions": {}, "grouped_schema_version": 7, "report_schema_version": 9}, "fixture"
    )
    result = figure_results("corpus-proof-recording-cdf", inputs, grouped, 3, 4.302652729749462)
    for metric in ("runtime", "memory"):
        coverage = result["coverage"][metric]
        assert coverage["saved_n"] == 3 and coverage["cohort_n"] == 2
        assert coverage["measured_n"] == 1 and coverage["failed_n"] == 1
        assert coverage["too_fast_n"] == 1 and coverage["missing_n"] == 0
        assert coverage["q50"] == 2 and coverage["q95"] is None
    macros, _ = latex_results(result)
    assert r"egglogfigure@corpus-proof-recording-cdf/coverage/runtime/q95\endcsname{\textnormal{unavailable}}" in macros


def test_shared_corpus_fixture_matches_export_counts_and_bound_view_layout(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = json.loads(Path(__file__).with_name("figure_statistics.json").read_text())["corpus"]
    grouped = GroupedReport(
        {"groups": fixture["groups"], "exclusions": {}, "grouped_schema_version": 7, "report_schema_version": 9},
        "fixture",
    )
    result = figure_results("corpus-proof-recording-cdf", fixture["inputs"], grouped, 3, 4.302652729749462)
    for metric in ("runtime", "memory"):
        assert {key: result["coverage"][metric][key] for key in fixture["expected"]} == fixture["expected"]
    assert corpus_view_domains(result) == fixture["view_domains"]
    # The real binder, including its atomic sidecars, must remove the whole
    # composition rather than leaving an empty axis below the detail.
    config = replace(figures.load_config(figures.DEFAULT_CONFIG), rounds=3)
    figure = next(item for item in config.figures if item.name == "corpus-proof-recording-cdf")
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        *[
            make_record(
                i,
                started_at=row["started_at"],
                file_sha256=row["file_sha256"],
                treatment=row["treatment"],
                binary_sha256="current",
                target_label="figures",
                wall_sec=row["wall_sec"],
                max_rss_bytes=row["max_rss_bytes"],
                status=row["status"],
            )
            for i, row in enumerate(row for group in fixture["groups"] for row in group["samples"])
        ],
    )
    files = tuple(
        FileSpec(
            item["label"] + ".egg",
            tmp_path / (item["label"] + ".egg"),
            item["logical_id"],
            exclusions=(Exclusion("expected-failure", "known mismatch", "issue/123", ("proof-testing",)),)
            if item["label"] == "excluded"
            else (),
        )
        for item in fixture["inputs"]
        if item["treatment"] == "off" and item["label"] in ("boundary", "same-rank", "slow", "fast")
    )

    def render(command: list[str], **_kwargs: Any) -> None:
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    figures.render_figures(
        [figures.ResolvedFigure(figure, files, json.loads(figure.spec.read_text()))],
        config,
        ReportStore(report).grouped_report(),
        report,
        make_target(target_label="figures", binary_sha256="current"),
        tmp_path / "out",
        Console(file=io.StringIO()),
        {"workloads": [], "unavailable_cases": []},
    )
    bound = json.loads((tmp_path / "out/corpus-proof-recording-cdf.bound.vl.json").read_text())
    assert len(bound["vconcat"]) == 1
    assert '"name": "cdf_points"' not in json.dumps(bound)
    assert next(p["value"] for p in bound["params"] if p["name"] == "view_domains") == fixture["view_domains"]
    output = json.loads((tmp_path / "out/corpus-proof-recording-cdf.results.json").read_text())
    assert output["provenance"]["view_domains"] == fixture["view_domains"]
    output["conditions"][0]["sample_n"] = 1000
    assert "/n\\endcsname{1000}" in latex_results(output)[0]


@pytest.mark.parametrize("kind", ["expected-failure", "unsupported", "resource"])
def test_recording_aliases_inherit_strict_exclusions_before_collection_and_export(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    kind: Any,
) -> None:
    config = figures.load_config(catalog_fixture(tmp_path))
    strict_rule = Exclusion(kind, "reviewed strict exclusion", "issue/123", ("proof-testing",))
    logical = FileSpec("case.egg", tmp_path / "case.egg", "sha256:file", exclusions=(strict_rule,))
    logical.absolute_path.write_text("(check true)\n")
    monkeypatch.setattr(figures, "resolve_files", lambda *_args: (logical,))
    # Actual resolution projects disjoint alias selectors before collection.
    resolved = figures.resolve_figures(config, [], tmp_path)[0]
    assert logical.exclusion_for("proof-testing", memory_limit_bytes=None) == strict_rule
    timed = resolved.files[0]
    assert (timed.exclusion_for("proofs", memory_limit_bytes=None) is None) == (kind == "expected-failure")
    assert (timed.exclusion_for("proof-testing", memory_limit_bytes=None) is None) == (kind == "expected-failure")
    figure = replace(resolved.figure, treatments=("off", "proofs"))
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        *[
            make_record(
                i,
                started_at=f"2026-10-01T00:00:0{i}Z",
                treatment=cast(Treatment, t),
                target_label="figures",
                max_rss_bytes=1048576,
            )
            for i, t in enumerate(("off", "off", "proofs", "proofs"))
        ],
    )
    grouped = ReportStore(report).grouped_report()

    def render(command: list[str], **_kwargs: Any) -> None:
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    if kind != "expected-failure":
        with pytest.raises(ValueError, match=f"excluded.*{kind}"):
            figures.render_figures(
                [figures.ResolvedFigure(figure, (timed,), resolved.spec)],
                config,
                grouped,
                report,
                make_target(target_label="figures"),
                tmp_path / "out",
                Console(file=io.StringIO()),
                {"workloads": [], "unavailable_cases": []},
            )
        assert not list((tmp_path / "out").iterdir())
        return
    figures.render_figures(
        [figures.ResolvedFigure(figure, (timed,), resolved.spec)],
        config,
        grouped,
        report,
        make_target(target_label="figures"),
        tmp_path / "out",
        Console(file=io.StringIO()),
        {"workloads": [], "unavailable_cases": []},
    )
    result = json.loads((tmp_path / "out/runtime.results.json").read_text())
    assert result["conditions"][1]["exclusion"] is None
    assert result["conditions"][1]["metrics"]["runtime"]["mean"] == 1
    assert result["conditions"][1]["selected_row_indices"] == [2, 3]


@pytest.mark.parametrize("strict_cached", [False, True])
def test_cached_recording_survives_strict_resource_deferral(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, strict_cached: bool
) -> None:
    config = figures.load_config(catalog_fixture(tmp_path))
    rule = Exclusion(
        "resource", "strict proof cap", "probe", ("proof-testing",), memory_limit_bytes=config.memory_limit_bytes
    )
    logical = FileSpec("case.egg", tmp_path / "case.egg", "sha256:file", exclusions=(rule,))
    logical.absolute_path.write_text("(check true)\n")
    monkeypatch.setattr(figures, "resolve_files", lambda *_args: (logical,))
    resolved = figures.resolve_figures(config, [], tmp_path)[0]
    figure = replace(resolved.figure, treatments=("off", "proofs"))
    report = tmp_path / "report.jsonl"
    rows = [
        make_record(
            i,
            started_at=f"2026-10-01T00:00:0{i}Z",
            treatment=cast(Treatment, t),
            target_label="figures",
            max_rss_bytes=1048576,
        )
        for i, t in enumerate(("off", "off", "proofs", "proofs"))
    ]
    if strict_cached:
        rows.extend(
            make_record(
                i,
                started_at=f"2026-10-01T00:00:0{i}Z",
                treatment="proof-testing",
                target_label="figures",
                status="memory-limited",
            )
            for i in (4, 5)
        )
    write_report(report, *rows)
    before = report.read_bytes()

    def render(command: list[str], **_kwargs: Any) -> None:
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    figures.render_figures(
        [figures.ResolvedFigure(figure, resolved.files, resolved.spec)],
        config,
        ReportStore(report).grouped_report(),
        report,
        make_target(target_label="figures"),
        tmp_path / "out",
        Console(file=io.StringIO()),
        {"workloads": [], "unavailable_cases": []},
    )
    result = json.loads((tmp_path / "out/runtime.results.json").read_text())
    recording = result["conditions"][1]
    assert recording["selected_row_indices"] == [2, 3]
    assert recording["exclusion"] is None and recording["validation_issue"] == ""
    assert recording["metrics"]["runtime"]["mean"] == 1
    assert report.read_bytes() == before


def test_recording_alias_manifest_validation_failure_vetoes_exported_successes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    config = figures.load_config(catalog_fixture(tmp_path))
    figure = replace(config.figures[0], treatments=("off", "proofs"))
    file = FileSpec("case.egg", tmp_path / "case.egg", "sha256:file")
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        *[
            make_record(
                i,
                started_at=f"2026-10-01T00:00:0{i}Z",
                treatment=cast(Treatment, t),
                target_label="figures",
                max_rss_bytes=1048576,
            )
            for i, t in enumerate(("off", "off", "proofs", "proofs"))
        ],
    )

    def render(command: list[str], **_kwargs: Any) -> None:
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    with pytest.raises(ValueError, match="Strict failure"):
        figures.render_figures(
            [figures.ResolvedFigure(figure, (file,), json.loads(figure.spec.read_text()))],
            config,
            ReportStore(report).grouped_report(),
            report,
            make_target(target_label="figures"),
            tmp_path / "out",
            Console(file=io.StringIO()),
            {
                "workloads": [
                    {
                        "file_sha256": file.sha256,
                        "family": "eggcc",
                        "label": "case",
                        "validation_failures": {"sha256:bin": "Strict failure"},
                    }
                ],
                "unavailable_cases": [],
            },
        )
    assert not list((tmp_path / "out").iterdir())
