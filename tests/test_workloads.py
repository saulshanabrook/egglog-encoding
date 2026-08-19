"""Test workload identity, commands, fact directories, defaults, and prove screening."""

from __future__ import annotations

from pathlib import Path

import pytest

from benchmarking import models, targets, workloads
from benchmarking.engines import validate_engine_workload

from .report_fixtures import ROOT


def test_validate_workloads_rejects_duplicate_cache_identities(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts")

    with pytest.raises(ValueError, match=r"first\.egg.*second\.egg.*identical file and fact-directory hashes"):
        workloads.validate_workloads((first, second))


def test_same_file_with_different_fact_contents_is_a_distinct_workload(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts-a")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts-b")

    workloads.validate_workloads((first, second))


def test_resolve_files_rejects_executable_prove_benchmark_file(tmp_path: Path) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(prove (Fact))\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="explicit prove command"):
        workloads.resolve_files([str(prove_file)], tmp_path)


@pytest.mark.parametrize(
    "source",
    (
        "(check (= 1 1)) (prove (= 1 1))\n",
        "( check (= 1 1))\n( ; comment between the parenthesis and command\n prove (= 1 1))\n",
    ),
)
def test_prove_scan_detects_top_level_commands_beyond_line_starts(tmp_path: Path, source: str) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(source, encoding="utf-8")

    assert workloads.file_contains_executable_prove_command(prove_file)


def test_resolve_files_allows_prove_mentions_in_comments(tmp_path: Path) -> None:
    check_file = tmp_path / "check.egg"
    check_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(check (Fact))\n",
        encoding="utf-8",
    )

    assert workloads.resolve_files([str(check_file)], tmp_path)[0].absolute_path == check_file.resolve()


def test_prove_scan_ignores_comments_strings_and_longer_atoms(tmp_path: Path) -> None:
    check_file = tmp_path / "check.egg"
    check_file.write_text(
        '; (prove (Comment))\n(let text "escaped \\"(prove (String))\\"")\n'
        "(check (= 1 1)) ; (prove (InlineComment))\n(prove-more (NotACommand))\n",
        encoding="utf-8",
    )

    assert not workloads.file_contains_executable_prove_command(check_file)


def test_default_workloads_are_the_ten_research_cases() -> None:
    files = workloads.resolve_files([], ROOT)
    assert tuple(file.display_path for file in files) == (
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg",
        "egglog/tests/pointer-analysis-initdb.egg",
        "egglog/tests/hardboiled_conv1d_32.egg",
        "egglog/tests/luminal-llama.egg",
        "egglog/tests/web-demo/herbie.egg",
        "egglog/tests/papers/misaal-hvx-dot-product.egg",
        "egglog/tests/papers/churchroad-wide-multiply.egg",
        "egglog-experimental/tests/papers/dialegg-nmm40.egg",
        "egglog/tests/papers/speq-preserved-reference-suite.egg",
    )
    pointer = next(file for file in files if file.display_path == "egglog/tests/pointer-analysis-initdb.egg")
    assert pointer.fact_directory == (ROOT / "egglog/tests/pointer-analysis-initdb").resolve()
    assert pointer.fact_directory_sha256.startswith("sha256:")


def test_disequality_suite_contains_the_two_large_proof_workloads() -> None:
    expected = (
        workloads.WorkloadConfig("egglog-experimental/benchmarks/disequality/euf-614981-model-0000.egg"),
        workloads.WorkloadConfig(
            file="egglog-experimental/tests/disequality/parameter-analysis.egg",
            fact_directory="egglog-experimental/benchmarks/disequality/parameter-analysis-facts",
            prepare_command="make disequality-parameter-facts",
        ),
    )
    assert expected == workloads.DISEQUALITY_WORKLOADS


def test_disequality_euf_benchmark_is_the_substantial_captured_model() -> None:
    path = ROOT / "egglog-experimental/benchmarks/disequality/euf-614981-model-0000.egg"
    source = path.read_text(encoding="utf-8")

    assert source.count("  (let term") == 3_199
    assert source.count("  (union ") == 1_442
    assert source.count("  (disequal ") == 447
    assert not workloads.file_contains_executable_prove_command(path)


def test_disequality_suite_assigns_facts_only_to_parameter_analysis(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    euf = tmp_path / "euf.egg"
    euf.write_text("(check (= 1 1))\n", encoding="utf-8")
    parameter = tmp_path / "parameter.egg"
    parameter.write_text('(relation Edge (i64 i64))\n(input Edge "edges.tsv")\n', encoding="utf-8")
    facts = tmp_path / "facts"
    facts.mkdir()
    (facts / "edges.tsv").write_text("1\t2\n", encoding="utf-8")
    monkeypatch.setitem(
        workloads.WORKLOAD_SUITES,
        "test-disequality",
        (
            workloads.WorkloadConfig("euf.egg"),
            workloads.WorkloadConfig(
                file="parameter.egg",
                fact_directory="facts",
                prepare_command="make facts",
            ),
        ),
    )

    resolved = workloads.resolve_files([], tmp_path, suite="test-disequality")

    assert resolved[0].fact_directory is None
    assert resolved[1].fact_directory == facts.resolve()
    assert resolved[1].fact_directory_sha256 == targets.sha256_directory(facts)


def test_disequality_suite_missing_facts_reports_preparation_command(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    program = tmp_path / "parameter.egg"
    program.write_text('(relation Edge (i64 i64))\n(input Edge "edges.tsv")\n', encoding="utf-8")
    monkeypatch.setitem(
        workloads.WORKLOAD_SUITES,
        "test-disequality",
        (
            workloads.WorkloadConfig(
                file="parameter.egg",
                fact_directory="facts",
                prepare_command="make facts",
            ),
        ),
    )

    with pytest.raises(FileNotFoundError, match="make facts"):
        workloads.resolve_files([], tmp_path, suite="test-disequality")


def test_named_suite_cannot_be_combined_with_explicit_files(tmp_path: Path) -> None:
    program = tmp_path / "input.egg"
    program.write_text("(check (= 1 1))\n", encoding="utf-8")

    with pytest.raises(ValueError, match="cannot be combined"):
        workloads.resolve_files(["input.egg"], tmp_path, suite="disequality")


def test_pointer_initdb_facts_are_the_complete_consumed_artifact_relations() -> None:
    fact_directory = ROOT / "egglog/tests/pointer-analysis-initdb"
    files = tuple(sorted(fact_directory.glob("*.csv")))

    assert len(files) == 23
    assert sum(len(path.read_text(encoding="utf-8").splitlines()) for path in files) == 73_864
    assert targets.sha256_directory(fact_directory) == (
        "sha256:28354d7f25d8c198d923be014bbb1ee2292501e12cdde29ea90e666bc86b6929"
    )


def test_explicit_fact_directory_is_resolved_and_hashed(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "input.egg"
    benchmark_file.write_text('(input Edge "edge.tsv")\n', encoding="utf-8")
    facts = tmp_path / "facts"
    facts.mkdir()
    (facts / "edge.tsv").write_text("a\tb\n", encoding="utf-8")

    (file_spec,) = workloads.resolve_files(["input.egg"], tmp_path, "facts")

    assert file_spec.fact_directory == facts.resolve()
    assert file_spec.fact_directory_sha256 == targets.sha256_directory(facts)


def test_fact_directory_requires_explicit_benchmark_file(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="requires at least one explicit benchmark file"):
        workloads.resolve_files([], tmp_path, "facts")


def test_workload_command_matches_benchmark_behavior() -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "off") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proofs") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--proofs",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proof-extraction") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--proof-extraction",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proof-testing") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--proof-testing",
        str(file_spec.absolute_path),
    ]

    facts = ROOT / "facts"
    file_with_facts = models.FileSpec(
        "file.egg",
        ROOT / "file.egg",
        "sha256:file",
        facts,
        "sha256:facts",
    )
    command = targets.workload_command(ROOT / "egglog-experimental", file_with_facts, "proofs")
    assert command[5:7] == ["--fact-directory", str(facts)]


def test_egg_workload_command_uses_the_fixed_math_driver_contract() -> None:
    (math,) = workloads.resolve_files(["egglog-experimental/tests/math-microbenchmark-rational.egg"], ROOT)

    assert targets.workload_command(ROOT / "egg-math-benchmark", math, "egg-proof-testing") == [
        str(ROOT / "egg-math-benchmark"),
        "--proof-mode",
        "check",
    ]


def test_egg_treatments_reject_other_workloads_and_fact_directories() -> None:
    other = models.FileSpec("other.egg", ROOT / "other.egg", "sha256:other")
    with pytest.raises(ValueError, match="only supports egglog-experimental/tests/math-microbenchmark-rational.egg"):
        validate_engine_workload(other, "egg")

    math = models.FileSpec(
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        ROOT / "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "sha256:math",
        ROOT / "facts",
    )
    with pytest.raises(ValueError, match="does not support --fact-directory"):
        validate_engine_workload(math, "egg-proofs")
