"""Test workload identity, commands, fact directories, defaults, and prove screening."""

from __future__ import annotations

from pathlib import Path

import pytest

from benchmarking import models, targets, workloads

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


def test_included_source_content_is_part_of_workload_identity(tmp_path: Path) -> None:
    base = tmp_path / "base.egg"
    base.write_text("(datatype Expr)\n", encoding="utf-8")
    wrapper = tmp_path / "wrapper.egg"
    wrapper.write_text('(include "base.egg")\n(check (= 1 1))\n', encoding="utf-8")

    before = workloads.resolve_files([wrapper.name], tmp_path)[0]
    base.write_text("(datatype Changed)\n", encoding="utf-8")
    after = workloads.resolve_files([wrapper.name], tmp_path)[0]

    assert before.sha256 != targets.sha256_file(wrapper)
    assert before.sha256 != after.sha256
    assert before.working_directory == tmp_path.resolve()


def test_standalone_workload_keeps_raw_file_hash(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")

    resolved = workloads.resolve_files([benchmark_file.name], tmp_path)[0]

    assert resolved.sha256 == targets.sha256_file(benchmark_file)


def test_nested_includes_are_hashed_and_checked_for_prove(tmp_path: Path) -> None:
    nested = tmp_path / "nested.egg"
    nested.write_text("(prove (= 1 1))\n", encoding="utf-8")
    base = tmp_path / "base.egg"
    base.write_text('(include "nested.egg")\n', encoding="utf-8")
    wrapper = tmp_path / "wrapper.egg"
    wrapper.write_text('(include "base.egg")\n', encoding="utf-8")

    identity = workloads.workload_source_identity(wrapper, tmp_path)

    assert identity.files == (wrapper.resolve(), base.resolve(), nested.resolve())
    with pytest.raises(ValueError, match="explicit prove command"):
        workloads.resolve_files([wrapper.name], tmp_path)


def test_include_cycle_is_rejected_before_execution(tmp_path: Path) -> None:
    first = tmp_path / "first.egg"
    second = tmp_path / "second.egg"
    first.write_text('(include "second.egg")\n', encoding="utf-8")
    second.write_text('(include "first.egg")\n', encoding="utf-8")

    with pytest.raises(ValueError, match="include cycle"):
        workloads.resolve_files([first.name], tmp_path)


def test_missing_include_is_rejected_before_execution(tmp_path: Path) -> None:
    wrapper = tmp_path / "wrapper.egg"
    wrapper.write_text('(include "missing.egg")\n', encoding="utf-8")

    with pytest.raises(FileNotFoundError, match="included egglog file does not exist"):
        workloads.resolve_files([wrapper.name], tmp_path)


def test_prove_scan_ignores_comments_strings_and_longer_atoms(tmp_path: Path) -> None:
    check_file = tmp_path / "check.egg"
    check_file.write_text(
        '; (prove (Comment))\n(let text "escaped \\"(prove (String))\\"")\n'
        "(check (= 1 1)) ; (prove (InlineComment))\n(prove-more (NotACommand))\n",
        encoding="utf-8",
    )

    assert not workloads.file_contains_executable_prove_command(check_file)


def test_require_workload_unchanged_detects_included_source_mutation(tmp_path: Path) -> None:
    base = tmp_path / "base.egg"
    base.write_text("(datatype Expr)\n", encoding="utf-8")
    wrapper = tmp_path / "wrapper.egg"
    wrapper.write_text('(include "base.egg")\n', encoding="utf-8")
    file_spec = workloads.resolve_files([wrapper.name], tmp_path)[0]

    base.write_text("(datatype Changed)\n", encoding="utf-8")

    with pytest.raises(ValueError, match=r"workload changed during execution: wrapper\.egg"):
        workloads.require_workload_unchanged(file_spec)


def test_default_workloads_are_the_six_research_cases() -> None:
    files = workloads.resolve_files([], ROOT)
    assert tuple(file.display_path for file in files) == (
        "benchmarks/math-microbenchmark/math-run-010.egg",
        "egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg",
        "benchmarks/pointer-analysis-initdb.egg",
        "egglog/tests/hardboiled_conv1d_32.egg",
        "benchmarks/luminal-llama.egg",
        "egglog/tests/web-demo/herbie.egg",
    )
    math = next(file for file in files if file.display_path.endswith("math-run-010.egg"))
    assert math.sha256 != targets.sha256_file(math.absolute_path)
    pointer = next(file for file in files if file.display_path == "benchmarks/pointer-analysis-initdb.egg")
    assert pointer.fact_directory == (ROOT / "benchmarks/data/pointer-analysis-initdb").resolve()
    assert pointer.fact_directory_sha256.startswith("sha256:")


def test_pointer_initdb_facts_are_the_complete_consumed_artifact_relations() -> None:
    fact_directory = ROOT / "benchmarks/data/pointer-analysis-initdb"
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

    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "main", "off") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "dd", "proofs") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--backend",
        "dd",
        "--proofs",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "main", "proof-extraction") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--proof-extraction",
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
    command = targets.workload_command(ROOT / "egglog-experimental", file_with_facts, "main", "proofs")
    assert command[5:7] == ["--fact-directory", str(facts)]
