"""Test workload identity, commands, defaults, and prove screening."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from benchmarking import models, targets, workloads
from benchmarking.engines import validate_binary_workload

from .report_fixtures import ROOT


def test_validate_workloads_rejects_duplicate_cache_identities(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same")

    with pytest.raises(ValueError, match=r"first\.egg.*second\.egg.*identical file hashes"):
        workloads.validate_workloads((first, second))


@pytest.mark.parametrize("command", ("prove", "prove-extract"))
def test_resolve_files_rejects_executable_prove_benchmark_file(tmp_path: Path, command: str) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(
        f"; comments may mention (prove ...)\n(datatype Expr)\n({command} (Fact))\n",
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

    with pytest.raises(ValueError, match="explicit prove command"):
        workloads.resolve_files([str(prove_file)], tmp_path)


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

    assert workloads.resolve_files([str(check_file)], tmp_path)[0].sha256 == targets.sha256_file(check_file)


def test_default_workloads_are_the_ten_self_contained_research_cases() -> None:
    files = workloads.resolve_files([], ROOT)
    assert tuple(file.display_path for file in files) == (
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg",
        "egglog/tests/hardboiled_conv1d_32.egg",
        "egglog/tests/luminal-llama.egg",
        "egglog/tests/web-demo/herbie.egg",
        "egglog/tests/papers/misaal-hvx-dot-product.egg",
        "egglog/tests/papers/churchroad-wide-multiply.egg",
        "egglog-experimental/tests/papers/dialegg-nmm40.egg",
        "egglog/tests/papers/speq-preserved-reference-suite.egg",
        "benchmarks/disequality/parameter-analysis.egg",
    )


def test_workload_command_matches_benchmark_behavior() -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "off") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--disequality-encoding",
        "ee",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proofs") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--disequality-encoding",
        "ee",
        "--proofs",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proof-extraction") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--disequality-encoding",
        "ee",
        "--proof-extraction",
        str(file_spec.absolute_path),
    ]
    assert targets.workload_command(ROOT / "egglog-experimental", file_spec, "proof-testing") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--disequality-encoding",
        "ee",
        "--proof-testing",
        str(file_spec.absolute_path),
    ]


def test_egg_workload_command_uses_the_fixed_math_driver_contract() -> None:
    (math,) = workloads.resolve_files(["egglog-experimental/tests/math-microbenchmark-rational.egg"], ROOT)

    assert targets.workload_command(ROOT / "egg-math-benchmark", math, "egg-proof-testing") == [
        str(ROOT / "egg-math-benchmark"),
        "--proof-mode",
        "check",
    ]


def test_egg_treatments_reject_unregistered_workloads(tmp_path: Path) -> None:
    other_path = tmp_path / "other.egg"
    other_path.write_text("(check (= 1 1))")
    other = models.FileSpec("other.egg", other_path, targets.sha256_file(other_path))
    with pytest.raises(ValueError, match="only supports registered Math workloads"):
        validate_binary_workload(other, "egg")


@pytest.mark.parametrize("newline", ["\n", "\r\n"])
def test_standalone_identity_ignores_control_words_in_comments(tmp_path: Path, newline: str) -> None:
    path = tmp_path / "main.egg"
    source = '; input include prove "\n(datatype T (A))\n(check (= (A) (A)))'
    path.write_bytes(source.replace("\n", newline).encode())
    assert workloads.resolve_files([str(path)], tmp_path)[0].sha256 == targets.sha256_file(path)


@pytest.mark.parametrize("note", ("not; a comment", "(", ")", 'escaped "(include file)"'))
def test_proof_after_quoted_text_is_not_hidden(tmp_path: Path, note: str) -> None:
    path = tmp_path / "main.egg"
    path.write_text(f"(let note {json.dumps(note)}) (prove (= 1 1))")
    with pytest.raises(ValueError, match="explicit prove command"):
        workloads.resolve_files([str(path)], tmp_path)


@pytest.mark.parametrize(
    "source", ('(include "other.egg")', '(fail (include "other.egg"))', '(let note "(") (include "other.egg")')
)
def test_benchmark_inputs_reject_includes(tmp_path: Path, source: str) -> None:
    path = tmp_path / "main.egg"
    path.write_text(source)
    with pytest.raises(ValueError, match="self-contained"):
        workloads.resolve_files([str(path)], tmp_path)


@pytest.mark.parametrize(
    "source", ('(input F "rows.csv")', '(fail (input F "rows.csv"))', '(let note "(") (input F "rows.csv")')
)
def test_external_input_commands_are_rejected(tmp_path: Path, source: str) -> None:
    path = tmp_path / "main.egg"
    path.write_text(source)
    with pytest.raises(ValueError, match="self-contained"):
        workloads.resolve_files([str(path)], tmp_path)


def test_shared_exclusions_match_logical_and_physical_configuration(tmp_path: Path) -> None:
    import json

    (tmp_path / "slotted").mkdir()
    (tmp_path / "slotted/a.egg").write_text("(check (= 1 1))")
    (tmp_path / "slotted/a.ref").write_text("{}")
    ignore = tmp_path / "ignore.json"
    ignore.write_text(
        json.dumps(
            [
                {
                    "file": "slotted/*.egg",
                    "treatments": ["slotted-ref-nested"],
                    "kind": "unsupported",
                    "reason": "fixture has no nested representation",
                    "evidence": "a.ref",
                }
            ]
        )
    )
    file = workloads.resolve_files(["slotted/a.egg"], tmp_path, ignore_file=ignore)[0]
    assert file.exclusion_for("slotted", memory_limit_bytes=None) is None
    rule = file.exclusion_for("slotted-ref-nested", memory_limit_bytes=None)
    assert rule is not None and rule.kind == "unsupported"
    assert file.for_binary("slotted-reference").exclusion_for("slotted-ref-nested", memory_limit_bytes=None) == rule


def test_cap_specific_exclusions_do_not_suppress_uncapped_results(tmp_path: Path) -> None:
    import json

    (tmp_path / "a.egg").write_text("(check (= 1 1))")
    ignore = tmp_path / "ignore.json"
    ignore.write_text(
        json.dumps(
            [
                {
                    "file": "a.egg",
                    "treatments": ["proof-testing"],
                    "kind": "resource",
                    "reason": "recorded address-space cap stop",
                    "evidence": "exit 86 in a fresh process",
                    "memory_limit_bytes": 10 * 1024**3,
                }
            ]
        )
    )
    file = workloads.resolve_files(["a.egg"], tmp_path, ignore_file=ignore)[0]
    assert file.exclusion_for("proof-testing", memory_limit_bytes=10 * 1024**3) is not None
    assert file.exclusion_for("proof-testing", memory_limit_bytes=8 * 1024**3) is not None
    assert file.exclusion_for("proof-testing", memory_limit_bytes=None) is None
    assert file.exclusion_for("proof-testing", memory_limit_bytes=16 * 1024**3) is None
    assert file.exclusion_for("off", memory_limit_bytes=10 * 1024**3) is None


@pytest.mark.parametrize("sizes", [None, {}, {"A": [1]}, {"A": [1, True]}, {"A": [-1, 2]}, {"A": [1, 1]}])
def test_expected_failure_requires_a_precise_table_size_difference(tmp_path: Path, sizes: object) -> None:
    source = tmp_path / "case.egg"
    source.write_text("(check (= 1 1))")
    policy = tmp_path / "ignore.json"
    policy.write_text(
        json.dumps(
            [
                {
                    "file": "case.egg",
                    "kind": "expected-failure",
                    "treatments": ["term"],
                    "reason": "tracked bug",
                    "evidence": "issue",
                    "expected_table_sizes": sizes,
                }
            ]
        )
    )
    with pytest.raises(ValueError, match="expected failures require"):
        workloads.resolve_files([str(source)], tmp_path, ignore_file=policy)


def test_expected_failure_is_quarantined_only_for_its_treatment(tmp_path: Path) -> None:
    source = tmp_path / "case.egg"
    source.write_text("(check (= 1 1))")
    policy = tmp_path / "ignore.json"
    policy.write_text(
        json.dumps(
            [
                {
                    "file": "case.egg",
                    "kind": "expected-failure",
                    "treatments": ["term"],
                    "reason": "tracked bug",
                    "evidence": "issue",
                    "expected_table_sizes": {"A": [1, 2]},
                }
            ]
        )
    )
    (file,) = workloads.resolve_files([str(source)], tmp_path, ignore_file=policy)
    excluded = file.exclusion_for("term", memory_limit_bytes=None)
    assert excluded is not None and excluded.kind == "expected-failure"
    assert file.exclusion_for("off", memory_limit_bytes=None) is None
    assert file.exclusion_for("proof-testing", memory_limit_bytes=None) is None


def test_overlapping_exclusions_reject_ambiguous_execution_policy(tmp_path: Path) -> None:
    resource = models.Exclusion("resource", "cap", "capture", ("term",), memory_limit_bytes=10 * 1024**3)
    expected = models.Exclusion("expected-failure", "bug", "issue", ("term",))
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file", exclusions=(resource, expected))
    with pytest.raises(ValueError, match="overlapping benchmark exclusions"):
        file.exclusion_for("term", memory_limit_bytes=10 * 1024**3)
    assert file.exclusion_for("term", memory_limit_bytes=None) == expected
    assert file.exclusion_for("off", memory_limit_bytes=10 * 1024**3) is None
