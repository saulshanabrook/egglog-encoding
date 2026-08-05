#!/usr/bin/env python3
"""Validate the stock-DuckDB 1.5.4 SQL kernel capability fixture."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FIXTURE = REPO_ROOT / "egglog-experimental" / "duckdb" / "tests" / "fixtures" / "stock-duckdb-1.5.4-kernel.sql"

EXPECTED_DUCKDB_SHA256 = "6c5abaff49f07ba3f6b2e41ed1adf338d10fcb2d98777331b285cc97938fb00a"
EXPECTED_DUCKDB_VERSION = b"v1.5.4 (Variegata) 08e34c447b\n"
EXPECTED_FIXTURE_SHA256 = "a4b7c005dec22952ae2ae94edae256aaf016f325776601beb277545f21c81529"
SQL_CLI_ARGUMENTS = (
    "-safe",
    "-no-init",
    "-batch",
    "-bail",
    "-json",
    ":memory:",
    "-f",
)
CLI_ENVIRONMENT = {
    "LANG": "C",
    "LC_ALL": "C",
    "PATH": "/usr/bin:/bin:/usr/sbin:/sbin",
}

VERSION_TIMEOUT_SECONDS = 5.0
PROBE_TIMEOUT_SECONDS = 30.0
LARGE_PROBE_TIMEOUT_SECONDS = 60.0
FIXTURE_TIMEOUT_SECONDS = 100.0
MAX_CAPTURE_BYTES = 4 * 1024 * 1024

# The smallest measured stock-1.5.4 parser/binder boundary is 988 nested unary
# NOT operators.  Seventy-five percent, rounded down to a multiple of 32, is
# the fail-closed compiler admission budget.
KERNEL_DEPTH_CAP = 736
UNARY_NOT_FIRST_FAILURE = 988
LEFT_DEEP_SET_FIRST_FAILURE = 9_979
CTE_DEPENDENCY_FIRST_FAILURE = 998
FLAT_SET_OPERATORS_PROBED = 50_000

EXPECTED_FIXTURE_TESTS = (
    "typed_nested_using_key",
    "recurring_only_strict_antidiff",
    "one_working_multiple_recurring",
    "deterministic_duplicate_fold",
    "fully_parenthesized_multibranch",
    "nullary_surrogate_key",
    "tombstone_reinsert_subsume",
    "repeat_and_first_saturate_iteration",
    "nested_last_child_vs_aggregate_flags",
    "sequence_non_short_circuit_aggregation",
    "same_rank_target_batch_latch",
    "one_fresh_packed2_hot_scc",
    "transactional_metadata_rollback",
    "transactional_metadata_commit",
    "checked_arithmetic_and_lazy_error",
    "partial_arithmetic_definedness",
)
EXPECTED_FIXTURE_STDOUT = b"".join(
    json.dumps(
        [{"test": test, "status": "ok"}],
        ensure_ascii=False,
        separators=(",", ":"),
    ).encode("utf-8")
    + b"\n"
    for test in EXPECTED_FIXTURE_TESTS
)

_FORBIDDEN_ROOT_STATEMENTS = frozenset(
    {
        "SET",
        "RESET",
        "PRAGMA",
        # These wrappers can hide a configuration statement from a first-word
        # check.  The capability fixture needs none of them, so deny them.
        "EXPLAIN",
        "PREPARE",
        "EXECUTE",
    }
)
_WORD_OR_PUNCTUATION = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*|[.,()]")
_DOLLAR_QUOTE = re.compile(r"\$\$|\$[A-Za-z_][A-Za-z0-9_]*\$")


class CheckFailure(RuntimeError):
    """A deterministic capability or provenance check failed."""


class AdmissionError(CheckFailure):
    """SQL is outside the deliberately narrow kernel admission policy."""


@dataclass(frozen=True)
class CommandResult:
    """Captured result of one bounded child process."""

    argv: tuple[str, ...]
    returncode: int
    stdout: bytes
    stderr: bytes


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _resolve_executable(path: Path) -> Path:
    try:
        resolved = path.expanduser().resolve(strict=True)
        mode = resolved.stat().st_mode
    except OSError as error:
        raise CheckFailure(f"DuckDB executable is unavailable: {path}: {error}") from error
    if not stat.S_ISREG(mode):
        raise CheckFailure(f"DuckDB executable is not a regular file: {resolved}")
    if not os.access(resolved, os.X_OK):
        raise CheckFailure(f"DuckDB executable is not executable: {resolved}")
    return resolved


def _copy_verified_executable(source: Path, destination: Path, source_hash: str) -> str:
    """Make and authenticate the private CLI copy that will actually run."""

    try:
        shutil.copyfile(source, destination)
        destination.chmod(stat.S_IRUSR | stat.S_IXUSR)
    except OSError as error:
        raise CheckFailure(f"could not make private DuckDB executable copy: {error}") from error
    executed_hash = _sha256(destination)
    if executed_hash != source_hash:
        raise CheckFailure(f"private DuckDB executable SHA-256 mismatch: source={source_hash}, copy={executed_hash}")
    return executed_hash


def _bounded_excerpt(output: bytes, *, limit: int = 600) -> str:
    text = output.decode("utf-8", errors="backslashreplace").strip()
    return text if len(text) <= limit else f"{text[:limit]}..."


def _run_command(argv: Sequence[str], *, timeout: float) -> CommandResult:
    command = tuple(argv)
    try:
        process = subprocess.Popen(
            command,
            env=CLI_ENVIRONMENT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
    except OSError as error:
        raise CheckFailure(f"could not launch {command[0]}: {error}") from error

    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            process.kill()
        stdout, stderr = process.communicate()
        raise CheckFailure(
            f"command timed out after {timeout:g}s: {command!r}; "
            f"stdout={_bounded_excerpt(stdout)!r}; stderr={_bounded_excerpt(stderr)!r}"
        ) from error

    if len(stdout) > MAX_CAPTURE_BYTES or len(stderr) > MAX_CAPTURE_BYTES:
        raise CheckFailure(f"command output exceeded {MAX_CAPTURE_BYTES} bytes: {command!r}")
    return CommandResult(command, process.returncode, stdout, stderr)


def _run_sql_file(binary: Path, sql_path: Path, *, timeout: float) -> CommandResult:
    # This argv is frozen.  In particular, probes do not append CLI options
    # after the fixture path or weaken safe mode for convenience.
    return _run_command(
        [str(binary), *SQL_CLI_ARGUMENTS, str(sql_path)],
        timeout=timeout,
    )


def _mask_sql(sql: str, *, reject_quoted_identifiers: bool = False) -> str:
    """Mask literals/comments while preserving SQL punctuation and newlines."""

    output: list[str] = []
    state = "code"
    block_depth = 0
    index = 0
    while index < len(sql):
        char = sql[index]
        pair = sql[index : index + 2]

        if state == "code":
            token_boundary = index == 0 or not (sql[index - 1].isalnum() or sql[index - 1] in {"_", "$"})
            if token_boundary and (
                (char in {"E", "e"} and sql[index + 1 : index + 2] == "'")
                or (
                    char in {"U", "u"}
                    and sql[index + 1 : index + 2] == "&"
                    and sql[index + 2 : index + 3] in {"'", '"'}
                )
            ):
                raise AdmissionError("escape-prefixed SQL strings or identifiers are outside the fixture lexer")
            if pair == "--":
                output.extend((" ", " "))
                state = "line_comment"
                index += 2
                continue
            if pair == "/*":
                output.extend((" ", " "))
                state = "block_comment"
                block_depth = 1
                index += 2
                continue
            if char == "'":
                output.append(" ")
                state = "single_quote"
                index += 1
                continue
            if char == '"':
                if reject_quoted_identifiers:
                    raise AdmissionError("quoted SQL identifiers are outside the working-source linter")
                output.append(" ")
                state = "double_quote"
                index += 1
                continue
            if char == "$" and _DOLLAR_QUOTE.match(sql, index):
                raise AdmissionError("dollar-quoted SQL is outside the fixture lexer")
            output.append(char)
            index += 1
            continue

        if state == "line_comment":
            if char == "\n":
                output.append("\n")
                state = "code"
            else:
                output.append(" ")
            index += 1
            continue

        if state == "block_comment":
            if pair == "/*":
                output.extend((" ", " "))
                block_depth += 1
                index += 2
            elif pair == "*/":
                output.extend((" ", " "))
                block_depth -= 1
                index += 2
                if block_depth == 0:
                    state = "code"
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue

        quote = "'" if state == "single_quote" else '"'
        if char == quote:
            if index + 1 < len(sql) and sql[index + 1] == quote:
                output.extend((" ", " "))
                index += 2
            else:
                output.append(" ")
                state = "code"
                index += 1
        else:
            output.append("\n" if char == "\n" else " ")
            index += 1

    if state == "block_comment":
        raise AdmissionError("unterminated SQL block comment")
    if state in {"single_quote", "double_quote"}:
        raise AdmissionError("unterminated SQL quoted value or identifier")
    return "".join(output)


def _admit_sql(sql: str) -> int:
    """Apply the fail-closed textual policy required before CLI execution."""

    if "\x00" in sql:
        raise AdmissionError("NUL bytes are not admitted in SQL source")
    masked = _mask_sql(sql)
    for line in masked.splitlines():
        if line.lstrip().startswith("."):
            raise AdmissionError("DuckDB dot commands are not admitted")

    count = 0
    for statement in masked.split(";"):
        match = re.search(r"[A-Za-z_][A-Za-z0-9_$]*", statement)
        if match is None:
            continue
        root = match.group(0).upper()
        if root in _FORBIDDEN_ROOT_STATEMENTS:
            raise AdmissionError(f"root statement {root} is not admitted")
        count += 1
    if count == 0:
        raise AdmissionError("SQL source contains no executable statement")
    return count


def _working_source_count(recursive_term: str, cte_name: str) -> int:
    """Count every unqualified occurrence of a unique recursive CTE name.

    Compiler-generated sources must use distinct aliases, so any additional
    unqualified occurrence is another working-table read. Qualified
    ``recurring.<cte>`` snapshot reads are deliberately excluded.
    """

    tokens = _WORD_OR_PUNCTUATION.findall(_mask_sql(recursive_term, reject_quoted_identifiers=True))
    lowered = [token.lower() for token in tokens]
    wanted = cte_name.lower()
    count = 0
    for index, token in enumerate(lowered):
        if token != wanted:
            continue
        if index == 0 or lowered[index - 1] != ".":
            count += 1
            continue
        if index < 2 or lowered[index - 2] != "recurring" or (index >= 3 and lowered[index - 3] == "."):
            raise AdmissionError(f"recursive CTE {cte_name} has a non-recurring qualified reference")
    return count


def _admit_working_sources(recursive_term: str, cte_name: str) -> int:
    """Admit zero-source FullRecompute or one-source seminaive recursion."""

    count = _working_source_count(recursive_term, cte_name)
    if count > 1:
        raise AdmissionError(f"recursive term for {cte_name} has {count} working-table sources; expected at most one")
    return count


def _json_documents(output: bytes) -> list[object]:
    try:
        text = output.decode("utf-8")
    except UnicodeDecodeError as error:
        raise CheckFailure("DuckDB stdout was not UTF-8 JSON") from error
    decoder = json.JSONDecoder()
    documents: list[object] = []
    index = 0
    while True:
        while index < len(text) and text[index].isspace():
            index += 1
        if index == len(text):
            return documents
        try:
            document, index = decoder.raw_decode(text, index)
        except json.JSONDecodeError as error:
            raise CheckFailure(f"DuckDB stdout was not a JSON document stream: {error}") from error
        documents.append(document)


def _expect_success(
    name: str,
    result: CommandResult,
    expected_documents: list[object],
) -> None:
    if result.returncode != 0:
        raise CheckFailure(f"{name} exited {result.returncode}; stderr={_bounded_excerpt(result.stderr)!r}")
    if result.stderr:
        raise CheckFailure(f"{name} wrote stderr: {_bounded_excerpt(result.stderr)!r}")
    observed = _json_documents(result.stdout)
    if observed != expected_documents:
        raise CheckFailure(f"{name} JSON mismatch: expected {expected_documents!r}, got {observed!r}")


def _expect_failure(
    name: str,
    result: CommandResult,
    *,
    stderr_fragments: Sequence[bytes],
    expected_stdout: bytes = b"",
) -> None:
    if result.returncode <= 0:
        raise CheckFailure(f"{name} should fail normally, got return code {result.returncode}")
    if result.stdout != expected_stdout:
        raise CheckFailure(f"{name} stdout mismatch: expected {expected_stdout!r}, got {result.stdout!r}")
    for fragment in stderr_fragments:
        if fragment not in result.stderr:
            raise CheckFailure(f"{name} stderr lacks {fragment!r}: {_bounded_excerpt(result.stderr)!r}")


def _write_sql(directory: Path, name: str, sql: str, *, admit: bool = True) -> Path:
    if admit:
        _admit_sql(sql)
    path = directory / f"{name}.sql"
    path.write_text(sql, encoding="utf-8", newline="\n")
    path.chmod(0o600)
    return path


def _run_sql(
    binary: Path,
    directory: Path,
    name: str,
    sql: str,
    *,
    timeout: float = PROBE_TIMEOUT_SECONDS,
    admit: bool = True,
) -> CommandResult:
    return _run_sql_file(
        binary,
        _write_sql(directory, name, sql, admit=admit),
        timeout=timeout,
    )


def _check_version(binary: Path, *, expected: bytes) -> None:
    result = _run_command([str(binary), "--version"], timeout=VERSION_TIMEOUT_SECONDS)
    if result.returncode != 0 or result.stdout != expected or result.stderr:
        raise CheckFailure(
            f"unexpected DuckDB version result: rc={result.returncode}, "
            f"stdout={result.stdout!r}, stderr={result.stderr!r}"
        )


def _check_fixture(binary: Path, snapshot: Path) -> str:
    first = _run_sql_file(binary, snapshot, timeout=FIXTURE_TIMEOUT_SECONDS)
    second = _run_sql_file(binary, snapshot, timeout=FIXTURE_TIMEOUT_SECONDS)
    for run_number, result in enumerate((first, second), start=1):
        if result.returncode != 0:
            raise CheckFailure(
                f"positive fixture run {run_number} exited {result.returncode}: {_bounded_excerpt(result.stderr)!r}"
            )
        if result.stderr:
            raise CheckFailure(f"positive fixture run {run_number} wrote stderr: {_bounded_excerpt(result.stderr)!r}")
        if result.stdout != EXPECTED_FIXTURE_STDOUT:
            raise CheckFailure(f"positive fixture run {run_number} did not match the pinned JSON oracle")
    if first.stdout != second.stdout:
        raise CheckFailure("positive fixture runs were not byte-identical")
    return hashlib.sha256(first.stdout).hexdigest()


def _check_admission_probes(binary: Path, directory: Path) -> None:
    # Hostile occurrences in literals/comments and an UPDATE SET clause remain
    # legal, while direct or wrapped configuration statements fail closed.
    _admit_sql(
        "-- SET threads=8\n"
        "CREATE TEMP TABLE allowed(i INTEGER);\n"
        "UPDATE allowed SET i = 1;\n"
        "SELECT 'SET threads=8' AS quoted;\n"
    )
    for rejected in (
        "SET threads = 1;",
        "EXPLAIN SET threads = 1;",
        r"SELECT E'escaped\' quote';",
        r"SELECT U&'d\0061t';",
        "SELECT $$SET threads = 1$$;",
    ):
        try:
            _admit_sql(rejected)
        except AdmissionError:
            pass
        else:
            raise CheckFailure(f"admission unexpectedly accepted {rejected!r}")

    safe_set = _run_sql(
        binary,
        directory,
        "safe_mode_set",
        "SET threads = 1;\nSELECT 1 AS unreachable;\n",
        admit=False,
    )
    _expect_failure(
        "safe-mode SET",
        safe_set,
        stderr_fragments=(b"Cannot change configuration option", b"configuration has been locked"),
    )

    join_two_term = """
SELECT left_row.key + 1, left_row.value + right_row.value
FROM working_twice AS left_row
JOIN working_twice AS right_row ON right_row.key = left_row.key
WHERE left_row.key < 2
"""
    two_working_sql = f"""
WITH RECURSIVE working_twice(key, value) USING KEY (key) AS (
    (VALUES (0::BIGINT, 1::BIGINT))
    UNION ALL
    ({join_two_term})
)
SELECT max(value) AS value FROM working_twice;
"""
    engine_result = _run_sql(binary, directory, "two_working_engine", two_working_sql)
    _expect_success("two-working engine reference", engine_result, [[{"value": 4}]])

    full_recompute_term = """
SELECT prior.key, least(prior.value + 1, 3)
FROM recurring.full_recompute AS prior
WHERE least(prior.value + 1, 3) IS DISTINCT FROM prior.value
"""
    if _admit_working_sources(full_recompute_term, "full_recompute") != 0:
        raise CheckFailure("zero-source FullRecompute linter probe was misclassified")
    legal_term = """
SELECT working.key + 1,
       (SELECT count(*) FROM recurring.legal_working),
       (SELECT max(key) FROM recurring.legal_working AS snapshot_two)
FROM legal_working AS working
"""
    if _admit_working_sources(legal_term, "legal_working") != 1:
        raise CheckFailure("one-source seminaive linter probe was misclassified")
    seed_then_working_term = """
SELECT working.key + seed.offset
FROM seed AS seed, legal_working AS working
"""
    if _admit_working_sources(seed_then_working_term, "legal_working") != 1:
        raise CheckFailure("seed-first one-source linter probe was misclassified")
    comma_two_term = """
SELECT left_row.key + right_row.key
FROM working_twice AS left_row, working_twice AS right_row
"""
    for name, rejected_term, cte_name in (
        ("JOIN-two", join_two_term, "working_twice"),
        ("comma-two", comma_two_term, "working_twice"),
        ("other-qualified", "SELECT * FROM other.working_twice AS working", "working_twice"),
        ("quoted-source", 'SELECT * FROM "working_twice" AS working', "working_twice"),
    ):
        try:
            _admit_working_sources(rejected_term, cte_name)
        except AdmissionError:
            pass
        else:
            raise CheckFailure(f"{name} working-source linter probe was unexpectedly accepted")
    print(
        "PASS admission set_rejected=true two_working_engine_accepts=true "
        "zero_full_recompute=true one_working=true join_two_rejected=true "
        "comma_two_rejected=true other_qualified_rejected=true quoted_source_rejected=true"
    )


def _check_filtered_rank(binary: Path, directory: Path) -> None:
    sql = """
CREATE TEMP TABLE filtered_rank(id INTEGER PRIMARY KEY);
INSERT INTO filtered_rank VALUES (1), (2), (3);

SELECT
    id,
    row_number() OVER (
        ORDER BY nullif(id % 3, 0) DESC NULLS LAST
    ) AS rn
FROM filtered_rank
QUALIFY rn <= 3
ORDER BY rn;

WITH ranked_input AS (
    SELECT id, nullif(id % 3, 0) AS value
    FROM filtered_rank
)
SELECT
    id,
    row_number() OVER (
        ORDER BY (value IS NULL) ASC, value DESC, id ASC
    ) AS rn
FROM ranked_input
QUALIFY rn <= 3
ORDER BY rn;
"""
    result = _run_sql(binary, directory, "filtered_rank_23677", sql)
    _expect_success(
        "filtered-rank mitigation",
        result,
        [
            [{"id": 2, "rn": 1}, {"id": 1, "rn": 2}],
            [{"id": 2, "rn": 1}, {"id": 1, "rn": 2}, {"id": 3, "rn": 3}],
        ],
    )
    print("PASS probe=filtered_rank_23677 vulnerable_rows=2 mitigated_rows=3 total_key=true")


def _check_late_failure_prefix(binary: Path, directory: Path) -> None:
    sql = """
CREATE TEMP TABLE late_failure(value BIGINT NOT NULL);
INSERT INTO late_failure VALUES (0);
BEGIN TRANSACTION;
UPDATE late_failure SET value = 1;
SELECT
    'retained' AS prefix,
    CASE WHEN FALSE THEN error('unreachable')::BIGINT ELSE 7::BIGINT END AS lazy;
SELECT 9223372036854775807::BIGINT + 1::BIGINT AS overflow;
ROLLBACK;
SELECT 'unreachable' AS trailing;
"""
    result = _run_sql(binary, directory, "late_failure_prefix", sql)
    _expect_failure(
        "late checked-overflow failure",
        result,
        stderr_fragments=(b"Out of Range Error", b"Overflow in addition of INT64"),
        expected_stdout=b'[{"prefix":"retained","lazy":7}]\n',
    )
    checked_guard = _run_sql(
        binary,
        directory,
        "checked_guard_failure",
        """
WITH arithmetic_input(lhs, rhs) AS (
    VALUES (9223372036854775807::HUGEINT, 1::HUGEINT)
)
SELECT CASE
    WHEN lhs + rhs
        BETWEEN '-9223372036854775808'::HUGEINT
            AND '9223372036854775807'::HUGEINT
    THEN (lhs + rhs)::BIGINT
    ELSE error('checked addition overflow')::BIGINT
END AS result
FROM arithmetic_input;
""",
    )
    _expect_failure(
        "selected checked-arithmetic rejection",
        checked_guard,
        stderr_fragments=(b"Invalid Input Error", b"checked addition overflow"),
    )
    raw_division = _run_sql(
        binary,
        directory,
        "raw_partial_arithmetic",
        """
SELECT
    1::BIGINT // 0::BIGINT AS integer_divide,
    1::BIGINT % 0::BIGINT AS integer_remainder;
""",
    )
    _expect_success(
        "raw partial-arithmetic engine observation",
        raw_division,
        [[{"integer_divide": None, "integer_remainder": None}]],
    )
    print(
        "PASS probe=checked_overflow_lazy_error direct_failed=true guard_failed=true "
        "raw_division_null=true prefix_retained=true trailing_suppressed=true"
    )
    print(
        "DEFERRED gate=standalone_command_transaction automatic_post_error_rollback "
        "reason='-bail exits the only :memory: connection before rollback state can be queried'"
    )


_REPEAT_SHAPE_TEMPLATE = """
WITH RECURSIVE repeat_shape(unit, repeat_limit, child_calls) USING KEY (unit) AS (
    (SELECT TRUE, '__N__'::UBIGINT, 0::UBIGINT)
    UNION ALL
    (
        SELECT TRUE, repeat_limit, child_calls + 1
        FROM repeat_shape
        WHERE child_calls < repeat_limit
    )
)
SELECT max(child_calls)::BIGINT AS child_calls FROM repeat_shape;
"""


def _repeat_shape_sql(limit: int) -> str:
    if limit < 0:
        raise CheckFailure("Repeat limit must be non-negative")
    return _REPEAT_SHAPE_TEMPLATE.replace("'__N__'", f"'{limit}'")


def _check_repeat_shape(binary: Path, directory: Path) -> None:
    rendered = {limit: _repeat_shape_sql(limit) for limit in (0, 1, 100_000)}
    for limit, sql in rendered.items():
        normalized = sql.replace(f"'{limit}'", "'__N__'")
        if normalized != _REPEAT_SHAPE_TEMPLATE:
            raise CheckFailure(f"Repeat {limit} rendering changed more than its N literal")
        result = _run_sql(binary, directory, f"repeat_shape_{limit}", sql)
        _expect_success(f"Repeat shape N={limit}", result, [[{"child_calls": limit}]])
    print("PASS probe=repeat_constant_shape limits=0,1,100000 only_n_literals_change=true")


def _unary_not_sql(depth: int) -> str:
    return f"SELECT {'NOT ' * depth}TRUE AS value;\n"


def _left_deep_set_sql(operator_count: int) -> str:
    tree = "(" * operator_count + "SELECT 1 AS value" + " UNION ALL SELECT 1)" * operator_count
    return f"SELECT count(*) AS rows FROM ({tree}) AS set_tree;\n"


def _flat_set_sql(operator_count: int) -> str:
    arms = " UNION ALL ".join("SELECT 1 AS value" for _ in range(operator_count + 1))
    return f"SELECT count(*) AS rows FROM ({arms}) AS flat_set_tree;\n"


def _cte_dependency_sql(dependency_count: int) -> str:
    definitions = ["cte_0 AS (SELECT 1 AS value)"]
    definitions.extend(
        f"cte_{index} AS (SELECT value FROM cte_{index - 1})" for index in range(1, dependency_count + 1)
    )
    return f"WITH {', '.join(definitions)} SELECT value FROM cte_{dependency_count};\n"


def _check_depth_boundaries(binary: Path, directory: Path) -> None:
    derived_cap = (
        (
            min(
                UNARY_NOT_FIRST_FAILURE,
                LEFT_DEEP_SET_FIRST_FAILURE,
                CTE_DEPENDENCY_FIRST_FAILURE,
            )
            * 3
            // 4
        )
        // 32
    ) * 32
    if derived_cap != KERNEL_DEPTH_CAP or KERNEL_DEPTH_CAP < 128:
        raise CheckFailure(f"invalid depth cap {KERNEL_DEPTH_CAP}; measured boundaries derive {derived_cap}")

    unary_cap = _run_sql(
        binary,
        directory,
        "unary_not_cap",
        _unary_not_sql(KERNEL_DEPTH_CAP),
    )
    _expect_success("unary NOT at cap", unary_cap, [[{"value": True}]])
    unary_pass = _run_sql(
        binary,
        directory,
        "unary_not_987",
        _unary_not_sql(UNARY_NOT_FIRST_FAILURE - 1),
    )
    _expect_success("unary NOT highest pass", unary_pass, [[{"value": False}]])
    unary_fail = _run_sql(
        binary,
        directory,
        "unary_not_988",
        _unary_not_sql(UNARY_NOT_FIRST_FAILURE),
    )
    _expect_failure(
        "unary NOT first failure",
        unary_fail,
        stderr_fragments=(b"Max expression depth limit of 1000 exceeded",),
    )

    set_cap = _run_sql(
        binary,
        directory,
        "left_deep_set_cap",
        _left_deep_set_sql(KERNEL_DEPTH_CAP),
        timeout=LARGE_PROBE_TIMEOUT_SECONDS,
    )
    _expect_success(
        "left-deep set at cap",
        set_cap,
        [[{"rows": KERNEL_DEPTH_CAP + 1}]],
    )
    set_pass = _run_sql(
        binary,
        directory,
        "left_deep_set_9978",
        _left_deep_set_sql(LEFT_DEEP_SET_FIRST_FAILURE - 1),
        timeout=LARGE_PROBE_TIMEOUT_SECONDS,
    )
    _expect_success(
        "left-deep set highest pass",
        set_pass,
        [[{"rows": LEFT_DEEP_SET_FIRST_FAILURE}]],
    )
    set_fail = _run_sql(
        binary,
        directory,
        "left_deep_set_9979",
        _left_deep_set_sql(LEFT_DEEP_SET_FIRST_FAILURE),
        timeout=LARGE_PROBE_TIMEOUT_SECONDS,
    )
    _expect_failure(
        "left-deep set first failure",
        set_fail,
        stderr_fragments=(b"Parser Error: memory exhausted",),
    )
    flat_set = _run_sql(
        binary,
        directory,
        "flat_set_50000",
        _flat_set_sql(FLAT_SET_OPERATORS_PROBED),
        timeout=LARGE_PROBE_TIMEOUT_SECONDS,
    )
    _expect_success(
        "flat set through 50000 operators",
        flat_set,
        [[{"rows": FLAT_SET_OPERATORS_PROBED + 1}]],
    )

    cte_cap = _run_sql(
        binary,
        directory,
        "cte_dependencies_cap",
        _cte_dependency_sql(KERNEL_DEPTH_CAP),
    )
    _expect_success("CTE dependencies at cap", cte_cap, [[{"value": 1}]])
    cte_pass = _run_sql(
        binary,
        directory,
        "cte_dependencies_997",
        _cte_dependency_sql(CTE_DEPENDENCY_FIRST_FAILURE - 1),
    )
    _expect_success("CTE dependency highest pass", cte_pass, [[{"value": 1}]])
    cte_fail = _run_sql(
        binary,
        directory,
        "cte_dependencies_998",
        _cte_dependency_sql(CTE_DEPENDENCY_FIRST_FAILURE),
    )
    _expect_failure(
        "CTE dependency first failure",
        cte_fail,
        stderr_fragments=(b"Max expression depth limit of 1000 exceeded",),
    )
    print(
        "PASS probe=depth_boundaries cap=736 unary_not_first_fail=988 "
        "left_deep_set_first_fail=9979 cte_dependency_first_fail=998 "
        "flat_set_passed_through=50000"
    )


def _compatibility_outcome(
    name: str,
    result: CommandResult,
    expected_documents: list[object],
    *,
    failure_stderr_fragments: Sequence[bytes],
) -> str:
    """Classify an adjacent-version boundary without imposing 1.5.4's result."""

    if result.returncode < 0:
        raise CheckFailure(f"{name} terminated by signal {-result.returncode}")
    if result.returncode > 0:
        if result.stdout:
            raise CheckFailure(f"{name} failed after writing stdout: {_bounded_excerpt(result.stdout)!r}")
        for fragment in failure_stderr_fragments:
            if fragment not in result.stderr:
                raise CheckFailure(f"{name} failure lacks {fragment!r}: {_bounded_excerpt(result.stderr)!r}")
        return "fail"
    if result.stderr:
        raise CheckFailure(f"{name} succeeded with stderr: {_bounded_excerpt(result.stderr)!r}")
    observed = _json_documents(result.stdout)
    if observed != expected_documents:
        raise CheckFailure(f"{name} successful JSON mismatch: {observed!r}")
    return "pass"


def _check_compatibility_depth(binary: Path, directory: Path) -> None:
    """Run cap and adjacent 1.5.4-boundary probes on DuckDB 1.5.5."""

    unary_cap = _run_sql(
        binary,
        directory,
        "compat_unary_not_cap",
        _unary_not_sql(KERNEL_DEPTH_CAP),
    )
    _expect_success("compat unary NOT at cap", unary_cap, [[{"value": True}]])
    set_cap = _run_sql(
        binary,
        directory,
        "compat_left_deep_set_cap",
        _left_deep_set_sql(KERNEL_DEPTH_CAP),
        timeout=LARGE_PROBE_TIMEOUT_SECONDS,
    )
    _expect_success(
        "compat left-deep set at cap",
        set_cap,
        [[{"rows": KERNEL_DEPTH_CAP + 1}]],
    )
    cte_cap = _run_sql(
        binary,
        directory,
        "compat_cte_dependencies_cap",
        _cte_dependency_sql(KERNEL_DEPTH_CAP),
    )
    _expect_success("compat CTE dependencies at cap", cte_cap, [[{"value": 1}]])

    unary_previous = _compatibility_outcome(
        "compat unary NOT 987",
        _run_sql(
            binary,
            directory,
            "compat_unary_not_987",
            _unary_not_sql(UNARY_NOT_FIRST_FAILURE - 1),
        ),
        [[{"value": False}]],
        failure_stderr_fragments=(b"Max expression depth limit of 1000 exceeded",),
    )
    unary_boundary = _compatibility_outcome(
        "compat unary NOT 988",
        _run_sql(
            binary,
            directory,
            "compat_unary_not_988",
            _unary_not_sql(UNARY_NOT_FIRST_FAILURE),
        ),
        [[{"value": True}]],
        failure_stderr_fragments=(b"Max expression depth limit of 1000 exceeded",),
    )
    set_previous = _compatibility_outcome(
        "compat left-deep set 9978",
        _run_sql(
            binary,
            directory,
            "compat_left_deep_set_9978",
            _left_deep_set_sql(LEFT_DEEP_SET_FIRST_FAILURE - 1),
            timeout=LARGE_PROBE_TIMEOUT_SECONDS,
        ),
        [[{"rows": LEFT_DEEP_SET_FIRST_FAILURE}]],
        failure_stderr_fragments=(b"Parser Error: memory exhausted",),
    )
    set_boundary = _compatibility_outcome(
        "compat left-deep set 9979",
        _run_sql(
            binary,
            directory,
            "compat_left_deep_set_9979",
            _left_deep_set_sql(LEFT_DEEP_SET_FIRST_FAILURE),
            timeout=LARGE_PROBE_TIMEOUT_SECONDS,
        ),
        [[{"rows": LEFT_DEEP_SET_FIRST_FAILURE + 1}]],
        failure_stderr_fragments=(b"Parser Error: memory exhausted",),
    )
    cte_previous = _compatibility_outcome(
        "compat CTE dependencies 997",
        _run_sql(
            binary,
            directory,
            "compat_cte_dependencies_997",
            _cte_dependency_sql(CTE_DEPENDENCY_FIRST_FAILURE - 1),
        ),
        [[{"value": 1}]],
        failure_stderr_fragments=(b"Max expression depth limit of 1000 exceeded",),
    )
    cte_boundary = _compatibility_outcome(
        "compat CTE dependencies 998",
        _run_sql(
            binary,
            directory,
            "compat_cte_dependencies_998",
            _cte_dependency_sql(CTE_DEPENDENCY_FIRST_FAILURE),
        ),
        [[{"value": 1}]],
        failure_stderr_fragments=(b"Max expression depth limit of 1000 exceeded",),
    )
    matches_1_5_4 = (
        unary_previous,
        unary_boundary,
        set_previous,
        set_boundary,
        cte_previous,
        cte_boundary,
    ) == ("pass", "fail", "pass", "fail", "pass", "fail")
    print(
        "PASS compatibility_depth cap=736 "
        f"unary_987_988={unary_previous}/{unary_boundary} "
        f"left_deep_set_9978_9979={set_previous}/{set_boundary} "
        f"cte_997_998={cte_previous}/{cte_boundary} "
        f"matches_1_5_4={str(matches_1_5_4).lower()}"
    )


def _check_compatibility(binary_argument: Path, snapshot: Path, directory: Path) -> None:
    source_binary = _resolve_executable(binary_argument)
    source_hash = _sha256(source_binary)
    binary = directory / "duckdb-1.5.5-compat"
    executed_hash = _copy_verified_executable(source_binary, binary, source_hash)
    version = _run_command([str(binary), "--version"], timeout=VERSION_TIMEOUT_SECONDS)
    if version.returncode != 0 or version.stderr or not version.stdout.startswith(b"v1.5.5 "):
        raise CheckFailure(
            f"compatibility binary is not a clean DuckDB 1.5.5 CLI: "
            f"rc={version.returncode}, stdout={version.stdout!r}, stderr={version.stderr!r}"
        )
    stdout_hash = _check_fixture(binary, snapshot)
    _check_compatibility_depth(binary, snapshot.parent)
    if _sha256(binary) != executed_hash:
        raise CheckFailure("private DuckDB 1.5.5 compatibility executable changed during the check")
    if _sha256(source_binary) != source_hash:
        raise CheckFailure("source DuckDB 1.5.5 compatibility executable changed during the check")
    print(
        f"PASS compatibility version={version.stdout.decode().strip()!r} "
        f"binary_sha256={executed_hash} private_copy=true minimal_environment=true "
        f"stdout_sha256={stdout_hash}"
    )


def _parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--duckdb", required=True, type=Path, help="pinned stock DuckDB 1.5.4 CLI")
    parser.add_argument(
        "--fixture",
        type=Path,
        default=DEFAULT_FIXTURE,
        help="path to the SHA-256-pinned stock-kernel SQL fixture",
    )
    parser.add_argument(
        "--compat-duckdb",
        type=Path,
        help="optional DuckDB 1.5.5 CLI for a separate fixture and boundary compatibility run",
    )
    return parser.parse_args(list(argv) if argv is not None else None)


def _main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    source_binary = _resolve_executable(args.duckdb)
    source_binary_hash = _sha256(source_binary)
    if source_binary_hash != EXPECTED_DUCKDB_SHA256:
        raise CheckFailure(f"DuckDB SHA-256 mismatch: expected {EXPECTED_DUCKDB_SHA256}, got {source_binary_hash}")

    try:
        fixture = args.fixture.expanduser().resolve(strict=True)
        fixture_bytes = fixture.read_bytes()
        fixture_sql = fixture_bytes.decode("utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise CheckFailure(f"could not read UTF-8 fixture {args.fixture}: {error}") from error
    fixture_hash = hashlib.sha256(fixture_bytes).hexdigest()
    if fixture_hash != EXPECTED_FIXTURE_SHA256:
        raise CheckFailure(f"fixture SHA-256 mismatch: expected {EXPECTED_FIXTURE_SHA256}, got {fixture_hash}")
    statement_count = _admit_sql(fixture_sql)

    with tempfile.TemporaryDirectory(prefix="egglog-duckdb-kernel-") as temporary:
        directory = Path(temporary)
        binary = directory / "duckdb-1.5.4"
        binary_hash = _copy_verified_executable(source_binary, binary, source_binary_hash)
        _check_version(binary, expected=EXPECTED_DUCKDB_VERSION)
        snapshot = directory / fixture.name
        snapshot.write_bytes(fixture_bytes)
        snapshot.chmod(0o600)

        if _sha256(binary) != binary_hash:
            raise CheckFailure("private DuckDB 1.5.4 executable changed before SQL execution")
        stdout_hash = _check_fixture(binary, snapshot)
        print(
            f"PASS provenance version={EXPECTED_DUCKDB_VERSION.decode().strip()!r} "
            f"binary_sha256={binary_hash} private_copy=true minimal_environment=true"
        )
        print(
            f"PASS fixture path={str(fixture)!r} statements={statement_count} "
            f"input_sha256={fixture_hash} stdout_sha256={stdout_hash} deterministic_runs=2"
        )

        _check_admission_probes(binary, directory)
        _check_filtered_rank(binary, directory)
        _check_late_failure_prefix(binary, directory)
        _check_repeat_shape(binary, directory)
        _check_depth_boundaries(binary, directory)

        if args.compat_duckdb is not None:
            _check_compatibility(args.compat_duckdb, snapshot, directory)

        if _sha256(binary) != binary_hash:
            raise CheckFailure("private DuckDB 1.5.4 executable changed during the check")

    if _sha256(source_binary) != source_binary_hash:
        raise CheckFailure("source DuckDB 1.5.4 executable changed during the check")
    try:
        if fixture.read_bytes() != fixture_bytes:
            raise CheckFailure("fixture changed during the check; rerun from a stable checkout")
    except OSError as error:
        raise CheckFailure(f"fixture became unreadable during the check: {error}") from error
    print(
        "PASS stock_duckdb_kernel_check checkpoint=1 status=pass explicit_rollback=true "
        "automatic_post_error_rollback=deferred_to_standalone_command_transaction_gate"
    )
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    """Run the checker and turn deterministic failures into concise diagnostics."""

    try:
        return _main(argv)
    except CheckFailure as error:
        print(f"FAIL {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
