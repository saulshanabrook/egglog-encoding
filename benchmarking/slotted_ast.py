"""Compile-only program-size exports for the restricted SDQL comparison."""

from __future__ import annotations

import csv
import hashlib
import io
import json
import subprocess
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from .config import DEFAULT_AST_CACHE
from .models import FileSpec, validate_unique_file_identities
from .targets import git_sha, sha256_file

ROOT = Path(__file__).resolve().parents[1]
STAGES = ("source", "slotted", "proof_congruence")
CACHE_VERSION = 1
PIPELINE = {"no_aliasing": True, "proof_mode": "Prove", "count": "sexp-list-atom-literal-v1"}
COLUMNS = ("Benchmark", "Input", "Slotted (s)", "Slotted + proofs (scp)")
NOTE = (
    "Whole-program S-expression AST nodes: each list, atom, and literal counts once; "
    "comments and whitespace do not count. These sizes describe the recorded input and compiler "
    "identities, not the checkout at rendering time. Compare their hashes separately with the timing "
    "figure. The second column of sizes is the recorded restricted-aliasing "
    "Slotted compiler output with proofs disabled. The output columns are independently compiled "
    "configurations, not consecutive intermediates. The final column first applies the public Slotted source proof "
    "profile (Compiler::compile_program with ProofMode::Prove), then lowers accepted output through "
    "core congruence and proof instrumentation. Each cached outcome retains that compiler's result "
    "and diagnostic. Counts cover emitted commands, excluding retained source programs and Rust "
    "implementations of runtime commands. Proof-compatible Check "
    "sizes and congruence-only attempts are separate diagnostics, not substitutes for the final "
    "Proofs stage. Compilation only: no saturation, proof extraction, or verification runs. These "
    "sizes do not establish proof correctness. Unsupported means compilation rejected the source "
    "profile or subsequent composition; a partially lowered program is not counted."
)


def slotted_ast_records(
    files: Sequence[FileSpec],
    cache: Path = Path(DEFAULT_AST_CACHE),
    *,
    collect: bool = False,
    compiler: Path | None = None,
) -> tuple[dict[str, Any], ...]:
    """Select one stored compiler cohort; explicitly collect missing identities."""
    validate_unique_file_identities(files)
    records = [json.loads(line) for line in cache.read_text(encoding="utf-8").splitlines()] if cache.exists() else []
    records = [record for record in records if record["version"] == CACHE_VERSION and record["pipeline"] == PIPELINE]
    if collect and compiler is None:
        built = subprocess.run(
            [
                "cargo",
                "build",
                "--locked",
                "--release",
                "-p",
                "egglog-experimental",
                "--example",
                "slotted_ast",
                "--message-format=json",
            ],
            cwd=ROOT,
            encoding="utf-8",
            stdout=subprocess.PIPE,
            check=True,
        )
        compiler = next(
            Path(message["executable"])
            for line in built.stdout.splitlines()
            if (message := json.loads(line)).get("reason") == "compiler-artifact"
            and message["target"]["name"] == "slotted_ast"
            and message.get("executable")
        )
    compiler_sha = (
        sha256_file(compiler) if compiler is not None else (records[-1]["compiler_binary_sha256"] if records else None)
    )
    indexed = {
        record["row"]["file_sha256"]: record for record in records if record["compiler_binary_sha256"] == compiler_sha
    }
    missing = [file for file in files if file.sha256 not in indexed]
    if missing and not collect:
        raise ValueError(f"AST cache {cache} is missing {len(missing)} inputs; use --collect to populate it")
    if missing:
        assert compiler is not None
        completed = subprocess.run(
            [str(compiler.resolve()), *(str(file.absolute_path) for file in missing)],
            cwd=ROOT,
            encoding="utf-8",
            stdout=subprocess.PIPE,
            check=True,
        )
        measured = [json.loads(line) for line in completed.stdout.splitlines()]
        if [row["file"] for row in measured] != [str(file.absolute_path) for file in missing]:
            raise ValueError("AST compiler returned a different workload selection")
        pending = []
        revision = git_sha(ROOT)
        for file, row in zip(missing, measured, strict=True):
            programs = row.pop("programs")
            source_hash = "sha256:" + hashlib.sha256(programs["source"].encode()).hexdigest()
            if source_hash != file.sha256 or sha256_file(Path(row.pop("compiler_binary"))) != compiler_sha:
                raise ValueError(f"AST compiler or input changed: {file.display_path}")
            native = file.for_binary("slotted-reference")
            row.update(
                file=file.display_path,
                file_sha256=source_hash,
                reference_file=native.display_path,
                reference_sha256=native.sha256,
                program_sha256={
                    stage: "sha256:" + hashlib.sha256(program.encode()).hexdigest()
                    for stage, program in programs.items()
                    if program is not None
                },
            )
            pending.append(
                {
                    "version": CACHE_VERSION,
                    "pipeline": PIPELINE,
                    "compiler_binary": str(compiler.resolve()),
                    "compiler_binary_sha256": compiler_sha,
                    "source_checkout": str(ROOT),
                    "source_revision": revision,
                    "row": row,
                }
            )
        cache.parent.mkdir(parents=True, exist_ok=True)
        with cache.open("a", encoding="utf-8") as handle:
            for record in pending:
                handle.write(json.dumps(record, ensure_ascii=False) + "\n")
                indexed[record["row"]["file_sha256"]] = record
    return tuple(indexed[file.sha256] for file in files)


def export_slotted_ast(records: Sequence[dict[str, Any]], destination: Path) -> tuple[Path, ...]:
    """Render a persisted measurement snapshot without inspecting inputs or compilers."""
    rows = []
    for record in records:
        row = dict(record["row"])
        row["measurement_source"] = {
            key: record[key] for key in ("source_checkout", "source_revision", "compiler_binary_sha256")
        }
        kernel, separator, phase = row["benchmark"].removesuffix("-44rules").rpartition("_")
        publication = {"batax": "BATAX", "mmm": "MMM", "mmm_sum": "ΣMMM", "mttkrp": "MTTKRP", "ttm": "TTM"}
        row["label"] = f"{publication.get(kernel, kernel)} / {phase}" if separator else row["benchmark"]
        rows.append(row)
    report = {
        **{key: value for key, value in records[0].items() if key != "row"},
        "figure": "slotted-runtime",
        "metric": NOTE,
        "timing_identity": "See slotted-runtime.results.json; compare its input/engine hashes separately",
        "proof_pipeline": "Compiler::compile_program(ProofMode::Prove) -> new_egraph_with_proofs().resolve_program",
        "diagnostics": "ProofMode::Check intermediate size and congruence-only lowering are diagnostic fields only",
        "rows": rows,
    }
    csv_output = io.StringIO()
    writer = csv.writer(csv_output, lineterminator="\n")
    writer.writerow(COLUMNS)
    markdown = ["| " + " | ".join(COLUMNS) + " |", "| :--- | ---: | ---: | ---: |"]
    latex = [
        r"\begin{tabular}{lrrr}",
        r"\toprule",
        r"Benchmark & Input & Slotted ($s$) & Slotted + proofs ($scp$) \\",
        r"\midrule",
    ]
    for row in rows:
        values = [row[f"{stage}_ast_nodes"] for stage in STAGES]
        writer.writerow([row["label"], *(value if value is not None else "Unsupported" for value in values)])
        markdown.append(
            "| "
            + " | ".join([row["label"], *(f"{value:,}" if value is not None else "Unsupported" for value in values)])
            + " |"
        )
        name = row["label"].replace("_", r"\_").replace("Σ", r"$\Sigma$")
        latex.append(
            name + " & " + " & ".join(f"{value:,}" if value is not None else "Unsupported" for value in values) + r" \\"
        )
    latex.extend([r"\bottomrule", r"\end{tabular}", ""])
    markdown.extend(["", NOTE, ""])
    failures = {
        next((line.removeprefix("Reason: ") for line in error.splitlines() if line.startswith("Reason: ")), error)
        for row in rows
        if (error := row["proof_congruence_error"])
    }
    if failures:
        markdown.extend(["The Proofs compilation stage is unavailable:", ""])
        markdown.extend(f"- {failure}" for failure in sorted(failures))
        markdown.append("")
    markdown.extend(["Files:", ""])
    markdown.extend(f"- `{row['file']}` (reference: `{row['reference_file']}`)" for row in rows)
    contents = {
        "ast.json": json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        "ast.csv": csv_output.getvalue(),
        "ast.tex": "\n".join(latex),
        "ast.md": "\n".join(markdown) + "\n",
        "files.txt": "".join(f"{row['file']}\t{row['reference_file']}\n" for row in rows),
    }
    destination.mkdir(parents=True, exist_ok=True)
    outputs = []
    for suffix, content in contents.items():
        path = destination / f"slotted-runtime.{suffix}"
        path.write_text(content, encoding="utf-8")
        outputs.append(path)
    return tuple(outputs)
