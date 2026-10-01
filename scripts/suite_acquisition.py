#!/usr/bin/env python3
"""Acquire pinned source inventories and materialize independent Egglog invocations.

Acquisition is separate from the correctness/resource pilot and measurement.
Sources, replay files, and acquisition evidence stay under benchmarks/local.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import subprocess
import sys
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
STORAGE = ROOT / "benchmarks/local"
CATALOG = ROOT / "benchmarks/catalog.json"
REVISIONS = {
    "luminal": ("saulshanabrook/egglog_repro", "7fb0194812b5b11e41a286d8b55e48e3b0bfcd66"),
    "eggcc": ("egraphs-good/eggcc", "16be0063133ef0b8ba21cd75ee377002dc3ecbed"),
    "hardboiled": ("yihozhang/cgo2026-hardboiled-artifact", "b99cf0c6400e954a278f697bf3a0596ac3fa4f25"),
    "misaal": ("RafaeNoor/MISAAL", "c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4"),
    "dialegg": ("AzizZayed/dialegg-cgo-artifact", "4d0d522e98c15becdc5e7d711348cb0891ff0d44"),
    "churchroad": ("gussmith23/churchroad", "9f82ca23b273a5a500cc6a1ca60b30d3c33c5721"),
    "speq": ("avery-laird/lleq", "00bd6254b3832d94558b7c38a394ea03d01a2763"),
}
LUMINAL_MODELS = ("gemma", "gemma4_moe", "llama", "paged_llama", "qwen", "qwen3_moe", "whisper")
SPEQ_PRESERVED = (
    "polybench_gemm",
    "taco_spmv_csc",
    "csparse_spmv_csc_nostruct",
    "SparseCompRow_matmult",
    "spmv_npb",
    "sparsebench_spmv_csr",
    "npb_is_hist",
    "parboil_hist",
)


def reconcile_inventory(existing: dict[str, Any], fresh: dict[str, Any], families: tuple[str, ...]) -> dict[str, Any]:
    """Refresh scoped source lists without erasing compatible capture evidence.

    New source/configuration identities start unprepared; old receipts remain
    diagnostic history. Families outside this refresh are byte-for-byte data
    equivalents, including their custom selections and current validation.
    """
    result = copy.deepcopy(existing)
    fresh_cases = {case["id"]: case for case in fresh["cases"] if case["family"] in families}
    for index, old in enumerate(result["cases"]):
        if old["family"] not in families:
            continue
        new = fresh_cases.pop(old["id"], None)
        if new is None:
            # Manually inventoried extras/configurations are not removed by a
            # narrower upstream file listing. Their scope remains auditable.
            continue
        old_revision = existing["families"][old["family"]]["revision"]
        same = old_revision == fresh["families"][new["family"]]["revision"] and all(
            old.get(key) == new.get(key) for key in ("source", "configuration")
        )
        if not same:
            result["cases"][index] = {
                **new,
                "status": "blocked",
                "workloads": [],
                "reason": "Source revision or configuration changed; fresh reproduction is required.",
                "previous_capture": {"revision": old_revision, "case": old},
            }
    result["cases"].extend(copy.deepcopy(list(fresh_cases.values())))
    for family in families:
        result["families"][family] = {**result["families"].get(family, {}), **fresh["families"][family]}
    return result


def fetch_source(family: str, source_path: str) -> Path:
    """Cache pinned bytes and record their URL and digest alongside the source."""
    repository, revision = REVISIONS[family]
    destination = STORAGE / "sources" / family / source_path
    url = f"https://raw.githubusercontent.com/{repository}/{revision}/{source_path}"
    if not destination.exists():
        destination.parent.mkdir(parents=True, exist_ok=True)
        with urllib.request.urlopen(url, timeout=60) as response:
            destination.write_bytes(response.read())
    digest = hashlib.sha256(destination.read_bytes()).hexdigest()
    evidence = STORAGE / "evidence" / "sources" / family / f"{source_path}.json"
    evidence.parent.mkdir(parents=True, exist_ok=True)
    record = {"url": url, "sha256": digest}
    if evidence.exists() and json.loads(evidence.read_text()) != record:
        raise ValueError(f"cached pinned source changed: {destination}")
    evidence.write_text(json.dumps(record, indent=2) + "\n")
    return destination


def inventory() -> dict[str, Any]:
    """Use complete pinned upstream lists rather than successful-run selection."""
    families: dict[str, Any] = {
        family: {"repository": f"https://github.com/{repo}", "revision": revision}
        for family, (repo, revision) in REVISIONS.items()
    }
    families["math-growth"] = {
        "artifact": "https://doi.org/10.5281/zenodo.7709794",
        "repository": "https://github.com/pldi23-eqlog-ae/micro-benchmarks",
        "revision": "5360490242ec846d3323f3a8e83e3df78cb81f2f",
        "description": "Original Rational Math application, 24 rules and seven combined seeds; cutoff 1 through 100.",
    }
    families["speq"].update(
        {
            "artifact": "https://zenodo.org/records/10963236",
            "archive_md5": "813c94e4c12a3466909849f38b6ac1fe",
            "license": "CC-BY-4.0",
            "description": (
                "Eight preserved REV inputs plus the two remaining paper applications; mapping requires artifact."
            ),
        }
    )
    families["misaal"]["description"] = "102 target/program pairs from three pinned benchmark Makefiles."
    families["hardboiled"]["description"] = (
        "Published generator configurations, including all calls from each compilation; counts are source inputs."
    )
    families["churchroad"]["deferred_feature_cases"] = [
        {
            "source": f"tests/egglog_tests/{name}.egg",
            "status": "deferred",
            "reason": "Feature/regression coverage is separate from the two mapping inputs.",
        }
        for name in ("agilex_alm", "construct_sequential_cycle", "counter_typing", "half_adder", "permuter", "typing")
    ] + [
        {
            "source": f"tests/egglog_tests.rs:{name}",
            "status": "deferred",
            "reason": "Rust-hosted module-enumeration coverage requires the custom debruijnify primitive.",
        }
        for name in ("antiunify", "antiunify_permuter", "find_loop")
    ]
    cases: list[dict[str, Any]] = []
    for cutoff in range(1, 101):
        cases.append(
            {
                "id": f"math-growth-{cutoff:03}",
                "family": "math-growth",
                "source": f"artifact Math cutoff {cutoff}",
                "obtainable": True,
                "status": "captured" if cutoff <= 11 else "deferred",
                "workloads": ["egglog-experimental/tests/math-microbenchmark-rational.egg"]
                if cutoff == 11
                else [f"benchmarks/math/math-{cutoff:02}.egg"]
                if cutoff < 11
                else [],
                **(
                    {}
                    if cutoff <= 11
                    else {
                        "reason": (
                            "Outside the initial predeclared 1–11 cutoff range; disabling historical backoff "
                            "makes larger "
                            "cutoffs require a separate resource pilot."
                        )
                    }
                ),
            }
        )
    for model in LUMINAL_MODELS:
        cases.append({"id": f"luminal-{model}", "family": "luminal", "source": f"{model}.egg"})
    repo, revision = REVISIONS["eggcc"]
    tree_bytes = subprocess.check_output(["gh", "api", f"repos/{repo}/git/trees/{revision}?recursive=1"])
    tree = json.loads(tree_bytes)
    if tree.get("truncated"):
        raise ValueError("Eggcc source inventory was truncated")
    tree_path = STORAGE / "evidence/eggcc-tree.json"
    tree_path.parent.mkdir(parents=True, exist_ok=True)
    tree_path.write_bytes(tree_bytes)
    for item in tree["tree"]:
        path = item["path"]
        if item["type"] == "blob" and path.startswith("benchmarks/passing/") and path.endswith((".bril", ".rs")):
            cases.append(
                {
                    "id": "eggcc-" + Path(path).stem,
                    "family": "eggcc",
                    "source": path,
                    "configuration": {"pass": 1},
                }
            )
    for size in (8, 16, 24, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256):
        cases.append(
            {
                "id": f"hardboiled-conv1d-{size}",
                "family": "hardboiled",
                "source": "apps/tensorcore_benchmarks/conv1d_generator.cpp",
                "configuration": {"gpu_schedule": "tensorcore", "kSize": size},
            }
        )
    for name in ("conv2d", "upsample", "downsample"):
        for size in (16, 32):
            cases.append(
                {
                    "id": f"hardboiled-{name}-{size}",
                    "family": "hardboiled",
                    "source": f"apps/tensorcore_benchmarks/{name}_generator.cpp",
                    "configuration": {"gpu_schedule": "tensorcore", "kSize": size},
                }
            )
    for name, config in (
        ("matmul", {"M": 1024, "N": 1024, "K": 1024}),
        ("conv_layer-16", {"N": 4096, "H": 64, "W": 64, "C": 16, "kSize": 3}),
        ("conv_layer-32", {"N": 4096, "H": 64, "W": 64, "C": 32, "kSize": 3}),
        ("attention", {"D": 64, "L": 4096, "N": 64}),
        ("resize-up", {"upsample": True}),
        ("resize-down", {"upsample": False}),
        ("rec_filter", {}),
        ("denoise", {}),
    ):
        cases.append(
            {
                "id": f"hardboiled-{name}",
                "family": "hardboiled",
                "source": f"apps/tensorcore_benchmarks/{name.split('-')[0]}_generator.cpp",
                "configuration": {"gpu_schedule": "tensorcore", **config},
            }
        )
    for name in (
        "matmul_vnni_1x1",
        "matmul_vnni_1x4",
        "matmul_vnni_1x4_preload_rhs",
        "matmul_flat_1x1",
        "matmul_flat_1x4",
    ):
        cases.append({"id": f"hardboiled-{name}", "family": "hardboiled", "source": f"instrsel-benchmarks/{name}.cpp"})
    for target in ("arm", "hexagon", "x86"):
        source = fetch_source("misaal", f"benchmarks/{target}/halide/Makefile").read_text()
        match = re.search(r"^benchmarks\s*=\s*((?:[^\n]*\\\n)*[^\n]*)", source, re.MULTILINE)
        if match is None:
            raise ValueError(f"missing MISAAL {target} benchmark list")
        for name in match[1].replace("\\\n", " ").split():
            cases.append(
                {
                    "id": f"misaal-{target}-{name}",
                    "family": "misaal",
                    "source": f"benchmarks/{target}/halide/{name}",
                    "configuration": {"target": target},
                }
            )
    for name in ("image_conversion", "vector_norm", "polynomial", "2mm", "3mm"):
        cases.append({"id": f"dialegg-{name}", "family": "dialegg", "source": f"bench/{name}/{name}.mlir"})
    for size in (10, 20, 40, 80, 160):
        cases.append({"id": f"dialegg-nmm-{size}", "family": "dialegg", "source": f"bench/nmm/{size}mm.mlir"})
    for name in ("simple_mul", "wide_mul"):
        cases.append(
            {"id": f"churchroad-{name}", "family": "churchroad", "source": f"tests/integration_tests/{name}.v"}
        )
    for name in (*SPEQ_PRESERVED, "tpal", "tsvc2"):
        cases.append(
            {
                "id": f"speq-{name}",
                "family": "speq",
                "source": f"REVTest.cpp:{name}" if name in SPEQ_PRESERVED else f"artifact paper application {name}",
            }
        )
    for case in cases:
        case.setdefault("status", "blocked")
        case.setdefault("workloads", [])
        if case["status"] == "blocked":
            case.setdefault("reason", "Source capture has not completed; see acquisition evidence.")
    return {"families": families, "cases": cases}


def luminal_witness(source: str) -> tuple[str, str]:
    """Select a seeded Iota whose KernelIota form is derived by the source rule."""
    rule = (
        "(rule ((= ?__rw0 (Op (Iota ?v4_expr ?v4_range) ?__inputs))) "
        "((union ?__rw0 (Op (KernelIota ?v4_expr ?v4_range) ?__inputs)) "
        "(set (dtype (Op (KernelIota ?v4_expr ?v4_range) ?__inputs)) (Int))) :ruleset kernel_lower)"
    )
    normalized_rules = re.sub(r"\?v[0-9]+_(expr|range)", r"?v4_\1", source)
    if rule not in normalized_rules or "(run kernel_lower)" not in source:
        raise ValueError("source does not contain the expected active Iota lowering rule")
    for line in source.splitlines():
        match = re.fullmatch(r"\(let (t[0-9]+) (\(Op \(Iota .*)\)", line)
        if match:
            root, original = match.groups()
            derived = original.replace("(Iota ", "(KernelIota ", 1)
            if any(derived in seed for seed in source.splitlines() if seed.startswith("(let ")):
                continue
            return root, f"(check (= {root} {derived}))"
    raise ValueError("no seeded Iota has a newly derived KernelIota witness")


def split_speq(source: str) -> dict[str, str]:
    """Separate independent recorded push/pop invocations with their shared prelude."""
    pieces = re.split(r"^;; Preserved artifact workload: (\w+)\n", source, flags=re.MULTILINE)
    if len(pieces) != 9:
        raise ValueError("expected exactly four recorded SpEQ scopes")
    prelude = pieces[0]
    result = {}
    for name, body in zip(pieces[1::2], pieces[2::2], strict=True):
        if body.count("(push 1)") != 1 or body.count("(pop 1)") != 1 or "(extract " not in body:
            raise ValueError(f"invalid SpEQ recording scope: {name}")
        result[name] = prelude + f";; Independent replay of preserved artifact workload: {name}\n" + body
    return result


def capture_available(catalog: dict[str, Any]) -> None:
    """Materialize source-complete captures that do not require external compilation."""
    recorded = split_speq((ROOT / "egglog/tests/papers/speq-preserved-reference-suite.egg").read_text())
    for case in catalog["cases"]:
        try:
            family = case["family"]
            content: str | None = None
            if family == "luminal":
                source = fetch_source(family, case["source"])
                original = source.read_text()
                case["obtainable"] = True
                case["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
                root, check = luminal_witness(original)
                content = (
                    f"; Source: {catalog['families'][family]['repository']}"
                    f"/blob/{REVISIONS[family][1]}/{case['source']}\n"
                    f"; Source SHA-256: {hashlib.sha256(source.read_bytes()).hexdigest()}\n"
                    f"; Adaptation: append the seeded {root} Iota-to-KernelIota equality; "
                    "preserve every original command.\n" + original.rstrip() + "\n\n" + check + "\n"
                )
            elif family == "speq" and case["id"].removeprefix("speq-") in recorded and not case.get("evidence"):
                content = recorded[case["id"].removeprefix("speq-")]
            if content is not None:
                output = STORAGE / "workloads" / family / f"{case['id']}.egg"
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_text(content)
                case.update(status="captured", workloads=[str(output.relative_to(ROOT))], obtainable=True)
                if family == "luminal":
                    case.update(
                        capture_complete=True,
                        oracle="Iota equals its derived KernelIota lowering; original schedules retained",
                        invocations=[
                            {
                                "index": 0,
                                "raw": str(source.relative_to(ROOT)),
                                "sha256": case["source_sha256"],
                                "workload": str(output.relative_to(ROOT)),
                            }
                        ],
                    )
                case.pop("reason", None)
        except (OSError, ValueError) as error:
            case.update(status="blocked", workloads=[], reason=f"capture failed: {error}")


def import_captures(catalog: dict[str, Any], paths: list[Path]) -> None:
    """Project source-capture outcomes into the catalog, retaining every raw call."""
    cases = {case["id"]: case for case in catalog["cases"]}
    for path in paths:
        path = path.resolve()
        raw = json.loads(path.read_text())
        records = raw.get("cases", raw) if isinstance(raw, dict) else raw
        if isinstance(records, dict):
            records = [{"id": key, **record} for key, record in records.items()]
        for record in records:
            case = cases[record["id"]]
            revision = record.get("revision")
            if revision and revision != catalog["families"][case["family"]]["revision"]:
                raise ValueError(f"capture revision differs for {case['id']}")
            workloads = record.get("workloads", [])
            for workload in workloads:
                if not (ROOT / workload).is_file():
                    raise ValueError(f"missing replay from capture: {workload}")
            calls = record.get("invocations")
            if calls is None:
                calls = [
                    {"index": index, "raw": source, "sha256": hashlib.sha256((ROOT / source).read_bytes()).hexdigest()}
                    for index, source in enumerate(record.get("raw_invocations", []))
                ]
                if record.get("engine_sessions") != 1 and len(calls) == len(workloads):
                    for call, workload in zip(calls, workloads, strict=True):
                        call["workload"] = workload
            source_hash = record.get("source_sha256", record.get("fir_sha256"))
            case.update(
                status="captured" if workloads else "blocked",
                workloads=workloads,
                obtainable=bool(source_hash),
                capture_complete=record.get("status") == "captured" or record.get("capture_status") == "complete",
                evidence=str(path.relative_to(ROOT)),
                reason=record.get("reason"),
            )
            if source_hash:
                case["source_sha256"] = source_hash
            projected = [
                {
                    "index": call.get("index", call.get("sequence", index)),
                    "raw": call.get("raw", call.get("path")),
                    **{k: v for k, v in call.items() if k in ("sha256", "status", "reason", "workload")},
                }
                for index, call in enumerate(calls)
            ]
            for call in projected:
                if not call["raw"]:
                    raise ValueError(f"capture lacks a raw invocation path: {case['id']}")
                digest = hashlib.sha256((ROOT / call["raw"]).read_bytes()).hexdigest()
                if call.get("sha256", digest) != digest:
                    raise ValueError(f"raw invocation changed: {call['raw']}")
                call["sha256"] = digest
            if record.get("engine_sessions") == 1:
                case["ordered_calls"] = projected
                case.pop("invocations", None)
            else:
                case["invocations"] = projected
            for key in (
                "source_sha256",
                "configuration",
                "capture_boundary",
                "oracle",
                "engine_sessions",
                "raw_call_semantics",
                "external_phases",
                "capture_reason",
                "classification",
            ):
                if key in record:
                    case[key] = record[key]


def main() -> None:
    if len(sys.argv) > 1 and sys.argv[1] == "reproduce":
        sys.path.insert(0, str(ROOT))
        from scripts.suite_reproduction import main as reproduce

        raise SystemExit(reproduce(sys.argv[2:]))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("inventory", "capture-available", "import-captures"))
    parser.add_argument("results", type=Path, nargs="*")
    args = parser.parse_args()
    if args.command == "inventory":
        catalog = inventory()
        if CATALOG.exists():
            catalog = reconcile_inventory(json.loads(CATALOG.read_text()), catalog, tuple(catalog["families"]))
    else:
        catalog = json.loads(CATALOG.read_text())
        if args.command == "capture-available":
            capture_available(catalog)
        else:
            if not args.results:
                parser.error("import-captures requires result JSON paths")
            import_captures(catalog, args.results)
    CATALOG.parent.mkdir(parents=True, exist_ok=True)
    CATALOG.write_text(json.dumps(catalog, indent=2) + "\n")


if __name__ == "__main__":
    main()
