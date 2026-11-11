"""Prepare a reviewed Eggcc observer-only adaptation; never overwrite the catalog.

Only generated observer declarations change from no-merge to merge-old. Source
rules, schedules, and checks stay byte-for-byte unchanged. Immutable receipts bind
the previous publication and its aliases; they do not claim new replay validation.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from scripts.eggcc_churchroad_complete import _eggcc_constructor_signatures, _eggcc_literal_sort, _eggcc_tree
from scripts.hardboiled_replay import egglog_forms

OBSERVER = re.compile(r"(?:reproduction_lookup_value_|reconstruction_lookup_value_|reproduction_derived_type_)\d+")


def adapt_observers(source: str) -> tuple[str, list[dict[str, Any]]]:
    """Change only grounded generated tables, rejecting unexpected writers/forms.

    Each constant observer key has one rule, whose value is read from constructors
    or another grounded observer. Merge-old cannot conceal conflicting values under
    these constructor functional dependencies. No new expressions enter the graph.
    """
    forms = egglog_forms(source)
    trees = [_eggcc_tree(tokens) for _, _, tokens in forms]
    constructors = _eggcc_constructor_signatures(source)
    declarations = {}
    anchors = {}
    globals_: dict[str, str] = {}
    for tree in trees:
        if tree[0] == "let" and isinstance(tree[2], list) and tree[2][0] in constructors:
            globals_[tree[1]] = constructors[tree[2][0]][1]
        if tree[0] != "function":
            continue
        if re.fullmatch(r"reproduction_anchor_\d+", tree[1]) and tree[2] == [] and tree[4:] == [":merge", "old"]:
            anchors[tree[1]] = tree[3]
        if not OBSERVER.fullmatch(tree[1]):
            continue
        expected_args = [] if tree[1].startswith("reproduction_derived_type_") else ["i64", "i64"]
        if (
            tree[1] in declarations
            or tree[2] != expected_args
            or not isinstance(tree[3], str)
            or tree[4:] not in ([":no-merge"], [":merge", "old"])
            or (not expected_args and tree[3] != "Type")
        ):
            raise ValueError(f"unexpected observer declaration: {tree[1]}")
        declarations[tree[1]] = tree
    if not declarations:
        return source, []

    writers: dict[tuple[str, ...], tuple[str, set[tuple[str, ...]]]] = {}
    for tree, (_, _, tokens) in zip(trees, forms, strict=True):
        used = set(tokens) & declarations.keys()
        if not used or tree[0] in {"function", "check", "print-size"}:
            continue
        if tree[0] != "rule" or len(tree[2]) != 1:
            raise ValueError("observer used outside a generated rule or output query")
        action = tree[2][0]
        if (
            len(action) != 3
            or action[0] != "set"
            or not isinstance(action[1], list)
            or action[1][0] not in declarations
        ):
            raise ValueError("observer rule has an unexpected action")
        key = tuple(action[1])
        table = declarations[key[0]]
        if len(key) != len(table[2]) + 1 or any(not re.fullmatch(r"\d+", value) for value in key[1:]):
            raise ValueError("observer key is not a fixed request/node identity")
        if key in writers:
            raise ValueError("observer key has more than one writer")
        prefix = "reconstruction_lookup_" if key[0].startswith("reconstruction_") else "reproduction_lookup_"
        if table[2]:
            if (
                len(tree) != 8
                or tree[3] != ":ruleset"
                or not re.fullmatch(prefix + r"depth_\d+", tree[4])
                or tree[5:] != [":internal-include-subsumed", ":name", json.dumps(prefix + f"rule_{key[1]}_{key[2]}")]
            ):
                raise ValueError("observer rule metadata differs from the generator")
        elif tree[3:] != [":ruleset", "reproduction_derived_types", ":internal-include-subsumed"]:
            raise ValueError("derived observer rule metadata differs from the generator")
        bound: dict[str, str] = {}
        dependencies = set()
        for fact in tree[1]:
            if len(fact) != 3 or fact[0] != "=" or not isinstance(fact[1], str) or fact[1] in bound:
                raise ValueError("observer body must contain ordered unique equalities")
            value = fact[2]
            if isinstance(value, str):
                sort = bound.get(value) or globals_.get(value) or _eggcc_literal_sort(value)
            elif value[0] in declarations:
                dependency = tuple(value)
                signature = declarations[value[0]]
                if len(value) != len(signature[2]) + 1 or any(not re.fullmatch(r"\d+", x) for x in value[1:]):
                    raise ValueError("observer dependency is not grounded")
                dependencies.add(dependency)
                sort = signature[3]
            elif value[0] in anchors and len(value) == 1:
                sort = anchors[value[0]]
            elif value[0] in constructors:
                arguments, sort = constructors[value[0]]
                if (
                    any(not isinstance(x, str) for x in value[1:])
                    or [bound.get(x) or globals_.get(x) or _eggcc_literal_sort(x) for x in value[1:]] != arguments
                ):
                    raise ValueError(f"observer constructor arguments are not grounded and typed: {value!r}")
            else:
                raise ValueError("observer body reads an unknown operation")
            if sort is None:
                raise ValueError(f"observer body contains an ungrounded value: {fact!r}")
            bound[fact[1]] = sort
        if bound.get(action[2]) != table[3]:
            raise ValueError("observer action does not retain a typed body value")
        writers[key] = (tree[4], dependencies)
    if set(declarations) != {key[0] for key in writers}:
        raise ValueError("observer declaration lacks its generated writer")
    remaining = set(writers)
    while remaining:
        grounded = {key for key in remaining if not (writers[key][1] & remaining)}
        if not grounded or any(dependency not in writers for key in grounded for dependency in writers[key][1]):
            raise ValueError("observer dependencies are missing or cyclic")
        remaining -= grounded

    changes = []
    for index, ((start, end, _), tree) in reversed(list(enumerate(zip(forms, trees, strict=True)))):
        if tree[0] == "function" and tree[1] in declarations and tree[4:] == [":no-merge"]:
            before = source[start:end]
            token = next(match for match in re.finditer(r";[^\n]*|:[a-z-]+", before) if match[0] == ":no-merge")
            after = before[: token.start()] + ":merge old" + before[token.end() :]
            source = source[:start] + after + source[end:]
            changes.append({"command": index, "before": before, "after": after})
    return source, list(reversed(changes))


def prepare_catalog(catalog: dict[str, Any], root: Path, directory: Path) -> dict[str, Any]:
    """Write immutable candidates and return a catalog projection for review.

    Receipts and inputs are checked before adapting. Previous file paths stay in
    workload history, while selection points to new hashes. Measurement caches and
    raw acquisition evidence are never read or changed.
    """
    root, directory = root.resolve(), directory.resolve()
    directory.relative_to(root)
    result = copy.deepcopy(catalog)
    publications: dict[str, dict[str, Any]] = {}
    pending: dict[str, bytes] = {}
    records: dict[str, dict[str, Any]] = {}
    changed_cases = []
    for case in result["cases"]:
        selected = case.get("benchmark_selection", {}).get("workloads", [])
        if case["family"] != "eggcc" or not selected:
            continue
        previous = case["complete_reproduction"]
        receipt = root / previous["receipt"]
        if previous["status"] != "complete" or sha256_file(receipt) != previous["receipt_sha256"]:
            raise ValueError("complete reproduction receipt changed")
        if previous["receipt"] not in publications:
            publications[previous["receipt"]] = json.loads(receipt.read_text())
        manifest = publications[previous["receipt"]]
        entries = {row["file"]: row for row in manifest["workloads"]}
        mapped = {}
        for old in selected:
            expected = previous["workloads"][old]
            path = root / old
            if sha256_file(path) != expected["file_sha256"] or expected["facts_sha256"]:
                raise ValueError("retained replay file/facts identity changed or is unsupported")
            entry = entries.get(path.name)
            aliases = [row for row in manifest["cases"] if row.get("catalog_id", row["id"]) == case["id"]]
            if (
                entry is None
                or entry["sha256"] != expected["file_sha256"]
                or entry["facts_sha256"] != expected["facts_sha256"]
                or not any(path.name in row["workloads"] for row in aliases)
            ):
                raise ValueError("reproduction receipt does not bind the selected replay and alias")
            adapted, changes = adapt_observers(path.read_text())
            if not changes:
                mapped[old] = old
                continue
            content = adapted.encode()
            digest = "sha256:" + hashlib.sha256(content).hexdigest()
            name = digest.removeprefix("sha256:") + ".egg"
            new = str((directory / name).relative_to(root))
            pending[name] = content
            record = records.setdefault(
                name,
                {"file": name, "sha256": digest, "facts_sha256": "", "aliases": [], "sources": []},
            )
            for alias in entry["aliases"]:
                if alias not in record["aliases"]:
                    record["aliases"].append(alias)
            source = {
                "file": old,
                **expected,
                "receipt": previous["receipt"],
                "receipt_sha256": previous["receipt_sha256"],
                "changes": changes,
            }
            if source not in record["sources"]:
                record["sources"].append(source)
            mapped[old] = new
        if any(old != new for old, new in mapped.items()):
            changed_cases.append((case, mapped))
    if not changed_cases:
        return result
    adapted_cases = []
    for case, mapped in changed_cases:
        adapted_cases.append(
            {"id": case["id"], "family": "eggcc", "workloads": [Path(x).name for x in mapped.values()]}
        )
        for old, new in mapped.items():
            if old == new:
                entry = next(
                    row
                    for row in publications[case["complete_reproduction"]["receipt"]]["workloads"]
                    if row["file"] == Path(old).name
                )
                records.setdefault(Path(old).name, copy.deepcopy(entry))
    manifest = {
        "adaptation": "eggcc-grounded-observers-merge-old-v1",
        "validation": "not performed; original receipts describe original bytes only",
        "cases": adapted_cases,
        "workloads": list(records.values()),
    }
    content = (json.dumps(manifest, indent=2) + "\n").encode()
    receipt_name = hashlib.sha256(content).hexdigest() + ".json"
    pending[receipt_name] = content
    directory.mkdir(parents=True, exist_ok=True)
    for name, content in pending.items():
        destination = directory / name
        if destination.exists():
            if destination.read_bytes() != content:
                raise ValueError(f"immutable adaptation artifact changed: {destination}")
        else:
            destination.write_bytes(content)
    for case, mapped in changed_cases:
        previous = case["complete_reproduction"]
        case["complete_reproduction"] = {
            **previous,
            "reason": "Retained workload with observer declarations adapted; new proof validation is not claimed.",
            "receipt": str((directory / receipt_name).relative_to(root)),
            "receipt_sha256": "sha256:" + receipt_name.removesuffix(".json"),
            "workloads": {new: {"file_sha256": sha256_file(root / new), "facts_sha256": ""} for new in mapped.values()},
        }
        case["benchmark_selection"] = {**case["benchmark_selection"], "workloads": list(mapped.values())}
        case["workloads"] = list(dict.fromkeys([*case["workloads"], *mapped.values()]))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--catalog-output", required=True, type=Path)
    args = parser.parse_args()
    catalog_path = args.root / "benchmarks/catalog.json"
    if args.catalog_output.resolve() == catalog_path.resolve():
        parser.error("write a separate catalog projection for review")
    projected = prepare_catalog(json.loads(catalog_path.read_text()), args.root, args.output)
    args.catalog_output.write_text(json.dumps(projected, indent=2) + "\n")


if __name__ == "__main__":
    main()
