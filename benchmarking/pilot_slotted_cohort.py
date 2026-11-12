"""Compose the corrected own-Slotted packet into a frozen paper snapshot offline.

The base's native references, other source endpoints and compiler-size evidence
remain unchanged. Neither this command nor its output opens a live timing cache,
builds an executable, or falls back to an earlier endpoint after a failed run.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from copy import deepcopy
from pathlib import Path
from typing import Any, cast

from .engines import PROOF_ORACLES, Treatment
from .models import BenchmarkEndpoint, FileSpec, TargetRow
from .proof_validation import select_remote_proof_validation

BASE_BINARY = "sha256:d118d70ef902332bdf21f729041486566cd1dce9cf7f77563047c7f3369c0264"
CORRECTED_BINARY = "sha256:2f7ef060dd7f707e3ae21e6c616cfb43435041b59e2abd6aaedfac4180b1d696"
SOURCE_ROLES = {
    "slotted": {"candidate": "slotted-no-aliasing"},
    "slotted-proofs": {"candidate": "slotted-proof-extraction-no-aliasing"},
    "slotted-complete": {"candidate": "slotted"},
    "slotted-complete-proofs": {"baseline": "slotted", "candidate": "slotted-proof-extraction"},
}
SOURCE_TREATMENTS = frozenset(t for roles in SOURCE_ROLES.values() for t in roles.values())
POLICY = {"rounds": 3, "threads": 4, "timeout_sec": 500, "memory_limit_bytes": 16 * 1024**3}


def compose_slotted_source(
    base: dict[str, Any],
    replacement: dict[str, Any],
    policy_receipt: dict[str, Any],
    source_binding_receipt: dict[str, Any],
    *,
    expected_binary: str = CORRECTED_BINARY,
) -> dict[str, Any]:
    """Retarget exactly the four own modes on the base's ten released SDQL inputs."""
    if base["pilot_data_version"] != 1 or replacement["pilot_data_version"] != 1 or expected_binary == BASE_BINARY:
        raise ValueError("replacement requires a distinct executable and supported portable snapshots")
    if "slotted_source_cohort" in base["provenance"]:
        raise ValueError("use the original frozen base, not an already composed snapshot")
    if base["provenance"]["binaries"]["egglog-experimental"] != BASE_BINARY:
        raise ValueError("base must retain the original d118 source cohort")
    for field, expected in POLICY.items():
        snapshot_field = "requested_threads" if field == "threads" else field
        if (
            base[snapshot_field] != expected
            or replacement[snapshot_field] != expected
            or policy_receipt.get(field) != expected
        ):
            raise ValueError(f"Slotted replacement must preserve {field}={expected}")
    if (
        policy_receipt.get("binary_sha256") != expected_binary
        or policy_receipt.get("rust_min_stack", "missing") is not None
    ):
        raise ValueError("policy receipt must bind the new binary and legacy unset RUST_MIN_STACK")
    target = TargetRow(**replacement["provenance"]["target"])
    if not target.label or policy_receipt.get("target_label") != target.label:
        raise ValueError("policy receipt must bind the distinct replacement target label")
    bindings = source_binding_receipt.get("binary_sources", {})
    validation_source = bindings.get(expected_binary)
    if not validation_source:
        raise ValueError("new executable requires its own canonical-compatible source binding")

    old = {c["id"]: c for c in base["conditions"]}
    if len(old) != len(base["conditions"]):
        raise ValueError("duplicate base condition identities")
    inputs: dict[str, set[str]] = {experiment: set() for experiment in SOURCE_ROLES}
    required: dict[tuple[str, str], dict[str, Any]] = {}
    for comparison in base["comparisons"]:
        for role, treatment in SOURCE_ROLES.get(comparison["experiment"], {}).items():
            logical = comparison["logical_id"]
            condition = old[comparison[role]]
            if (
                condition["binary_sha256"] != BASE_BINARY
                or condition["treatment"] != treatment
                or condition["file_sha256"] != logical
            ):
                raise ValueError("base own-Slotted identity does not match its declared comparison")
            inputs[comparison["experiment"]].add(logical)
            required[(logical, treatment)] = condition
    universe = inputs["slotted"]
    if len(universe) != 10 or any(value != universe for value in inputs.values()) or len(required) != 40:
        raise ValueError("base must contain the same ten inputs in all four own-Slotted configurations")
    old_validation_sources = {
        c["validation"].get("production_source_git_sha") for c in required.values() if c["validation"] is not None
    }
    if validation_source in old_validation_sources:
        raise ValueError("corrected runtime needs its own source closure, not the old de5 validation binding")

    fresh: dict[tuple[str, str], dict[str, Any]] = {}
    for condition in replacement["conditions"]:
        if condition["treatment"] not in SOURCE_TREATMENTS:
            continue
        key = (condition["logical_id"], condition["treatment"])
        if key not in required or key in fresh:
            raise ValueError("replacement has extra or duplicate own-Slotted profiles")
        if (
            condition["id"] in old
            or condition["binary_sha256"] != expected_binary
            or condition["file_sha256"] != key[0]
        ):
            raise ValueError(
                "replacement condition must have a distinct new-binary identity and unchanged physical input"
            )
        if condition["threads"] != 4 or condition["requested_threads"] != 4 or len(condition["observations"]) > 3:
            raise ValueError("replacement condition violates the four-worker, three-observation contract")
        prior = required[key]
        if prior["exclusion"] is not None and condition["exclusion"] != prior["exclusion"]:
            raise ValueError("existing explicit Slotted exclusions must remain qualified and unchanged")
        for observation in condition["observations"]:
            expected_fields = {
                "binary_sha256": expected_binary,
                "file_sha256": key[0],
                "treatment": key[1],
                "target_label": target.label,
                "threads": 4,
                "requested_threads": 4,
                "timeout_sec": 500,
                "memory_limit_bytes": POLICY["memory_limit_bytes"],
            }
            if any(observation.get(field) != value for field, value in expected_fields.items()):
                raise ValueError("a selected observation mixes an executable, input, mode or resource policy")
        validation = condition["validation"]
        if validation and validation.get("observation"):
            observation = validation["observation"]
            if observation.get("production_binary_sha256") != expected_binary:
                raise ValueError("old validation evidence cannot qualify the new executable")
            qualified = select_remote_proof_validation(
                [observation],
                BenchmarkEndpoint(target, expected_binary, cast(Treatment, key[1]), threads=4),
                FileSpec(condition["path"], Path(condition["path"]), key[0]),
                source_bindings=bindings,
            )
            if qualified is None or qualified["status"] != validation["status"]:
                raise ValueError("replacement proof validation does not match its own source/input/profile")
        elif validation and validation["status"] == "passed":
            raise ValueError("a new proof pass requires its own executed source-bound receipt")
        if key[1] not in PROOF_ORACLES and validation and validation["status"] == "passed":
            raise ValueError("certificate evidence cannot qualify an ordinary control")
        fresh[key] = condition
    if fresh.keys() != required.keys() or len({c["id"] for c in fresh.values()}) != 40:
        raise ValueError("replacement must include all forty condition identities, including failures and exclusions")

    result = deepcopy(base)
    for comparison in result["comparisons"]:
        for role, treatment in SOURCE_ROLES.get(comparison["experiment"], {}).items():
            comparison[role] = fresh[(comparison["logical_id"], treatment)]["id"]
    for condition in fresh.values():
        copied = deepcopy(condition)
        copied["endpoint_cohort"] = "corrected-slotted"
        copied["validation_source_git_sha"] = validation_source
        result["conditions"].append(copied)
    result["provenance"]["default_binary_map_scope"] = "Default endpoints; own Slotted uses slotted_source_cohort"
    result["provenance"]["slotted_source_cohort"] = {
        "id": "corrected-slotted",
        "binary_sha256": expected_binary,
        "validation_source_git_sha": validation_source,
        "collector_target": deepcopy(replacement["provenance"]["target"]),
        "policy_receipt": deepcopy(policy_receipt),
        "source_binding_receipt": deepcopy(source_binding_receipt),
        "condition_ids": sorted(c["id"] for c in fresh.values()),
        "old_conditions_retained": True,
        "old_count_oracles_requalified": False,
    }
    return result


def runtime_source_cohorts(results: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Check integrated-figure candidate identities against the explicit source cohorts."""
    provenance = results["provenance"]
    default = provenance["binaries"]["egglog-experimental"]
    slotted = provenance.get("slotted_source_cohort")
    groups: dict[str, dict[str, Any]] = {}
    for row in results["comparisons"]:
        cohort = "corrected-slotted" if slotted and row["experiment"] in SOURCE_ROLES else "default"
        expected = slotted["binary_sha256"] if cohort == "corrected-slotted" else default
        condition = row["ours"]
        if condition["binary_sha256"] != expected or any(
            o["binary_sha256"] != expected for o in condition["observations"]
        ):
            raise ValueError(f"unexpected candidate binary for {row['experiment']}/{row['label']}")
        group = groups.setdefault(
            cohort, {"binary_sha256": expected, "planned_comparisons": 0, "complete_comparisons": 0}
        )
        group["planned_comparisons"] += 1
        group["complete_comparisons"] += row["state"] == "complete"
    return groups


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, type=Path)
    parser.add_argument("--slotted", required=True, type=Path)
    parser.add_argument("--policy-receipt", required=True, type=Path)
    parser.add_argument("--source-binding-receipt", required=True, type=Path)
    parser.add_argument(
        "--receipt", action="append", default=[], type=Path, help="additional immutable build/source attestations"
    )
    parser.add_argument("--expected-slotted-binary", default=CORRECTED_BINARY)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    paths = [args.base, args.slotted, args.policy_receipt, args.source_binding_receipt, *args.receipt]
    documents: list[dict[str, Any]] = []
    receipts: list[dict[str, str]] = []
    for path in paths:
        raw = path.read_bytes()
        documents.append(json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw))
        receipts.append({"path": str(path), "sha256": "sha256:" + hashlib.sha256(raw).hexdigest()})
    base, replacement = (d["pilot_snapshot"] for d in documents[:2])
    snapshot = compose_slotted_source(
        base, replacement, documents[2], documents[3], expected_binary=args.expected_slotted_binary
    )
    snapshot["provenance"]["slotted_source_cohort"]["input_receipts"] = receipts
    snapshot["provenance"]["slotted_source_cohort"]["additional_attestations"] = documents[4:]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"pilot_snapshot": snapshot}, ensure_ascii=False, separators=(",", ":")) + "\n")
    print(f"Composed forty new own-Slotted conditions; retained all historical endpoints: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
