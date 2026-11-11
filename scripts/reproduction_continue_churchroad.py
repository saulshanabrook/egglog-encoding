"""Continue only Churchroad's observed spec_filepath borrow build failure.

The old receipt/logs and original source bytes are retained before a one-line
repair. Verified native prerequisites are reused; only the driver is rebuilt.
"""

from __future__ import annotations

import argparse
import json
import platform
import re
import shlex
import shutil
from dataclasses import asdict
from pathlib import Path
from typing import Any

from benchmarking.pilot import run_bounded_command
from benchmarking.targets import sha256_file
from scripts.eggcc_churchroad_complete import patched_churchroad_sources, write_native_patch
from scripts.reproduction_prepare_churchroad import REVISIONS, RUST_VERSION, tree_identity
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]


def continue_churchroad(
    previous: Path, output: Path, engine: Path, capture_before: Path, *, timeout_sec: float = 1200
) -> dict[str, Any]:
    """Preserve the failed checkpoint, verify the sole repair, then complete native gates."""
    previous, output, engine = previous.resolve(), output.resolve(), engine.resolve()
    durable = (ROOT / "benchmarks/local/reproduction").resolve()
    if not previous.is_relative_to(durable) or not output.is_relative_to(durable) or output.exists():
        raise ValueError("continuation requires a retained preparation and fresh output below reproduction storage")
    saved_receipt = previous / "preparation.json"
    saved = json.loads(saved_receipt.read_text())
    steps = saved["steps"]
    if (
        saved["status"] != "failure"
        or not steps
        or steps[-1]["name"] != "churchroad-build"
        or "error[E0382]" not in str(saved.get("reason"))
        or "spec_filepath" not in str(saved.get("reason"))
        or any(row["status"] != "success" for row in steps[:-1])
    ):
        raise ValueError("continuation is limited to the observed final spec_filepath ownership failure")
    preparer = ROOT / "scripts/reproduction_prepare_churchroad.py"
    if sha256_file(preparer) != saved["implementation_sha256"]:
        raise ValueError("original preparer changed; retain its exact snapshot before continuing")
    if sha256_file(capture_before) != saved["capture_implementation_sha256"]:
        raise ValueError("original capture implementation snapshot does not match the failed receipt")
    if not engine.is_file() or timeout_sec <= 0:
        raise ValueError("existing ordinary engine and positive timeout required")
    sources, prefix = previous / "sources", previous / "prefix"
    churchroad = sources / "churchroad"
    plugin = churchroad / "yosys-plugin/churchroad.so"
    argv = steps[-1]["command"]
    environment: dict[str, str] = {}
    i = 1
    while i < len(argv) and "=" in argv[i]:
        key, value = argv[i].split("=", 1)
        environment[key] = value
        i += 1
    expected_command = ["cargo", f"+{RUST_VERSION}", "build", "--locked", "-j1", "--bin", "churchroad"]
    if argv[0] != "env" or argv[i:] != expected_command or Path(steps[-1]["cwd"]).resolve() != churchroad:
        raise ValueError("saved final compiler invocation differs from the reviewed serial command")
    target = Path(environment["CARGO_TARGET_DIR"])
    if not target.is_relative_to(previous):
        raise ValueError("saved compiler output escapes the retained preparation")
    binary = target / "debug/churchroad"
    for name, row in saved["host_tools"].items():
        if sha256_file(Path(row["path"])) != row["sha256"]:
            raise ValueError(f"host prerequisite changed since the failed preparation: {name}")
    output.mkdir(parents=True)
    evidence = output / "evidence"
    evidence.mkdir()
    record: dict[str, Any] = {
        "status": "blocked",
        "reason": None,
        "steps": [],
        "previous": str(previous),
        "previous_receipt_sha256": sha256_file(saved_receipt),
        "implementation_sha256": sha256_file(Path(__file__)),
        "device_execution": False,
        "benchmark_execution": False,
    }
    receipt = output / "continuation.json"

    def step(name: str, command: list[str]) -> str:
        """Run one guarded continuation command with durable intent and outcome."""
        command = ["env", *(f"{key}={value}" for key, value in environment.items()), *command]
        row: dict[str, Any] = {
            "name": name,
            "command": command,
            "cwd": str(churchroad),
            "status": "running",
            "timeout_sec": timeout_sec,
            "memory_limit_bytes": 5 * 1024**3,
            "disk_reserve_bytes": 10 * 1024**3,
            "allow_warning_pressure": True,
        }
        record["steps"].append(row)
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
        try:
            result = run_bounded_command(
                command,
                churchroad,
                evidence / f"{len(record['steps']):03}-{name}",
                timeout_sec=timeout_sec,
                memory_limit_bytes=5 * 1024**3,
                require_guard=True,
                disk_reserve_bytes=10 * 1024**3,
                allow_warning_pressure=True,
            )
        except ValueError as error:
            row.update(status="resource-stopped" if "guard refused" in str(error) else "blocked", reason=str(error))
            record.update(status=row["status"], reason=str(error))
            raise
        row.update(asdict(result))
        if result.status != "success":
            record.update(status=result.status, reason=f"{name}: {result.message or result.status}")
            raise ValueError(record["reason"])
        return result.stdout_path.read_text()

    try:
        # Freeze original bytes, source manifests and finished native outputs before modifying anything.
        snapshots = {
            "previous-preparation.json": saved_receipt,
            "previous-preparer.py": preparer,
            "previous-capture.py": capture_before,
            "current-capture.py": ROOT / "scripts/eggcc_churchroad_complete.py",
            "previous-native.patch": previous / "evidence/churchroad-native-capture.patch",
            "previous-lib.rs": churchroad / "src/lib.rs",
            "Cargo.lock": churchroad / "Cargo.lock",
        }
        for name, path in snapshots.items():
            shutil.copyfile(path, evidence / name)
        inventory = {
            "churchroad_source": tree_identity(churchroad),
            "native_prefix": tree_identity(prefix),
            "racket_packages": tree_identity(previous / "racket-user"),
        }
        (evidence / "before-inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
        products = [
            prefix / "bin/bitwuzla",
            prefix / "bin/yosys",
            prefix / "bin/yosys-config",
            plugin,
            sources / "lakeroad/racket/generated/xilinx-ultrascale-plus-dsp48e2.rkt",
            churchroad / "Cargo.lock",
        ]
        record["before_products"] = {str(path): sha256_file(path) for path in products}
        record["before_snapshots"] = {path.name: sha256_file(path) for path in evidence.iterdir() if path.is_file()}
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
        # Recreate instrumentation from the pinned Git blobs; the only source delta may be this borrow.
        revision = step("source-revision", ["git", "rev-parse", "HEAD"]).strip()
        if revision != REVISIONS["churchroad"][1]:
            raise ValueError("retained Churchroad revision changed")
        original = evidence / "original-source"
        for relative in ("src/lib.rs", "src/main.rs", "Cargo.toml"):
            source = step("source-" + Path(relative).name, ["git", "show", "HEAD:" + relative])
            path = original / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        patched = patched_churchroad_sources(original)
        before = (churchroad / "src/lib.rs").read_text()
        old, new = "        .arg(spec_filepath)", "        .arg(&spec_filepath)"
        if before.count(old) != 1 or patched["src/lib.rs"] != before.replace(old, new, 1):
            raise ValueError("current capture patch changes more than the reviewed spec_filepath borrow")
        for relative in ("src/main.rs", "Cargo.toml"):
            if patched[relative] != (churchroad / relative).read_text():
                raise ValueError(f"capture changes outside the reviewed borrow: {relative}")
        repair = evidence / "borrow-repair.patch"
        write_native_patch(churchroad, {"src/lib.rs": patched["src/lib.rs"]}, repair)
        record["repair_sha256"] = sha256_file(repair)
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
        (churchroad / "src/lib.rs").write_text(patched["src/lib.rs"])
        step("churchroad-build", expected_command)
        step("churchroad-help", [str(binary), "--help"])
        if not binary.is_file() or not binary.stat().st_size:
            raise ValueError("continuation did not produce the native driver")
        if any(sha256_file(Path(path)) != digest for path, digest in record["before_products"].items()):
            raise ValueError("an existing solver/Yosys/plugin/model/lock output changed during the driver continuation")
        if sha256_file(saved_receipt) != record["previous_receipt_sha256"]:
            raise ValueError("failed preparation receipt changed during continuation")
        linked: set[Path] = set()
        for name, executable in [
            ("bitwuzla", prefix / "bin/bitwuzla"),
            ("yosys", prefix / "bin/yosys"),
            ("churchroad", binary),
            ("plugin", plugin),
            ("racket", Path(saved["host_tools"]["racket"]["path"])),
        ]:
            command = ["otool", "-L", str(executable)] if platform.system() == "Darwin" else ["ldd", str(executable)]
            observed = step("linked-" + name, command)
            linked.update(
                Path(path)
                for path in re.findall(r"(?:=>\s+|^\s*)(/[^\s]+)\s+\(", observed, re.M)
                if Path(path).is_file()
            )
        for info in sorted((target.parent / "bitwuzla/meson-info").glob("*.json")):
            shutil.copyfile(info, evidence / f"bitwuzla-{info.name}")
        launcher = output / "churchroad-capture"
        launcher.write_text(
            "#!/bin/sh\nexec env "
            + " ".join(shlex.quote(f"{k}={v}") for k, v in environment.items())
            + " "
            + shlex.quote(str(binary))
            + ' "$@"\n'
        )
        launcher.chmod(0o755)
        runtime = [
            binary,
            plugin,
            prefix,
            sources / "lakeroad",
            sources / "rosette",
            sources / "yaml",
            previous / "racket-user",
            churchroad / "Cargo.lock",
            previous / "evidence",
            evidence,
            Path(__file__).resolve(),
            preparer,
            ROOT / "scripts/eggcc_churchroad_complete.py",
            *(Path(row["path"]) for row in saved["host_tools"].values()),
            *(Path(path) for path in saved["racket_runtime_paths"]),
            *sorted(linked),
        ]
        if saved.get("optional_rosette_setup_z3"):
            runtime.append(Path(saved["optional_rosette_setup_z3"]["path"]))
        settings = {
            "churchroad": {
                "revision": REVISIONS["churchroad"][1],
                "timeout_sec": 300,
                "paths": {"checkout": str(churchroad), "binary": str(launcher), "egglog": str(engine)},
                "identity_paths": [str(path) for path in dict.fromkeys(runtime)],
            }
        }
        settings_path = output / "settings.json"
        settings_path.write_text(json.dumps(settings, indent=2) + "\n")
        record.update(
            status="success",
            settings=str(settings_path),
            settings_sha256=sha256_file(settings_path),
            artifacts={str(path): sha256_file(path) for path in [binary, launcher, plugin, settings_path]},
            reason="Native dependency gates complete; source optimization and ordinary replay remain unrun",
        )
    except (OSError, ValueError) as error:
        if record["reason"] is None:
            record.update(status="blocked", reason=str(error))
    finally:
        receipt.write_text(json.dumps(record, indent=2, default=str) + "\n")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--previous", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--capture-before", type=Path, required=True)
    parser.add_argument("--egglog", type=Path, default=ROOT / "target/release/egglog-experimental")
    parser.add_argument("--timeout-sec", type=float, default=1200)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        result = continue_churchroad(
            args.previous, args.output, args.egglog, args.capture_before, timeout_sec=args.timeout_sec
        )
    print(json.dumps({key: result.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if result["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
