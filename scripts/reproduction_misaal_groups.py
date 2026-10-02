"""Contain only MISAAL's pinned, detached Racket launch behind a live lease.

This is not containment for arbitrary process trees. The source launcher keeps
its own session and local killpg timeout; no Racket work starts before the outer
guard acknowledges that group. Losing the guard lease kills the owned group.
"""

from __future__ import annotations

import argparse
import hashlib
import inspect
import json
import os
import secrets
import select
import shutil
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import time
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path
from types import FrameType, ModuleType
from typing import Any

CONTRACT = "misaal-racket-lease-v1"
SOURCE = "lib/utils/DSLInstructionUtils.py"
SOURCE_SHA256 = "e385eaa17a81bbcb8106ad33cbbe1ac2ed4307879b0f366f3b72219744b43bdb"


def process_snapshot() -> dict[int, dict[str, int | str]]:
    """Read one coherent process table; malformed monitoring data is a stop."""
    result = subprocess.run(
        ["ps", "-axo", "pid=,ppid=,pgid=,rss=,stat="],
        check=True,
        capture_output=True,
        text=True,
        timeout=1,
    )
    rows: dict[int, dict[str, int | str]] = {}
    for line in result.stdout.splitlines():
        values = line.split()
        if len(values) != 5:
            raise ValueError("Malformed process-group monitoring snapshot")
        pid, parent, group, rss = map(int, values[:4])
        if pid in rows or pid <= 0 or rss < 0:
            raise ValueError("Inconsistent process-group monitoring snapshot")
        rows[pid] = {"parent": parent, "group": group, "rss": rss * 1024, "state": values[4]}
    return rows


def peer_identity(connection: socket.socket) -> tuple[int, str]:
    """Authenticate the connected supervisor PID using kernel socket metadata."""
    if sys.platform == "darwin":
        # sys/un.h: SOL_LOCAL=0, LOCAL_PEERTOKEN=6. The audit token includes
        # both the peer PID and its kernel PID version, unlike ps lstart.
        token = connection.getsockopt(0, 6, 32)
        words = struct.unpack("=8I", token)
        return words[5], f"darwin-audit:{token.hex()}"
    if sys.platform.startswith("linux"):
        pid, _, _ = struct.unpack("=3i", connection.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))
        fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
        return pid, f"linux-start:{fields[19]}"
    raise ValueError("Known-launch containment supports only macOS and Linux")


class RacketGroups:
    """Own launch reservations, acknowledgments, sampling and group drain."""

    def __init__(self, directory: Path):
        directory.mkdir(parents=True, exist_ok=False)
        self.directory = directory
        self.socket_directory = Path(tempfile.mkdtemp(prefix="misaal-groups-", dir="/tmp"))
        self.listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.listener.bind(str(self.socket_directory / "guard.sock"))
        self.listener.listen(32)
        self.listener.setblocking(False)
        self.endpoint = self.socket_directory / "guard.sock"
        self.connections: dict[socket.socket, dict[str, Any]] = {}
        self.root: int | None = None
        self.closed = False
        self.record: dict[str, Any] = {
            "contract": CONTRACT,
            "scope": "root group plus reserved/acknowledged pinned Racket supervisor groups",
            "implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "control_endpoint": str(self.endpoint),
            "bootstrap": "pinned Python -I -S; no Racket work before acknowledgment",
            "launches": {},
            "groups": [],
            "status": "awaiting-root",
        }
        self._persist()

    def _persist(self) -> None:
        temporary = self.directory / "groups.json.tmp"
        temporary.write_text(json.dumps(self.record, indent=2) + "\n")
        temporary.replace(self.directory / "groups.json")

    def _exchange(self, *, stopping: bool) -> dict[int, dict[str, int | str]]:
        while True:
            try:
                connection, _ = self.listener.accept()
            except BlockingIOError:
                break
            try:
                pid, identity = peer_identity(connection)
                connection.setblocking(False)
                self.connections[connection] = {"pid": pid, "identity": identity, "role": None, "buffer": ""}
            except BaseException:
                connection.close()
                raise
        # Read messages before taking the one RSS snapshot. A completion message
        # means Racket has already been reaped, so its stale pre-message row must
        # not be mistaken for a residual descendant.
        for connection, peer in self.connections.items():
            try:
                content = connection.recv(65536)
            except BlockingIOError:
                content = None
            except ConnectionResetError:
                content = b""
            if content == b"":
                peer["eof"] = True
            elif content:
                peer["buffer"] += content.decode()
            if len(peer["buffer"]) > 65536:
                raise ValueError("Oversized supervisor protocol message")
        rows = process_snapshot()
        for connection, peer in list(self.connections.items()):
            pid = peer["pid"]
            if peer.get("eof") and peer["role"] is None:
                # This peer received no reservation or launch permission.
                connection.close()
                del self.connections[connection]
                continue
            while "\n" in peer["buffer"]:
                line, peer["buffer"] = peer["buffer"].split("\n", 1)
                message = json.loads(line)
                kind = message.get("kind")
                if kind == "reserve" and peer["role"] is None:
                    if stopping:
                        connection.sendall(b"stop\n")
                        continue
                    if self.root not in rows or pid not in rows or rows[pid]["group"] != self.root:
                        raise ValueError("Launch reservation is outside the guarded source group")
                    nonce = secrets.token_hex(24)
                    self.record["launches"][nonce] = {
                        "parent": pid,
                        "parent_identity": peer["identity"],
                        "status": "reserved",
                        "reported": False,
                    }
                    peer.update(role="parent", reservation=nonce)
                    connection.sendall((nonce + "\n").encode())
                elif kind in {"spawned", "spawn-failed"} and peer["role"] == "parent":
                    launch = self.record["launches"][peer["reservation"]]
                    if launch["reported"] or launch["status"] not in {"reserved", "registering"}:
                        raise ValueError("Native launch reservation was reused")
                    if kind == "spawned":
                        child = message.get("pid")
                        if not isinstance(child, int) or isinstance(child, bool) or child <= 0:
                            raise ValueError("Invalid reserved supervisor PID")
                        if launch.get("pid", child) != child:
                            raise ValueError("Supervisor PID differs from its reserved source child")
                        launch.update(status="spawned", pid=child, reported=True)
                    else:
                        if "pid" in launch:
                            raise ValueError("Source reported a failed fork after supervisor registration")
                        launch.update(status="spawn-failed", reported=True)
                    connection.sendall(b"recorded\n")
                elif kind == "register" and peer["role"] is None:
                    nonce = message.get("reservation")
                    launch = self.record["launches"].get(nonce)
                    if (
                        launch is None
                        or launch["status"] not in {"reserved", "spawned"}
                        or launch.get("pid", pid) != pid
                        or message.get("pid") != pid
                        or message.get("contract") != CONTRACT
                    ):
                        raise ValueError("Supervisor does not match its source launch reservation")
                    if pid not in rows or rows[pid]["group"] != pid:
                        raise ValueError("Supervisor does not lead its reserved group")
                    if any(group["pid"] == pid and not group.get("retired") for group in self.record["groups"]):
                        raise ValueError("Supervisor PID already has a live registration")
                    group = {
                        "pid": pid,
                        "identity": peer["identity"],
                        "status": "pending",
                        "reservation": nonce,
                        "command": message["command"],
                        "script_sha256": message["script_sha256"],
                    }
                    self.record["groups"].append(group)
                    launch.update(pid=pid, status="spawned" if launch["reported"] else "registering")
                    peer.update(role="group", group=group)
                elif kind == "done" and peer["role"] == "group":
                    group = peer["group"]
                    if group["status"] != "acknowledged":
                        raise ValueError("Unexpected supervisor completion")
                    members = {p for p, row in rows.items() if row["group"] == pid and "Z" not in str(row["state"])}
                    if members != {pid}:
                        raise ValueError(f"Racket exited with unexpected residual descendants in group {pid}")
                    group.update(status="releasing", returncode=message["returncode"])
                    connection.sendall(b"release\n")
                else:
                    raise ValueError("Unexpected supervisor lifecycle message")
            if peer.get("eof"):
                if peer["role"] == "group":
                    group = peer["group"]
                    members = {p for p, row in rows.items() if row["group"] == pid and "Z" not in str(row["state"])}
                    if members:
                        # Group-wide signals do not retire every member at the
                        # same instant. Continue accounting for this group while
                        # allowing a bounded observed drain, without signaling a
                        # potentially reused numeric group ID from the guard.
                        group.update(status="draining", drain_deadline=time.monotonic() + 1)
                        self.record["launches"][group["reservation"]]["status"] = "draining"
                    else:
                        group.update(status="drained", retired=True)
                        self.record["launches"][group["reservation"]]["status"] = "drained"
                connection.close()
                del self.connections[connection]
        # Registration and the parent's fork receipt can arrive in either
        # order. Neither is permission to launch native work on its own.
        for connection, peer in self.connections.items():
            if peer["role"] != "group" or peer["group"]["status"] != "pending":
                continue
            group = peer["group"]
            launch = self.record["launches"][group["reservation"]]
            if stopping or launch["reported"]:
                group["status"] = "refused" if stopping else "acknowledged"
                launch["status"] = "registered"
                connection.sendall(b"stop\n" if stopping else b"go\n")
        for group in self.record["groups"]:
            if group["status"] != "draining":
                continue
            members = {p for p, row in rows.items() if row["group"] == group["pid"] and "Z" not in str(row["state"])}
            if not members:
                group.update(status="drained", retired=True)
                self.record["launches"][group["reservation"]]["status"] = "drained"
            elif time.monotonic() >= group["drain_deadline"]:
                raise ValueError(f"Supervisor {group['pid']} lost its lease with residual or ambiguous group members")
        # A reported child that exits before registering never received native
        # launch permission. Retire its number once no process still uses that
        # group, so later PID reuse cannot enter our accounting scope.
        for launch in self.record["launches"].values():
            if launch["status"] == "spawned" and not any(row["group"] == launch["pid"] for row in rows.values()):
                launch["status"] = "drained"
        self._persist()
        return rows

    def sample(self, root: int) -> int:
        try:
            if self.closed or self.root not in {None, root}:
                raise ValueError("Known-launch guard root changed or already closed")
            self.root = root
            rows = self._exchange(stopping=False)
            owned = {root} | {
                item["pid"]
                for item in self.record["launches"].values()
                if "pid" in item and item["status"] != "drained"
            }
            measured = [int(row["rss"]) for row in rows.values() if row["group"] in owned]
            rss = sum(measured)
            self.record.update(
                status="monitoring", last_sample={"rss_bytes": rss, "max_process_rss_bytes": max(measured, default=0)}
            )
            self._persist()
            return rss
        except BaseException as error:
            self.record.update(status="monitoring-failed", reason=f"{type(error).__name__}: {error}")
            self._persist()
            raise

    def close(self) -> None:
        """Refuse new reservations and drain both pending and acknowledged work."""
        if self.closed:
            return
        errors = []
        deadline = time.monotonic() + 6
        remaining = set()
        pending = []
        try:
            while True:
                rows = self._exchange(stopping=True)
                # Revoke active group leases; retain parent connections until
                # their already-authorized fork is reported or fails.
                for connection, peer in list(self.connections.items()):
                    if peer["role"] == "group":
                        peer["group"]["status"] = "revoked"
                        connection.close()
                        del self.connections[connection]
                launches = self.record["launches"]
                pending = [nonce for nonce, entry in launches.items() if "pid" not in entry and not entry["reported"]]
                owned = {entry["pid"] for entry in launches.values() if "pid" in entry and entry["status"] != "drained"}
                remaining = {pid for pid, row in rows.items() if row["group"] in owned and "Z" not in str(row["state"])}
                if not pending and not remaining:
                    break
                if time.monotonic() >= deadline:
                    break
                time.sleep(0.05)
        except BaseException as error:
            errors.append(f"Terminal process monitoring failed: {error}")
        finally:
            self.closed = True
            self.listener.close()
            for connection in self.connections:
                connection.close()
        if remaining or pending:
            errors.append(
                f"Residual/ambiguous processes {sorted(remaining)} or unresolved launch reservations {pending}"
            )
        self.record["cleanup"] = {"status": "failure" if errors else "success", "errors": errors}
        self._persist()
        shutil.rmtree(self.socket_directory)
        if errors:
            raise ValueError("; ".join(errors))


def launch_registered(command: list[str], endpoint: Path, python: str, **kwargs: Any) -> subprocess.Popen[Any]:
    """Reserve before fork and report the child PID before returning to source."""
    control = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    control.settimeout(5)
    try:
        control.connect(str(endpoint))
        control.sendall(b'{"kind":"reserve"}\n')
        nonce = control.recv(128).decode().strip()
        if len(nonce) != 48 or any(char not in "0123456789abcdef" for char in nonce):
            raise ValueError("Guard refused native launch reservation")
        try:
            process = subprocess.Popen(
                [
                    python,
                    "-I",
                    "-S",
                    str(Path(__file__).resolve()),
                    "--endpoint",
                    str(endpoint),
                    "--reservation",
                    nonce,
                    "--",
                    *command,
                ],
                **kwargs,
            )
        except BaseException:
            control.sendall(b'{"kind":"spawn-failed"}\n')
            raise
        control.sendall(json.dumps({"kind": "spawned", "pid": process.pid}).encode() + b"\n")
        if control.recv(64) != b"recorded\n":
            raise ValueError("Guard did not record the reserved native child")
        return process
    finally:
        control.close()


@contextmanager
def observe_racket_launch(module: ModuleType, request: dict[str, Any], endpoint: Path) -> Iterator[None]:
    """Replace only the exact source module's detached Popen call site."""
    source = (Path(request["checkout"]) / SOURCE).resolve()
    if (
        request.get("racket_group_containment") != CONTRACT
        or Path(module.__file__ or "").resolve() != source
        or request["source_hashes"].get(SOURCE) != SOURCE_SHA256
        or hashlib.sha256(source.read_bytes()).hexdigest() != SOURCE_SHA256
        or module.subprocess is not subprocess
    ):
        raise ValueError("Unsupported native Racket launch source or containment contract")
    expected = compile(source.read_text(), str(source), "exec", dont_inherit=True)
    candidates = [
        value
        for value in expected.co_consts
        if inspect.iscode(value) and value.co_name == "run_command_child_processes"
    ]
    if len(candidates) != 1 or module.run_command_child_processes.__code__ != candidates[0]:
        raise ValueError("Native Racket launch function was already changed")
    original = module.subprocess
    failures: list[str] = []

    class ScopedSubprocess:
        def Popen(self, command: Any, **kwargs: Any) -> subprocess.Popen[Any]:
            frame = inspect.currentframe()
            caller = frame.f_back if frame else None
            if (
                caller is None
                or caller.f_code != candidates[0]
                or not isinstance(command, list)
                or len(command) != 2
                or command[0] != "racket"
                or shutil.which("racket") != request["racket"]
                or hashlib.sha256(Path(request["racket"]).read_bytes()).hexdigest() != request["racket_sha256"]
                or not isinstance(command[1], str)
                or not Path(command[1]).is_file()
                or kwargs != {"start_new_session": True, "stdout": subprocess.DEVNULL, "stderr": subprocess.DEVNULL}
            ):
                failures.append("Unrecognized detached native launch refused before spawning")
                raise ValueError(failures[-1])
            try:
                return launch_registered(command, endpoint, request["python"], **kwargs)
            except BaseException as error:
                failures.append(f"Native launch containment failed: {type(error).__name__}: {error}")
                raise

        def __getattr__(self, name: str) -> Any:
            # Other source functions use inherited-group run/call for cleanup.
            if name not in {"DEVNULL", "TimeoutExpired", "run", "call"}:
                failures.append(f"Unsupported native subprocess operation: {name}")
                raise ValueError(failures[-1])
            return getattr(original, name)

    module.__dict__["subprocess"] = ScopedSubprocess()
    try:
        yield
    finally:
        module.__dict__["subprocess"] = original
        if failures:
            raise ValueError(
                "Native launcher observation failed, including possibly swallowed errors: " + "; ".join(failures)
            )


def supervise(endpoint: Path, command: list[str], reservation: str) -> int:
    """Keep the source-created session leader alive through native completion."""
    if os.getpid() != os.getpgrp() or len(command) != 2 or command[0] != "racket":
        raise ValueError("Supervisor must lead the original Racket launch group")
    connection = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    connection.settimeout(5)
    released = False

    def source_timeout(signum: int, _frame: FrameType | None) -> None:
        # The source deliberately signals this whole group. Keep its existing
        # timeout/fallback, but ensure TERM-resistant descendants cannot outlive
        # the supervisor by entering the same self-group cleanup as lease loss.
        raise SystemExit(128 + signum)

    previous_term = signal.signal(signal.SIGTERM, source_timeout)
    try:
        connection.connect(str(endpoint))
        registration = {
            "kind": "register",
            "reservation": reservation,
            "contract": CONTRACT,
            "pid": os.getpid(),
            "command": command,
            "script_sha256": hashlib.sha256(Path(command[1]).read_bytes()).hexdigest(),
        }
        connection.sendall(json.dumps(registration).encode() + b"\n")
        if connection.recv(64) != b"go\n":
            raise ValueError("Guard did not acknowledge Racket launch")
        connection.setblocking(False)
        if select.select([connection], [], [], 0)[0]:
            raise ValueError("Guard lease ended before Racket could start")
        process = subprocess.Popen(command)  # Inherits this acknowledged group and source streams.
        done = False
        while True:
            readable, _, _ = select.select([connection], [], [], 0.05)
            if readable:
                response = connection.recv(64)
                if response == b"release\n" and done:
                    released = True
                    return int(process.returncode)
                raise ValueError("Guard lease ended before native group release")
            if not done and process.poll() is not None:
                connection.sendall(json.dumps({"kind": "done", "returncode": process.returncode}).encode() + b"\n")
                done = True
    finally:
        if not released:
            os.killpg(os.getpgrp(), signal.SIGKILL)
        connection.close()
        signal.signal(signal.SIGTERM, previous_term)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", type=Path, required=True)
    parser.add_argument("--reservation", required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    result = supervise(
        args.endpoint, args.command[1:] if args.command[:1] == ["--"] else args.command, args.reservation
    )
    if result < 0:
        signal.signal(-result, signal.SIG_DFL)
        os.kill(os.getpid(), -result)
    raise SystemExit(result)
