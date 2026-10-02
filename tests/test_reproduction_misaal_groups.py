"""Known-launch protocol tests: sockets are local; no native children execute."""

from __future__ import annotations

import hashlib
import json
import signal
import socket
import subprocess
from collections.abc import Iterator
from pathlib import Path
from types import ModuleType, SimpleNamespace
from typing import Any

import pytest

from scripts import reproduction_misaal_groups as groups


@pytest.fixture(params=["eof", "reset"])
def registry(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, request: pytest.FixtureRequest) -> Iterator[tuple]:
    identities = iter([(201, "test-birth-201"), (202, "test-birth-202")])
    monkeypatch.setattr(groups, "peer_identity", lambda _connection: next(identities))
    state = {
        100: {"parent": 1, "group": 100, "rss": 10, "state": "S"},
        201: {"parent": 100, "group": 100, "rss": 20, "state": "S"},
        202: {"parent": 201, "group": 202, "rss": 30, "state": "S"},
        203: {"parent": 202, "group": 202, "rss": 40, "state": "S"},
        204: {"parent": 203, "group": 202, "rss": 50, "state": "S"},
        900: {"parent": 1, "group": 900, "rss": 999, "state": "S"},
    }
    monkeypatch.setattr(groups, "process_snapshot", lambda: state)
    guard = groups.RacketGroups(tmp_path / "groups")
    if request.param == "reset":
        original_recv = socket.socket.recv

        def recv(connection: socket.socket, buffersize: int, flags: int = 0) -> bytes:
            content = original_recv(connection, buffersize, flags)
            if connection in guard.connections and content == b"":
                # Linux can report reset instead of EOF when the peer closes
                # with an unread lifecycle acknowledgment.
                raise ConnectionResetError("simulated peer reset")
            return content

        monkeypatch.setattr(socket.socket, "recv", recv)
    control = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    control.connect(str(guard.endpoint))
    control.sendall(b'{"kind":"reserve"}\n')
    assert guard.sample(100) == 30
    nonce = control.recv(128).decode().strip()
    control.sendall(b'{"kind":"spawned","pid":202}\n')
    client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    client.connect(str(guard.endpoint))
    client.sendall(
        json.dumps(
            {
                "kind": "register",
                "reservation": nonce,
                "pid": 202,
                "contract": groups.CONTRACT,
                "command": ["racket", "actual.rkt"],
                "script_sha256": "actual-script",
            }
        ).encode()
        + b"\n"
    )
    yield guard, client, state
    state.clear()
    client.close()
    control.close()
    guard.close()


def test_registration_waits_for_guard_and_counts_both_groups_once(registry: tuple) -> None:
    guard, client, _ = registry
    client.setblocking(False)
    with pytest.raises(BlockingIOError):
        client.recv(64)
    assert guard.sample(100) == 150
    assert client.recv(64) == b"go\n"
    assert guard.record["groups"][0]["identity"] == "test-birth-202"


def test_immediate_root_exit_refuses_reservation_before_first_sample(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(groups, "peer_identity", lambda _: (201, "birth"))
    monkeypatch.setattr(groups, "process_snapshot", lambda: {})
    guard = groups.RacketGroups(tmp_path / "groups")
    client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    client.connect(str(guard.endpoint))
    client.sendall(b'{"kind":"reserve"}\n')
    guard.close()
    assert client.recv(64) == b"stop\n"
    assert guard.record["launches"] == {}
    assert guard.record["cleanup"]["status"] == "success"
    client.close()


def test_source_local_timeout_with_empty_group_preserves_source_failure(registry: tuple) -> None:
    guard, client, state = registry
    guard.sample(100)
    assert client.recv(64) == b"go\n"
    client.close()
    for pid in (202, 203, 204):
        del state[pid]
    assert guard.sample(100) == 30
    assert guard.record["groups"][0]["status"] == "drained"


@pytest.mark.parametrize("replacement", [False, True])
def test_lost_lease_with_residual_or_reused_pid_never_signals_other_groups(
    registry: tuple, monkeypatch: pytest.MonkeyPatch, replacement: bool
) -> None:
    guard, client, state = registry
    guard.sample(100)
    client.recv(64)
    client.close()
    state.pop(202)
    if replacement:
        state[202] = {"parent": 1, "group": 202, "rss": 17, "state": "S"}
    monkeypatch.setattr(groups.os, "killpg", lambda *_: pytest.fail("must not signal an ambiguous/reused group"))
    guard.sample(100)
    assert guard.record["groups"][0]["status"] == "draining"
    deadline = guard.record["groups"][0]["drain_deadline"]
    monkeypatch.setattr(groups.time, "monotonic", lambda: deadline + 1)
    with pytest.raises(ValueError, match="residual or ambiguous"):
        guard.sample(100)
    assert guard.record["status"] == "monitoring-failed"


def test_unrelated_reservation_is_not_acknowledged(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(groups, "peer_identity", lambda _: (900, "unrelated"))
    monkeypatch.setattr(groups, "process_snapshot", lambda: {900: {"group": 900}, 100: {"group": 100}})
    guard = groups.RacketGroups(tmp_path / "groups")
    client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    client.connect(str(guard.endpoint))
    client.sendall(b'{"kind":"reserve"}\n')
    with pytest.raises(ValueError, match="outside the guarded"):
        guard.sample(100)
    client.setblocking(False)
    with pytest.raises(BlockingIOError):
        client.recv(64)
    client.close()
    guard.close()


def test_racket_result_releases_only_a_drained_group(registry: tuple) -> None:
    guard, client, state = registry
    guard.sample(100)
    client.recv(64)
    state.pop(203)
    state.pop(204)
    client.sendall(b'{"kind":"done","returncode":7}\n')
    guard.sample(100)
    assert client.recv(64) == b"release\n"
    assert guard.record["groups"][0]["returncode"] == 7


def test_racket_success_with_residual_processes_fails_closed(registry: tuple) -> None:
    guard, client, _ = registry
    guard.sample(100)
    client.recv(64)
    client.sendall(b'{"kind":"done","returncode":0}\n')
    with pytest.raises(ValueError, match="unexpected residual"):
        guard.sample(100)


def test_monitoring_failure_is_retained_and_pending_leases_are_closed(
    registry: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    guard, client, state = registry
    monkeypatch.setattr(groups, "process_snapshot", lambda: (_ for _ in ()).throw(OSError("monitor failed")))
    with pytest.raises(OSError, match="monitor failed"):
        guard.sample(100)
    with pytest.raises(ValueError, match="Terminal process monitoring failed"):
        guard.close()
    assert client.recv(64) == b""
    assert guard.record["cleanup"]["status"] == "failure"
    assert "monitor failed" in guard.record["reason"]
    state.clear()


@pytest.mark.parametrize("failure", ["before-ack", "after-ack", None])
def test_supervisor_lease_controls_launch_and_preserves_real_result(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure: str | None
) -> None:
    script = tmp_path / "program.rkt"
    script.write_text("unchanged source")
    launched = []
    signals = []
    sent = []
    responses = iter([b"" if failure == "before-ack" else b"go\n", b"release\n"])
    connection = SimpleNamespace(
        settimeout=lambda _: None,
        connect=lambda _: None,
        setblocking=lambda _: None,
        recv=lambda _: next(responses),
        sendall=lambda value: sent.append(value),
        close=lambda: None,
    )
    monkeypatch.setattr(groups.socket, "socket", lambda *_: connection)
    monkeypatch.setattr(groups.os, "getpid", lambda: 202)
    monkeypatch.setattr(groups.os, "getpgrp", lambda: 202)
    monkeypatch.setattr(groups.os, "killpg", lambda *args: signals.append(args))
    selections = iter([failure == "after-ack", False, True])
    monkeypatch.setattr(groups.select, "select", lambda *args: ([connection] if next(selections) else [], [], []))

    def popen(command: list[str]) -> Any:
        launched.append(command)
        return SimpleNamespace(returncode=7, poll=lambda: 7)

    monkeypatch.setattr(groups.subprocess, "Popen", popen)
    if failure:
        with pytest.raises(ValueError, match="Guard"):
            groups.supervise(tmp_path / "socket", ["racket", str(script)], "a" * 48)
        assert launched == [] and signals == [(202, signal.SIGKILL)]
    else:
        assert groups.supervise(tmp_path / "socket", ["racket", str(script)], "a" * 48) == 7
        assert launched == [["racket", str(script)]] and signals == []
        assert json.loads(sent[-1]) == {"kind": "done", "returncode": 7}


def test_malformed_process_monitoring_is_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(groups.subprocess, "run", lambda *_args, **_kw: subprocess.CompletedProcess([], 0, "bad row"))
    with pytest.raises(ValueError, match="Malformed"):
        groups.process_snapshot()


def test_only_pinned_source_launch_is_wrapped_with_unchanged_streams_and_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = tmp_path / groups.SOURCE
    source.parent.mkdir(parents=True)
    source.write_text(
        "import subprocess\n"
        "def run_command_child_processes(cmd):\n"
        "    return subprocess.Popen(cmd, start_new_session=True,\n"
        "                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)\n"
    )
    module = ModuleType("utils.DSLInstructionUtils")
    module.__file__ = str(source)
    exec(compile(source.read_text(), str(source), "exec", dont_inherit=True), module.__dict__)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    monkeypatch.setattr(groups, "SOURCE_SHA256", digest)
    script = tmp_path / "source.rkt"
    script.write_text("unchanged Racket statements")
    executable = tmp_path / "racket"
    executable.write_text("pinned fake executable; never run")
    request = {
        "checkout": str(tmp_path),
        "racket_group_containment": groups.CONTRACT,
        "source_hashes": {groups.SOURCE: digest},
        "python": "pinned-python",
        "racket": str(executable),
        "racket_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
    }
    monkeypatch.setattr(groups.shutil, "which", lambda _: str(executable))
    launches = []
    sentinel = object()

    def launch(command: list[str], endpoint: Path, python: str, **kw: Any) -> Any:
        launches.append((command, endpoint, python, kw))
        return sentinel

    monkeypatch.setattr(groups, "launch_registered", launch)
    with (
        pytest.raises(ValueError, match="possibly swallowed errors"),
        groups.observe_racket_launch(module, request, tmp_path / "socket"),
    ):
        assert module.run_command_child_processes(["racket", str(script)]) is sentinel
        with pytest.raises(ValueError, match="Unrecognized detached"):
            module.subprocess.Popen(["unexpected"], start_new_session=True)
    assert len(launches) == 1
    command, endpoint, python, kwargs = launches[0]
    assert command == ["racket", str(script)]
    assert endpoint == tmp_path / "socket" and python == "pinned-python"
    assert kwargs == {"start_new_session": True, "stdout": subprocess.DEVNULL, "stderr": subprocess.DEVNULL}
    assert module.subprocess is subprocess
    source.write_text(source.read_text() + "# changed native source\n")
    with (
        pytest.raises(ValueError, match="Unsupported native Racket"),
        groups.observe_racket_launch(module, request, tmp_path / "socket"),
    ):
        pytest.fail("changed source cannot install containment")


def test_retired_group_number_is_not_counted_after_pid_reuse(registry: tuple) -> None:
    guard, client, state = registry
    guard.sample(100)
    client.recv(64)
    client.close()
    for pid in (202, 203, 204):
        del state[pid]
    assert guard.sample(100) == 30
    state[202] = {"parent": 1, "group": 202, "rss": 9999, "state": "S"}
    assert guard.sample(100) == 30


def test_registration_before_parent_pid_report_stays_pending(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    identities = iter([(201, "source-birth"), (202, "supervisor-birth")])
    monkeypatch.setattr(groups, "peer_identity", lambda _: next(identities))
    state = {
        100: {"group": 100, "rss": 1, "state": "S"},
        201: {"group": 100, "rss": 2, "state": "S"},
        202: {"group": 202, "rss": 3, "state": "S"},
    }
    monkeypatch.setattr(groups, "process_snapshot", lambda: state)
    guard = groups.RacketGroups(tmp_path / "groups")
    control = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    control.connect(str(guard.endpoint))
    control.sendall(b'{"kind":"reserve"}\n')
    guard.sample(100)
    nonce = control.recv(128).decode().strip()
    client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    client.connect(str(guard.endpoint))
    client.sendall(
        json.dumps(
            {
                "kind": "register",
                "reservation": nonce,
                "contract": groups.CONTRACT,
                "pid": 202,
                "command": ["racket", "actual.rkt"],
                "script_sha256": "actual",
            }
        ).encode()
        + b"\n"
    )
    assert guard.sample(100) == 6
    client.setblocking(False)
    with pytest.raises(BlockingIOError):
        client.recv(64)
    assert guard.record["groups"][0]["status"] == "pending"
    control.sendall(b'{"kind":"spawned","pid":202}\n')
    guard.sample(100)
    assert control.recv(64) == b"recorded\n"
    assert client.recv(64) == b"go\n"
    state.clear()
    client.close()
    control.close()
    guard.close()


def test_interrupted_reservation_is_cleanup_failure_not_success(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(groups, "peer_identity", lambda _: (201, "source-birth"))
    state = {100: {"group": 100, "rss": 1}, 201: {"group": 100, "rss": 2}}
    monkeypatch.setattr(groups, "process_snapshot", lambda: state)
    guard = groups.RacketGroups(tmp_path / "groups")
    control = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    control.connect(str(guard.endpoint))
    control.sendall(b'{"kind":"reserve"}\n')
    guard.sample(100)
    assert len(control.recv(128).strip()) == 48
    control.close()
    state.clear()
    clock = iter([0, 7])
    monkeypatch.setattr(groups.time, "monotonic", lambda: next(clock))
    with pytest.raises(ValueError, match="unresolved launch reservations"):
        guard.close()
    assert guard.record["cleanup"]["status"] == "failure"
    assert not guard.endpoint.exists()


@pytest.mark.parametrize("failure", [None, "refused", "fork", "record"])
def test_launch_reserves_before_fork_and_reports_pid_before_return(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure: str | None
) -> None:
    events: list[Any] = []
    responses = iter(
        [b"stop\n" if failure == "refused" else b"a" * 48 + b"\n", b"" if failure == "record" else b"recorded\n"]
    )
    connection = SimpleNamespace(
        settimeout=lambda _: None,
        connect=lambda _: None,
        recv=lambda _: next(responses),
        sendall=lambda b: events.append(json.loads(b)),
        close=lambda: events.append("closed"),
    )
    monkeypatch.setattr(groups.socket, "socket", lambda *_: connection)
    process = SimpleNamespace(pid=202)

    def popen(command: list[str], **kwargs: Any) -> Any:
        events.append(("fork", command, kwargs))
        if failure == "fork":
            raise OSError("fork failed")
        return process

    monkeypatch.setattr(groups.subprocess, "Popen", popen)
    kwargs = {"start_new_session": True, "stdout": subprocess.DEVNULL, "stderr": subprocess.DEVNULL}
    if failure:
        with pytest.raises((ValueError, OSError)):
            groups.launch_registered(["racket", "actual.rkt"], tmp_path / "socket", "python", **kwargs)
    else:
        assert groups.launch_registered(["racket", "actual.rkt"], tmp_path / "socket", "python", **kwargs) is process
    assert events[0] == {"kind": "reserve"} and events[-1] == "closed"
    if failure == "refused":
        assert events == [{"kind": "reserve"}, "closed"]
    else:
        assert events[1][0] == "fork" and events[1][2] == kwargs
        assert events[1][1][-5:] == ["--reservation", "a" * 48, "--", "racket", "actual.rkt"]
        assert events[2] == ({"kind": "spawn-failed"} if failure == "fork" else {"kind": "spawned", "pid": 202})


def test_source_local_timeout_allows_transient_signal_drain(registry: tuple) -> None:
    guard, client, state = registry
    guard.sample(100)
    client.recv(64)
    client.close()
    state.pop(202)
    assert guard.sample(100) == 120
    assert guard.record["groups"][0]["status"] == "draining"
    state.pop(203)
    state.pop(204)
    assert guard.sample(100) == 30
    assert guard.record["groups"][0]["status"] == "drained"
    assert guard.record["status"] == "monitoring"


def test_native_source_sigterm_reaches_self_group_kill_before_socket_close(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    script = tmp_path / "actual.rkt"
    script.write_text("unchanged Racket statements")
    events: list[Any] = []
    handlers: dict[int, Any] = {}
    connection = SimpleNamespace(
        settimeout=lambda _: None,
        connect=lambda _: None,
        recv=lambda _: b"go\n",
        setblocking=lambda _: None,
        sendall=lambda _: None,
        close=lambda: events.append("closed"),
    )
    monkeypatch.setattr(groups.socket, "socket", lambda *_: connection)
    monkeypatch.setattr(groups.os, "getpid", lambda: 202)
    monkeypatch.setattr(groups.os, "getpgrp", lambda: 202)
    monkeypatch.setattr(groups.os, "killpg", lambda *args: events.append(("kill", *args)))

    def signal_handler(signum: int, handler: Any) -> int:
        handlers[signum] = handler
        return signal.SIG_DFL

    monkeypatch.setattr(groups.signal, "signal", signal_handler)
    selections = iter([False, True])

    def select(*_args: Any) -> tuple:
        if next(selections):
            handlers[signal.SIGTERM](signal.SIGTERM, None)
        return [], [], []

    monkeypatch.setattr(groups.select, "select", select)
    monkeypatch.setattr(groups.subprocess, "Popen", lambda command: events.append(("work", command)))
    with pytest.raises(SystemExit) as stopped:
        groups.supervise(tmp_path / "socket", ["racket", str(script)], "a" * 48)
    assert stopped.value.code == 128 + signal.SIGTERM
    assert events == [("work", ["racket", str(script)]), ("kill", 202, signal.SIGKILL), "closed"]
