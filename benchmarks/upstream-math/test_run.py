"""Small standalone checks; no Cargo builds or benchmark engines are invoked."""

from __future__ import annotations

import importlib.util
import io
import json
import os
import signal
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from typing import Any
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("math_runner", Path(__file__).with_name("run.py"))
assert spec is not None and spec.loader is not None
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class RunnerTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.output = self.directory / "results.json"
        for name in (
            "Cargo.lock",
            "rust-toolchain.toml",
            "egg.rs",
            "egglog.rs",
            "math.egg",
            "run.py",
            *runner.ENGINES.values(),
        ):
            (self.directory / name).write_text(name)
        (self.directory / "Cargo.toml").write_text(
            '[dependencies]\negg = {git="egg-url",rev="egg-pin"}\negglog = {git="egglog-url",rev="egglog-pin"}\n'
        )

    def test_default_run_uses_seven_gib_and_existing_timeout(self) -> None:
        with patch.object(runner, "collect", return_value=0) as collect:
            self.assertEqual(runner.main(["--output", str(self.output)]), 0)
        self.assertEqual(collect.call_args.args[-2:], (7 * runner.GIB, 120))
        self.assertEqual(runner.HOST_RESERVE, 2 * runner.GIB)

    def test_cache_resumes_missing_points_and_separates_changed_identities(self) -> None:
        success = {"status": "success", "wall_seconds": 0.1, "peak_rss_bytes": 100, "reason": None}
        with (
            patch.object(runner, "run_process", return_value=(success, False)) as launch,
            patch("sys.stderr", io.StringIO()),
        ):
            self.assertEqual(runner.collect(self.directory, self.directory, self.output, 1, 1, 1000, 120), 0)
            self.assertEqual(launch.call_count, 2)
            self.assertEqual(runner.collect(self.directory, self.directory, self.output, 1, 1, 1000, 120), 0)
            self.assertEqual(launch.call_count, 2)
            self.assertEqual(runner.collect(self.directory, self.directory, self.output, 2, 2, 1000, 120), 0)
            self.assertEqual(launch.call_count, 8)
        before = self.output.read_bytes()
        with self.assertRaisesRegex(ValueError, "new --output"):
            runner.collect(self.directory, self.directory, self.output, 2, 2, 2000, 120)
        for filename in ("egg-math", "math.egg", "rust-toolchain.toml"):
            path = self.directory / filename
            original = path.read_text()
            path.write_text("changed")
            with self.assertRaisesRegex(ValueError, "new --output"):
                runner.collect(self.directory, self.directory, self.output, 2, 2, 1000, 120)
            path.write_text(original)
        self.assertEqual(self.output.read_bytes(), before)
        previous_method = json.loads(before)
        previous_method["metadata"]["timing"] = "old engine-reported duration"
        self.output.write_text(json.dumps(previous_method))
        with self.assertRaisesRegex(ValueError, "new --output"):
            runner.collect(self.directory, self.directory, self.output, 2, 2, 1000, 120)

    def test_job_failure_keeps_missing_larger_cutoffs_and_continues_other_engine(self) -> None:
        launched = []

        def fake(command: list[str], *_args: Any) -> tuple[dict[str, Any], bool]:
            engine, cutoff = Path(command[0]).name, int(command[1])
            launched.append((engine, cutoff))
            return (
                ({"status": "memory-limit", "reason": "limit"}, False)
                if (engine, cutoff) == ("egg-math", 2)
                else ({"status": "success", "wall_seconds": 0.01, "reason": None}, False)
            )

        with patch.object(runner, "run_process", side_effect=fake), patch("sys.stderr", io.StringIO()):
            self.assertEqual(runner.collect(self.directory, self.directory, self.output, 3, 2, 1000, 120), 1)
            calls = list(launched)
            self.assertEqual(runner.collect(self.directory, self.directory, self.output, 3, 2, 1000, 120), 1)
            self.assertEqual(launched, calls)
        self.assertNotIn(("egg-math", 3), launched)
        self.assertEqual(launched.count(("egg-math", 2)), 1)
        self.assertEqual(launched.count(("egglog-math", 3)), 2)
        rows = json.loads(self.output.read_text())["rows"]
        self.assertEqual(len(rows), 12)
        missing = [r for r in rows if r["engine"] == "Egg" and r["iterations"] == 3]
        self.assertTrue(all(r["status"] == "not-run" and r["wall_seconds"] is None for r in missing))

    def test_initial_host_stop_writes_complete_missing_grid_without_launch(self) -> None:
        with (
            patch.object(runner, "check_host", side_effect=RuntimeError("host pressure")),
            patch.object(runner.subprocess, "Popen") as launch,
            patch("sys.stderr", io.StringIO()),
        ):
            self.assertEqual(runner.collect(self.directory, self.directory, self.output, 3, 2, 1000, 120), 2)
            launch.assert_not_called()
        rows = json.loads(self.output.read_text())["rows"]
        self.assertEqual(len(rows), 12)
        self.assertTrue(all(r["status"] == "not-run" and r["wall_seconds"] is None for r in rows))
        self.assertTrue(all("host pressure" in r["reason"] for r in rows))

    def test_runtime_safety_stop_halts_remaining_engines(self) -> None:
        stopped = {"status": "resource-stopped", "wall_seconds": 0.1, "reason": "host pressure"}
        with (
            patch.object(runner, "run_process", return_value=(stopped, True)) as launch,
            patch("sys.stderr", io.StringIO()),
        ):
            self.assertEqual(runner.collect(self.directory, self.directory, self.output, 2, 2, 1000, 120), 2)
            self.assertEqual(launch.call_count, 1)
        rows = json.loads(self.output.read_text())["rows"]
        self.assertEqual(rows[0]["status"], "resource-stopped")
        self.assertTrue(all(r["status"] == "not-run" for r in rows[1:]))

    def test_process_group_sampling_includes_descendants_only(self) -> None:
        with patch.object(runner.subprocess, "check_output", return_value="10 12 S\n10 23 R\n10 0 Z\n20 9000 S\n"):
            self.assertEqual(runner.group_state(10), (35 * 1024, True))

    def test_memory_stop_kills_and_reaps_launched_child(self) -> None:
        children = []
        original = subprocess.Popen

        def launch(*args: Any, **kwargs: Any) -> subprocess.Popen[bytes]:
            child = original(*args, **kwargs)
            children.append(child)
            return child

        with (
            patch.object(runner, "check_host"),
            patch.object(runner, "group_state", return_value=(2000, True)),
            patch.object(runner.subprocess, "Popen", side_effect=launch),
        ):
            result, halt = runner.run_process(
                [sys.executable, "-c", "import time;time.sleep(10)"], self.directory, 1000, 2
            )
        self.assertEqual(result["status"], "memory-limit")
        self.assertFalse(halt)
        self.assertEqual(children[0].returncode, -signal.SIGKILL)
        with self.assertRaises(ChildProcessError):
            os.waitpid(children[0].pid, os.WNOHANG)

    def test_success_cleanup_also_kills_descendant(self) -> None:
        pidfile = self.directory / "group.txt"
        source = (
            "import os,subprocess,sys;from pathlib import Path;"
            "subprocess.Popen([sys.executable,'-c','import time;time.sleep(10)']);"
            f"Path({str(pidfile)!r}).write_text(str(os.getpid()))"
        )
        with patch.object(runner, "check_host"):
            result, halt = runner.run_process([sys.executable, "-c", source], self.directory, runner.GIB, 2)
        self.assertEqual(result["status"], "success")
        self.assertGreater(result["wall_seconds"], 0)
        self.assertNotIn("seconds", result)
        self.assertFalse(halt)
        # A terminated descendant can briefly remain a zombie; it must not live.
        for _ in range(20):
            if not runner.group_state(int(pidfile.read_text()))[1]:
                break
            runner.time.sleep(0.01)
        self.assertFalse(runner.group_state(int(pidfile.read_text()))[1])

    def test_post_exit_peak_rejects_fast_success_even_when_sampling_misses_it(self) -> None:
        original = os.wait4
        for system in ("darwin", "linux"):
            reaped: list[int] = []
            expected_peak = 8 * runner.GIB

            def wait4(
                pid: int,
                flags: int,
                recorded: list[int] = reaped,
                raw_peak: int = expected_peak if system == "darwin" else expected_peak // 1024,
            ) -> tuple[int, int, Any]:
                child, status, usage = original(pid, flags)
                if child:
                    recorded.append(child)
                    return child, status, SimpleNamespace(ru_maxrss=raw_peak)
                return child, status, usage

            with (
                self.subTest(system=system),
                patch.object(runner.sys, "platform", system),
                patch.object(runner, "check_host"),
                patch.object(runner, "group_state", return_value=(0, False)),
                patch.object(runner.os, "wait4", side_effect=wait4),
                patch.object(runner.subprocess.Popen, "poll", side_effect=AssertionError("poll must not reap child")),
            ):
                result, halt = runner.run_process([sys.executable, "-c", "pass"], self.directory, runner.GIB, 2)
            self.assertEqual(result["status"], "memory-limit")
            self.assertEqual(result["peak_rss_bytes"], expected_peak)
            self.assertIn("detected after exit", result["reason"])
            self.assertNotIn("seconds", result)
            self.assertFalse(halt)
            self.assertEqual(len(reaped), 1)
            with self.assertRaises(ChildProcessError):
                os.waitpid(reaped[0], os.WNOHANG)

    def test_unexpected_sigkill_stops_campaign_without_claiming_oom(self) -> None:
        with patch.object(runner, "check_host"):
            result, halt = runner.run_process(
                [sys.executable, "-c", "import os,signal;os.kill(os.getpid(),signal.SIGKILL)"],
                self.directory,
                runner.GIB,
                2,
            )
        self.assertTrue(halt)
        self.assertEqual(result["status"], "resource-stopped")
        self.assertIn("SIGKILL (cause unknown)", result["reason"])
        self.assertNotIn("seconds", result)

    def test_timeout_is_not_reported_as_unexpected_sigkill(self) -> None:
        with patch.object(runner, "check_host"):
            result, halt = runner.run_process(
                [sys.executable, "-c", "import time;time.sleep(10)"], self.directory, runner.GIB, 0.05
            )
        self.assertFalse(halt)
        self.assertEqual(result["status"], "timed-out")

    def test_large_failure_logs_keep_bounded_stderr_tail(self) -> None:
        with patch.object(runner, "check_host"):
            result, halt = runner.run_process(
                [
                    sys.executable,
                    "-c",
                    "import sys;sys.stdout.write('x'*2000000);sys.stderr.write('specific error');sys.exit(1)",
                ],
                self.directory,
                runner.GIB,
                2,
            )
        self.assertEqual(result["reason"], "exit 1: specific error")
        self.assertFalse(halt)

    def test_monitor_failure_stops_child(self) -> None:
        with (
            patch.object(runner, "check_host"),
            patch.object(runner, "group_state", side_effect=ValueError("bad ps output")),
        ):
            result, halt = runner.run_process(
                [sys.executable, "-c", "import time;time.sleep(10)"], self.directory, runner.GIB, 2
            )
        self.assertEqual(result["status"], "resource-stopped")
        self.assertIn("bad ps output", result["reason"])
        self.assertTrue(halt)

    def test_mac_pressure_and_linux_reserve_are_not_disabled_by_job_limit(self) -> None:
        with (
            patch.object(runner.sys, "platform", "darwin"),
            patch.object(runner.subprocess, "check_output", return_value=b"2\n"),
            self.assertRaisesRegex(RuntimeError, "kernel level 2"),
        ):
            runner.check_host()
        with (
            patch.object(runner.sys, "platform", "linux"),
            patch.object(Path, "read_text", return_value="MemAvailable: 1048576 kB\n"),
            self.assertRaisesRegex(RuntimeError, "2 GiB reserve"),
        ):
            runner.check_host()

    def test_zero_duration_and_out_of_range_cutoff_are_rejected(self) -> None:
        with (
            patch.object(runner, "check_host"),
            patch.object(runner, "group_state", return_value=(0, False)),
            patch.object(runner.time, "monotonic", return_value=1),
        ):
            result, halt = runner.run_process([sys.executable, "-c", "pass"], self.directory, runner.GIB, 2)
        self.assertEqual(result["status"], "failure")
        self.assertIn("positive", result["reason"])
        self.assertIsNone(result["wall_seconds"])
        self.assertFalse(halt)
        with patch("sys.stderr", io.StringIO()), self.assertRaises(SystemExit):
            runner.main(["--iterations", "14"])

    def test_slow_monitor_does_not_quantize_silent_child_wall_time(self) -> None:
        def slow_sample(_group: int) -> tuple[int, bool]:
            runner.time.sleep(0.5)
            return 0, False

        before = runner.time.monotonic()
        with patch.object(runner, "check_host"), patch.object(runner, "group_state", side_effect=slow_sample):
            result, halt = runner.run_process([sys.executable, "-c", "pass"], self.directory, runner.GIB, 2)
        elapsed = runner.time.monotonic() - before
        self.assertEqual(result["status"], "success")
        self.assertFalse(halt)
        self.assertNotIn("seconds", result)
        self.assertGreater(result["wall_seconds"], 0)
        self.assertLess(result["wall_seconds"], 0.25)
        self.assertGreater(elapsed - result["wall_seconds"], 0.25)

    def test_watchdog_host_stop_kills_child_and_retains_failure(self) -> None:
        with patch.object(runner, "check_host", side_effect=[None, RuntimeError("host pressure")]):
            result, halt = runner.run_process(
                [sys.executable, "-c", "import time;time.sleep(10)"], self.directory, runner.GIB, 2
            )
        self.assertEqual(result["status"], "resource-stopped")
        self.assertIn("host pressure", result["reason"])
        self.assertNotIn("Unexpected", result["reason"])
        self.assertGreater(result["wall_seconds"], 0)
        self.assertTrue(halt)

    def test_delayed_monitor_errors_after_completion_do_not_invalidate_success(self) -> None:
        original_event = runner.threading.Event
        events: list[Any] = []
        failures: list[str] = []

        def event_factory() -> Any:
            event = original_event()
            events.append(event)
            return event

        def delayed_failure(*_args: Any) -> Any:
            self.assertTrue(events[0].wait(2))
            failures.append("after completion")
            raise RuntimeError("late monitor failure")

        for failing_monitor in ("group_state", "check_host"):
            events.clear()
            failures.clear()
            with (
                self.subTest(monitor=failing_monitor),
                patch.object(runner.threading, "Event", side_effect=event_factory),
                patch.object(runner, "group_state", return_value=(0, False)) as sample,
                patch.object(runner, "check_host") as host,
            ):
                if failing_monitor == "group_state":
                    sample.side_effect = delayed_failure
                else:
                    host.side_effect = lambda *_args: delayed_failure() if events else None
                result, halt = runner.run_process(
                    [sys.executable, "-c", "import time;time.sleep(0.05)"], self.directory, runner.GIB, 2
                )
            self.assertEqual(failures, ["after completion"])
            self.assertEqual(result["status"], "success")
            self.assertFalse(halt)

    def test_group_signal_failure_uses_only_owned_child_fallback(self) -> None:
        original_kill = os.kill
        with (
            patch.object(runner, "check_host", side_effect=[None, RuntimeError("host pressure")]),
            patch.object(runner.os, "killpg", side_effect=PermissionError("group denied")) as group_signal,
            patch.object(runner.os, "kill", wraps=original_kill) as child_signal,
        ):
            result, halt = runner.run_process(
                [sys.executable, "-c", "import time;time.sleep(10)"], self.directory, runner.GIB, 2
            )
        self.assertEqual(result["status"], "resource-stopped")
        self.assertIn("owned-child fallback", result["reason"])
        self.assertTrue(halt)
        self.assertEqual(child_signal.call_args.args, group_signal.call_args_list[0].args)
        self.assertEqual(child_signal.call_count, 1)
        with self.assertRaises(ChildProcessError):
            os.waitpid(child_signal.call_args.args[0], os.WNOHANG)

    def test_post_exit_timeout_survives_delayed_monitor(self) -> None:
        def delayed_sample(_group: int) -> tuple[int, bool]:
            runner.time.sleep(0.2)
            return 0, False

        with patch.object(runner, "check_host"), patch.object(runner, "group_state", side_effect=delayed_sample):
            result, halt = runner.run_process(
                [sys.executable, "-c", "import time;time.sleep(0.05)"], self.directory, runner.GIB, 0.01
            )
        self.assertEqual(result["status"], "timed-out")
        self.assertIn("detected after exit", result["reason"])
        self.assertGreaterEqual(result["wall_seconds"], 0.01)
        self.assertFalse(halt)

    def test_interrupted_blocking_wait_kills_and_reaps_owned_child(self) -> None:
        original = os.wait4
        reaped: list[int] = []
        first = True

        def interrupted(pid: int, flags: int) -> tuple[int, int, Any]:
            nonlocal first
            if first:
                first = False
                raise KeyboardInterrupt
            child, status, usage = original(pid, flags)
            reaped.append(child)
            return child, status, usage

        with (
            patch.object(runner, "check_host"),
            patch.object(runner.os, "wait4", side_effect=interrupted),
            self.assertRaises(KeyboardInterrupt),
        ):
            runner.run_process([sys.executable, "-c", "import time;time.sleep(10)"], self.directory, runner.GIB, 2)
        self.assertEqual(len(reaped), 1)
        with self.assertRaises(ChildProcessError):
            os.waitpid(reaped[0], os.WNOHANG)

    def test_build_disk_reserve_blocks_before_launch(self) -> None:
        with (
            patch.object(runner.sys, "platform", "linux"),
            patch.object(Path, "read_text", return_value="MemAvailable: 9999999 kB\n"),
            patch.object(runner.shutil, "disk_usage", return_value=type("Disk", (), {"free": runner.GIB})()),
            patch.object(runner.subprocess, "Popen") as launch,
        ):
            result, halt = runner.run_process(["cargo", "build"], self.directory, runner.GIB, 2, build=True)
        self.assertEqual(result["status"], "not-run")
        self.assertIn("3 GiB", result["reason"])
        self.assertTrue(halt)
        launch.assert_not_called()


if __name__ == "__main__":
    unittest.main()
