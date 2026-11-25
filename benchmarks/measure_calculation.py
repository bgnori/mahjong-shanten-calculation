#!/usr/bin/env python3
"""Time a calculation after a ready/start handshake, separately from startup."""

import argparse
import json
import os
import re
import select
import subprocess
import sys
import tempfile
import time

from measure import kill_group, limit_memory


class ProtocolReader:
    def __init__(self, stream):
        self.fd = stream.fileno()
        self.pending = b""
        self.lines = []

    def wait_for(self, marker, deadline):
        while True:
            while b"\n" in self.pending:
                line, self.pending = self.pending.split(b"\n", 1)
                text = line.decode("utf-8")
                self.lines.append(text)
                if text == marker or (marker == "SHANTEN_RESULT" and text.startswith(marker + " ")):
                    return text
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([self.fd], [], [], remaining)[0]:
                raise TimeoutError
            chunk = os.read(self.fd, 4096)
            if not chunk:
                raise EOFError
            self.pending += chunk


def wait_child(pid, deadline):
    while True:
        waited, status, usage = os.wait4(pid, os.WNOHANG)
        if waited:
            return status, usage
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError
        time.sleep(min(0.01, remaining))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--startup-timeout", type=float, required=True)
    parser.add_argument("--calculation-timeout", type=float, required=True)
    parser.add_argument("--shutdown-timeout", type=float, default=5)
    parser.add_argument("--max-memory-mib", type=int, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER, help="controlled command after --")
    args = parser.parse_args()
    if any(not 0 < timeout < float("inf") for timeout in (
        args.startup_timeout, args.calculation_timeout, args.shutdown_timeout
    )):
        parser.error("timeouts must be positive finite numbers")
    if args.max_memory_mib <= 0:
        parser.error("--max-memory-mib must be positive")
    if args.command and args.command[0] == "--":
        args.command.pop(0)
    if not args.command:
        parser.error("a controlled command is required after --")

    with tempfile.TemporaryFile(mode="w+t") as errors:
        launch = time.monotonic()
        try:
            process = subprocess.Popen(
                args.command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=errors, start_new_session=True,
                preexec_fn=lambda: limit_memory(args.max_memory_mib),
            )
        except OSError as error:
            print(f"failed to start {args.command[0]}: {error}", file=sys.stderr)
            return 1
        reader = ProtocolReader(process.stdout)
        phase = "startup"
        startup_elapsed = None
        calculation_wall = None
        result_line = None
        calculation_ns = None
        iterations = None
        calculation_ns_per_iteration = None
        status = "success"
        try:
            try:
                reader.wait_for("SHANTEN_READY", launch + args.startup_timeout)
                startup_elapsed = time.monotonic() - launch
                if startup_elapsed > args.startup_timeout:
                    raise TimeoutError
                phase = "calculation"
                calculation_start = time.monotonic()
                process.stdin.write(b"RUN\n")
                process.stdin.flush()
                result_line = reader.wait_for(
                    "SHANTEN_RESULT", calculation_start + args.calculation_timeout
                )
                calculation_wall = time.monotonic() - calculation_start
                match = re.fullmatch(
                    r"SHANTEN_RESULT operation=(?:mentsu|overall|suit-dp|suit-overall|tile-dp|tile-overall|pruned-suit|pruned-overall|seven|orphans) "
                    r"case=[a-z0-9-]+ result=(?:none|some \(-\d+\)|some \d+) "
                    r"calculation_ns=(\d+)(?: iterations=(\d+))?", result_line,
                )
                if not match or (match.group(2) is not None and int(match.group(2)) == 0):
                    status = "invalid_result"
                else:
                    calculation_ns = int(match.group(1))
                    iterations = int(match.group(2)) if match.group(2) is not None else 1
                    if (calculation_wall > args.calculation_timeout or
                            calculation_ns > args.calculation_timeout * 1_000_000_000):
                        status = "calculation_timeout"
                    else:
                        calculation_ns_per_iteration = calculation_ns / iterations
                phase = "shutdown"
                child_status, usage = wait_child(
                    process.pid, time.monotonic() + args.shutdown_timeout
                )
            except TimeoutError:
                status = phase + "_timeout"
                if phase == "startup":
                    startup_elapsed = time.monotonic() - launch
                elif phase == "calculation":
                    calculation_wall = time.monotonic() - calculation_start
                kill_group(process.pid)
                _, child_status, usage = os.wait4(process.pid, 0)
            except (EOFError, BrokenPipeError):
                status = phase + "_failure"
                kill_group(process.pid)
                _, child_status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(child_status)
        finally:
            if process.returncode is None:
                kill_group(process.pid)
                _, child_status, _ = os.wait4(process.pid, 0)
                process.returncode = os.waitstatus_to_exitcode(child_status)
        if status == "success" and process.returncode != 0:
            status = "process_failure"
        errors.seek(0)
        sys.stderr.write(errors.read())
        print(json.dumps({
            "command": args.command,
            "status": status,
            "startup_timeout_seconds": args.startup_timeout,
            "calculation_timeout_seconds": args.calculation_timeout,
            "shutdown_timeout_seconds": args.shutdown_timeout,
            "max_memory_mib": args.max_memory_mib,
            "startup_elapsed_seconds": startup_elapsed,
            "calculation_wall_seconds": calculation_wall,
            "calculation_ns": calculation_ns,
            "iterations": iterations,
            "calculation_ns_per_iteration": calculation_ns_per_iteration,
            "result": result_line,
            "stdout_lines": reader.lines,
            "max_rss_kib": usage.ru_maxrss,
            "exit_code": process.returncode,
        }, ensure_ascii=False))
        if status.endswith("_timeout"):
            return 124
        return 0 if status == "success" else 1


if __name__ == "__main__":
    sys.exit(main())
