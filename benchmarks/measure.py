#!/usr/bin/env python3
"""Measure one command on Linux, including timed-out and failed runs."""

import argparse
import json
import os
import resource
import signal
import subprocess
import sys
import tempfile
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, required=True, help="timeout in seconds")
    parser.add_argument(
        "--max-memory-mib", type=int, required=True,
        help="per-process virtual memory limit in MiB",
    )
    parser.add_argument("command", nargs=argparse.REMAINDER, help="command after --")
    args = parser.parse_args()
    if not 0 < args.timeout < float("inf"):
        parser.error("--timeout must be a positive finite number")
    if args.max_memory_mib <= 0:
        parser.error("--max-memory-mib must be positive")
    if args.command and args.command[0] == "--":
        args.command.pop(0)
    if not args.command:
        parser.error("a command is required after --")

    def limit_memory():
        limit = args.max_memory_mib * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))

    def kill_group(pid):
        try:
            os.killpg(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    with tempfile.TemporaryFile(mode="w+t") as output, tempfile.TemporaryFile(mode="w+t") as errors:
        start = time.monotonic()
        try:
            process = subprocess.Popen(
                args.command, stdout=output, stderr=errors, start_new_session=True,
                preexec_fn=limit_memory,
            )
        except OSError as error:
            print(f"failed to start {args.command[0]}: {error}", file=sys.stderr)
            return 1
        timed_out = False
        try:
            while True:
                pid, status, usage = os.wait4(process.pid, os.WNOHANG)
                if pid:
                    break
                remaining = args.timeout - (time.monotonic() - start)
                if remaining <= 0:
                    timed_out = True
                    kill_group(process.pid)
                    _, status, usage = os.wait4(process.pid, 0)
                    break
                time.sleep(min(0.01, remaining))
        except KeyboardInterrupt:
            kill_group(process.pid)
            os.wait4(process.pid, 0)
            process.returncode = -signal.SIGKILL
            raise
        elapsed = time.monotonic() - start
        process.returncode = os.waitstatus_to_exitcode(status)
        output.seek(0)
        errors.seek(0)
        text = output.read()
        sys.stdout.write(text)
        if text and not text.endswith("\n"):
            sys.stdout.write("\n")
        sys.stderr.write(errors.read())
        print(json.dumps({
            "command": args.command,
            "timeout_seconds": args.timeout,
            "max_memory_mib": args.max_memory_mib,
            "elapsed_seconds": elapsed,
            "max_rss_kib": usage.ru_maxrss,
            "exit_code": process.returncode,
            "timed_out": timed_out,
        }, ensure_ascii=False))
        return 124 if timed_out else process.returncode if process.returncode >= 0 else 128 - process.returncode


if __name__ == "__main__":
    sys.exit(main())
