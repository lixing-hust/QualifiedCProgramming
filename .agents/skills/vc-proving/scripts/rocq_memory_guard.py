#!/usr/bin/env python3
"""Kill wrapped Rocq processes once total process-tree RSS exceeds a limit."""

from __future__ import annotations

import argparse
import os
import signal
import subprocess
import sys
import time


POLL_INTERVAL_SECONDS = 0.2
DEFAULT_LIMIT_BYTES = 4 * 1024 * 1024 * 1024


def _children_of(pid: int) -> list[int]:
    path = f"/proc/{pid}/task/{pid}/children"
    try:
        text = open(path, "r", encoding="utf-8").read().strip()
    except OSError:
        return []
    if not text:
        return []
    result: list[int] = []
    for chunk in text.split():
        try:
            result.append(int(chunk))
        except ValueError:
            continue
    return result


def _rss_bytes(pid: int) -> int:
    try:
        with open(f"/proc/{pid}/status", "r", encoding="utf-8") as fh:
            for line in fh:
                if line.startswith("VmRSS:"):
                    parts = line.split()
                    if len(parts) >= 2:
                        return int(parts[1]) * 1024
    except OSError:
        return 0
    return 0


def _process_tree_rss(pid: int) -> int:
    total = 0
    stack = [pid]
    seen: set[int] = set()
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        total += _rss_bytes(cur)
        stack.extend(_children_of(cur))
    return total


def _kill_process_group(proc: subprocess.Popen[bytes | str]) -> None:
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        return


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run a Rocq command and kill it once RSS exceeds a limit."
    )
    parser.add_argument("--label", default="rocq", help="Label for diagnostics")
    parser.add_argument(
        "--limit-bytes",
        type=int,
        default=DEFAULT_LIMIT_BYTES,
        help="RSS limit in bytes before killing the process tree",
    )
    parser.add_argument("command", nargs=argparse.REMAINDER, help="Command after --")
    args = parser.parse_args()

    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        print("rocq_memory_guard.py: missing command to run", file=sys.stderr)
        return 2

    proc = subprocess.Popen(command, start_new_session=True)
    try:
        while True:
            code = proc.poll()
            if code is not None:
                return code
            rss = _process_tree_rss(proc.pid)
            if rss > args.limit_bytes:
                _kill_process_group(proc)
                try:
                    proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
                rss_mb = rss / (1024 * 1024)
                limit_mb = args.limit_bytes / (1024 * 1024)
                print(
                    f"{args.label} killed: process tree RSS {rss_mb:.1f} MiB "
                    f"exceeded limit {limit_mb:.1f} MiB",
                    file=sys.stderr,
                )
                return 137
            time.sleep(POLL_INTERVAL_SECONDS)
    except KeyboardInterrupt:
        _kill_process_group(proc)
        raise


if __name__ == "__main__":
    raise SystemExit(main())
