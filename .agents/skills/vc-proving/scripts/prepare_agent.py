#!/usr/bin/env python3
"""Deprecated serial vc-proving entrypoint.

The current vc-proving contract requires ``prepare_agent_concurrent.py`` plus
``run_agent_concurrent.py`` so proof search always runs through script-created
worker-local manuals.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Deprecated: vc-proving must use the concurrent worker pipeline."
    )
    parser.add_argument("manifest", nargs="?", help="Unused deprecated argument")
    parser.add_argument("task_local_scratch_lib", nargs="?", help="Unused deprecated argument")
    parser.parse_args()
    print(
        "prepare_agent.py is disabled. Use prepare_agent_concurrent.py followed by "
        "run_agent_concurrent.py; vc-proving must run through script-created "
        "worker-local manuals.",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
