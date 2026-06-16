#!/usr/bin/env python3
"""Deprecated serial vc-proving entrypoint.

The current vc-proving contract requires ``run_agent_concurrent.py`` so proof
search always runs through script-created worker-local manuals.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

DEFAULT_AGENT_TIMEOUT = 1200  # 20 minutes


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Deprecated: vc-proving must use run_agent_concurrent.py."
    )
    parser.add_argument("manifest", nargs="?", help="Unused deprecated argument")
    parser.add_argument("--timeout", type=int, default=DEFAULT_AGENT_TIMEOUT,
                        help=argparse.SUPPRESS)
    parser.parse_args()
    print(
        "run_agent.py is disabled. Use run_agent_concurrent.py; vc-proving must "
        "run through script-created worker-local manuals.",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
