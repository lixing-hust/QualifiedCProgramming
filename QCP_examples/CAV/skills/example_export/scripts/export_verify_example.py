#!/usr/bin/env python3

from __future__ import annotations

import argparse
import shutil
from pathlib import Path


ROOT = Path("/home/yangfp/QualifiedCProgramming/QCP_examples/CAV")
EXAMPLES_DIR = ROOT / "examples"
ANNOTATED_DIR = ROOT / "annotated"


def copy_if_exists(src: Path, dst: Path) -> None:
    if not src.exists():
        return
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def parse_workspace(workspace: Path) -> str:
    name = workspace.name
    if not name.startswith("verify_"):
        raise ValueError(f"workspace basename must start with 'verify_': {name}")
    parts = name.split("_", 3)
    if len(parts) < 4:
        raise ValueError(f"workspace basename must match verify_<timestamp>_<name>: {name}")
    return parts[3]


def export_workspace(workspace: Path) -> Path:
    workspace = workspace.resolve()
    if not workspace.exists():
        raise FileNotFoundError(f"workspace not found: {workspace}")

    func_name = parse_workspace(workspace)
    generated_dir = workspace / "coq" / "generated"
    if not generated_dir.is_dir():
        raise FileNotFoundError(f"generated Coq dir not found: {generated_dir}")

    proof_manual = generated_dir / f"{func_name}_proof_manual.v"
    if not proof_manual.exists():
        raise FileNotFoundError(f"manual proof file not found: {proof_manual}")

    dst_root = EXAMPLES_DIR / func_name
    if dst_root.exists():
        shutil.rmtree(dst_root)
    dst_root.mkdir(parents=True, exist_ok=True)

    original_dir = workspace / "original"
    logs_dir = workspace / "logs"

    copy_if_exists(original_dir / f"{func_name}.c", dst_root / "original" / f"{func_name}.c")
    copy_if_exists(original_dir / f"{func_name}.v", dst_root / "original" / f"{func_name}.v")
    copy_if_exists(
        ANNOTATED_DIR / f"{workspace.name}.c",
        dst_root / "annotated" / f"{func_name}.c",
    )

    for src in sorted(generated_dir.glob("*.v")):
      copy_if_exists(src, dst_root / "coq" / "generated" / src.name)

    copy_if_exists(logs_dir / "workspace_fingerprint.json", dst_root / "logs" / "workspace_fingerprint.json")
    copy_if_exists(logs_dir / "annotation_reasoning.md", dst_root / "logs" / "annotation_reasoning.md")
    copy_if_exists(logs_dir / "proof_reasoning.md", dst_root / "logs" / "proof_reasoning.md")
    copy_if_exists(logs_dir / "issues.md", dst_root / "logs" / "issues.md")

    for pattern in ("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux"):
        for artifact in dst_root.rglob(pattern):
            artifact.unlink()
    metrics = dst_root / "logs" / "metrics.md"
    if metrics.exists():
        metrics.unlink()

    return dst_root


def main() -> int:
    parser = argparse.ArgumentParser(description="Export a finished verify workspace into CAV/examples.")
    parser.add_argument("workspace", help="Path to output/verify_<timestamp>_<name>/")
    args = parser.parse_args()

    workspace = Path(args.workspace)
    if not workspace.is_absolute():
        workspace = (ROOT / workspace).resolve()

    dst = export_workspace(workspace)
    print(dst)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
