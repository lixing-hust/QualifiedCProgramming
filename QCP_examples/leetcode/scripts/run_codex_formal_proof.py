#!/usr/bin/env python3
import argparse
import datetime as dt
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time


REPO_ROOT = Path("/home/yangfp/QualifiedCProgramming/QCP_examples/leetcode")
DEFAULT_SKILL = REPO_ROOT / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"


def timestamp_now() -> str:
    return dt.datetime.now().strftime("%Y%m%d_%H%M%S")


def iso_now() -> str:
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")


def stem_from_input(input_path: Path) -> str:
    return input_path.stem


def whitespace_token_count(text: str) -> int:
    return len(text.split())


def count_file_tokens(paths: list[Path]) -> int:
    total = 0
    for path in paths:
      if path.exists():
        total += whitespace_token_count(path.read_text(encoding="utf-8"))
    return total


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def build_prompt(
    skill_path: Path,
    input_path: Path,
    function_name: str,
    workspace_path: Path,
) -> str:
    return f"""Read and follow this skill first:
{skill_path}

Task:
- Verify function `{function_name}` from `{input_path}`.
- Work fully automatically without asking for human input.
- Use workspace `{workspace_path}`.
- Before writing `annotated/<name>.c`, first output natural-language annotation reasoning into `logs/annotation_reasoning.md` inside the workspace.
- Before writing `coq/generated/<name>_proof_manual.v`, first output natural-language proof reasoning into `logs/proof_reasoning.md` inside the workspace.
- Treat those reasoning files as mandatory workflow artifacts, not optional notes.

Keep the final response short and state whether the proof passed and whether any blocker remains.
"""


def parse_usage(stdout_jsonl: Path) -> dict[str, int] | None:
    usage = None
    if not stdout_jsonl.exists():
        return None
    with stdout_jsonl.open("r", encoding="utf-8") as f:
        for raw_line in f:
            line = raw_line.strip()
            if not line.startswith("{"):
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if obj.get("type") == "turn.completed":
                maybe_usage = obj.get("usage")
                if isinstance(maybe_usage, dict):
                    usage = maybe_usage
    return usage


def append_metrics_section(
    proof_metrics_path: Path,
    run_label: str,
    start_iso: str,
    end_iso: str,
    wall_clock_seconds: float,
    usage: dict[str, int] | None,
    prompt_tokens_approx: int,
    final_message_tokens_approx: int,
    workspace_tokens_approx: int,
    prompt_path: Path,
    stdout_jsonl: Path,
    stderr_log: Path,
    last_message_path: Path,
) -> None:
    lines = []
    lines.append("")
    lines.append(f"## External Codex Run `{run_label}`")
    lines.append("")
    lines.append(f"- Start time: `{start_iso}`")
    lines.append(f"- End time: `{end_iso}`")
    lines.append(f"- Wall-clock time (seconds): `{wall_clock_seconds:.2f}`")
    if usage is not None:
        input_tokens = usage.get("input_tokens")
        cached_input_tokens = usage.get("cached_input_tokens")
        output_tokens = usage.get("output_tokens")
        total_tokens = None
        if isinstance(input_tokens, int) and isinstance(output_tokens, int):
            total_tokens = input_tokens + output_tokens
        lines.append("- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.")
        if input_tokens is not None:
            lines.append(f"- Codex CLI input tokens: `{input_tokens}`")
        if cached_input_tokens is not None:
            lines.append(f"- Codex CLI cached input tokens: `{cached_input_tokens}`")
        if output_tokens is not None:
            lines.append(f"- Codex CLI output tokens: `{output_tokens}`")
        if total_tokens is not None:
            lines.append(f"- Codex CLI total tokens: `{total_tokens}`")
    else:
        total_tokens = prompt_tokens_approx + final_message_tokens_approx
        lines.append("- Token source: approximate whitespace-delimited word counts because exact CLI usage was unavailable.")
        lines.append(f"- Approx prompt tokens: `{prompt_tokens_approx}`")
        lines.append(f"- Approx final-message tokens: `{final_message_tokens_approx}`")
        lines.append(f"- Approx total tokens: `{total_tokens}`")
    lines.append(f"- Approx workspace-authored text tokens: `{workspace_tokens_approx}`")
    lines.append(f"- Prompt file: `{prompt_path}`")
    lines.append(f"- Codex stdout JSONL: `{stdout_jsonl}`")
    lines.append(f"- Codex stderr log: `{stderr_log}`")
    lines.append(f"- Codex last message: `{last_message_path}`")

    if proof_metrics_path.exists():
        existing = proof_metrics_path.read_text(encoding="utf-8")
    else:
        existing = "# Proof Metrics\n"
    proof_metrics_path.write_text(existing.rstrip() + "\n" + "\n".join(lines) + "\n", encoding="utf-8")


def update_issues_on_failure(issues_path: Path, stage: str, exit_code: int, stderr_log: Path) -> None:
    issues_path.parent.mkdir(parents=True, exist_ok=True)
    if issues_path.exists():
        existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Execution Issues\n\n"
    block = (
        "## External Codex Failure\n\n"
        f"- Stage: `{stage}`\n"
        f"- Exit code: `{exit_code}`\n"
        f"- Stderr log: `{stderr_log}`\n"
    )
    issues_path.write_text(existing + block, encoding="utf-8")


def bootstrap_workspace(workspace_path: Path, input_path: Path) -> None:
    (workspace_path / "logs").mkdir(parents=True, exist_ok=True)
    (workspace_path / "original").mkdir(parents=True, exist_ok=True)
    dst = workspace_path / "original" / input_path.name
    shutil.copy2(input_path, dst)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex externally to produce a formal proof workspace.")
    parser.add_argument("input_c", help="Path to input C file, relative to repo root or absolute.")
    parser.add_argument("function_name", help="Function name to verify.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to SKILL.md.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to input file stem.")
    parser.add_argument("--timestamp", help="Explicit workspace timestamp; defaults to current local time.")
    parser.add_argument("--model", help="Optional Codex model override.")
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke Codex.")
    parser.add_argument("--codex-bin", default="codex", help="Codex CLI binary.")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    input_path = Path(args.input_c)
    if not input_path.is_absolute():
        input_path = (REPO_ROOT / input_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    if not input_path.exists():
        print(f"input file not found: {input_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    workspace_stem = args.workspace_name or stem_from_input(input_path)
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"workspace_{workspace_timestamp}_{workspace_stem}"
    bootstrap_workspace(workspace_path, input_path)

    logs_dir = workspace_path / "logs"
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
    last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"

    prompt = build_prompt(skill_path, input_path, args.function_name, workspace_path)
    ensure_parent(prompt_path)
    prompt_path.write_text(prompt, encoding="utf-8")

    if args.dry_run:
        print(str(workspace_path))
        return 0

    start_wall = time.time()
    start_iso = iso_now()
    cmd = [
        args.codex_bin,
        "exec",
        "--json",
        "--full-auto",
        "--skip-git-repo-check",
        "-C",
        str(REPO_ROOT),
        "-o",
        str(last_message_path),
    ]
    if args.model:
        cmd.extend(["--model", args.model])
    cmd.append("-")

    with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
        proc = subprocess.run(
            cmd,
            input=prompt,
            text=True,
            stdout=out_f,
            stderr=err_f,
            cwd=REPO_ROOT,
        )
    end_wall = time.time()
    end_iso = iso_now()

    usage = parse_usage(stdout_jsonl)
    final_message = last_message_path.read_text(encoding="utf-8") if last_message_path.exists() else ""

    workspace_text_files = [
        p for p in workspace_path.rglob("*")
        if p.is_file() and p.suffix in {".c", ".v", ".md", ".txt", ".log", ".json"}
        and p != proof_metrics_path(workspace_path)
    ]
    workspace_tokens_approx = count_file_tokens(workspace_text_files)

    append_metrics_section(
        proof_metrics_path(workspace_path),
        run_label,
        start_iso,
        end_iso,
        end_wall - start_wall,
        usage,
        whitespace_token_count(prompt),
        whitespace_token_count(final_message),
        workspace_tokens_approx,
        prompt_path,
        stdout_jsonl,
        stderr_log,
        last_message_path,
    )

    if proc.returncode != 0:
        update_issues_on_failure(
            workspace_path / "logs" / "issues.md",
            "external-codex-run",
            proc.returncode,
            stderr_log,
        )

    print(str(workspace_path))
    return proc.returncode


def proof_metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "proof_metrics.md"


if __name__ == "__main__":
    sys.exit(main())
