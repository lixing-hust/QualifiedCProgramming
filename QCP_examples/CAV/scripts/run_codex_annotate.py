#!/usr/bin/env python3
import argparse
import datetime as dt
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


REPO_ROOT = Path("/home/yangfp/QualifiedCProgramming/QCP_examples/CAV")
DEFAULT_SKILL = REPO_ROOT / "skills" / "annotate" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
INPUT_ROOT = REPO_ROOT / "input"
NOISE_PATTERNS = [
    "WARNING: proceeding, even though we could not update PATH: Read-only file system",
    "failed to renew cache TTL: Read-only file system",
    "failed to record rollout items: failed to queue rollout items: channel closed",
    "failed to connect to websocket: IO error: Connection reset by peer",
]


def timestamp_now() -> str:
    return dt.datetime.now().strftime("%Y%m%d_%H%M%S")


def iso_now() -> str:
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")


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


def build_codex_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    home_dir = logs_dir / ".home"
    cache_dir = logs_dir / ".codex_cache"
    state_dir = logs_dir / ".state"
    data_dir = logs_dir / ".data"
    config_dir = logs_dir / ".config"
    tmp_dir = logs_dir / ".tmp"
    home_dir.mkdir(parents=True, exist_ok=True)
    cache_dir.mkdir(parents=True, exist_ok=True)
    state_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)
    config_dir.mkdir(parents=True, exist_ok=True)
    tmp_dir.mkdir(parents=True, exist_ok=True)
    env["HOME"] = str(home_dir)
    env["CODEX_HOME"] = str(home_dir / ".codex")
    env["XDG_CACHE_HOME"] = str(cache_dir)
    env["XDG_STATE_HOME"] = str(state_dir)
    env["XDG_DATA_HOME"] = str(data_dir)
    env["XDG_CONFIG_HOME"] = str(config_dir)
    env["TMPDIR"] = str(tmp_dir)
    env["TMP"] = str(tmp_dir)
    env["TEMP"] = str(tmp_dir)
    return env


def filter_stderr_in_place(stderr_log: Path) -> None:
    if not stderr_log.exists():
        return
    clean_lines = []
    for raw_line in stderr_log.read_text(encoding="utf-8", errors="replace").splitlines():
        if any(pattern in raw_line for pattern in NOISE_PATTERNS):
            continue
        clean_lines.append(raw_line)
    stderr_log.write_text("\n".join(clean_lines) + ("\n" if clean_lines else ""), encoding="utf-8")


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


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


def issues_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "issues.md"


def reasoning_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "reasoning.md"


def bootstrap_workspace(workspace_path: Path, raw_path: Path) -> dict[str, Path]:
    logs_dir = workspace_path / "logs"
    raw_dir = workspace_path / "raw"
    workspace_input_dir = workspace_path / "input"
    logs_dir.mkdir(parents=True, exist_ok=True)
    raw_dir.mkdir(parents=True, exist_ok=True)
    workspace_input_dir.mkdir(parents=True, exist_ok=True)

    raw_copy = raw_dir / raw_path.name
    shutil.copy2(raw_path, raw_copy)
    return {
        "logs_dir": logs_dir,
        "raw_dir": raw_dir,
        "workspace_input_dir": workspace_input_dir,
        "raw_copy": raw_copy,
    }


def build_prompt(
    skill_path: Path,
    raw_path: Path,
    workspace_path: Path,
    target_c_path: Path,
    target_v_path: Path,
    function_name: str,
) -> str:
    return f"""Use this skill as the complete workflow:
{skill_path}

Inputs:
- Raw markdown: `{raw_path}`
- Target function: `{function_name}`
- Workspace: `{workspace_path}`
- Output C: `{target_c_path}`
- Optional output V: `{target_v_path}`
"""


def append_metrics_section(
    metrics_md: Path,
    run_label: str,
    status: str,
    exit_code: int,
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
    produced_c: Path,
    produced_v: Path,
) -> None:
    lines = []
    lines.append("# Annotate Metrics")
    lines.append("")
    lines.append(f"## External Codex Run `{run_label}`")
    lines.append("")
    lines.append(f"- Stage: `annotate`")
    lines.append(f"- Status: `{status}`")
    lines.append(f"- Exit code: `{exit_code}`")
    lines.append(f"- Start time: `{start_iso}`")
    lines.append(f"- End time: `{end_iso}`")
    lines.append(f"- Total wall-clock time (seconds): `{wall_clock_seconds:.2f}`")
    lines.append(f"- Step `external_codex_run` wall-clock time (seconds): `{wall_clock_seconds:.2f}`")
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
    lines.append(f"- Produced input C: `{produced_c}`")
    if produced_v.exists():
        lines.append(f"- Produced input V: `{produced_v}`")
    else:
        lines.append("- Produced input V: `<not created>`")
    lines.append(f"- Workspace input snapshot: `{metrics_md.parent.parent / 'input'}`")
    lines.append(f"- Prompt file: `{prompt_path}`")
    lines.append(f"- Codex stdout JSONL: `{stdout_jsonl}`")
    lines.append(f"- Codex stderr log: `{stderr_log}`")
    lines.append(f"- Codex last message: `{last_message_path}`")
    metrics_md.write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_issues_on_failure(issues_md: Path, stage: str, exit_code: int, stderr_log: Path, detail: str | None = None) -> None:
    issues_md.parent.mkdir(parents=True, exist_ok=True)
    if issues_md.exists():
        existing = issues_md.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Annotate Issues\n\n"
    block = (
        "## External Codex Failure\n\n"
        f"- Stage: `{stage}`\n"
        f"- Exit code: `{exit_code}`\n"
        f"- Stderr log: `{stderr_log}`\n"
    )
    if detail:
        block += f"- Detail: `{detail}`\n"
    issues_md.write_text(existing + block, encoding="utf-8")


def ensure_reasoning_placeholder(reasoning_md: Path, stage: str, detail: str | None = None) -> None:
    if reasoning_md.exists():
        return
    lines = [
        "# Annotate Reasoning",
        "",
        "## Unavailable",
        "",
        f"- This file was not produced by the annotate run because stage `{stage}` failed before reasoning was written.",
    ]
    if detail:
        lines.append(f"- Failure detail: `{detail}`")
    reasoning_md.write_text("\n".join(lines) + "\n", encoding="utf-8")


def snapshot_generated_inputs(workspace_path: Path, input_c: Path, input_v: Path) -> None:
    generated_input_dir = workspace_path / "input"
    generated_input_dir.mkdir(parents=True, exist_ok=True)
    if input_c.exists():
        shutil.copy2(input_c, generated_input_dir / input_c.name)
    if input_v.exists():
        shutil.copy2(input_v, generated_input_dir / input_v.name)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex externally to produce annotate-stage inputs from raw markdown.")
    parser.add_argument("input_md", help="Path to raw markdown input, relative to repo root or absolute.")
    parser.add_argument("--function-name", help="Explicit target function name. Defaults to markdown stem.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to annotate skill markdown.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to markdown stem.")
    parser.add_argument("--timestamp", help="Explicit annotate timestamp; defaults to current local time.")
    parser.add_argument("--model", help="Optional Codex model override.")
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke Codex.")
    parser.add_argument("--codex-bin", default="codex", help="Codex CLI binary.")
    parser.add_argument("--timeout-seconds", type=int, default=300, help="Kill the external Codex run if it exceeds this wall-clock timeout.")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    raw_path = Path(args.input_md)
    if not raw_path.is_absolute():
        raw_path = (REPO_ROOT / raw_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    if not raw_path.exists():
        print(f"input markdown not found: {raw_path}", file=sys.stderr)
        return 2
    if raw_path.suffix != ".md":
        print(f"input markdown must be a .md file: {raw_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    workspace_stem = args.workspace_name or raw_path.stem
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"annotate_{workspace_timestamp}_{workspace_stem}"
    bootstrap_workspace(workspace_path, raw_path)

    function_name = args.function_name or raw_path.stem
    target_c_path = INPUT_ROOT / f"{raw_path.stem}.c"
    target_v_path = INPUT_ROOT / f"{raw_path.stem}.v"

    logs_dir = workspace_path / "logs"
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
    last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"

    prompt = build_prompt(
        skill_path,
        raw_path,
        workspace_path,
        target_c_path,
        target_v_path,
        function_name,
    )
    ensure_parent(prompt_path)
    prompt_path.write_text(prompt, encoding="utf-8")

    if args.dry_run:
        print(str(workspace_path))
        return 0

    start_wall = time.time()
    start_iso = iso_now()
    cmd = [
        args.codex_bin,
        "--ask-for-approval",
        "never",
        "exec",
        "--json",
        "--sandbox",
        "workspace-write",
        "--skip-git-repo-check",
        "-C",
        str(REPO_ROOT),
        "-o",
        str(last_message_path),
    ]
    if args.model:
        cmd.extend(["--model", args.model])
    cmd.append("-")

    proc_returncode = 0
    status = "completed"
    failure_detail = None
    try:
        with stdout_jsonl.open("w", encoding="utf-8") as out_f, stderr_log.open("w", encoding="utf-8") as err_f:
            proc = subprocess.run(
                cmd,
                input=prompt,
                text=True,
                stdout=out_f,
                stderr=err_f,
                cwd=REPO_ROOT,
                timeout=args.timeout_seconds,
                env=build_codex_env(logs_dir),
            )
        proc_returncode = proc.returncode
    except subprocess.TimeoutExpired:
        status = "timeout"
        proc_returncode = 124
        failure_detail = f"external codex run exceeded timeout of {args.timeout_seconds} seconds"
    end_wall = time.time()
    end_iso = iso_now()
    filter_stderr_in_place(stderr_log)

    snapshot_generated_inputs(workspace_path, target_c_path, target_v_path)

    usage = parse_usage(stdout_jsonl)
    final_message = last_message_path.read_text(encoding="utf-8") if last_message_path.exists() else ""
    workspace_text_files = [
        p for p in workspace_path.rglob("*")
        if p.is_file() and p.suffix in {".c", ".v", ".md", ".txt", ".log", ".json"}
        and p != metrics_path(workspace_path)
    ]
    workspace_tokens_approx = count_file_tokens(workspace_text_files)

    append_metrics_section(
        metrics_path(workspace_path),
        run_label,
        status,
        proc_returncode,
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
        target_c_path,
        target_v_path,
    )

    if proc_returncode != 0:
        ensure_reasoning_placeholder(
            reasoning_path(workspace_path),
            "external-codex-run",
            failure_detail,
        )
        update_issues_on_failure(
            issues_path(workspace_path),
            "external-codex-run",
            proc_returncode,
            stderr_log,
            failure_detail,
        )

    print(str(workspace_path))
    return proc_returncode


if __name__ == "__main__":
    sys.exit(main())
