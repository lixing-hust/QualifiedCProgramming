#!/usr/bin/env python3
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


REPO_ROOT = Path("/home/yangfp/QualifiedCProgramming/QCP_examples/CAV")
DEFAULT_SKILL = REPO_ROOT / "skills" / "verify" / "SKILL.md"
OUTPUT_ROOT = REPO_ROOT / "output"
EXAMPLES_ROOT = REPO_ROOT / "examples"
EXPORT_SCRIPT = REPO_ROOT / "skills" / "example_export" / "scripts" / "export_verify_example.py"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_REASONING_EFFORT = "medium"
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


def stem_from_input(input_path: Path) -> str:
    return input_path.stem


def sha256_hex(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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


def emit_log(message: str) -> None:
    print(f"[verify] {message}", flush=True)


def build_codex_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    cache_dir = logs_dir / ".codex_cache"
    state_dir = logs_dir / ".state"
    data_dir = logs_dir / ".data"
    config_dir = logs_dir / ".config"
    tmp_dir = logs_dir / ".tmp"
    cache_dir.mkdir(parents=True, exist_ok=True)
    state_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)
    config_dir.mkdir(parents=True, exist_ok=True)
    tmp_dir.mkdir(parents=True, exist_ok=True)
    env["XDG_CACHE_HOME"] = str(cache_dir)
    env["XDG_STATE_HOME"] = str(state_dir)
    env["XDG_DATA_HOME"] = str(data_dir)
    env["XDG_CONFIG_HOME"] = str(config_dir)
    env["TMPDIR"] = str(tmp_dir)
    env["TMP"] = str(tmp_dir)
    env["TEMP"] = str(tmp_dir)
    return env


def codex_supports_reasoning_effort(codex_bin: str, cwd: Path, env: dict[str, str]) -> bool:
    try:
        proc = subprocess.run(
            [codex_bin, "exec", "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=cwd,
            env=env,
            timeout=10,
        )
    except (subprocess.SubprocessError, OSError):
        return False
    return "--reasoning-effort" in proc.stdout


def filter_stderr_in_place(stderr_log: Path) -> None:
    if not stderr_log.exists():
        return
    clean_lines = []
    for raw_line in stderr_log.read_text(encoding="utf-8", errors="replace").splitlines():
        if any(pattern in raw_line for pattern in NOISE_PATTERNS):
            continue
        clean_lines.append(raw_line)
    stderr_log.write_text("\n".join(clean_lines) + ("\n" if clean_lines else ""), encoding="utf-8")


def paired_input_v(input_path: Path) -> Path | None:
    candidate = input_path.with_suffix(".v")
    if candidate.exists():
        return candidate
    return None


def build_prompt(
    skill_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    workspace_path: Path,
    annotated_c_path: Path,
) -> str:
    input_v_line = f"- Optional input V: `{input_v_path}`\n" if input_v_path else "- Optional input V: `<not provided>`\n"
    return f"""Use this skill as the complete workflow:
{skill_path}

Inputs:
- Input C: `{input_path}`
{input_v_line}- Target function: `{function_name}`
- Workspace: `{workspace_path}`
- Active annotated C: `{annotated_c_path}`
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
    metrics_md_path: Path,
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

    if metrics_md_path.exists():
        existing = metrics_md_path.read_text(encoding="utf-8")
    else:
        existing = "# Verify Metrics\n"
    metrics_md_path.write_text(existing.rstrip() + "\n" + "\n".join(lines) + "\n", encoding="utf-8")


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


def export_example_if_needed(workspace_path: Path, function_name: str) -> tuple[bool, str]:
    target_dir = EXAMPLES_ROOT / function_name
    if target_dir.exists():
        return False, f"skip_existing:{target_dir}"
    if not EXPORT_SCRIPT.exists():
        return False, f"missing_export_script:{EXPORT_SCRIPT}"
    proc = subprocess.run(
        [sys.executable, str(EXPORT_SCRIPT), str(workspace_path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=REPO_ROOT,
    )
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip() or "unknown export failure"
        return False, f"export_failed:{detail}"
    return True, target_dir.as_posix()


def bootstrap_workspace(workspace_path: Path, input_path: Path, input_v_path: Path | None, function_name: str) -> Path:
    (workspace_path / "logs").mkdir(parents=True, exist_ok=True)
    (workspace_path / "original").mkdir(parents=True, exist_ok=True)
    (workspace_path / "coq").mkdir(parents=True, exist_ok=True)
    (REPO_ROOT / "annotated").mkdir(parents=True, exist_ok=True)

    original_c = workspace_path / "original" / input_path.name
    annotated_c = REPO_ROOT / "annotated" / f"{workspace_path.name}.c"
    shutil.copy2(input_path, original_c)
    shutil.copy2(input_path, annotated_c)

    original_v = ""
    if input_v_path is not None:
        dst_v = workspace_path / "original" / input_v_path.name
        shutil.copy2(input_v_path, dst_v)
        original_v = str(dst_v)

    fingerprint_path = workspace_path / "logs" / "workspace_fingerprint.json"
    fingerprint = {
        "fingerprint_version": 2,
        "workspace": workspace_path.name,
        "stage": "verify",
        "input_c": str(input_path),
        "input_v": str(input_v_path) if input_v_path else "",
        "original_c": str(original_c),
        "original_v": original_v,
        "annotated_c": str(annotated_c),
        "function_name": function_name,
        "program_sha256": sha256_hex(input_path),
        "semantic_description": "",
        "keywords": {},
        "assume_contract_is_correct": True,
        "contract_source": "contract_input_c",
    }
    fingerprint_path.write_text(json.dumps(fingerprint, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return annotated_c


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run Codex externally to execute the full verify workflow.")
    parser.add_argument("input_c", help="Path to input C file, relative to repo root or absolute.")
    parser.add_argument("function_name_positional", nargs="?", help="Optional function name to verify. Kept for CLI compatibility.")
    parser.add_argument("--function-name", help="Function name to verify. Preferred form.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to verification skill markdown.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to input file stem.")
    parser.add_argument("--timestamp", help="Explicit verify timestamp; defaults to current local time.")
    parser.add_argument("--model", default=DEFAULT_MODEL, help="Codex model. Defaults to gpt-5.4.")
    parser.add_argument(
        "--reasoning-effort",
        default=DEFAULT_REASONING_EFFORT,
        help="Codex reasoning effort. Defaults to medium.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke Codex.")
    parser.add_argument(
        "--export-examples",
        action="store_true",
        help="If verify succeeds, export the workspace into examples/<function_name>/ unless that example already exists.",
    )
    parser.add_argument("--codex-bin", default="codex", help="Codex CLI binary.")
    parser.add_argument("--timeout-seconds", type=int, default=3600, help="Kill the external Codex run if it exceeds this wall-clock timeout.")
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
    if input_path.suffix != ".c":
        print(f"input file must be a .c file: {input_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    function_name = args.function_name or args.function_name_positional
    if not function_name:
        print("function name is required: pass --function-name NAME or a positional NAME", file=sys.stderr)
        return 2

    input_v_path = paired_input_v(input_path)

    workspace_stem = args.workspace_name or stem_from_input(input_path)
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"verify_{workspace_timestamp}_{workspace_stem}"
    annotated_c_path = bootstrap_workspace(workspace_path, input_path, input_v_path, function_name)
    emit_log(f"workspace={workspace_path}")
    emit_log(f"input_c={input_path}")
    emit_log(f"function_name={function_name}")
    emit_log(f"input_v={input_v_path if input_v_path else '<not provided>'}")
    emit_log(f"annotated_c={annotated_c_path}")
    emit_log(f"model={args.model}")
    logs_dir = workspace_path / "logs"
    codex_env = build_codex_env(logs_dir)
    reasoning_effort_supported = codex_supports_reasoning_effort(args.codex_bin, REPO_ROOT, codex_env)
    emit_log(f"reasoning_effort={args.reasoning_effort}")
    emit_log(f"reasoning_effort_supported={reasoning_effort_supported}")
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"codex_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"codex_stdout_{run_label}.jsonl"
    stderr_log = logs_dir / f"codex_stderr_{run_label}.log"
    last_message_path = logs_dir / f"codex_last_message_{run_label}.txt"

    prompt = build_prompt(skill_path, input_path, input_v_path, function_name, workspace_path, annotated_c_path)
    ensure_parent(prompt_path)
    prompt_path.write_text(prompt, encoding="utf-8")

    if args.dry_run:
        emit_log("dry_run=true")
        print(str(workspace_path))
        return 0

    start_wall = time.time()
    start_iso = iso_now()
    cmd = [
        args.codex_bin,
        "--dangerously-bypass-approvals-and-sandbox",
        "exec",
        "--json",
        "--skip-git-repo-check",
        "-C",
        str(REPO_ROOT),
        "-o",
        str(last_message_path),
    ]
    if args.model:
        cmd.extend(["--model", args.model])
    if args.reasoning_effort and reasoning_effort_supported:
        cmd.extend(["--reasoning-effort", args.reasoning_effort])
    cmd.append("-")
    emit_log(f"codex_exec_start timeout_seconds={args.timeout_seconds}")

    proc_returncode = 0
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
                env=codex_env,
            )
        proc_returncode = proc.returncode
    except subprocess.TimeoutExpired:
        proc_returncode = 124
        failure_detail = f"external codex run exceeded timeout of {args.timeout_seconds} seconds"
        emit_log(f"codex_exec_timeout detail={failure_detail}")
    end_wall = time.time()
    end_iso = iso_now()
    filter_stderr_in_place(stderr_log)

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

    if proc_returncode != 0:
        update_issues_on_failure(
            workspace_path / "logs" / "issues.md",
            "external-codex-run",
            proc_returncode,
            stderr_log,
        )
        if failure_detail is not None:
            issues_path = workspace_path / "logs" / "issues.md"
            existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n"
            issues_path.write_text(existing + f"- Detail: `{failure_detail}`\n", encoding="utf-8")
        emit_log(f"codex_exec_failed exit_code={proc_returncode}")
    else:
        emit_log("codex_exec_completed exit_code=0")
        if args.export_examples:
            exported, detail = export_example_if_needed(workspace_path, function_name)
            if exported:
                emit_log(f"examples_exported={detail}")
            else:
                emit_log(f"examples_export_skipped={detail}")

    emit_log(f"stdout_jsonl={stdout_jsonl}")
    emit_log(f"stderr_log={stderr_log}")
    emit_log(f"last_message={last_message_path}")

    print(str(workspace_path))
    return proc_returncode


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


if __name__ == "__main__":
    sys.exit(main())
