#!/usr/bin/env python3
"""Verification case log automation tool.

This tool manages per-case logging for:
- start timestamp
- finish record append to VERIFICATION_CASE_LOG.md
- optional token and result metadata
"""

from __future__ import annotations

import argparse
import json
import re
import shlex
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
LOG_FILE = ROOT / "VERIFICATION_CASE_LOG.md"
STATE_DIR = ROOT / ".verification_case_state"

STATUS_MAP = {
    "passed": "已通过",
    "failed": "未通过",
    "in-progress": "进行中",
}


def parse_case_number(case_id: str) -> str:
    m = re.fullmatch(r"C_(\d+)", case_id)
    if not m:
        raise SystemExit("case_id 格式必须是 C_数字，例如 C_131")
    return m.group(1)


def case_file_map(case_id: str, int_dir: Path) -> dict[str, Path]:
    n = parse_case_number(case_id)
    return {
        "c": int_dir / f"C_{n}.c",
        "coins": int_dir / f"coins_{n}.v",
        "goal": int_dir / f"C_{n}_goal.v",
        "auto": int_dir / f"C_{n}_auto.v",
        "manual": int_dir / f"C_{n}_manual.v",
        "check": int_dir / f"C_{n}_goal_check.v",
    }


def coqproject_args(int_dir: Path) -> list[str]:
    p = int_dir / "_CoqProject"
    if not p.exists():
        raise SystemExit(f"未找到 _CoqProject: {p}")
    args: list[str] = []
    for raw in p.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        args.extend(shlex.split(line))
    return args


def maybe_extra_logical_path(file_map: dict[str, Path]) -> list[str]:
    # Heuristic: generated files importing SimpleC.EE.humaneval typically
    # need this extra mapping at compile time.
    for k in ["goal", "auto", "manual", "check"]:
        p = file_map[k]
        if p.exists():
            text = p.read_text(encoding="utf-8", errors="ignore")
            if "SimpleC.EE.humaneval" in text:
                return ["-R", ".", "SimpleC.EE.humaneval"]
    return []


def run_cmd(cmd: list[str], cwd: Path) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True)
    return proc.returncode, proc.stdout, proc.stderr


def compile_chain(
    case_id: str,
    int_dir: Path,
    coqc_bin: str,
    force_logical_path: str | None,
) -> tuple[bool, str, list[str]]:
    fm = case_file_map(case_id, int_dir)
    required_order = ["coins", "goal", "auto", "manual", "check"]

    missing = [str(fm[k]) for k in required_order if not fm[k].exists()]
    if missing:
        return False, f"未通过（缺文件: {', '.join(missing)}）", [f"缺文件: {m}" for m in missing]

    coq_args = coqproject_args(int_dir)
    extra = ["-R", ".", force_logical_path] if force_logical_path else maybe_extra_logical_path(fm)
    detail_lines: list[str] = []

    for k in required_order:
        target = fm[k].name
        cmd = [coqc_bin] + coq_args + extra + [target]
        rc, out, err = run_cmd(cmd, int_dir)
        if rc != 0:
            tail = (err.strip() or out.strip() or "无错误输出")
            if len(tail) > 800:
                tail = tail[-800:]
            detail_lines.append(f"{target} 编译失败")
            detail_lines.append(tail)
            return False, f"未通过（失败于 {target}）", detail_lines
        detail_lines.append(f"{target} 通过")

    return True, "通过", detail_lines


def scan_pattern(p: Path, pat: str) -> list[str]:
    if not p.exists():
        return []
    lines: list[str] = []
    rx = re.compile(pat)
    for i, line in enumerate(p.read_text(encoding="utf-8", errors="ignore").splitlines(), 1):
        if rx.search(line):
            lines.append(f"{p.name}:{i}: {line.strip()}")
    return lines


def auto_checks(case_id: str, int_dir: Path) -> tuple[bool, str, bool, str, bool, str, list[str]]:
    fm = case_file_map(case_id, int_dir)
    details: list[str] = []

    admitted_hits = scan_pattern(fm["coins"], r"Admitted\\.") + scan_pattern(fm["manual"], r"Admitted\\.")
    axiom_hits = scan_pattern(fm["coins"], r"Axiom\s") + scan_pattern(fm["manual"], r"Axiom\s")

    admitted_ok = len(admitted_hits) == 0
    axiom_ok = len(axiom_hits) == 0

    admitted_text = "通过（无）" if admitted_ok else f"未通过（{len(admitted_hits)} 处）"
    axiom_text = "通过（无）" if axiom_ok else f"未通过（{len(axiom_hits)} 处）"

    if admitted_hits:
        details.extend(admitted_hits[:20])
    if axiom_hits:
        details.extend(axiom_hits[:20])

    all_ok = admitted_ok and axiom_ok
    return all_ok, "检查完成", admitted_ok, admitted_text, axiom_ok, axiom_text, details


def now_iso_local() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def now_date() -> str:
    return datetime.now().astimezone().date().isoformat()


def parse_iso(iso_text: str) -> datetime:
    # Accept both local offset forms and trailing Z.
    if iso_text.endswith("Z"):
        iso_text = iso_text[:-1] + "+00:00"
    return datetime.fromisoformat(iso_text)


def format_elapsed_seconds(seconds: float) -> str:
    if seconds < 0:
        return "未记录"
    total = int(round(seconds))
    h = total // 3600
    m = (total % 3600) // 60
    s = total % 60
    return f"{h:02d}:{m:02d}:{s:02d}"


def ensure_state_dir() -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)


def state_path(case_id: str) -> Path:
    safe = re.sub(r"[^A-Za-z0-9_\-]", "_", case_id)
    return STATE_DIR / f"{safe}.json"


def load_state(case_id: str) -> dict[str, Any] | None:
    p = state_path(case_id)
    if not p.exists():
        return None
    return json.loads(p.read_text(encoding="utf-8"))


def save_state(case_id: str, data: dict[str, Any]) -> None:
    ensure_state_dir()
    state_path(case_id).write_text(
        json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8"
    )


def delete_state(case_id: str) -> bool:
    p = state_path(case_id)
    if p.exists():
        p.unlink()
        return True
    return False


def next_record_index(log_text: str) -> int:
    nums = [int(x) for x in re.findall(r"^## 记录\s+(\d+)\s*$", log_text, flags=re.M)]
    return (max(nums) + 1) if nums else 1


def format_record(
    index: int,
    case_id: str,
    program_file: str,
    date_text: str,
    status_cn: str,
    changed_files: list[str],
    issues: list[str],
    solutions: list[str],
    compile_chain: str,
    admitted_check: str,
    axiom_check: str,
    failure_reason: str,
    token_in: str,
    token_out: str,
    token_total: str,
    start_time: str,
    end_time: str,
    elapsed: str,
    lessons: list[str],
) -> str:
    idx = f"{index:03d}"

    def bullet_list(items: list[str], fallback: str = "无") -> str:
        if not items:
            return f"- {fallback}\n"
        return "".join(f"- {it}\n" for it in items)

    def ordered_list(items: list[str], fallback: str = "无") -> str:
        if not items:
            return f"1. {fallback}\n"
        return "".join(f"{i}. {it}\n" for i, it in enumerate(items, 1))

    return (
        f"\n---\n\n"
        f"## 记录 {idx}\n\n"
        f"- 例子编号: {case_id}\n"
        f"- 程序文件: {program_file}\n"
        f"- 记录日期: {date_text}\n"
        f"- 状态: {status_cn}\n\n"
        f"### 变更范围\n\n"
        f"{bullet_list(changed_files)}\n"
        f"### 遇到的问题\n\n"
        f"{ordered_list(issues)}\n"
        f"### 解决方式\n\n"
        f"{ordered_list(solutions)}\n"
        f"### 验收结果\n\n"
        f"- 编译链通过: {compile_chain}\n"
        f"- Admitted 检查: {admitted_check}\n"
        f"- Axiom 检查: {axiom_check}\n"
        f"- 未通过原因: {failure_reason}\n\n"
        f"### 成本统计\n\n"
        f"- 输入 token: {token_in}\n"
        f"- 输出 token: {token_out}\n"
        f"- 总 token: {token_total}\n"
        f"- 开始时间: {start_time}\n"
        f"- 结束时间: {end_time}\n"
        f"- 总耗时: {elapsed}\n\n"
        f"### 可复用经验\n\n"
        f"{ordered_list(lessons)}"
    )


def cmd_start(args: argparse.Namespace) -> int:
    old = load_state(args.case_id)
    if old and not args.force:
        raise SystemExit(
            "该 case 已有进行中的会话。可先执行 clear，或 start --force 覆盖。"
        )

    st = {
        "case_id": args.case_id,
        "program_file": args.program_file,
        "start_time": now_iso_local(),
        "token_in_at_start": args.token_in if args.token_in is not None else "未记录",
        "note": args.note or "",
    }
    save_state(args.case_id, st)
    print(f"[start] case={args.case_id}")
    print(f"[start] time={st['start_time']}")
    return 0


def cmd_finish(args: argparse.Namespace) -> int:
    if not LOG_FILE.exists():
        raise SystemExit(f"日志文件不存在: {LOG_FILE}")

    st = load_state(args.case_id)

    program_file = (
        args.program_file
        or (st.get("program_file") if st else None)
        or "未记录"
    )

    start_time = (
        args.start_time
        or (st.get("start_time") if st else None)
        or "未记录"
    )
    end_time = args.end_time or now_iso_local()

    if args.elapsed:
        elapsed = args.elapsed
    else:
        elapsed = "未记录"
        try:
            if start_time != "未记录":
                delta = parse_iso(end_time) - parse_iso(start_time)
                elapsed = format_elapsed_seconds(delta.total_seconds())
        except Exception:
            elapsed = "未记录"

    token_in = str(args.tokens_in) if args.tokens_in is not None else "未记录"
    token_out = str(args.tokens_out) if args.tokens_out is not None else "未记录"
    token_total = str(args.tokens_total) if args.tokens_total is not None else "未记录"

    date_text = args.date or now_date()
    status_cn = STATUS_MAP[args.status]

    changed_files = args.changed_file or []
    issues = args.issue or []
    solutions = args.solution or []
    lessons = args.lesson or []

    record = format_record(
        index=next_record_index(LOG_FILE.read_text(encoding="utf-8")),
        case_id=args.case_id,
        program_file=program_file,
        date_text=date_text,
        status_cn=status_cn,
        changed_files=changed_files,
        issues=issues,
        solutions=solutions,
        compile_chain=args.compile_chain,
        admitted_check=args.admitted_check,
        axiom_check=args.axiom_check,
        failure_reason=args.failure_reason,
        token_in=token_in,
        token_out=token_out,
        token_total=token_total,
        start_time=start_time,
        end_time=end_time,
        elapsed=elapsed,
        lessons=lessons,
    )

    if args.dry_run:
        print(record)
    else:
        with LOG_FILE.open("a", encoding="utf-8") as f:
            f.write(record)
        print(f"[finish] 已追加记录到 {LOG_FILE}")
        # Consume state by default after completion.
        delete_state(args.case_id)

    return 0


def cmd_clear(args: argparse.Namespace) -> int:
    ok = delete_state(args.case_id)
    if ok:
        print(f"[clear] 已清理会话: {args.case_id}")
    else:
        print(f"[clear] 未找到会话: {args.case_id}")
    return 0


def cmd_auto_finish(args: argparse.Namespace) -> int:
    if not LOG_FILE.exists():
        raise SystemExit(f"日志文件不存在: {LOG_FILE}")

    int_dir = Path(args.int_dir).resolve()
    if not int_dir.exists():
        raise SystemExit(f"IntClaude 目录不存在: {int_dir}")

    # Read session state (if started with `start` before).
    st = load_state(args.case_id)
    program_file = (
        args.program_file
        or (st.get("program_file") if st else None)
        or f"QCP_examples/humaneval/IntClaude/{args.case_id}.c"
    )
    start_time = args.start_time or (st.get("start_time") if st else None) or "未记录"
    end_time = now_iso_local()

    elapsed = "未记录"
    try:
        if start_time != "未记录":
            delta = parse_iso(end_time) - parse_iso(start_time)
            elapsed = format_elapsed_seconds(delta.total_seconds())
    except Exception:
        elapsed = "未记录"

    compile_ok, compile_text, compile_details = compile_chain(
        case_id=args.case_id,
        int_dir=int_dir,
        coqc_bin=args.coqc_bin,
        force_logical_path=args.force_logical_path,
    )

    _, _, admitted_ok, admitted_text, axiom_ok, axiom_text, check_details = auto_checks(
        case_id=args.case_id,
        int_dir=int_dir,
    )

    status = "passed" if (compile_ok and admitted_ok and axiom_ok) else "failed"
    failure_reason = "无"
    if status == "failed":
        reasons = []
        if not compile_ok:
            reasons.append(compile_text)
        if not admitted_ok:
            reasons.append(admitted_text)
        if not axiom_ok:
            reasons.append(axiom_text)
        failure_reason = "；".join(reasons)

    # Default changed-file list: case related files that exist.
    fm = case_file_map(args.case_id, int_dir)
    auto_changed_files = []
    for k in ["c", "coins", "goal", "auto", "manual", "check"]:
        p = fm[k]
        if p.exists():
            auto_changed_files.append(f"QCP_examples/humaneval/IntClaude/{p.name}")
    changed_files = args.changed_file or auto_changed_files

    issues = args.issue or ["自动化收尾：由脚本执行编译链和洁净性检查"]
    solutions = args.solution or ["自动执行 coqc 编译链 + Admitted/Axiom 扫描并写入日志"]
    lessons = args.lesson or ["若自动收尾失败，优先查看 failure_reason 和编译失败文件"]

    token_in = str(args.tokens_in) if args.tokens_in is not None else "未记录"
    token_out = str(args.tokens_out) if args.tokens_out is not None else "未记录"
    token_total = str(args.tokens_total) if args.tokens_total is not None else "未记录"

    detail_note = []
    detail_note.extend(compile_details)
    detail_note.extend(check_details)
    if args.detail_to_issue:
        issues = issues + detail_note[: args.detail_limit]

    record = format_record(
        index=next_record_index(LOG_FILE.read_text(encoding="utf-8")),
        case_id=args.case_id,
        program_file=program_file,
        date_text=args.date or now_date(),
        status_cn=STATUS_MAP[status],
        changed_files=changed_files,
        issues=issues,
        solutions=solutions,
        compile_chain=compile_text,
        admitted_check=admitted_text,
        axiom_check=axiom_text,
        failure_reason=failure_reason,
        token_in=token_in,
        token_out=token_out,
        token_total=token_total,
        start_time=start_time,
        end_time=end_time,
        elapsed=elapsed,
        lessons=lessons,
    )

    if args.dry_run:
        print(record)
    else:
        with LOG_FILE.open("a", encoding="utf-8") as f:
            f.write(record)
        print(f"[auto-finish] 已追加记录到 {LOG_FILE}")
        print(f"[auto-finish] 状态: {STATUS_MAP[status]}")
        delete_state(args.case_id)

    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="HumanEval 验证日志自动化工具")
    sp = p.add_subparsers(dest="cmd", required=True)

    p_start = sp.add_parser("start", help="开始记录一个 case 会话")
    p_start.add_argument("case_id", help="例子编号，例如 C_131")
    p_start.add_argument("--program-file", required=True, help="程序文件路径")
    p_start.add_argument("--token-in", type=int, help="开始时已消耗输入 token")
    p_start.add_argument("--note", help="开始备注")
    p_start.add_argument("--force", action="store_true", help="覆盖已有会话")
    p_start.set_defaults(func=cmd_start)

    p_finish = sp.add_parser("finish", help="结束会话并写入日志")
    p_finish.add_argument("case_id", help="例子编号，例如 C_131")
    p_finish.add_argument(
        "--status",
        choices=["passed", "failed", "in-progress"],
        default="passed",
        help="验证状态",
    )
    p_finish.add_argument("--program-file", help="程序文件路径（可覆盖 start 记录）")

    p_finish.add_argument("--changed-file", action="append", help="变更文件，可重复")
    p_finish.add_argument("--issue", action="append", help="遇到的问题，可重复")
    p_finish.add_argument("--solution", action="append", help="解决方式，可重复")
    p_finish.add_argument("--lesson", action="append", help="可复用经验，可重复")

    p_finish.add_argument("--compile-chain", default="未记录", help="编译链结果")
    p_finish.add_argument("--admitted-check", default="未记录", help="Admitted 检查结果")
    p_finish.add_argument("--axiom-check", default="未记录", help="Axiom 检查结果")
    p_finish.add_argument("--failure-reason", default="无", help="未通过原因")

    p_finish.add_argument("--tokens-in", type=int, help="输入 token")
    p_finish.add_argument("--tokens-out", type=int, help="输出 token")
    p_finish.add_argument("--tokens-total", type=int, help="总 token")

    p_finish.add_argument("--start-time", help="开始时间 ISO8601，优先级高于会话记录")
    p_finish.add_argument("--end-time", help="结束时间 ISO8601，默认当前时间")
    p_finish.add_argument("--elapsed", help="总耗时，格式自定，例如 00:12:33")
    p_finish.add_argument("--date", help="记录日期 YYYY-MM-DD，默认今天")

    p_finish.add_argument("--dry-run", action="store_true", help="只输出，不落盘")
    p_finish.set_defaults(func=cmd_finish)

    p_clear = sp.add_parser("clear", help="清理一个 case 的临时会话")
    p_clear.add_argument("case_id", help="例子编号，例如 C_131")
    p_clear.set_defaults(func=cmd_clear)

    p_auto = sp.add_parser("auto-finish", help="自动编译+检查并写入日志")
    p_auto.add_argument("case_id", help="例子编号，例如 C_131")
    p_auto.add_argument("--program-file", help="程序文件路径（可覆盖 start 记录）")
    p_auto.add_argument(
        "--int-dir",
        default=str(ROOT / "IntClaude"),
        help="IntClaude 目录路径",
    )
    p_auto.add_argument("--coqc-bin", default="coqc", help="coqc 可执行文件")
    p_auto.add_argument(
        "--force-logical-path",
        help="强制追加 -R . <logical-path>，例如 SimpleC.EE.humaneval",
    )

    p_auto.add_argument("--changed-file", action="append", help="变更文件，可重复")
    p_auto.add_argument("--issue", action="append", help="遇到的问题，可重复")
    p_auto.add_argument("--solution", action="append", help="解决方式，可重复")
    p_auto.add_argument("--lesson", action="append", help="可复用经验，可重复")
    p_auto.add_argument(
        "--detail-to-issue",
        action="store_true",
        help="把自动检查细节附加到问题列表",
    )
    p_auto.add_argument(
        "--detail-limit",
        type=int,
        default=20,
        help="附加细节条数上限",
    )

    p_auto.add_argument("--tokens-in", type=int, help="输入 token")
    p_auto.add_argument("--tokens-out", type=int, help="输出 token")
    p_auto.add_argument("--tokens-total", type=int, help="总 token")
    p_auto.add_argument("--start-time", help="开始时间 ISO8601，优先级高于会话记录")
    p_auto.add_argument("--date", help="记录日期 YYYY-MM-DD，默认今天")

    p_auto.add_argument("--dry-run", action="store_true", help="只输出，不落盘")
    p_auto.set_defaults(func=cmd_auto_finish)

    return p


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
