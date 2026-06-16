#!/usr/bin/env python3
"""Validate worker proof manuals and build a merged scratch manual.

This script never edits the source `*_proof_manual.v`. It reads worker-local
manual copies, validates assigned target lemmas, collects any proved helper
lemmas added by workers, and writes a merged manual artifact under the proving
work directory unless `--output` points to another non-source path.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from manual_goal_utils import (
    added_forbidden_toplevels,
    added_require_import_lines,
    block_has_admitted,
    check_rocq_file_with_deps,
    ensure_unique_lemma_names,
    lemma_by_name,
    load_manifest,
    manifest_coq_project,
    parse_manual_file,
    sorted_dependency_files,
    validate_helper_import_lines,
)


def _resolve_task_local_scratch_lib_file(manifest: dict) -> Path | None:
    task_local_scratch_lib_file = manifest.get("task_local_scratch_lib_file")
    if task_local_scratch_lib_file:
        p = Path(str(task_local_scratch_lib_file)).resolve()
        if p.is_file():
            return p
    return None


def _has_admitted(file_path: Path) -> bool:
    text = file_path.read_text(encoding="utf-8")
    return "Admitted." in text


def _goal_is_solved(split_file: Path, lib_file: Path | None) -> bool:
    """Compatibility helper for older per-goal tests and callers."""
    if _has_admitted(split_file):
        return False
    try:
        dep_files = [lib_file] if lib_file else None
        check_rocq_file_with_deps(split_file, dep_files)
        return True
    except SystemExit:
        return False


def _load_proof_report(work_dir: Path) -> list[dict]:
    report_path = work_dir / "proof_report.json"
    if not report_path.exists():
        return []
    try:
        data = json.loads(report_path.read_text(encoding="utf-8"))
        return data if isinstance(data, list) else []
    except (json.JSONDecodeError, ValueError):
        return []


def _find_report_entry(goal_name: str, proof_report: list[dict]) -> dict | None:
    for entry in proof_report:
        if str(entry.get("goal", "")) == goal_name:
            return entry
    return None


def _validate_and_refine_entry(
    name: str,
    split_file: Path,
    lib_file: Path | None,
    agent_entry: dict | None,
) -> dict:
    """Compatibility validator for a single split goal file."""
    if _has_admitted(split_file):
        report = agent_entry.get("report", "") if agent_entry else ""
        return {"goal": name, "status": "admitted", "report": report}
    if _goal_is_solved(split_file, lib_file):
        return {"goal": name, "status": "solved"}
    report = "file does not compile"
    if agent_entry and agent_entry.get("report"):
        report = str(agent_entry["report"]) + " (does not compile)"
    return {"goal": name, "status": "broken", "report": report}


def _write_proof_report(work_dir: Path, entries: list[dict]) -> Path:
    path = work_dir / "proof_report.json"
    path.write_text(json.dumps(entries, indent=2), encoding="utf-8")
    return path


def _load_groups_manifest(work_dir: Path) -> list[dict] | None:
    path = work_dir / "groups_manifest.json"
    if not path.is_file():
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise SystemExit(f"{path} is not a JSON array")
    return data


def _worker_entries(manifest: dict) -> list[dict]:
    work_dir = Path(str(manifest["work_dir"])).resolve()
    groups = _load_groups_manifest(work_dir)
    if groups is not None:
        return groups
    worker_manual = manifest.get("worker_manual_file")
    if worker_manual:
        return [{
            "work_dir": str(work_dir),
            "worker_manual_file": str(worker_manual),
            "goals": manifest["lemmas"],
        }]
    return [{
        "work_dir": str(work_dir),
        "worker_manual_file": str(manifest["source_file"]),
        "goals": manifest["lemmas"],
    }]


def _compile_manual(
    manual_file: Path,
    lib_file: Path | None,
    project_context: tuple[Path, list[str]] | None = None,
) -> bool:
    try:
        deps = [lib_file] if lib_file else None
        if project_context is not None:
            project_root, flags = project_context
            check_rocq_file_with_deps(
                manual_file,
                deps,
                project_root=project_root,
                flags=flags,
            )
        else:
            check_rocq_file_with_deps(manual_file, deps)
        return True
    except SystemExit:
        return False


def _dependency_files_from_manifest_entry(entry: dict, lib_file: Path | None) -> list[Path]:
    deps: list[Path] = []
    for raw in entry.get("case_dependency_files", []):
        path = Path(str(raw)).resolve()
        if path.is_file():
            deps.append(path)
    helper_lib = entry.get("worker_helper_scratch_lib_file")
    if helper_lib:
        path = Path(str(helper_lib)).resolve()
        if path.is_file():
            deps.append(path)
    has_task_local_overlay = any(
        Path(str(raw)).resolve().is_file()
        for raw in entry.get("case_dependency_task_local_scratch_lib_files", [])
    )
    if not has_task_local_overlay and lib_file is not None and lib_file.is_file():
        deps.append(lib_file)
    seen: set[Path] = set()
    unique: list[str] = []
    for dep in deps:
        if dep not in seen:
            unique.append(str(dep))
            seen.add(dep)
    return sorted_dependency_files(unique)


def _worker_helper_lemmas(
    helper_lib: Path,
    original_text: str,
) -> tuple[list[dict[str, object]], list[str], list[str]]:
    if not helper_lib.is_file():
        return [], [f"worker_helper_scratch_lib not found: {helper_lib}"], []
    text = helper_lib.read_text(encoding="utf-8")
    forbidden = added_forbidden_toplevels(original_text, text)
    helper_imports = added_require_import_lines(original_text, text)
    forbidden.extend(validate_helper_import_lines(helper_imports))
    try:
        _prelude, lemmas = parse_manual_file(text)
    except ValueError:
        return [], forbidden, helper_imports
    ensure_unique_lemma_names(lemmas)
    return lemmas, forbidden, helper_imports


def _compile_manual_with_deps(
    manual_file: Path,
    deps: list[Path],
    project_context: tuple[Path, list[str]] | None = None,
) -> bool:
    try:
        if project_context is not None:
            project_root, flags = project_context
            check_rocq_file_with_deps(
                manual_file,
                deps,
                project_root=project_root,
                flags=flags,
            )
        else:
            check_rocq_file_with_deps(manual_file, deps)
        return True
    except SystemExit:
        return False


def _status_from_worker_report(goal_name: str, worker_dir: Path) -> str:
    entry = _find_report_entry(goal_name, _load_proof_report(worker_dir))
    if entry and entry.get("report"):
        return str(entry["report"])
    return ""


def _append_unique_helper(
    helper_blocks: list[str],
    helper_by_name: dict[str, str],
    helper_name: str,
    helper_block: str,
    worker_manual: Path,
) -> None:
    old = helper_by_name.get(helper_name)
    normalized = helper_block.strip()
    if old is not None:
        if old.strip() != normalized:
            raise SystemExit(
                f"Conflicting helper lemma `{helper_name}` found while merging {worker_manual}"
            )
        return
    helper_by_name[helper_name] = helper_block
    helper_blocks.append(helper_block)


def _append_unique_import(
    helper_imports: list[str],
    helper_import_set: set[str],
    import_line: str,
) -> None:
    if import_line in helper_import_set:
        return
    helper_imports.append(import_line)
    helper_import_set.add(import_line)


def _merge_worker_manuals(
    manifest: dict,
    lib_file: Path | None,
    selected_goals: set[str] | None,
) -> tuple[str, list[dict]]:
    source_file = Path(str(manifest["source_file"])).resolve()
    original_text = source_file.read_text(encoding="utf-8")
    original_prelude, original_lemmas = parse_manual_file(original_text)
    ensure_unique_lemma_names(original_lemmas)
    original_names = [str(lemma["name"]) for lemma in original_lemmas]
    original_name_set = set(original_names)
    original_map = lemma_by_name(original_lemmas)

    target_names = [str(entry["name"]) for entry in manifest["lemmas"]]
    if selected_goals is not None:
        target_names = [name for name in target_names if name in selected_goals]
    target_set = set(target_names)

    replacements: dict[str, str] = {}
    helper_blocks: list[str] = []
    helper_by_name: dict[str, str] = {}
    helper_imports: list[str] = []
    helper_import_set: set[str] = set()
    refined_report: list[dict] = []
    status_by_goal: dict[str, dict] = {}

    for worker in _worker_entries(manifest):
        worker_dir = Path(str(worker["work_dir"])).resolve()
        worker_manual = Path(str(worker["worker_manual_file"])).resolve()
        worker_helper_scratch_lib_raw = worker.get("worker_helper_scratch_lib_file")
        worker_helper_scratch_lib = Path(str(worker_helper_scratch_lib_raw)).resolve() if worker_helper_scratch_lib_raw else None
        assigned = [str(goal["name"]) for goal in worker["goals"] if str(goal["name"]) in target_set]
        if not assigned:
            continue
        if not worker_manual.is_file():
            for name in assigned:
                status_by_goal[name] = {
                    "goal": name,
                    "status": "broken",
                    "report": f"worker manual not found: {worker_manual}",
                }
            continue

        worker_text = worker_manual.read_text(encoding="utf-8")
        forbidden = added_forbidden_toplevels(original_text, worker_text)
        compiled = _compile_manual_with_deps(
            worker_manual,
            _dependency_files_from_manifest_entry(worker, lib_file),
            manifest_coq_project(worker),
        )
        _worker_prelude, worker_lemmas = parse_manual_file(worker_text)
        ensure_unique_lemma_names(worker_lemmas)
        worker_map = lemma_by_name(worker_lemmas)

        if forbidden:
            report = "forbidden top-level declaration(s): " + "; ".join(forbidden)
            for name in assigned:
                status_by_goal[name] = {"goal": name, "status": "broken", "report": report}
            continue
        if not compiled:
            for name in assigned:
                status_by_goal[name] = {
                    "goal": name,
                    "status": "broken",
                    "report": "worker manual does not compile",
                }
            continue

        helper_error: str | None = None
        if worker_helper_scratch_lib is not None:
            helper_lemmas, helper_forbidden, worker_helper_imports = _worker_helper_lemmas(
                worker_helper_scratch_lib,
                original_text,
            )
            if helper_forbidden:
                helper_error = (
                    "forbidden top-level declaration(s) in worker_helper_scratch_lib: "
                    + "; ".join(helper_forbidden)
                )
            if helper_error is None:
                for lemma in helper_lemmas:
                    helper_name = str(lemma["name"])
                    if helper_name in original_name_set:
                        helper_error = (
                            f"worker_helper_scratch_lib must not redefine original witness `{helper_name}`"
                        )
                        break
                    helper_block = str(lemma["block"])
                    if block_has_admitted(helper_block):
                        helper_error = f"helper lemma `{helper_name}` contains Admitted"
                        break
                    _append_unique_helper(
                        helper_blocks,
                        helper_by_name,
                        helper_name,
                        helper_block,
                        worker_helper_scratch_lib,
                    )
                if helper_error is None:
                    for import_line in worker_helper_imports:
                        _append_unique_import(
                            helper_imports,
                            helper_import_set,
                            import_line,
                        )
        for lemma in worker_lemmas:
            helper_name = str(lemma["name"])
            if helper_name in original_name_set:
                continue
            helper_error = (
                f"helper lemma `{helper_name}` was added to worker manual; "
                "add helper lemmas to worker_helper_scratch_lib instead"
            )
            break
        if helper_error:
            for name in assigned:
                status_by_goal[name] = {"goal": name, "status": "broken", "report": helper_error}
            continue

        for name in assigned:
            lemma = worker_map.get(name)
            if lemma is None:
                status_by_goal[name] = {
                    "goal": name,
                    "status": "broken",
                    "report": f"assigned lemma missing from {worker_manual}",
                }
                continue
            block = str(lemma["block"])
            if block_has_admitted(block):
                report = _status_from_worker_report(name, worker_dir)
                status_by_goal[name] = {"goal": name, "status": "admitted", "report": report}
                continue
            replacements[name] = block
            status_by_goal[name] = {"goal": name, "status": "solved"}

    for name in target_names:
        refined_report.append(status_by_goal.get(name, {
            "goal": name,
            "status": "admitted",
            "report": "no worker produced a solved proof",
        }))

    merged_parts = [original_prelude]
    if helper_imports:
        merged_parts.append("(* Helper imports collected from worker_helper_scratch_lib. *)\n")
        merged_parts.append("\n".join(helper_imports).rstrip() + "\n\n")
    if helper_blocks:
        merged_parts.append("\n".join(block.rstrip() for block in helper_blocks).rstrip() + "\n\n")
    for name in original_names:
        block = replacements.get(name, str(original_map[name]["block"]))
        merged_parts.append(block if block.endswith("\n") else block + "\n")
    return "".join(merged_parts), refined_report


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate worker manuals and build a merged scratch proof manual."
    )
    parser.add_argument("manifest", help="Path to manifest.json after agent work")
    parser.add_argument("--goals", nargs="*", default=None,
                        help="Validate only these target lemma names")
    parser.add_argument("--output", default=None,
                        help="Merged proof manual output path. Defaults inside the work dir.")
    args = parser.parse_args()

    manifest_path = Path(args.manifest).expanduser().resolve()
    manifest = load_manifest(manifest_path)
    lib_file = _resolve_task_local_scratch_lib_file(manifest)
    work_dir = Path(str(manifest["work_dir"])).resolve()
    source_file = Path(str(manifest["source_file"])).resolve()
    selected = set(args.goals) if args.goals else None

    merged_text, refined_report = _merge_worker_manuals(manifest, lib_file, selected)
    if args.output:
        output_path = Path(args.output).expanduser().resolve()
    else:
        output_path = work_dir / f"{source_file.stem}__merged_proof_manual.v"
    if output_path == source_file:
        raise SystemExit("Refusing to overwrite the source proof manual; choose a scratch output path")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(merged_text, encoding="utf-8")
    manifest["merged_proof_manual_file"] = str(output_path)
    source_text = source_file.read_text(encoding="utf-8")
    manifest["merged_helper_imports"] = added_require_import_lines(source_text, merged_text)
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    # Compile the merged artifact. It may still contain Admitted in unselected or
    # unsolved targets, but it must be syntactically and dependency-correct.
    merged_compiles = _compile_manual_with_deps(
        output_path,
        _dependency_files_from_manifest_entry(manifest, lib_file),
        manifest_coq_project(manifest),
    )
    if not merged_compiles:
        refined_report = [
            entry if entry["status"] != "solved" else {
                "goal": entry["goal"],
                "status": "broken",
                "report": "merged manual does not compile",
            }
            for entry in refined_report
        ]

    report_path = _write_proof_report(work_dir, refined_report)
    print(f"Authoritative proof_report.json written to {report_path}")
    print(f"Merged proof manual written to {output_path}")

    solved = sum(1 for entry in refined_report if entry["status"] == "solved")
    total = len(refined_report)
    print(f"\n=== Summary ===\n  solved: {solved}\n  total: {total}")
    failures = [entry for entry in refined_report if entry.get("report")]
    if failures:
        print("\n=== Failure Reports ===")
        for entry in failures:
            print(f"  {entry['goal']} ({entry['status']}): {entry['report']}")
    return 0 if merged_compiles and solved == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
