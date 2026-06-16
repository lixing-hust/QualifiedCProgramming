#!/usr/bin/env python3
"""Move proved helper lemmas from a merged proof manual into task_local_scratch_lib.

The worker pipeline first proves everything in worker-local manuals and
``validate_and_merge.py`` builds one merged manual.  This post-merge step keeps
the witness proofs in the manual, moves newly added helper lemma blocks into a
task_local_scratch_lib, and verifies the resulting pair before handoff.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from manual_goal_utils import (
    DEFAULT_HELPER_IMPORT_ROOTS,
    added_require_import_lines,
    block_has_admitted,
    check_rocq_file,
    check_rocq_file_with_deps,
    ensure_unique_lemma_names,
    lemma_by_name,
    load_manifest,
    manifest_coq_project,
    make_readonly,
    make_user_writable,
    parse_manual_file,
    require_import_lines,
    sorted_dependency_files,
    validate_helper_import_lines,
)


def _lemma_blocks_or_empty(text: str) -> list[dict[str, object]]:
    try:
        _prelude, lemmas = parse_manual_file(text)
    except ValueError:
        return []
    ensure_unique_lemma_names(lemmas)
    return lemmas


def _default_manual_output(work_dir: Path, merged_manual: Path) -> Path:
    return work_dir / f"{merged_manual.stem}__helpers_migrated_proof_manual.v"


def _default_lib_output(manifest: dict) -> Path:
    task_local_scratch_lib_file = manifest.get("task_local_scratch_lib_file")
    if not task_local_scratch_lib_file:
        raise SystemExit("manifest does not contain task_local_scratch_lib; pass --lib-output")
    return Path(str(task_local_scratch_lib_file)).resolve()


def _dependency_lib_copy(manifest: dict, lib_output: Path) -> Path | None:
    task_local_files = manifest.get("case_dependency_task_local_scratch_lib_files", [])
    if isinstance(task_local_files, list):
        existing = []
        for raw in task_local_files:
            path = Path(str(raw)).resolve()
            if path.is_file():
                existing.append(path)
        if len(existing) == 1:
            return existing[0]
        if len(existing) > 1:
            raise SystemExit(
                "manifest contains multiple task_local_scratch_lib overlay files: "
                + ", ".join(str(path) for path in existing)
            )

    module_map = manifest.get("case_dependency_module_map", {})
    if isinstance(module_map, dict):
        for raw in module_map.values():
            path = Path(str(raw)).resolve()
            if path.name == lib_output.name:
                return path
        lib_candidates: list[Path] = []
        for logical, raw in module_map.items():
            path = Path(str(raw)).resolve()
            if str(logical).endswith("_lib") or path.stem.endswith("_lib"):
                lib_candidates.append(path)
        if len(lib_candidates) == 1:
            return lib_candidates[0]

    work_dir = Path(str(manifest["work_dir"])).resolve()
    candidates = sorted((work_dir / "case_deps").rglob(lib_output.name))
    if candidates:
        return candidates[0].resolve()
    lib_candidates = sorted((work_dir / "case_deps").rglob("*_lib.v"))
    return lib_candidates[0].resolve() if len(lib_candidates) == 1 else None


def _dependency_files(manifest: dict) -> list[Path]:
    module_map = manifest.get("case_dependency_module_map", {})
    files: list[str] = []
    if isinstance(module_map, dict):
        files.extend(str(path) for path in module_map.values())
    for raw in manifest.get("case_dependency_files", []):
        files.append(str(raw))
    seen: set[Path] = set()
    unique: list[str] = []
    for raw in files:
        path = Path(raw).resolve()
        if path in seen or not path.is_file():
            continue
        unique.append(str(path))
        seen.add(path)
    return sorted_dependency_files(unique)


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
    worker_helper_scratch_lib = manifest.get("worker_helper_scratch_lib_file")
    if worker_helper_scratch_lib:
        return [{"worker_helper_scratch_lib_file": str(worker_helper_scratch_lib)}]
    return []


def _allowed_helper_import_roots(
    manifest: dict,
    extra_allowed_roots: list[str] | None = None,
) -> tuple[str, ...]:
    roots = list(DEFAULT_HELPER_IMPORT_ROOTS)
    for raw in manifest.get("allowed_helper_import_roots", []):
        root = str(raw).strip()
        if root and root not in roots:
            roots.append(root)
    if extra_allowed_roots:
        for raw in extra_allowed_roots:
            root = str(raw).strip()
            if root and root not in roots:
                roots.append(root)
    return tuple(roots)


def _append_unique_import(
    import_lines: list[str],
    seen: set[str],
    import_line: str,
) -> None:
    if import_line in seen:
        return
    import_lines.append(import_line)
    seen.add(import_line)


def _add_audited_helper_import(
    helper_imports: list[str],
    seen: set[str],
    import_line: str,
    allowed_roots: tuple[str, ...],
) -> None:
    errors = validate_helper_import_lines([import_line], allowed_roots)
    if errors:
        raise SystemExit("Unsupported helper suffix import(s): " + "; ".join(errors))
    _append_unique_import(helper_imports, seen, import_line)


def _add_ambient_helper_import_if_allowed(
    helper_imports: list[str],
    seen: set[str],
    import_line: str,
    allowed_roots: tuple[str, ...],
) -> None:
    if validate_helper_import_lines([import_line], allowed_roots):
        return
    _append_unique_import(helper_imports, seen, import_line)


def _collect_helper_imports(
    manifest: dict,
    seed_text: str,
    merged_prelude: str,
    lib_text: str,
    allowed_roots: tuple[str, ...],
) -> list[str]:
    existing_imports = set(require_import_lines(lib_text))
    helper_imports: list[str] = []
    seen = set(existing_imports)

    for raw in manifest.get("merged_helper_imports", []):
        import_line = str(raw).strip()
        if import_line:
            _add_audited_helper_import(helper_imports, seen, import_line, allowed_roots)

    for import_line in added_require_import_lines(seed_text, merged_prelude):
        _add_audited_helper_import(helper_imports, seen, import_line, allowed_roots)

    for worker in _worker_entries(manifest):
        raw_helper = worker.get("worker_helper_scratch_lib_file")
        if not raw_helper:
            continue
        helper_lib = Path(str(raw_helper)).resolve()
        if not helper_lib.is_file():
            continue
        helper_text = helper_lib.read_text(encoding="utf-8")
        for import_line in added_require_import_lines(seed_text, helper_text):
            _add_audited_helper_import(helper_imports, seen, import_line, allowed_roots)

    # Helper lemmas can also depend on general-purpose imports inherited from
    # the seed manual prelude.  Bring over allowed non-case imports missing from
    # task_local_scratch_lib, but silently skip generated case imports such as
    # `<case>_goal` / `<case>_lib` modules; those are frozen dependencies, not
    # helper suffix dependencies.
    for import_line in require_import_lines(merged_prelude):
        _add_ambient_helper_import_if_allowed(helper_imports, seen, import_line, allowed_roots)
    for worker in _worker_entries(manifest):
        raw_helper = worker.get("worker_helper_scratch_lib_file")
        if not raw_helper:
            continue
        helper_lib = Path(str(raw_helper)).resolve()
        if not helper_lib.is_file():
            continue
        for import_line in require_import_lines(helper_lib.read_text(encoding="utf-8")):
            _add_ambient_helper_import_if_allowed(helper_imports, seen, import_line, allowed_roots)

    return helper_imports


def _append_helpers_to_lib(
    lib_text: str,
    helper_imports: list[str],
    helper_blocks: list[str],
    source_name: str,
) -> str:
    if not helper_blocks and not helper_imports:
        return lib_text if lib_text.endswith("\n") else lib_text + "\n"

    sections: list[str] = []
    if helper_imports:
        sections.append(
            f"(* Helper imports migrated from {source_name}. *)\n"
            + "\n".join(helper_imports).rstrip()
        )
    if helper_blocks:
        body = "\n\n".join(block.rstrip() for block in helper_blocks).rstrip()
        sections.append(f"(* Helper lemmas migrated from {source_name}. *)\n\n{body}")
    base = lib_text.rstrip()
    return f"{base}\n\n" + "\n\n".join(sections).rstrip() + "\n"


def _write_if_distinct(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    make_user_writable(path)
    path.write_text(text, encoding="utf-8")


def migrate_helpers(
    manifest_path: Path,
    manual_output: Path | None = None,
    lib_output: Path | None = None,
    extra_allowed_import_roots: list[str] | None = None,
) -> tuple[Path, Path, list[str], list[str]]:
    manifest = load_manifest(manifest_path)
    work_dir = Path(str(manifest["work_dir"])).resolve()
    seed_manual = Path(str(manifest["source_file"])).resolve()
    merged_manual = Path(str(manifest.get("merged_proof_manual_file", seed_manual))).resolve()
    lib_seed = Path(str(manifest.get("task_local_scratch_lib_file", lib_output or ""))).resolve()
    if not seed_manual.is_file():
        raise SystemExit(f"Seed manual file not found: {seed_manual}")
    if not merged_manual.is_file():
        raise SystemExit(f"Merged manual file not found: {merged_manual}")
    if not lib_seed.is_file():
        raise SystemExit(f"task_local_scratch_lib file not found: {lib_seed}")

    manual_output = manual_output.resolve() if manual_output else _default_manual_output(work_dir, merged_manual)
    lib_output = lib_output.resolve() if lib_output else _default_lib_output(manifest)
    if manual_output == seed_manual:
        raise SystemExit("Refusing to overwrite the seed proof manual")

    seed_text = seed_manual.read_text(encoding="utf-8")
    seed_prelude, seed_lemmas = parse_manual_file(seed_text)
    ensure_unique_lemma_names(seed_lemmas)
    seed_names = [str(lemma["name"]) for lemma in seed_lemmas]
    seed_name_set = set(seed_names)

    merged_text = merged_manual.read_text(encoding="utf-8")
    merged_prelude, merged_lemmas = parse_manual_file(merged_text)
    ensure_unique_lemma_names(merged_lemmas)
    merged_map = lemma_by_name(merged_lemmas)

    missing = [name for name in seed_names if name not in merged_map]
    if missing:
        raise SystemExit("Merged manual is missing original lemma(s): " + ", ".join(missing))

    helper_blocks: list[str] = []
    helper_names: list[str] = []
    for lemma in merged_lemmas:
        name = str(lemma["name"])
        if name in seed_name_set:
            continue
        block = str(lemma["block"])
        if block_has_admitted(block):
            raise SystemExit(f"Helper lemma `{name}` still contains Admitted")
        helper_names.append(name)
        helper_blocks.append(block)

    lib_text = lib_seed.read_text(encoding="utf-8")
    allowed_roots = _allowed_helper_import_roots(manifest, extra_allowed_import_roots)
    helper_imports = _collect_helper_imports(
        manifest=manifest,
        seed_text=seed_text,
        merged_prelude=merged_prelude,
        lib_text=lib_text,
        allowed_roots=allowed_roots,
    )
    existing_lib_lemmas = _lemma_blocks_or_empty(lib_text)
    existing_by_name = lemma_by_name(existing_lib_lemmas) if existing_lib_lemmas else {}
    new_helper_blocks: list[str] = []
    for name, block in zip(helper_names, helper_blocks):
        old = existing_by_name.get(name)
        if old is None:
            new_helper_blocks.append(block)
            continue
        if str(old["block"]).strip() != block.strip():
            raise SystemExit(f"Conflicting helper lemma `{name}` already exists in lib")

    migrated_manual_parts = [seed_prelude]
    for name in seed_names:
        block = str(merged_map[name]["block"])
        migrated_manual_parts.append(block if block.endswith("\n") else block + "\n")
    migrated_manual_text = "".join(migrated_manual_parts)

    effective_helper_imports = helper_imports if new_helper_blocks else []
    migrated_lib_text = _append_helpers_to_lib(
        lib_text,
        effective_helper_imports,
        new_helper_blocks,
        merged_manual.name,
    )
    _write_if_distinct(lib_output, migrated_lib_text)

    dep_lib = _dependency_lib_copy(manifest, lib_output)
    if dep_lib is not None and dep_lib != lib_output:
        _write_if_distinct(dep_lib, migrated_lib_text)
        make_readonly(dep_lib)

    _write_if_distinct(manual_output, migrated_manual_text)

    # Compile the dependency copy that the worker-local _CoqProject resolves,
    # then the migrated manual.  Normal concurrent proving prepares a read-only
    # canonical case_deps overlay, so when the canonical task_local_scratch_lib
    # overlay copy changes we must recompile every overlay dependency in order
    # (lib before goal) to
    # avoid stale `.vo` assumption mismatches.
    project_context = manifest_coq_project(manifest)
    manual_compile_deferred = bool(helper_names and dep_lib is None)

    if dep_lib is not None:
        dep_files = _dependency_files(manifest)
        if not dep_files:
            dep_files = [dep_lib]
        if not manual_compile_deferred:
            if project_context is not None:
                project_root, flags = project_context
                check_rocq_file_with_deps(
                    manual_output,
                    dep_files,
                    project_root=project_root,
                    flags=flags,
                    force_deps=True,
                )
            else:
                check_rocq_file_with_deps(manual_output, dep_files, force_deps=True)
    else:
        if project_context is not None:
            project_root, flags = project_context
            check_rocq_file_with_deps(
                lib_output,
                [],
                project_root=project_root,
                flags=flags,
            )
        else:
            check_rocq_file(lib_output)
        if not manual_compile_deferred:
            if project_context is not None:
                project_root, flags = project_context
                check_rocq_file_with_deps(
                    manual_output,
                    [],
                    project_root=project_root,
                    flags=flags,
                )
            else:
                check_rocq_file(manual_output)

    manifest["helper_merged_proof_manual_file"] = str(merged_manual)
    manifest["migrated_proof_manual_file"] = str(manual_output)
    manifest["migrated_task_local_scratch_lib_file"] = str(lib_output)
    manifest["migrated_case_dependency_task_local_scratch_lib_file"] = str(dep_lib) if dep_lib else None
    manifest["migrated_helper_lemmas"] = helper_names
    manifest["migrated_helper_imports"] = effective_helper_imports
    manifest["allowed_helper_import_roots"] = list(allowed_roots)
    manifest["migrated_manual_compile_deferred_until_main_lib_integration"] = (
        manual_compile_deferred
    )
    # Downstream verify_manual_goals.py treats merged_proof_manual_file as the
    # final manual artifact, so point it at the helper-free migrated manual.
    manifest["merged_proof_manual_file"] = str(manual_output)
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    return manual_output, lib_output, helper_names, effective_helper_imports


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Move helper lemmas from merged manual into task_local_scratch_lib."
    )
    parser.add_argument("manifest", help="Path to manifest.json after validate_and_merge.py")
    parser.add_argument("--manual-output", default=None, help="Helper-free manual output path")
    parser.add_argument("--lib-output", default=None, help="Migrated task_local_scratch_lib output path")
    parser.add_argument(
        "--allow-helper-import-root",
        action="append",
        default=None,
        help="Additional allowed logical module root for helper suffix Require Import lines",
    )
    args = parser.parse_args()

    manifest_path = Path(args.manifest).expanduser().resolve()
    manual_output = Path(args.manual_output).expanduser() if args.manual_output else None
    lib_output = Path(args.lib_output).expanduser() if args.lib_output else None

    migrated_manual, migrated_lib, helper_names, helper_imports = migrate_helpers(
        manifest_path=manifest_path,
        manual_output=manual_output,
        lib_output=lib_output,
        extra_allowed_import_roots=args.allow_helper_import_root,
    )
    print(f"Migrated proof manual written to {migrated_manual}")
    print(f"Migrated task_local_scratch_lib written to {migrated_lib}")
    if helper_imports:
        print("Migrated helper imports:")
        for import_line in helper_imports:
            print(f"  - {import_line}")
    if helper_names:
        print("Migrated helper lemmas:")
        for name in helper_names:
            print(f"  - {name}")
    else:
        print("No helper lemmas needed migration")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
