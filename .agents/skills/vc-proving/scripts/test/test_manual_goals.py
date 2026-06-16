#!/usr/bin/env python3
"""Tests for refinement manual-goal split/merge/verify scripts."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent

from manual_goal_utils import (
    ensure_unique_lemma_names,
    find_single_lemma_by_name,
    parse_manual_file,
    resolve_keep_dest,
    prepare_keep_dest,
    check_rocq_file,
    _find_coq_project,
    _parse_coq_project_flags,
)


def _run_split(manual_file: Path, *extra_args: str) -> Path:
    """Run split_manual_goals and return the tmp work_dir from the manifest path printed to stdout."""
    result = subprocess.run(
        [sys.executable, str(SCRIPT_DIR / "split_manual_goals.py"), str(manual_file), *extra_args],
        capture_output=True, text=True, check=True,
    )
    # split prints "Manifest: <path>" on stdout
    for line in result.stdout.splitlines():
        if line.startswith("Manifest: "):
            return Path(line[len("Manifest: "):]).parent
    raise RuntimeError(f"could not find manifest path in stdout:\n{result.stdout}")

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

SAMPLE_MANUAL = """\
Require Import VST.floyd.proofauto.
Require Import sll_rel_lib.

Lemma goal1 : forall x, x = x.
Proof. intros. reflexivity. Qed.

Lemma goal2 : forall y, y = y.
Proof. intros. reflexivity. Qed.

Theorem goal3 : True.
Proof. exact I. Qed.
"""

SAMPLE_PRELUDE = "Require Import VST.floyd.proofauto.\nRequire Import sll_rel_lib.\n\n"


@pytest.fixture
def manual_file(tmp_path: Path) -> Path:
    p = tmp_path / "test_manual.v"
    p.write_text(SAMPLE_MANUAL, encoding="utf-8")
    return p


@pytest.fixture
def coq_project(tmp_path: Path) -> Path:
    """Create a minimal _CoqProject."""
    p = tmp_path / "_CoqProject"
    p.write_text("-Q . MyLib\n# comment\n\n-R foo Bar\n", encoding="utf-8")
    return tmp_path


# ---------------------------------------------------------------------------
# parse_manual_file
# ---------------------------------------------------------------------------

class TestParseManualFile:
    def test_basic_parse(self):
        prelude, lemmas = parse_manual_file(SAMPLE_MANUAL)
        assert prelude == SAMPLE_PRELUDE
        assert len(lemmas) == 3
        assert lemmas[0]["name"] == "goal1"
        assert lemmas[1]["name"] == "goal2"
        assert lemmas[2]["name"] == "goal3"

    def test_block_content(self):
        _prelude, lemmas = parse_manual_file(SAMPLE_MANUAL)
        assert "Lemma goal1" in str(lemmas[0]["block"])
        assert "reflexivity" in str(lemmas[0]["block"])

    def test_theorem_keyword(self):
        """Theorem should be matched by the broadened regex."""
        _prelude, lemmas = parse_manual_file(SAMPLE_MANUAL)
        assert lemmas[2]["name"] == "goal3"
        assert "Theorem goal3" in str(lemmas[2]["header_line"])

    def test_all_proof_keywords(self):
        text = (
            "Require Import Foo.\n\n"
            "Lemma a : True.\nProof. exact I. Qed.\n"
            "Theorem b : True.\nProof. exact I. Qed.\n"
            "Proposition c : True.\nProof. exact I. Qed.\n"
            "Corollary d : True.\nProof. exact I. Qed.\n"
            "Example e : True.\nProof. exact I. Qed.\n"
            "Fact f : True.\nProof. exact I. Qed.\n"
            "Remark g : True.\nProof. exact I. Qed.\n"
        )
        _prelude, lemmas = parse_manual_file(text)
        names = [str(l["name"]) for l in lemmas]
        assert names == ["a", "b", "c", "d", "e", "f", "g"]

    def test_no_lemmas_raises(self):
        with pytest.raises(ValueError, match="No lemma blocks found"):
            parse_manual_file("Require Import Foo.\n")

    def test_prelude_offsets_roundtrip(self):
        """Concatenating prelude + all blocks reproduces the original text."""
        prelude, lemmas = parse_manual_file(SAMPLE_MANUAL)
        reconstructed = prelude + "".join(str(l["block"]) for l in lemmas)
        assert reconstructed == SAMPLE_MANUAL


# ---------------------------------------------------------------------------
# ensure_unique_lemma_names
# ---------------------------------------------------------------------------

class TestEnsureUniqueLemmaNames:
    def test_unique_passes(self):
        _prelude, lemmas = parse_manual_file(SAMPLE_MANUAL)
        ensure_unique_lemma_names(lemmas)  # should not raise

    def test_duplicate_raises(self):
        dup_text = (
            "Require Import Foo.\n\n"
            "Lemma dup : True.\nProof. exact I. Qed.\n"
            "Lemma dup : True.\nProof. exact I. Qed.\n"
        )
        _prelude, lemmas = parse_manual_file(dup_text)
        with pytest.raises(ValueError, match="Duplicate lemma names"):
            ensure_unique_lemma_names(lemmas)


# ---------------------------------------------------------------------------
# find_single_lemma_by_name
# ---------------------------------------------------------------------------

class TestFindSingleLemmaByName:
    def test_found(self):
        _prelude, lemmas = parse_manual_file(SAMPLE_MANUAL)
        lemma = find_single_lemma_by_name(lemmas, "goal2")
        assert lemma["name"] == "goal2"

    def test_not_found(self):
        _prelude, lemmas = parse_manual_file(SAMPLE_MANUAL)
        with pytest.raises(ValueError, match="Expected exactly one"):
            find_single_lemma_by_name(lemmas, "nonexistent")


# ---------------------------------------------------------------------------
# resolve_work_dir / prepare_work_dir
# ---------------------------------------------------------------------------

class TestKeepDest:
    def test_default_keep_dest(self, tmp_path: Path):
        manual = tmp_path / "foo_manual.v"
        result = resolve_keep_dest(manual, None)
        assert result.name == "foo_manual__kept_manual_goals"
        assert ".tmp" in result.parts

    def test_custom_keep_dest(self, tmp_path: Path):
        manual = tmp_path / "foo_manual.v"
        custom = tmp_path / "my_work"
        result = resolve_keep_dest(manual, str(custom))
        assert result == custom

    def test_prepare_nonexistent_passes(self, tmp_path: Path):
        # prepare_keep_dest only validates collision; it does NOT mkdir.
        dest = tmp_path / "new_dest"
        prepare_keep_dest(dest, force=False)
        assert not dest.exists()

    def test_prepare_existing_no_force_exits(self, tmp_path: Path):
        dest = tmp_path / "existing"
        dest.mkdir()
        with pytest.raises(SystemExit):
            prepare_keep_dest(dest, force=False)

    def test_prepare_existing_force_removes(self, tmp_path: Path):
        dest = tmp_path / "existing"
        dest.mkdir()
        (dest / "old_file.txt").write_text("old")
        prepare_keep_dest(dest, force=True)
        assert not dest.exists()


# ---------------------------------------------------------------------------
# _find_coq_project / _parse_coq_project_flags
# ---------------------------------------------------------------------------

class TestCoqProject:
    def test_find_coq_project(self, coq_project: Path):
        subdir = coq_project / "a" / "b"
        subdir.mkdir(parents=True)
        assert _find_coq_project(subdir) == coq_project

    def test_find_coq_project_not_found(self, tmp_path: Path):
        with pytest.raises(SystemExit, match="_CoqProject not found"):
            _find_coq_project(tmp_path)

    def test_parse_flags(self, coq_project: Path):
        flags = _parse_coq_project_flags(coq_project)
        assert flags == ["-Q", ".", "MyLib", "-R", "foo", "Bar"]


# ---------------------------------------------------------------------------
# check_rocq_file
# ---------------------------------------------------------------------------

class TestCheckRocqFile:
    def test_success(self, coq_project: Path):
        vfile = coq_project / "test.v"
        vfile.write_text("Definition x := 1.\n", encoding="utf-8")
        completed = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")
        with patch("manual_goal_utils.subprocess.run", return_value=completed):
            check_rocq_file(vfile)  # should not raise

    def test_failure_prints_and_exits(self, coq_project: Path, capsys):
        vfile = coq_project / "test.v"
        vfile.write_text("bad syntax\n", encoding="utf-8")
        completed = subprocess.CompletedProcess(
            args=[], returncode=1, stdout="", stderr="Error: Syntax error\n"
        )
        with patch("manual_goal_utils.subprocess.run", return_value=completed):
            with pytest.raises(SystemExit):
                check_rocq_file(vfile)
        captured = capsys.readouterr()
        assert "Syntax error" in captured.err


# ---------------------------------------------------------------------------
# split_manual_goals.py (end-to-end via subprocess)
# ---------------------------------------------------------------------------

class TestSplitScript:
    def test_split_produces_manifest_and_files(self, manual_file: Path, tmp_path: Path):
        work_dir = _run_split(manual_file)
        manifest_path = work_dir / "manifest.json"
        assert manifest_path.is_file()

        manifest = json.loads(manifest_path.read_text())
        assert manifest["goal_count"] == 3
        assert manifest["lemma_order"] == ["goal1", "goal2", "goal3"]
        assert len(manifest["lemmas"]) == 3
        # work_dir is now a tmp dir; keep_dest is None unless --keep-workdir was passed.
        assert manifest["keep_dest"] is None
        assert manifest["debug_keep_workdir"] is False

        for entry in manifest["lemmas"]:
            split_file = Path(entry["split_rocq_file"])
            assert split_file.is_file()
            content = split_file.read_text()
            assert SAMPLE_PRELUDE in content
            assert entry["name"] in content

    def test_split_with_keep_records_dest(self, manual_file: Path, tmp_path: Path):
        keep_dest = tmp_path / "kept"
        work_dir = _run_split(manual_file, "--keep-workdir", str(keep_dest))
        manifest = json.loads((work_dir / "manifest.json").read_text())
        assert manifest["keep_dest"] == str(keep_dest)
        assert manifest["debug_keep_workdir"] is True
        # destination is NOT populated yet — only step 5 copies to it
        assert not keep_dest.exists()

    def test_split_keep_existing_no_force_fails(self, manual_file: Path, tmp_path: Path):
        keep_dest = tmp_path / "kept"
        keep_dest.mkdir()
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "split_manual_goals.py"),
             str(manual_file), "--keep-workdir", str(keep_dest)],
            capture_output=True, text=True,
        )
        assert result.returncode != 0
        assert "already exists" in result.stderr


# ---------------------------------------------------------------------------
# merge_manual_goals.py
# ---------------------------------------------------------------------------

class TestMergeScript:
    def _setup_split(self, manual_file: Path, tmp_path: Path) -> tuple[Path, dict]:
        """Split and return (work_dir, manifest). Creates _CoqProject in the
        tmp work_dir so the merge script's parent walk can find it."""
        work_dir = _run_split(manual_file)
        (work_dir / "_CoqProject").write_text("", encoding="utf-8")
        manifest = json.loads((work_dir / "manifest.json").read_text())
        return work_dir, manifest

    @staticmethod
    def _fake_coqc_env(tmp_path: Path) -> dict[str, str]:
        """Return env with a fake coqc shim prepended to PATH."""
        import os
        shim_dir = tmp_path / "shim"
        shim_dir.mkdir(exist_ok=True)
        shim = shim_dir / "coqc"
        shim.write_text("#!/bin/sh\nexit 0\n")
        shim.chmod(0o755)
        env = os.environ.copy()
        env["PATH"] = str(shim_dir) + ":" + env.get("PATH", "")
        return env

    def test_dry_run_shows_diff(self, manual_file: Path, tmp_path: Path):
        work_dir, manifest = self._setup_split(manual_file, tmp_path)
        split_file = Path(manifest["lemmas"][0]["split_rocq_file"])

        # Modify the proof in the split file
        text = split_file.read_text()
        text = text.replace("intros. reflexivity.", "auto.")
        split_file.write_text(text)

        env = self._fake_coqc_env(tmp_path)
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "merge_manual_goals.py"),
             str(work_dir / "manifest.json"), str(split_file), "--dry-run"],
            capture_output=True, text=True, env=env,
        )
        assert result.returncode == 0
        assert "auto." in result.stdout
        # Original file unchanged
        assert manual_file.read_text() == SAMPLE_MANUAL

    def test_in_place_is_rejected(self, manual_file: Path, tmp_path: Path):
        work_dir, manifest = self._setup_split(manual_file, tmp_path)
        split_file = Path(manifest["lemmas"][0]["split_rocq_file"])

        text = split_file.read_text()
        text = text.replace("intros. reflexivity.", "auto.")
        split_file.write_text(text)

        env = self._fake_coqc_env(tmp_path)
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "merge_manual_goals.py"),
             str(work_dir / "manifest.json"), str(split_file), "--in-place"],
            capture_output=True, text=True, env=env,
        )
        assert result.returncode != 0
        assert manual_file.read_text() == SAMPLE_MANUAL


# ---------------------------------------------------------------------------
# verify_manual_goals.py
# ---------------------------------------------------------------------------

class TestVerifyScript:
    def _setup_split(self, manual_file: Path, tmp_path: Path) -> Path:
        # Create _CoqProject so check_rocq_file can find it
        (tmp_path / "_CoqProject").write_text("", encoding="utf-8")
        # Use --keep-workdir without DEST so the manifest carries its default dest;
        # tests pass --keep-workdir to verify_manual_goals.py to skip copy-back.
        return _run_split(manual_file, "--keep-workdir")

    @staticmethod
    def _fake_coqc_env(tmp_path: Path) -> dict[str, str]:
        import os
        shim_dir = tmp_path / "shim"
        shim_dir.mkdir(exist_ok=True)
        shim = shim_dir / "coqc"
        shim.write_text("#!/bin/sh\nexit 0\n")
        shim.chmod(0o755)
        env = os.environ.copy()
        env["PATH"] = str(shim_dir) + ":" + env.get("PATH", "")
        return env

    def test_verify_passes_on_unmodified(self, manual_file: Path, tmp_path: Path):
        work_dir = self._setup_split(manual_file, tmp_path)
        env = self._fake_coqc_env(tmp_path)
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "verify_manual_goals.py"),
             str(work_dir / "manifest.json"), "--keep-workdir"],
            capture_output=True, text=True, env=env,
        )
        assert result.returncode == 0
        assert "Verified" in result.stdout

    def test_verify_detects_missing_lemma(self, manual_file: Path, tmp_path: Path):
        work_dir = self._setup_split(manual_file, tmp_path)
        # Remove goal3 from the manual file
        text = manual_file.read_text()
        _prelude, lemmas = parse_manual_file(text)
        manual_file.write_text(
            text[: int(lemmas[2]["start_offset"])],
            encoding="utf-8",
        )
        env = self._fake_coqc_env(tmp_path)
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "verify_manual_goals.py"),
             str(work_dir / "manifest.json"), "--keep-workdir"],
            capture_output=True, text=True, env=env,
        )
        assert result.returncode != 0

    def test_verify_detects_reordered_lemmas(self, manual_file: Path, tmp_path: Path):
        work_dir = self._setup_split(manual_file, tmp_path)
        _prelude, lemmas = parse_manual_file(manual_file.read_text())
        reordered = SAMPLE_PRELUDE + str(lemmas[1]["block"]) + str(lemmas[0]["block"]) + str(lemmas[2]["block"])
        manual_file.write_text(reordered, encoding="utf-8")
        env = self._fake_coqc_env(tmp_path)
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "verify_manual_goals.py"),
             str(work_dir / "manifest.json"), "--keep-workdir"],
            capture_output=True, text=True, env=env,
        )
        assert result.returncode != 0


# ---------------------------------------------------------------------------
# migrate_helpers_to_lib.py
# ---------------------------------------------------------------------------

class TestMigrateHelpersToLibScript:
    @staticmethod
    def _fake_coqc_env(tmp_path: Path) -> dict[str, str]:
        import os
        shim_dir = tmp_path / "shim"
        shim_dir.mkdir(exist_ok=True)
        shim = shim_dir / "coqc"
        shim.write_text(
            "#!/bin/sh\n"
            "for last; do true; done\n"
            "if [ -f \"$last\" ]; then touch \"${last%.v}.vo\"; fi\n"
            "exit 0\n",
            encoding="utf-8",
        )
        shim.chmod(0o755)
        env = os.environ.copy()
        env["PATH"] = str(shim_dir) + ":" + env.get("PATH", "")
        return env

    def test_migrates_new_helpers_to_lib_and_updates_manifest(self, tmp_path: Path):
        work = tmp_path / "work"
        case_deps = work / "case_deps"
        case_deps.mkdir(parents=True)
        (work / "_CoqProject").write_text("-Q case_deps MyLib\n", encoding="utf-8")

        seed = work / "foo_proof_manual.v"
        seed.write_text(
            "Require Import Coq.micromega.Psatz.\n"
            "Require Import MyLib.foo_lib.\n\n"
            "Lemma proof_of_goal : True.\n"
            "Proof. Admitted.\n",
            encoding="utf-8",
        )
        merged = work / "foo_merged.v"
        merged.write_text(
            "Require Import Coq.micromega.Psatz.\n"
            "Require Import MyLib.foo_lib.\n\n"
            "Require Import Coq.micromega.Lia.\n\n"
            "Lemma helper_goal : True.\n"
            "Proof. exact I. Qed.\n\n"
            "Lemma proof_of_goal : True.\n"
            "Proof. exact helper_goal. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = work / "foo_task_local_scratch_lib.v"
        task_local_scratch_lib.write_text("", encoding="utf-8")
        dep_lib = case_deps / "foo_lib.v"
        dep_lib.write_text("", encoding="utf-8")

        manifest = {
            "source_file": str(seed),
            "work_dir": str(work),
            "task_local_scratch_lib_file": str(task_local_scratch_lib),
            "merged_proof_manual_file": str(merged),
            "source_lemma_order": ["proof_of_goal"],
            "lemma_order": ["proof_of_goal"],
            "all_lemmas": [
                {
                    "name": "proof_of_goal",
                    "statement_header": "Lemma proof_of_goal : True.",
                }
            ],
            "lemmas": [
                {
                    "name": "proof_of_goal",
                    "statement_header": "Lemma proof_of_goal : True.",
                }
            ],
            "case_dependency_module_map": {"MyLib.foo_lib": str(dep_lib)},
        }
        manifest_path = work / "manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "migrate_helpers_to_lib.py"), str(manifest_path)],
            capture_output=True,
            text=True,
            env=self._fake_coqc_env(tmp_path),
        )
        assert result.returncode == 0, result.stderr

        updated = json.loads(manifest_path.read_text(encoding="utf-8"))
        migrated_manual = Path(updated["migrated_proof_manual_file"])
        migrated_manual_text = migrated_manual.read_text(encoding="utf-8")
        assert "Lemma helper_goal" not in migrated_manual_text
        assert "exact helper_goal" in migrated_manual_text
        task_local_scratch_lib_text = task_local_scratch_lib.read_text(encoding="utf-8")
        assert "Require Import Coq.micromega.Lia." in task_local_scratch_lib_text
        assert "Require Import Coq.micromega.Psatz." in task_local_scratch_lib_text
        assert "Lemma helper_goal" in task_local_scratch_lib_text
        assert task_local_scratch_lib.read_text(encoding="utf-8") == dep_lib.read_text(encoding="utf-8")
        assert updated["merged_proof_manual_file"] == updated["migrated_proof_manual_file"]
        assert updated["migrated_helper_lemmas"] == ["helper_goal"]
        assert updated["migrated_helper_imports"] == [
            "Require Import Coq.micromega.Lia.",
            "Require Import Coq.micromega.Psatz.",
        ]

        verify = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "verify_manual_goals.py"),
             str(manifest_path), "--keep-workdir"],
            capture_output=True,
            text=True,
            env=self._fake_coqc_env(tmp_path),
        )
        assert verify.returncode == 0, verify.stderr

    def test_migration_updates_readonly_overlay_and_recompiles_goal(self, tmp_path: Path):
        import os

        work = tmp_path / "work"
        case_deps = work / "case_deps"
        case_deps.mkdir(parents=True)
        (work / "_CoqProject").write_text("-Q case_deps MyLib\n", encoding="utf-8")

        shim_dir = tmp_path / "shim"
        shim_dir.mkdir()
        compile_log = tmp_path / "coqc.log"
        shim = shim_dir / "coqc"
        shim.write_text(
            "#!/bin/sh\n"
            "for last; do true; done\n"
            "printf '%s\\n' \"$last\" >> \"$COQC_LOG\"\n"
            "if [ -f \"$last\" ]; then touch \"${last%.v}.vo\"; fi\n"
            "exit 0\n",
            encoding="utf-8",
        )
        shim.chmod(0o755)
        env = os.environ.copy()
        env["PATH"] = str(shim_dir) + ":" + env.get("PATH", "")
        env["COQC_LOG"] = str(compile_log)

        seed = work / "foo_proof_manual.v"
        seed.write_text(
            "Require Import MyLib.foo_goal.\n"
            "Require Import MyLib.foo_lib.\n\n"
            "Lemma proof_of_goal : True.\n"
            "Proof. Admitted.\n",
            encoding="utf-8",
        )
        merged = work / "foo_merged.v"
        merged.write_text(
            "Require Import MyLib.foo_goal.\n"
            "Require Import MyLib.foo_lib.\n\n"
            "Lemma helper_goal : True.\n"
            "Proof. exact I. Qed.\n\n"
            "Lemma proof_of_goal : True.\n"
            "Proof. exact helper_goal. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = work / "foo_task_local_scratch_lib.v"
        task_local_scratch_lib.write_text("", encoding="utf-8")
        dep_lib = case_deps / "foo_lib.v"
        dep_goal = case_deps / "foo_goal.v"
        dep_lib.write_text("", encoding="utf-8")
        dep_goal.write_text("Require Import MyLib.foo_lib.\n", encoding="utf-8")
        dep_lib.chmod(0o444)
        dep_goal.chmod(0o444)

        manifest = {
            "source_file": str(seed),
            "work_dir": str(work),
            "task_local_scratch_lib_file": str(task_local_scratch_lib),
            "merged_proof_manual_file": str(merged),
            "source_lemma_order": ["proof_of_goal"],
            "lemma_order": ["proof_of_goal"],
            "all_lemmas": [
                {
                    "name": "proof_of_goal",
                    "statement_header": "Lemma proof_of_goal : True.",
                }
            ],
            "lemmas": [
                {
                    "name": "proof_of_goal",
                    "statement_header": "Lemma proof_of_goal : True.",
                }
            ],
            "case_dependency_module_map": {
                "MyLib.foo_goal": str(dep_goal),
                "MyLib.foo_lib": str(dep_lib),
            },
            "case_dependency_files": [str(dep_goal), str(dep_lib)],
        }
        manifest_path = work / "manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "migrate_helpers_to_lib.py"), str(manifest_path)],
            capture_output=True,
            text=True,
            env=env,
        )
        assert result.returncode == 0, result.stderr
        assert "Lemma helper_goal" in dep_lib.read_text(encoding="utf-8")
        assert not (dep_lib.stat().st_mode & 0o200)
        compiled = [Path(line).name for line in compile_log.read_text(encoding="utf-8").splitlines()]
        assert compiled.index("foo_lib.v") < compiled.index("foo_goal.v")

    def test_rejects_generated_case_import_during_migration(self, tmp_path: Path):
        work = tmp_path / "work"
        work.mkdir(parents=True)
        (work / "_CoqProject").write_text("-Q . MyLib\n", encoding="utf-8")

        seed = work / "foo_proof_manual.v"
        seed.write_text(
            "Require Import MyLib.foo_lib.\n\n"
            "Lemma proof_of_goal : True.\n"
            "Proof. Admitted.\n",
            encoding="utf-8",
        )
        merged = work / "foo_merged.v"
        merged.write_text(
            "Require Import MyLib.foo_lib.\n\n"
            "From SimpleC.EE.QCP_demos_LLM Require Import foo_goal.\n\n"
            "Lemma helper_goal : True.\n"
            "Proof. exact I. Qed.\n\n"
            "Lemma proof_of_goal : True.\n"
            "Proof. exact helper_goal. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = work / "foo_task_local_scratch_lib.v"
        task_local_scratch_lib.write_text("", encoding="utf-8")

        manifest = {
            "source_file": str(seed),
            "work_dir": str(work),
            "task_local_scratch_lib_file": str(task_local_scratch_lib),
            "merged_proof_manual_file": str(merged),
            "lemmas": [{"name": "proof_of_goal"}],
        }
        manifest_path = work / "manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "migrate_helpers_to_lib.py"), str(manifest_path)],
            capture_output=True,
            text=True,
            env=self._fake_coqc_env(tmp_path),
        )
        assert result.returncode != 0
        assert "generated case module" in result.stderr
