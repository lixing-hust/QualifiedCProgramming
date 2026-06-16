#!/usr/bin/env python3
"""Tests for vc-proving worker scripts and the lib recompilation guarantee."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent

from manual_goal_utils import (
    _find_coq_project,
    _parse_coq_project_flags,
    check_rocq_file,
    check_rocq_file_with_deps,
)


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
"""

SAMPLE_LIB = """\
Definition foo := 1.
"""


@pytest.fixture
def coq_project(tmp_path: Path) -> Path:
    """Create a directory with _CoqProject."""
    (tmp_path / "_CoqProject").write_text("-Q . MyLib\n", encoding="utf-8")
    return tmp_path


@pytest.fixture
def nested_coq_project(tmp_path: Path) -> Path:
    """Create a nested directory structure with _CoqProject at the top."""
    (tmp_path / "_CoqProject").write_text("-Q . MyLib\n-R foo Bar\n", encoding="utf-8")
    sub = tmp_path / "a" / "b" / "c"
    sub.mkdir(parents=True)
    return sub


@pytest.fixture
def manual_and_lib(tmp_path: Path) -> tuple[Path, Path, Path]:
    """Set up a manual file, lib file, and _CoqProject. Returns (manual, lib, work_dir)."""
    (tmp_path / "_CoqProject").write_text("-Q . MyLib\n", encoding="utf-8")

    vcs_dir = tmp_path / "output" / "gen" / "vcs"
    vcs_dir.mkdir(parents=True)

    manual = vcs_dir / "test_manual.v"
    manual.write_text(SAMPLE_MANUAL, encoding="utf-8")

    lib = vcs_dir / "test_rel_lib.v"
    lib.write_text(SAMPLE_LIB, encoding="utf-8")

    return manual, lib, tmp_path


def _fake_coqc_shim(tmp_path: Path) -> Path:
    """Create a fake coqc that always succeeds and write a .vo file."""
    shim_dir = tmp_path / "shim"
    shim_dir.mkdir(exist_ok=True)
    shim = shim_dir / "coqc"
    # The shim creates a .vo file alongside the input .v to simulate compilation
    shim.write_text(
        '#!/bin/sh\n'
        '# Find the .v file argument (last arg)\n'
        'for last; do true; done\n'
        'if [ -f "$last" ]; then\n'
        '  vo="${last%.v}.vo"\n'
        '  touch "$vo"\n'
        'fi\n'
        'exit 0\n'
    )
    shim.chmod(0o755)
    return shim_dir


def _fake_coqc_env(shim_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    env["PATH"] = str(shim_dir) + ":" + env.get("PATH", "")
    return env


# ---------------------------------------------------------------------------
# _find_coq_project resolution
# ---------------------------------------------------------------------------

class TestCoqProjectResolution:
    def test_finds_in_same_dir(self, coq_project: Path):
        assert _find_coq_project(coq_project) == coq_project

    def test_finds_walking_up(self, nested_coq_project: Path):
        """Should walk up from a/b/c to find _CoqProject at the root."""
        root = nested_coq_project.parents[2]  # tmp_path
        assert _find_coq_project(nested_coq_project) == root

    def test_fails_when_not_found(self, tmp_path: Path):
        """No _CoqProject anywhere — should exit."""
        lonely = tmp_path / "no_project"
        lonely.mkdir()
        with pytest.raises(SystemExit, match="_CoqProject not found"):
            _find_coq_project(lonely)

    def test_picks_nearest(self, tmp_path: Path):
        """If both parent and child have _CoqProject, should find the nearest (child)."""
        (tmp_path / "_CoqProject").write_text("-Q . Top\n")
        child = tmp_path / "sub"
        child.mkdir()
        (child / "_CoqProject").write_text("-Q . Sub\n")
        assert _find_coq_project(child) == child

    def test_parses_flags_correctly(self, tmp_path: Path):
        (tmp_path / "_CoqProject").write_text(
            "# comment\n"
            "-Q . MyLib\n"
            "\n"
            "-R extra ExtraLib\n"
            "# another comment\n",
            encoding="utf-8",
        )
        flags = _parse_coq_project_flags(tmp_path)
        assert flags == ["-Q", ".", "MyLib", "-R", "extra", "ExtraLib"]

    def test_parses_empty_project(self, tmp_path: Path):
        (tmp_path / "_CoqProject").write_text("# only comments\n\n")
        flags = _parse_coq_project_flags(tmp_path)
        assert flags == []

    def test_parses_quoted_empty_string(self, tmp_path: Path):
        """Handles -Q /path "" correctly (strips quotes)."""
        (tmp_path / "_CoqProject").write_text('-Q /some/path ""\n')
        flags = _parse_coq_project_flags(tmp_path)
        assert flags == ["-Q", "/some/path", ""]

    def test_parses_quoted_name(self, tmp_path: Path):
        (tmp_path / "_CoqProject").write_text('-Q . "My Lib"\n')
        flags = _parse_coq_project_flags(tmp_path)
        assert flags == ["-Q", ".", "My Lib"]


# ---------------------------------------------------------------------------
# check_rocq_file — coqc compilation
# ---------------------------------------------------------------------------

class TestCheckRocqFile:
    def test_compiles_successfully(self, coq_project: Path):
        vfile = coq_project / "test.v"
        vfile.write_text("Definition x := 1.\n", encoding="utf-8")
        completed = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")
        with patch("manual_goal_utils.subprocess.run", return_value=completed) as mock_run:
            check_rocq_file(vfile)
        # Verify coqc was called with correct flags
        call_args = mock_run.call_args
        cmd = call_args[0][0]
        assert cmd[0] == "coqc"
        assert "-Q" in cmd
        assert str(vfile.resolve()) in cmd

    def test_passes_coq_project_flags(self, tmp_path: Path):
        (tmp_path / "_CoqProject").write_text("-Q . MyLib\n-R foo Bar\n")
        vfile = tmp_path / "test.v"
        vfile.write_text("Definition x := 1.\n")
        completed = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")
        with patch("manual_goal_utils.subprocess.run", return_value=completed) as mock_run:
            check_rocq_file(vfile)
        cmd = mock_run.call_args[0][0]
        # Flags should appear in order
        q_idx = cmd.index("-Q")
        assert cmd[q_idx + 1] == "."
        assert cmd[q_idx + 2] == "MyLib"
        r_idx = cmd.index("-R")
        assert cmd[r_idx + 1] == "foo"
        assert cmd[r_idx + 2] == "Bar"

    def test_cwd_is_coqproject_root(self, tmp_path: Path):
        (tmp_path / "_CoqProject").write_text("-Q . MyLib\n")
        sub = tmp_path / "sub"
        sub.mkdir()
        vfile = sub / "test.v"
        vfile.write_text("Definition x := 1.\n")
        completed = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")
        with patch("manual_goal_utils.subprocess.run", return_value=completed) as mock_run:
            check_rocq_file(vfile)
        # cwd should be the _CoqProject root, not the file's directory
        assert mock_run.call_args.kwargs["cwd"] == tmp_path

    def test_failure_prints_errors(self, coq_project: Path, capsys):
        vfile = coq_project / "bad.v"
        vfile.write_text("bad syntax\n")
        completed = subprocess.CompletedProcess(
            args=[], returncode=1, stdout="", stderr="Error: Syntax error on line 1\n"
        )
        with patch("manual_goal_utils.subprocess.run", return_value=completed):
            with pytest.raises(SystemExit):
                check_rocq_file(vfile)
        captured = capsys.readouterr()
        assert "Syntax error" in captured.err


# ---------------------------------------------------------------------------
# check_rocq_file_with_deps — lib recompilation guarantee
# ---------------------------------------------------------------------------

class TestLibRecompilation:
    def test_recompiles_stale_lib(self, coq_project: Path):
        """If lib .vo is older than lib .v, lib must be recompiled before the goal."""
        lib = coq_project / "lib.v"
        lib.write_text("Definition foo := 1.\n")
        goal = coq_project / "goal.v"
        goal.write_text("Require Import lib.\nLemma g : True. Proof. exact I. Qed.\n")

        # Create a stale .vo
        vo = lib.with_suffix(".vo")
        vo.write_text("stale")
        # Backdate the .vo so it's older than the .v
        old_time = time.time() - 100
        os.utime(vo, (old_time, old_time))

        compile_order: list[str] = []

        def fake_run(cmd, **kwargs):
            # Record which file was compiled
            vfile = cmd[-1]
            compile_order.append(Path(vfile).name)
            # Touch .vo to simulate compilation
            Path(vfile).with_suffix(".vo").write_text("compiled")
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

        with patch("manual_goal_utils.subprocess.run", side_effect=fake_run):
            check_rocq_file_with_deps(goal, dep_files=[lib])

        # lib.v must be compiled before goal.v
        assert compile_order == ["lib.v", "goal.v"]

    def test_skips_fresh_lib(self, coq_project: Path):
        """If lib .vo is newer than lib .v, lib should NOT be recompiled."""
        lib = coq_project / "lib.v"
        lib.write_text("Definition foo := 1.\n")
        goal = coq_project / "goal.v"
        goal.write_text("Lemma g : True. Proof. exact I. Qed.\n")

        # Create a fresh .vo (newer than .v)
        vo = lib.with_suffix(".vo")
        vo.write_text("fresh")
        future_time = time.time() + 100
        os.utime(vo, (future_time, future_time))

        compile_order: list[str] = []

        def fake_run(cmd, **kwargs):
            vfile = cmd[-1]
            compile_order.append(Path(vfile).name)
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

        with patch("manual_goal_utils.subprocess.run", side_effect=fake_run):
            check_rocq_file_with_deps(goal, dep_files=[lib])

        # Only goal should be compiled, not lib
        assert compile_order == ["goal.v"]

    def test_recompiles_when_no_vo_exists(self, coq_project: Path):
        """If lib has no .vo at all, it must be compiled."""
        lib = coq_project / "lib.v"
        lib.write_text("Definition foo := 1.\n")
        goal = coq_project / "goal.v"
        goal.write_text("Lemma g : True. Proof. exact I. Qed.\n")

        compile_order: list[str] = []

        def fake_run(cmd, **kwargs):
            vfile = cmd[-1]
            compile_order.append(Path(vfile).name)
            Path(vfile).with_suffix(".vo").write_text("compiled")
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

        with patch("manual_goal_utils.subprocess.run", side_effect=fake_run):
            check_rocq_file_with_deps(goal, dep_files=[lib])

        assert compile_order == ["lib.v", "goal.v"]

    def test_no_deps_just_compiles_target(self, coq_project: Path):
        """With no dep_files, should behave like plain check_rocq_file."""
        goal = coq_project / "goal.v"
        goal.write_text("Lemma g : True. Proof. exact I. Qed.\n")

        compile_order: list[str] = []

        def fake_run(cmd, **kwargs):
            vfile = cmd[-1]
            compile_order.append(Path(vfile).name)
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

        with patch("manual_goal_utils.subprocess.run", side_effect=fake_run):
            check_rocq_file_with_deps(goal, dep_files=None)

        assert compile_order == ["goal.v"]

    def test_lib_compile_failure_propagates(self, coq_project: Path):
        """If lib fails to compile, the error should propagate — don't proceed to goal."""
        lib = coq_project / "lib.v"
        lib.write_text("bad lib\n")
        goal = coq_project / "goal.v"
        goal.write_text("Lemma g : True. Proof. exact I. Qed.\n")

        def fake_run(cmd, **kwargs):
            vfile = cmd[-1]
            if Path(vfile).name == "lib.v":
                return subprocess.CompletedProcess(
                    args=cmd, returncode=1, stdout="", stderr="Error in lib\n"
                )
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

        with patch("manual_goal_utils.subprocess.run", side_effect=fake_run):
            with pytest.raises(SystemExit):
                check_rocq_file_with_deps(goal, dep_files=[lib])


# ---------------------------------------------------------------------------
# Deprecated serial entrypoints
# ---------------------------------------------------------------------------

class TestDeprecatedSerialEntrypoints:
    def test_prepare_agent_is_disabled(self):
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "prepare_agent.py")],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 2
        assert "prepare_agent_concurrent.py" in result.stderr
        assert "must run through script-created worker-local manuals" in result.stderr

    def test_run_agent_is_disabled(self):
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / "run_agent.py")],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 2
        assert "run_agent_concurrent.py" in result.stderr
        assert "must run through script-created worker-local manuals" in result.stderr


# ---------------------------------------------------------------------------
# _goal_is_solved with lib deps
# ---------------------------------------------------------------------------

class TestRunAgentAdmitted:
    """Test that goals with Admitted are not considered solved."""

    def test_admitted_is_not_solved(self, coq_project: Path):
        from validate_and_merge import _goal_is_solved

        goal = coq_project / "goal.v"
        goal.write_text("Lemma g : True.\nProof. Admitted.\n")

        # Should return False without even trying to compile
        result = _goal_is_solved(goal, None)
        assert result is False

    def test_qed_is_solved(self, coq_project: Path):
        from validate_and_merge import _goal_is_solved

        goal = coq_project / "goal.v"
        goal.write_text("Lemma g : True.\nProof. exact I. Qed.\n")

        def fake_run(cmd, **kwargs):
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

        with patch("manual_goal_utils.subprocess.run", side_effect=fake_run):
            result = _goal_is_solved(goal, None)
        assert result is True

    def test_admitted_in_prelude_is_not_solved(self, coq_project: Path):
        """Even if Admitted appears in a comment or prelude import, reject it."""
        from validate_and_merge import _goal_is_solved

        goal = coq_project / "goal.v"
        goal.write_text(
            "Require Import Foo.\n\n"
            "Lemma g : True.\nProof. Admitted.\n"
        )

        result = _goal_is_solved(goal, None)
        assert result is False


class TestRunAgentLibDeps:
    """Test that run_agent recompiles lib before checking goals."""

    def test_goal_is_solved_recompiles_stale_lib(self, coq_project: Path):
        """_goal_is_solved should recompile lib if .vo is stale."""
        from validate_and_merge import _goal_is_solved

        lib = coq_project / "lib.v"
        lib.write_text("Definition foo := 1.\n")
        goal = coq_project / "goal.v"
        goal.write_text("Lemma g : True. Proof. exact I. Qed.\n")

        # Stale .vo
        vo = lib.with_suffix(".vo")
        vo.write_text("stale")
        old_time = time.time() - 100
        os.utime(vo, (old_time, old_time))

        compile_order: list[str] = []

        def fake_run(cmd, **kwargs):
            vfile = cmd[-1]
            compile_order.append(Path(vfile).name)
            Path(vfile).with_suffix(".vo").write_text("compiled")
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

        with patch("manual_goal_utils.subprocess.run", side_effect=fake_run):
            result = _goal_is_solved(goal, lib)

        assert result is True
        assert compile_order == ["lib.v", "goal.v"]

    def test_goal_is_solved_without_lib(self, coq_project: Path):
        """_goal_is_solved with no lib should just compile the goal."""
        from validate_and_merge import _goal_is_solved

        goal = coq_project / "goal.v"
        goal.write_text("Lemma g : True. Proof. exact I. Qed.\n")

        compile_order: list[str] = []

        def fake_run(cmd, **kwargs):
            vfile = cmd[-1]
            compile_order.append(Path(vfile).name)
            return subprocess.CompletedProcess(args=cmd, returncode=0, stdout="", stderr="")

        with patch("manual_goal_utils.subprocess.run", side_effect=fake_run):
            result = _goal_is_solved(goal, None)

        assert result is True
        assert compile_order == ["goal.v"]
