#!/usr/bin/env python3
"""Tests for validate_and_merge.py proof_report.json refinement."""

from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from validate_and_merge import (
    _find_report_entry,
    _load_proof_report,
    _merge_worker_manuals,
    _validate_and_refine_entry,
    _write_proof_report,
)


# ---------------------------------------------------------------------------
# _load_proof_report
# ---------------------------------------------------------------------------

class TestLoadProofReport:
    def test_valid(self, tmp_path):
        report = [{"goal": "a", "status": "solved"}]
        (tmp_path / "proof_report.json").write_text(json.dumps(report))
        assert _load_proof_report(tmp_path) == report

    def test_missing(self, tmp_path):
        assert _load_proof_report(tmp_path) == []

    def test_invalid_json(self, tmp_path):
        (tmp_path / "proof_report.json").write_text("broken")
        assert _load_proof_report(tmp_path) == []


# ---------------------------------------------------------------------------
# _find_report_entry
# ---------------------------------------------------------------------------

class TestFindReportEntry:
    def test_found(self):
        report = [{"goal": "a", "status": "solved"}, {"goal": "b", "status": "admitted"}]
        assert _find_report_entry("b", report)["status"] == "admitted"

    def test_not_found(self):
        assert _find_report_entry("c", [{"goal": "a", "status": "solved"}]) is None


# ---------------------------------------------------------------------------
# _validate_and_refine_entry
# ---------------------------------------------------------------------------

class TestValidateAndRefineEntry:
    def test_solved_confirmed(self, tmp_path):
        """Agent says solved, file has Qed, compiles → solved."""
        f = tmp_path / "goal.v"
        f.write_text("Lemma a : True.\nProof. auto. Qed.\n")
        agent = {"goal": "a", "status": "solved"}
        with patch("validate_and_merge._goal_is_solved", return_value=True):
            result = _validate_and_refine_entry("a", f, None, agent)
        assert result["status"] == "solved"
        assert "report" not in result

    def test_solved_but_doesnt_compile(self, tmp_path):
        """Agent says solved, but file doesn't compile → broken."""
        f = tmp_path / "goal.v"
        f.write_text("Lemma a : True.\nProof. bad_tactic. Qed.\n")
        agent = {"goal": "a", "status": "solved"}
        with patch("validate_and_merge._goal_is_solved", return_value=False):
            result = _validate_and_refine_entry("a", f, None, agent)
        assert result["status"] == "broken"
        assert "does not compile" in result["report"]

    def test_admitted_confirmed(self, tmp_path):
        """Agent says admitted, file has Admitted → admitted with report."""
        f = tmp_path / "goal.v"
        f.write_text("Lemma a : True.\nProof. Admitted.\n")
        agent = {"goal": "a", "status": "admitted", "report": "tactic failed"}
        result = _validate_and_refine_entry("a", f, None, agent)
        assert result["status"] == "admitted"
        assert result["report"] == "tactic failed"

    def test_admitted_no_agent_entry(self, tmp_path):
        """File has Admitted but no agent report → admitted with empty report."""
        f = tmp_path / "goal.v"
        f.write_text("Lemma a : True.\nProof. Admitted.\n")
        result = _validate_and_refine_entry("a", f, None, None)
        assert result["status"] == "admitted"
        assert result["report"] == ""

    def test_missing_from_report_doesnt_compile(self, tmp_path):
        """Goal not in agent report, file doesn't compile → broken."""
        f = tmp_path / "goal.v"
        f.write_text("Lemma a : True.\nProof.\n")  # incomplete
        with patch("validate_and_merge._goal_is_solved", return_value=False):
            result = _validate_and_refine_entry("a", f, None, None)
        assert result["status"] == "broken"


# ---------------------------------------------------------------------------
# _write_proof_report
# ---------------------------------------------------------------------------

class TestWriteProofReport:
    def test_writes_json(self, tmp_path):
        entries = [
            {"goal": "a", "status": "solved"},
            {"goal": "b", "status": "admitted", "report": "failed"},
        ]
        path = _write_proof_report(tmp_path, entries)
        assert path.exists()
        data = json.loads(path.read_text())
        assert len(data) == 2
        assert data[0]["status"] == "solved"
        assert data[1]["report"] == "failed"


# ---------------------------------------------------------------------------
# _merge_worker_manuals helper-lib boundary
# ---------------------------------------------------------------------------

class TestMergeWorkerManualsHelperLib:
    def _manifest_with_worker(self, tmp_path, worker_manual_text, helper_lib_text):
        source = tmp_path / "source_manual.v"
        source.write_text(
            "Lemma proof_of_goal : True.\nProof. Admitted.\n",
            encoding="utf-8",
        )
        work = tmp_path / "work"
        group = work / "group_00"
        group.mkdir(parents=True)
        worker_manual = group / "source_manual.v"
        worker_manual.write_text(worker_manual_text, encoding="utf-8")
        helper_lib = group / "worker_helper_scratch_lib.v"
        helper_lib.write_text(helper_lib_text, encoding="utf-8")
        return {
            "source_file": str(source),
            "work_dir": str(work),
            "lemmas": [{"name": "proof_of_goal"}],
            "groups": [],
        }, {
            "work_dir": str(group),
            "worker_manual_file": str(worker_manual),
            "worker_helper_scratch_lib_file": str(helper_lib),
            "goals": [{"name": "proof_of_goal"}],
        }

    def test_collects_helper_from_worker_helper_scratch_lib(self, tmp_path):
        manifest, group_entry = self._manifest_with_worker(
            tmp_path,
            "Lemma proof_of_goal : True.\nProof. exact helper_goal. Qed.\n",
            "Lemma helper_goal : True.\nProof. exact I. Qed.\n",
        )
        (Path(manifest["work_dir"]) / "groups_manifest.json").write_text(
            json.dumps([group_entry]),
            encoding="utf-8",
        )
        with patch("validate_and_merge._compile_manual_with_deps", return_value=True):
            merged, report = _merge_worker_manuals(manifest, None, None)
        assert "Lemma helper_goal" in merged
        assert "exact helper_goal" in merged
        assert report == [{"goal": "proof_of_goal", "status": "solved"}]

    def test_collects_helper_import_from_worker_helper_scratch_lib(self, tmp_path):
        manifest, group_entry = self._manifest_with_worker(
            tmp_path,
            "Lemma proof_of_goal : True.\nProof. exact helper_goal. Qed.\n",
            "Require Import Coq.micromega.Lia.\n\n"
            "Lemma helper_goal : True.\nProof. exact I. Qed.\n",
        )
        (Path(manifest["work_dir"]) / "groups_manifest.json").write_text(
            json.dumps([group_entry]),
            encoding="utf-8",
        )
        with patch("validate_and_merge._compile_manual_with_deps", return_value=True):
            merged, report = _merge_worker_manuals(manifest, None, None)
        assert "(* Helper imports collected from worker_helper_scratch_lib. *)" in merged
        assert "Require Import Coq.micromega.Lia." in merged
        assert "Lemma helper_goal" in merged
        assert report == [{"goal": "proof_of_goal", "status": "solved"}]

    def test_rejects_generated_case_import_in_worker_helper_scratch_lib(self, tmp_path):
        manifest, group_entry = self._manifest_with_worker(
            tmp_path,
            "Lemma proof_of_goal : True.\nProof. exact helper_goal. Qed.\n",
            "From SimpleC.EE.QCP_demos_LLM Require Import foo_goal.\n\n"
            "Lemma helper_goal : True.\nProof. exact I. Qed.\n",
        )
        (Path(manifest["work_dir"]) / "groups_manifest.json").write_text(
            json.dumps([group_entry]),
            encoding="utf-8",
        )
        with patch("validate_and_merge._compile_manual_with_deps", return_value=True):
            merged, report = _merge_worker_manuals(manifest, None, None)
        assert "Lemma helper_goal" not in merged
        assert report[0]["status"] == "broken"
        assert "generated case module" in report[0]["report"]

    def test_rejects_helper_added_to_worker_manual(self, tmp_path):
        manifest, group_entry = self._manifest_with_worker(
            tmp_path,
            "Lemma helper_goal : True.\nProof. exact I. Qed.\n\n"
            "Lemma proof_of_goal : True.\nProof. exact helper_goal. Qed.\n",
            "",
        )
        (Path(manifest["work_dir"]) / "groups_manifest.json").write_text(
            json.dumps([group_entry]),
            encoding="utf-8",
        )
        with patch("validate_and_merge._compile_manual_with_deps", return_value=True):
            merged, report = _merge_worker_manuals(manifest, None, None)
        assert "Lemma helper_goal" not in merged
        assert report[0]["status"] == "broken"
        assert "worker_helper_scratch_lib" in report[0]["report"]
