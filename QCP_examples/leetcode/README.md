# LeetCode Verification Workspace

This directory is for per-problem verification workspaces.

## Layout

- `input/`: raw source files, one input program per `.c`
- `output/`: generated `workspace_<timestamp>_<stem>/`
- `scripts/make_verification_workspace.py`: workspace generator and QCP runner
- `doc/`: local documentation

## Main Command

```bash
python3 scripts/make_verification_workspace.py init input/<name>.c
```

## Codex Driver

To delegate end-to-end proof construction to an external Codex CLI process and record external
wall-clock / token usage into the workspace logs, run:

```bash
python3 run_codex_formal_proof.py input/<name>.c <function_name>
```

The script will:

- create `output/workspace_<timestamp>_<name>/`
- ask Codex to read [SKILL.md](/home/yangfp/QualifiedCProgramming/QCP_examples/leetcode/SKILL.md) and work inside that workspace
- seed `logs/workspace_fingerprint.json` with stable metadata for retrieval
- require Codex to fill `logs/workspace_fingerprint.json` with a semantic description and structured keywords
- require Codex to write natural-language reasoning to `logs/annotation_reasoning.md` before annotation
- require Codex to write natural-language reasoning to `logs/proof_reasoning.md` before manual proof work
- capture `codex exec --json` stdout/stderr under `logs/`
- append external timing and token metrics to `logs/proof_metrics.md`

That command creates:

```text
output/workspace_<timestamp>_<name>/
```

with:

- copied raw `.c/.h`
- editable annotated source tree
- copied strategy files when found
- best-effort copied Coq `.v` references when found
- `coq/generated/<name>_goal.v`
- `coq/generated/<name>_proof_auto.v`
- `coq/generated/<name>_proof_manual.v`
- `coq/generated/<name>_goal_check.v`
- `coq/defs/<name>_defs.v`
- `run_qcp.sh`
- `manifest.json`

## QCP Generation

After you annotate the copied source in `annotated/`, run:

```bash
python3 scripts/make_verification_workspace.py run-qcp output/workspace_<timestamp>_<name> --symexec /path/to/symexec
```

Or directly:

```bash
output/workspace_<timestamp>_<name>/run_qcp.sh
```

If the default repo binary is not executable, pass `--symexec` explicitly.
