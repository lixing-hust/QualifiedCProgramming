# Verify Metrics

## Manual Verify Run

- Start time: `2026-04-20 03:28:42 +0800` from workspace name.
- End time: `2026-04-20 03:38:31 +0800`.
- Workspace: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032842_string_count_not_char`.
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_count_not_char.c`.
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_count_not_char.v`.
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_032842_string_count_not_char.c`.

## Symexec

- symexec_start: `2026-04-20 03:31:16 +0800`.
- symexec_end: `2026-04-20 03:31:16 +0800`.
- symexec_elapsed: `<1s`.
- latest_symexec_status: `success`.
- Symexec log: `logs/qcp_run.log`.
- Generated files:
  - `coq/generated/string_count_not_char_goal.v`
  - `coq/generated/string_count_not_char_proof_auto.v`
  - `coq/generated/string_count_not_char_proof_manual.v`
  - `coq/generated/string_count_not_char_goal_check.v`

## Proof And Compile

- Manual proof lemmas completed: `5`.
- Final compile command: ordered `coqc` chain for original V, goal, proof_auto, proof_manual, and goal_check from `/home/yangfp/QualifiedCProgramming/SeparationLogic`.
- Compile result: `success`.
- Compile log: `logs/compile.log` (empty on final successful run).
- `proof_manual.v` check: no `Admitted.` and no new `Axiom`.
- `goal_check.v` compile: passed.
- Non-`.v` Coq intermediates: cleaned.

## Experience Updates

- Experience updates: none. The user required all work to stay inside the existing workspace, so repository-level experience documents were not modified.

Final Result: Success

## External Codex Run `20260420_032842`

- Start time: `2026-04-20 03:28:42 +0800`
- End time: `2026-04-20 03:39:32 +0800`
- Wall-clock time (seconds): `650.48`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `6006975`
- Codex CLI cached input tokens: `5878528`
- Codex CLI output tokens: `25217`
- Codex CLI total tokens: `6032192`
- Approx workspace-authored text tokens: `6351`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032842_string_count_not_char/logs/codex_prompt_20260420_032842.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032842_string_count_not_char/logs/codex_stdout_20260420_032842.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032842_string_count_not_char/logs/codex_stderr_20260420_032842.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_032842_string_count_not_char/logs/codex_last_message_20260420_032842.txt`
