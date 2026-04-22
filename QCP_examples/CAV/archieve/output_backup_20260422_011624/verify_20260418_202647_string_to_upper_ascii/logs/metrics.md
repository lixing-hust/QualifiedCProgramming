# Verify Metrics

- Workspace: `verify_20260418_202647_string_to_upper_ascii`
- Function: `string_to_upper_ascii`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_to_upper_ascii.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_to_upper_ascii.v`
- Annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_202647_string_to_upper_ascii.c`

## Annotation

- Annotation changes required: yes
- Annotation artifacts:
  - `logs/annotation_reasoning.md`
  - updated active annotated copy with one loop invariant and one exit assertion

## Symexec

- symexec_start: `not separately timestamped in the workspace`
- symexec_end: `not separately timestamped in the workspace`
- symexec_elapsed: `not separately recorded`
- symexec_result: `Success`
- symexec_log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_202647_string_to_upper_ascii/logs/qcp_run.log`

## Proof

- Manual proof required: yes
- proof_reasoning_log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_202647_string_to_upper_ascii/logs/proof_reasoning.md`
- proof_manual_status: `Fail`
- goal_check_status: `Fail`
- latest compile log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_202647_string_to_upper_ascii/logs/proof_manual_compile.log`

## Compile Replay

- original `<name>.v`: `pass`
- `goal.v`: `pass`
- `proof_auto.v`: `pass`
- `proof_manual.v`: `fail`
- `goal_check.v`: `not reached in a successful replay because proof_manual.v failed`

## Cleanup

- coq_non_v_artifacts_removed: `yes`

## Experience

- Experience updates: none

Final Result: Fail

## External Codex Run `20260418_202647`

- Start time: `2026-04-18 20:26:47 +0800`
- End time: `2026-04-18 20:43:44 +0800`
- Wall-clock time (seconds): `1016.82`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `11258138`
- Codex CLI cached input tokens: `11098368`
- Codex CLI output tokens: `42643`
- Codex CLI total tokens: `11300781`
- Approx workspace-authored text tokens: `22635`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_202647_string_to_upper_ascii/logs/codex_prompt_20260418_202647.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_202647_string_to_upper_ascii/logs/codex_stdout_20260418_202647.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_202647_string_to_upper_ascii/logs/codex_stderr_20260418_202647.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_202647_string_to_upper_ascii/logs/codex_last_message_20260418_202647.txt`
