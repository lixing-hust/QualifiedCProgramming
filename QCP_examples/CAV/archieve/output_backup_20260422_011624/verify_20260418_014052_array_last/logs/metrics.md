# Verify Metrics

## Run Summary

- Workspace: `output/verify_20260418_014052_array_last`
- Function: `array_last`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/array_last.c`
- Input V: `<not provided>`
- Annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_014052_array_last.c`
- Annotation edits applied: `0`
- Manual proof edits applied: `0`

## Symexec

- symexec_start: `2026-04-18 01:42:18 +0800`
- symexec_end: `2026-04-18 01:42:18 +0800`
- symexec_elapsed: `<1s`
- command: `/home/yangfp/QualifiedCProgramming/linux-binary/symexec --goal-file=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_014052_array_last/coq/generated/array_last_goal.v --proof-auto-file=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_014052_array_last/coq/generated/array_last_proof_auto.v --proof-manual-file=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_014052_array_last/coq/generated/array_last_proof_manual.v --coq-logic-path=SimpleC.EE.CAV.verify_20260418_014052_array_last -slp /home/yangfp/QualifiedCProgramming/QCP_examples/ SimpleC.EE --input-file=/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260418_014052_array_last.c --no-exec-info`
- log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_014052_array_last/logs/qcp_run.log`

## Compile

- compile_workdir: `/home/yangfp/QualifiedCProgramming/SeparationLogic`
- compile_end: `2026-04-18 01:43:05 +0800`
- compiled_files:
  - `array_last_goal.v`
  - `array_last_proof_auto.v`
  - `array_last_proof_manual.v`
  - `array_last_goal_check.v`
- result: success

## Cleanup

- removed_non_v_intermediates: `yes`
- remaining_generated_files:
  - `array_last_goal.v`
  - `array_last_proof_auto.v`
  - `array_last_proof_manual.v`
  - `array_last_goal_check.v`

## External Codex Run `20260418_014052`

- Start time: `2026-04-18 01:40:52 +0800`
- End time: `2026-04-18 01:43:42 +0800`
- Wall-clock time (seconds): `169.92`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `922948`
- Codex CLI cached input tokens: `875392`
- Codex CLI output tokens: `7268`
- Codex CLI total tokens: `930216`
- Approx workspace-authored text tokens: `949`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_014052_array_last/logs/codex_prompt_20260418_014052.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_014052_array_last/logs/codex_stdout_20260418_014052.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_014052_array_last/logs/codex_stderr_20260418_014052.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260418_014052_array_last/logs/codex_last_message_20260418_014052.txt`
