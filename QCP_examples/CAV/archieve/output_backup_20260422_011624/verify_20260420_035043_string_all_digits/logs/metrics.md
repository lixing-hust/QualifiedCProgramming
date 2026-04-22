# Verify Metrics

- Workspace: `verify_20260420_035043_string_all_digits`
- Target function: `string_all_digits`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_all_digits.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/string_all_digits.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260420_035043_string_all_digits.c`

## Symexec

- symexec_start: recorded in this run before invoking `/home/yangfp/QualifiedCProgramming/linux-binary/symexec`
- symexec_end: recorded immediately after the process exited
- symexec_elapsed: `0` seconds
- symexec_status: `0`
- symexec_log: `logs/qcp_run.log`

## Compile

- compile_elapsed: `5` seconds
- compile_status: `0`
- compile_log: `logs/compile_all.log`
- compiled_original_v: `original/string_all_digits.v`
- compiled_goal: `coq/generated/string_all_digits_goal.v`
- compiled_proof_auto: `coq/generated/string_all_digits_proof_auto.v`
- compiled_proof_manual: `coq/generated/string_all_digits_proof_manual.v`
- compiled_goal_check: `coq/generated/string_all_digits_goal_check.v`

## Proof And Cleanup

- manual_obligations_completed: `5`
- proof_manual_admitted_remaining: `0`
- proof_manual_new_axiom_remaining: `0`
- coq_non_v_artifacts_remaining_after_cleanup: `0`
- Experience updates: none

Final Result: Success

## External Codex Run `20260420_035043`

- Start time: `2026-04-20 03:50:43 +0800`
- End time: `2026-04-20 03:55:54 +0800`
- Wall-clock time (seconds): `311.17`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `1407363`
- Codex CLI cached input tokens: `1312000`
- Codex CLI output tokens: `13454`
- Codex CLI total tokens: `1420817`
- Approx workspace-authored text tokens: `6174`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_035043_string_all_digits/logs/codex_prompt_20260420_035043.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_035043_string_all_digits/logs/codex_stdout_20260420_035043.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_035043_string_all_digits/logs/codex_stderr_20260420_035043.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260420_035043_string_all_digits/logs/codex_last_message_20260420_035043.txt`
