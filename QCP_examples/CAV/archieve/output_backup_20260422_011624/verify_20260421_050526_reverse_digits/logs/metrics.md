# Verify Metrics

- Workspace: `verify_20260421_050526_reverse_digits`
- Target function: `reverse_digits`
- Input C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/reverse_digits.c`
- Input V: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/input/reverse_digits.v`
- Active annotated C: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/annotated/verify_20260421_050526_reverse_digits.c`
- Workspace-local helper: `coq/deps/reverse_digits_verify_aux.v`

## Symexec

- symexec_start: `2026-04-21 05:08:43 +0800`
- symexec_end: `2026-04-21 05:08:43 +0800`
- symexec_elapsed: `0`
- Symexec log: `logs/qcp_run.log`
- Result: success

## Coq Compile

- compile_start: `2026-04-21 05:21:04 +0800`
- compile_end: `2026-04-21 05:21:09 +0800`
- compiled_original_v: `original/reverse_digits.v`
- compiled_helper_v: `coq/deps/reverse_digits_verify_aux.v`
- compiled_goal: `coq/generated/reverse_digits_goal.v`
- compiled_proof_auto: `coq/generated/reverse_digits_proof_auto.v`
- compiled_proof_manual: `coq/generated/reverse_digits_proof_manual.v`
- compiled_goal_check: `coq/generated/reverse_digits_goal_check.v`
- Result: success

## Artifact Counts

- annotated_c_lines: `39`
- helper_v_lines: `7`
- goal_v_lines: `283`
- proof_manual_v_lines: `236`
- goal_check_v_lines: `7`

## Completion Checks

- proof_manual_admitted: `0`
- proof_manual_new_axiom: `0`
- coq_non_v_intermediates_after_cleanup: `0`
- Experience updates: none

Final Result: Success

## External Codex Run `20260421_050526`

- Start time: `2026-04-21 05:05:26 +0800`
- End time: `2026-04-21 05:22:44 +0800`
- Wall-clock time (seconds): `1038.24`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `18899735`
- Codex CLI cached input tokens: `18675584`
- Codex CLI output tokens: `38522`
- Codex CLI total tokens: `18938257`
- Approx workspace-authored text tokens: `4677`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_050526_reverse_digits/logs/codex_prompt_20260421_050526.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_050526_reverse_digits/logs/codex_stdout_20260421_050526.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_050526_reverse_digits/logs/codex_stderr_20260421_050526.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_050526_reverse_digits/logs/codex_last_message_20260421_050526.txt`
