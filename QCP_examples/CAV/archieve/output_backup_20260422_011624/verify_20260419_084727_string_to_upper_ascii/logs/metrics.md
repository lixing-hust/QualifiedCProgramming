# Verify Metrics

- workspace: `output/verify_20260419_084727_string_to_upper_ascii`
- target_function: `string_to_upper_ascii`
- annotated_c: `annotated/verify_20260419_084727_string_to_upper_ascii.c`
- input_c: `input/string_to_upper_ascii.c`
- input_v: `input/string_to_upper_ascii.v`
- symexec_start: 2026-04-19 manual run
- symexec_end: 2026-04-19 manual run
- symexec_elapsed: <1s as measured by the shell wrapper
- symexec_status: success
- generated_files:
  - `coq/generated/string_to_upper_ascii_goal.v`
  - `coq/generated/string_to_upper_ascii_proof_auto.v`
  - `coq/generated/string_to_upper_ascii_proof_manual.v`
  - `coq/generated/string_to_upper_ascii_goal_check.v`
- manual_proof_obligations: 5
- manual_proof_status: success
- compile_status:
  - `original/string_to_upper_ascii.v`: success
  - `coq/generated/string_to_upper_ascii_goal.v`: success
  - `coq/generated/string_to_upper_ascii_proof_auto.v`: success
  - `coq/generated/string_to_upper_ascii_proof_manual.v`: success
  - `coq/generated/string_to_upper_ascii_goal_check.v`: success
- proof_manual_forbidden_tokens: no `Admitted.` and no `Axiom`
- cleanup: deleted non-`.v` files under `coq/`
- Experience updates: none

Final Result: Success

## External Codex Run `20260419_084727`

- Start time: `2026-04-19 08:47:27 +0800`
- End time: `2026-04-19 09:06:08 +0800`
- Wall-clock time (seconds): `1120.57`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `21497346`
- Codex CLI cached input tokens: `21100032`
- Codex CLI output tokens: `42826`
- Codex CLI total tokens: `21540172`
- Approx workspace-authored text tokens: `8380`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_084727_string_to_upper_ascii/logs/codex_prompt_20260419_084727.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_084727_string_to_upper_ascii/logs/codex_stdout_20260419_084727.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_084727_string_to_upper_ascii/logs/codex_stderr_20260419_084727.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260419_084727_string_to_upper_ascii/logs/codex_last_message_20260419_084727.txt`
