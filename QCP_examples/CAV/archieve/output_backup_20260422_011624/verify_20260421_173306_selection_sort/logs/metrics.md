# Metrics

- workspace: `output/verify_20260421_173306_selection_sort`
- input_c: `input/selection_sort.c`
- input_v: `input/selection_sort.v`
- target_function: `selection_sort`
- annotated_c: `annotated/verify_20260421_173306_selection_sort.c`
- symexec_start: `2026-04-21T17:36:22+08:00`
- symexec_end: `2026-04-21T17:36:26+08:00`
- symexec_elapsed: `4s`
- symexec_status: `success`
- coq_compile_status: `goal`, `proof_auto`, `proof_manual`, and `goal_check` compile with current files
- proof_manual_admitted_remaining: `proof_of_selection_sort_entail_wit_4`
- coq_cleanup: removed non-`.v` files under workspace `coq/`
- Experience updates: none

Final Result: Fail

## External Codex Run `20260421_173306`

- Start time: `2026-04-21 17:33:06 +0800`
- End time: `2026-04-21 17:41:31 +0800`
- Wall-clock time (seconds): `504.92`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `4747250`
- Codex CLI cached input tokens: `4603136`
- Codex CLI output tokens: `19167`
- Codex CLI total tokens: `4766417`
- Approx workspace-authored text tokens: `8461`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_173306_selection_sort/logs/codex_prompt_20260421_173306.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_173306_selection_sort/logs/codex_stdout_20260421_173306.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_173306_selection_sort/logs/codex_stderr_20260421_173306.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_173306_selection_sort/logs/codex_last_message_20260421_173306.txt`

## Retry Verification Completion

- retry_compile_status: `goal`, `proof_auto`, `proof_manual`, and `goal_check` compile with current files
- proof_manual_admitted_remaining: none
- proof_manual_axiom_added: none
- goal_check_status: success
- coq_cleanup: removed non-`.v` files under workspace `coq/`
- symexec_status_for_current_generated_files: success from existing latest run `2026-04-21T17:36:22+08:00` to `2026-04-21T17:36:26+08:00`; annotated C was not changed in this retry
- Experience updates: none

Final Result: Success

## External Codex Run `20260421_174131`

- Start time: `2026-04-21 17:41:31 +0800`
- End time: `2026-04-21 18:06:28 +0800`
- Wall-clock time (seconds): `1497.03`
- Token source: exact Codex CLI `turn.completed.usage` values from `codex exec --json`.
- Codex CLI input tokens: `24502000`
- Codex CLI cached input tokens: `24246784`
- Codex CLI output tokens: `50799`
- Codex CLI total tokens: `24552799`
- Approx workspace-authored text tokens: `11368`
- Prompt file: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_173306_selection_sort/logs/codex_prompt_20260421_174131.txt`
- Codex stdout JSONL: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_173306_selection_sort/logs/codex_stdout_20260421_174131.jsonl`
- Codex stderr log: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_173306_selection_sort/logs/codex_stderr_20260421_174131.log`
- Codex last message: `/home/yangfp/QualifiedCProgramming/QCP_examples/CAV/output/verify_20260421_173306_selection_sort/logs/codex_last_message_20260421_174131.txt`
